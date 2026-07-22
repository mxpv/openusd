//! Composed layer-stack identity and storage, the composed-view half of
//! composition's layer model.
//!
//! A [`LayerId`] names a physical loaded layer (owned by
//! [`layer_graph`](super::layer_graph)); a [`LayerStackId`] names a composed view
//! of layers — the stage root stack, or a reference/payload target's sublayer
//! stack under a particular expression-variable override source. Every composed
//! stack, root included, is a [`LayerStackInstance`] in the [`LayerStackRegistry`]
//! addressed by an opaque [`LayerStackId`]; composition (`Node`, duplicate
//! detection, edit-target info, invalidation, relocate queries) never branches on
//! what kind of stack a handle names — the registry owns the kind, root, source,
//! and members.
//!
//! This module is identity and storage only. Composing an instance's members
//! needs the layers, which `layer_graph` owns, so it builds them and hands them
//! here (see `LayerGraph::build_stack_members`).

use std::collections::{HashMap, HashSet};

use crate::sdf::{LayerOffset, Value};

use super::layer_graph::LayerId;

/// An opaque handle to a composed layer stack within one
/// [`LayerGraph`](super::layer_graph::LayerGraph) — an index into its
/// [`LayerStackRegistry`].
///
/// Every composition [`Node`](super::prim_graph::Node) stores this `Copy` handle
/// instead of cloning the stack's members; resolve it back to them with
/// [`LayerGraph::layer_stack`](super::layer_graph::LayerGraph::layer_stack). The
/// handle is stable for the life of the graph even as a mute or `subLayers`
/// rebuild changes the resolved members. It is not a cross-stage identity key
/// (contrast `LayerStackIdentifier`); it is meaningful only within the graph that
/// minted it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct LayerStackId(u32);

impl LayerStackId {
    /// The stage root layer stack — always instance 0, minted when the graph is
    /// finalized.
    pub(crate) const ROOT: LayerStackId = LayerStackId(0);

    /// Wraps a raw index, for tests that build synthetic handles for comparison;
    /// production handles come from the registry.
    #[cfg(test)]
    pub(crate) const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    fn idx(self) -> usize {
        self.0 as usize
    }
}

/// The layer stack whose composed expression variables seed another stack's own
/// — the Rust analog of C++ `PcpExpressionVariablesSource`: the stage root
/// stack (C++'s null source) or a contextual instance. A target stack's
/// identity key carries one ([`LayerStackKey::Target`]), and every instance
/// stores the source of its own composed variables
/// ([`LayerStackRegistry::vars_source`]), so an arc keys its target by where the
/// arc-carrying stack's variables actually come from rather than by their
/// value.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum VarsSource {
    /// The stage root layer stack.
    Root,
    /// The contextual instance whose composed variables are the source.
    Instance(LayerStackId),
}

impl VarsSource {
    /// The instance this source names: the root stack, or the carried instance.
    pub(crate) fn referent(self) -> LayerStackId {
        match self {
            VarsSource::Root => LayerStackId::ROOT,
            VarsSource::Instance(id) => id,
        }
    }
}

/// Index of an interned expression-variable context (a canonicalized, name-sorted
/// `(name, value)` list). [`Value`] is not `Eq`/`Hash`, so a composed variable
/// map cannot be compared cheaply; interning it to this `Copy` handle lets two
/// composed sets be compared by id — the comparison behind rebuild change
/// detection and the source-reuse rule in
/// [`LayerStackRegistry::set_composed`].
///
/// An `ExprVarId` is meaningful only within the [`ExprVarInterner`] that minted it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct ExprVarId(u32);

/// Interns expression-variable contexts to [`ExprVarId`]s, deduplicating by
/// structural equality so two equal contexts share one id. [`Value`] is not
/// `Eq`/`Hash`, so the dedup is a linear scan comparing the canonicalized,
/// name-sorted forms with [`value_eq`]. The context count is tiny (bounded by
/// the variable-authoring layers), so the linear scan is not a concern.
// TODO(perf): a hash-indexed table would drop the linear `value_eq` scan if a
// pathological stack ever interns many distinct contexts.
#[derive(Default)]
pub(crate) struct ExprVarInterner {
    contexts: Vec<Vec<(String, Value)>>,
}

impl ExprVarInterner {
    /// Interns `vars`, returning the existing id of an equal context or minting a
    /// fresh one.
    pub(crate) fn intern(&mut self, vars: &HashMap<String, Value>) -> ExprVarId {
        let canon = canonical_context(vars);
        if let Some(id) = self.find_canonical(&canon) {
            return id;
        }
        let id = ExprVarId(self.contexts.len() as u32);
        self.contexts.push(canon);
        id
    }

    fn find_canonical(&self, canon: &[(String, Value)]) -> Option<ExprVarId> {
        self.contexts
            .iter()
            .position(|context| {
                context.len() == canon.len()
                    && context
                        .iter()
                        .zip(canon)
                        .all(|((cn, cv), (n, v))| cn == n && value_eq(cv, v))
            })
            .map(|i| ExprVarId(i as u32))
    }
}

/// What composition input a [`LayerStackInstance`] is keyed by.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum LayerStackKey {
    /// The stage root layer stack (session layers, the root layer, its sublayers).
    Root,
    /// A reference/payload target's sublayer stack rooted at `root`, its
    /// expression variables seeded by the composed set of `source`'s referent —
    /// the Rust analog of C++ `PcpLayerStackIdentifier`'s
    /// `expressionVariablesOverrideSource`. An arc keys its target by the source
    /// of the arc-carrying stack's composed variables
    /// ([`LayerStackRegistry::vars_source`], the C++ `primIndex.cpp` rule), so
    /// the same target reached from stacks that author different variables gets
    /// one instance each — its `${VAR}` sublayers and asset paths resolve
    /// independently — while a chain of stacks that contribute no new variables
    /// propagates one source and shares one instance.
    Target { root: LayerId, source: VarsSource },
}

/// One composed layer stack: its identity ([`LayerStackKey`]), resolved members,
/// and composed expression-variable context.
struct LayerStackInstance {
    key: LayerStackKey,
    /// The resolved members in strength order with composed offsets.
    members: Vec<(LayerId, LayerOffset)>,
    /// The member layer ids as a set, for fast containment tests (invalidation,
    /// "indices touching layers").
    member_set: HashSet<LayerId>,
    /// The composed expression variables of the stack — its root layer's own
    /// `expressionVariables` overlaid by the seed (the seed winning) — the single
    /// set its `${VAR}` sublayers, reference/payload asset paths, and value-time
    /// asset attributes all resolve against.
    // TODO(perf): every instance owns its map even though source-aware identity
    // would let a non-authoring chain share one stored set (keyed by `expr_id`).
    expr_vars: HashMap<String, Value>,
    /// [`expr_vars`](Self::expr_vars) interned, the cheap composed-content
    /// comparison behind rebuild change detection and the source-reuse rule.
    expr_id: ExprVarId,
    /// The source of this stack's composed variables, per the C++
    /// `Pcp_ComposeExpressionVariables` reuse rule (see
    /// [`LayerStackRegistry::set_composed`]): the key's source when the stack's
    /// own authored variables changed nothing, else the stack itself. The value
    /// an arc out of this stack keys its target by.
    vars_source: VarsSource,
}

/// Every composed layer stack a [`LayerGraph`](super::layer_graph::LayerGraph) has
/// built, addressed by [`LayerStackId`] and interned by composition input
/// ([`LayerStackKey`]). Instance 0 is always the stage root stack.
///
/// Not every physical layer gets an instance — the set is sparse. Instances exist
/// only for composition roots: the stage root, the sublayer-DAG roots an eagerly
/// built graph needs (`LayerGraph::rebuild_sublayer_stacks`), and the
/// reference/payload targets minted on demand through the load barrier
/// (`LayerGraph::intern_external`). A sublayer-only layer never gets its own
/// instance; it participates through its root's members, so a deep sublayer chain
/// stays O(n) rather than minting O(n) stacks of O(n) members each.
///
/// Two invariants tie the source-keyed identities together:
///
/// - A stored [`VarsSource`] is canonical: its referent's own
///   [`vars_source`](Self::vars_source) equals it at mint, so equal variable
///   contexts derived through different arc chains key identically.
/// - A key's source referent has a smaller index than its owner (keys are
///   immutable and the registry append-only), so ascending index order is
///   dependency order: a rebuild pass reads every seed after refreshing its
///   referent.
///
/// Storage and interning only: the graph composes members (it owns the layers) and
/// hands them to [`set_root`](Self::set_root) / [`intern_target`](Self::intern_target).
#[derive(Default)]
pub(crate) struct LayerStackRegistry {
    instances: Vec<LayerStackInstance>,
    by_key: HashMap<LayerStackKey, LayerStackId>,
    /// The interned composed expression-variable sets, keyed by [`ExprVarId`].
    contexts: ExprVarInterner,
}

impl LayerStackRegistry {
    /// The target stack for `(root, source)`, if one has been interned.
    pub(crate) fn lookup_target(&self, root: LayerId, source: VarsSource) -> Option<LayerStackId> {
        self.by_key.get(&LayerStackKey::Target { root, source }).copied()
    }

    /// Records (or, for the root, updates) the stage root stack as instance 0 with
    /// its resolved members and composed expression variables. The root is always
    /// the first instance, so a rebuild updates it in place. Returns whether the
    /// composed variables changed, like [`set_composed`](Self::set_composed).
    pub(crate) fn set_root(&mut self, members: Vec<(LayerId, LayerOffset)>, expr_vars: HashMap<String, Value>) -> bool {
        if self.instances.is_empty() {
            let id = self.insert(LayerStackKey::Root, members, expr_vars);
            debug_assert_eq!(id, LayerStackId::ROOT, "the root stack must be instance 0");
            true
        } else {
            debug_assert!(
                matches!(self.instances[LayerStackId::ROOT.idx()].key, LayerStackKey::Root),
                "instance 0 must be the root stack",
            );
            self.set_composed(LayerStackId::ROOT, members, expr_vars)
        }
    }

    /// Records a freshly composed target stack for `(root, source)` with its
    /// resolved members and composed expression variables, returning its id. The
    /// caller guarantees `(root, source)` is not already present (via
    /// [`lookup_target`](Self::lookup_target)).
    pub(crate) fn intern_target(
        &mut self,
        root: LayerId,
        source: VarsSource,
        members: Vec<(LayerId, LayerOffset)>,
        expr_vars: HashMap<String, Value>,
    ) -> LayerStackId {
        self.insert(LayerStackKey::Target { root, source }, members, expr_vars)
    }

    /// Inserts a fresh instance for `key`, deriving its member set, interned
    /// composed context, and variable source, and records it in
    /// [`by_key`](Self::by_key).
    fn insert(
        &mut self,
        key: LayerStackKey,
        members: Vec<(LayerId, LayerOffset)>,
        expr_vars: HashMap<String, Value>,
    ) -> LayerStackId {
        let member_set = members.iter().map(|&(id, _)| id).collect();
        let expr_id = self.contexts.intern(&expr_vars);
        let id = LayerStackId(self.instances.len() as u32);
        if let LayerStackKey::Target { source, .. } = key {
            debug_assert!(
                source.referent().idx() < id.idx(),
                "a key's source referent must precede its owner",
            );
            debug_assert_eq!(
                self.instances[source.referent().idx()].vars_source,
                source,
                "a minted key's source must be canonical",
            );
        }
        let vars_source = self.derive_vars_source(id, key, expr_id);
        self.instances.push(LayerStackInstance {
            key,
            members,
            member_set,
            expr_vars,
            expr_id,
            vars_source,
        });
        self.by_key.insert(key, id);
        id
    }

    /// The source of the composed variables `id` would store, per the C++
    /// `Pcp_ComposeExpressionVariables` reuse rule: when the composed set equals
    /// the seed — the stack's own authored variables changed nothing — the
    /// (weaker) source is reused, read as the referent's current
    /// [`vars_source`](Self::vars_source) so a chain of non-authoring stacks
    /// propagates one canonical source; otherwise the stack becomes the source
    /// itself. The root stack's source is always the root.
    fn derive_vars_source(&self, id: LayerStackId, key: LayerStackKey, expr_id: ExprVarId) -> VarsSource {
        match key {
            LayerStackKey::Root => VarsSource::Root,
            LayerStackKey::Target { source, .. } => {
                let referent = &self.instances[source.referent().idx()];
                if expr_id == referent.expr_id {
                    referent.vars_source
                } else {
                    VarsSource::Instance(id)
                }
            }
        }
    }

    /// The resolved members of a stack, or an empty slice for a handle the registry
    /// has not minted yet — the root stack before [`set_root`](Self::set_root) runs
    /// at finalize, or a target whose root is unknown.
    pub(crate) fn members(&self, id: LayerStackId) -> &[(LayerId, LayerOffset)] {
        self.instances.get(id.idx()).map_or(&[], |inst| inst.members.as_slice())
    }

    /// The member layer ids of a stack as a set, for containment tests, or `None`
    /// for a handle the registry has not minted yet.
    pub(crate) fn member_set(&self, id: LayerStackId) -> Option<&HashSet<LayerId>> {
        self.instances.get(id.idx()).map(|inst| &inst.member_set)
    }

    /// Every layer that is a member of some composed stack — the root stack and
    /// each interned reference/payload target stack. Muting rebuilds every stack
    /// with its muted subtrees pruned (a fully muted target root resolves to an
    /// empty stack), so this is the effectively-present layer set and carries no
    /// muted layer. Independent of which prim indices are cached.
    pub(crate) fn member_layers(&self) -> HashSet<LayerId> {
        self.instances
            .iter()
            .flat_map(|inst| inst.member_set.iter().copied())
            .collect()
    }

    /// The `(root, source)` key of a non-root target stack, or `None` for the
    /// root stack.
    pub(crate) fn target_key(&self, id: LayerStackId) -> Option<(LayerId, VarsSource)> {
        match self.instances[id.idx()].key {
            LayerStackKey::Root => None,
            LayerStackKey::Target { root, source } => Some((root, source)),
        }
    }

    /// Every non-root target instance as `(id, root, key source)`, in ascending
    /// index order — dependency order, since a key's source referent always
    /// precedes its owner. A rebuild walks this after refreshing the root stack
    /// so each instance's seed referent is already up to date when it is read.
    pub(crate) fn targets(&self) -> impl Iterator<Item = (LayerStackId, LayerId, VarsSource)> + '_ {
        self.instances
            .iter()
            .enumerate()
            .filter_map(|(i, inst)| match inst.key {
                LayerStackKey::Root => None,
                LayerStackKey::Target { root, source } => Some((LayerStackId(i as u32), root, source)),
            })
    }

    /// Replaces a stack's members and composed expression variables after a
    /// re-resolve, keeping the id stable so a handle held by a surviving prim index
    /// stays valid, and re-deriving the stack's variable source
    /// ([`derive_vars_source`](Self::derive_vars_source)). Returns whether the
    /// composed variables or their source changed, so a rebuild pass can cascade
    /// the re-seed to the stacks keyed by this one.
    pub(crate) fn set_composed(
        &mut self,
        id: LayerStackId,
        members: Vec<(LayerId, LayerOffset)>,
        expr_vars: HashMap<String, Value>,
    ) -> bool {
        let expr_id = self.contexts.intern(&expr_vars);
        let vars_source = self.derive_vars_source(id, self.instances[id.idx()].key, expr_id);
        let instance = &mut self.instances[id.idx()];
        let changed = instance.expr_id != expr_id || instance.vars_source != vars_source;
        instance.member_set = members.iter().map(|&(id, _)| id).collect();
        instance.members = members;
        instance.expr_vars = expr_vars;
        instance.expr_id = expr_id;
        instance.vars_source = vars_source;
        changed
    }

    /// The composed expression variables of a stack. Unlike [`members`](Self::members)
    /// there is no pre-finalize empty fallback: an expression lookup always comes
    /// from a composition node, which always references a minted stack, so an
    /// unminted handle is an invariant break and panics.
    pub(crate) fn expression_variables(&self, id: LayerStackId) -> &HashMap<String, Value> {
        &self.instances[id.idx()].expr_vars
    }

    /// The source of a stack's composed expression variables — the value an arc
    /// out of this stack keys its target stack by (C++ `primIndex.cpp` keys the
    /// target identifier by the parent stack's composed-variables source, not by
    /// the parent itself). Panics on an unminted handle, like
    /// [`expression_variables`](Self::expression_variables).
    pub(crate) fn vars_source(&self, id: LayerStackId) -> VarsSource {
        self.instances[id.idx()].vars_source
    }
}

/// Canonicalizes an expression-variable context to a name-sorted `(name, value)`
/// list, the interning form for an [`ExprVarId`]. Sorting makes the form
/// independent of the source `HashMap`'s iteration order, so two equal contexts
/// canonicalize identically and intern to one id.
fn canonical_context(vars: &HashMap<String, Value>) -> Vec<(String, Value)> {
    let mut canon: Vec<(String, Value)> = vars.iter().map(|(name, value)| (name.clone(), value.clone())).collect();
    canon.sort_by(|a, b| a.0.cmp(&b.0));
    canon
}

/// Whether two context values are equal for deduplication, treating two `NaN`s
/// with the same bit pattern as equal so a context always matches its own
/// re-derived clone.
///
/// [`Value`] derives `PartialEq`, under which `NaN != NaN`, so a composed set
/// carrying a float `NaN` — only reachable from non-conformant
/// `expressionVariables`, which the spec restricts to string/bool/int — would
/// otherwise never compare equal to its own rebuild: every rebuild would report
/// it changed and re-derive its stack as its own variable source. A scalar float
/// compares by bit pattern, so a `NaN` equals its clone; a dictionary recurses,
/// matching values by key (order-independently, reaching a `NaN` nested in a
/// dictionary value); every other value uses `==`.
fn value_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Half(a), Value::Half(b)) => a.to_bits() == b.to_bits(),
        (Value::Float(a), Value::Float(b)) => a.to_bits() == b.to_bits(),
        (Value::Double(a), Value::Double(b)) => a.to_bits() == b.to_bits(),
        (Value::Dictionary(a), Value::Dictionary(b)) => {
            a.len() == b.len() && a.iter().all(|(key, av)| b.get(key).is_some_and(|bv| value_eq(av, bv)))
        }
        _ => a == b,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A context carrying a float `NaN` interns to one id across re-derivation,
    /// so a rebuild recognizes an unchanged composed set instead of reporting a
    /// change (and re-deriving the variable source) forever. Under `Value`'s
    /// derived `PartialEq` (`NaN != NaN`) this would return two ids.
    #[test]
    fn nan_seed_dedups() {
        let mut interner = ExprVarInterner::default();
        let vars = || HashMap::from([("V".to_string(), Value::Double(f64::NAN))]);
        let first = interner.intern(&vars());
        let second = interner.intern(&vars());
        assert_eq!(first, second, "a NaN-valued context must intern to a single id");
    }
}
