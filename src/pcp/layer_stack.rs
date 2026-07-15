//! Composed layer-stack identity and storage, the composed-view half of
//! composition's layer model.
//!
//! A [`LayerId`] names a physical loaded layer (owned by
//! [`layer_graph`](super::layer_graph)); a [`LayerStackId`] names a composed view
//! of layers — the stage root stack, or a reference/payload target's sublayer
//! stack under a particular inherited expression-variable context. Every composed
//! stack, root included, is a [`LayerStackInstance`] in the [`LayerStackRegistry`]
//! addressed by an opaque [`LayerStackId`]; composition (`Node`, duplicate
//! detection, edit-target info, invalidation, relocate queries) never branches on
//! what kind of stack a handle names — the registry owns the kind, root, seed, and
//! members.
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

/// Index of an interned expression-variable context (a canonicalized, name-sorted
/// `(name, value)` list). [`Value`] is not `Eq`/`Hash`, so a context cannot key a
/// hash map directly; interning it to this `Copy` handle lets a stack be keyed by
/// `(root, seed)`.
///
/// An `ExprVarId` is meaningful only within the [`ExprVarInterner`] that minted it.
/// The registry holds one interner for stack seeds, so a seed id is only ever
/// produced by the registry.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct ExprVarId(u32);

impl ExprVarId {
    fn idx(self) -> usize {
        self.0 as usize
    }
}

/// Interns expression-variable contexts to [`ExprVarId`]s, deduplicating by
/// structural equality so two equal contexts share one id. [`Value`] is not
/// `Eq`/`Hash`, so the dedup is a linear scan comparing the canonicalized,
/// name-sorted forms with [`value_eq`]. The registry holds one to key stacks by
/// their seed. The context count is tiny (bounded by the variable-authoring
/// layers), so the linear scan is not a concern.
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
        let canon = canonical_seed(vars);
        if let Some(id) = self.find_canonical(&canon) {
            return id;
        }
        let id = ExprVarId(self.contexts.len() as u32);
        self.contexts.push(canon);
        id
    }

    /// The interned id of `vars`, if it has been interned (read-only twin of
    /// [`intern`](Self::intern)).
    pub(crate) fn find(&self, vars: &HashMap<String, Value>) -> Option<ExprVarId> {
        self.find_canonical(&canonical_seed(vars))
    }

    /// Reconstructs an interned context as a variable map.
    pub(crate) fn vars(&self, id: ExprVarId) -> HashMap<String, Value> {
        self.contexts[id.idx()].iter().cloned().collect()
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
    /// A reference/payload target's sublayer stack rooted at `root`, resolved with
    /// the inherited expression-variable context `seed` (the empty seed for a plain
    /// stack). The same target reached through two contexts gets one instance each,
    /// so its `${VAR}` sublayers resolve independently.
    Target { root: LayerId, seed: ExprVarId },
}

/// One composed layer stack: its identity ([`LayerStackKey`]) and resolved
/// members.
struct LayerStackInstance {
    key: LayerStackKey,
    /// The resolved members in strength order with composed offsets.
    members: Vec<(LayerId, LayerOffset)>,
    /// The member layer ids as a set, for fast containment tests (invalidation,
    /// "indices touching layers").
    member_set: HashSet<LayerId>,
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
/// Storage and interning only: the graph composes members (it owns the layers) and
/// hands them to [`set_root`](Self::set_root) / [`intern_target`](Self::intern_target).
pub(crate) struct LayerStackRegistry {
    instances: Vec<LayerStackInstance>,
    by_key: HashMap<LayerStackKey, LayerStackId>,
    /// The interned stack seeds, keyed by [`ExprVarId`].
    seeds: ExprVarInterner,
    /// The interned empty context, the seed of every plain (no-inherited-context)
    /// stack.
    empty_seed: ExprVarId,
}

impl Default for LayerStackRegistry {
    fn default() -> Self {
        // Intern the empty seed as id 0 so plain stacks have a stable key before any
        // variable context is seen.
        let mut seeds = ExprVarInterner::default();
        let empty_seed = seeds.intern(&HashMap::new());
        Self {
            instances: Vec::new(),
            by_key: HashMap::new(),
            seeds,
            empty_seed,
        }
    }
}

impl LayerStackRegistry {
    /// The seed of a plain (no-inherited-context) stack.
    pub(crate) fn empty_seed(&self) -> ExprVarId {
        self.empty_seed
    }

    /// Interns `vars` to its stack-seed [`ExprVarId`].
    pub(crate) fn intern_expr_seed(&mut self, vars: &HashMap<String, Value>) -> ExprVarId {
        self.seeds.intern(vars)
    }

    /// The interned id of `vars`, if it has been interned (read-only twin of
    /// [`intern_expr_seed`](Self::intern_expr_seed)).
    pub(crate) fn find_expr_seed(&self, vars: &HashMap<String, Value>) -> Option<ExprVarId> {
        self.seeds.find(vars)
    }

    /// Reconstructs an interned seed as a variable map, for re-resolving an
    /// instance's members on a stack rebuild.
    pub(crate) fn seed_vars(&self, seed: ExprVarId) -> HashMap<String, Value> {
        self.seeds.vars(seed)
    }

    /// The target stack for `(root, seed)`, if one has been interned.
    pub(crate) fn lookup_target(&self, root: LayerId, seed: ExprVarId) -> Option<LayerStackId> {
        self.by_key.get(&LayerStackKey::Target { root, seed }).copied()
    }

    /// Records (or, for the root, updates) the stage root stack as instance 0. The
    /// root is always the first instance, so a rebuild updates it in place.
    pub(crate) fn set_root(&mut self, members: Vec<(LayerId, LayerOffset)>) {
        if self.instances.is_empty() {
            let member_set = members.iter().map(|&(id, _)| id).collect();
            self.instances.push(LayerStackInstance {
                key: LayerStackKey::Root,
                members,
                member_set,
            });
            self.by_key.insert(LayerStackKey::Root, LayerStackId::ROOT);
        } else {
            debug_assert!(
                matches!(self.instances[LayerStackId::ROOT.idx()].key, LayerStackKey::Root),
                "instance 0 must be the root stack",
            );
            self.set_members(LayerStackId::ROOT, members);
        }
    }

    /// Records a freshly composed target stack for `(root, seed)`, returning its id.
    /// The caller guarantees `(root, seed)` is not already present (via
    /// [`lookup_target`](Self::lookup_target)).
    pub(crate) fn intern_target(
        &mut self,
        root: LayerId,
        seed: ExprVarId,
        members: Vec<(LayerId, LayerOffset)>,
    ) -> LayerStackId {
        let key = LayerStackKey::Target { root, seed };
        let member_set = members.iter().map(|&(id, _)| id).collect();
        let id = LayerStackId(self.instances.len() as u32);
        self.instances.push(LayerStackInstance {
            key,
            members,
            member_set,
        });
        self.by_key.insert(key, id);
        id
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

    /// Whether the stack is the stage root stack.
    pub(crate) fn is_root(&self, id: LayerStackId) -> bool {
        matches!(self.instances[id.idx()].key, LayerStackKey::Root)
    }

    /// The inherited expression-variable context a stack resolved against — empty
    /// for the root stack and for a plain target. Captured into an edit target so a
    /// later authoring query reconstructs the same contextual stack.
    pub(crate) fn instance_seed_vars(&self, id: LayerStackId) -> HashMap<String, Value> {
        match self.instances[id.idx()].key {
            LayerStackKey::Root => HashMap::new(),
            LayerStackKey::Target { seed, .. } => self.seed_vars(seed),
        }
    }

    /// The target root layer of a non-root stack — its representative member.
    pub(crate) fn target_root(&self, id: LayerStackId) -> LayerId {
        match self.instances[id.idx()].key {
            LayerStackKey::Root => self.instances[id.idx()]
                .members
                .first()
                .map(|&(l, _)| l)
                .unwrap_or(LayerId::INVALID),
            LayerStackKey::Target { root, .. } => root,
        }
    }

    /// The `(id, root, seed-vars)` of every non-root target stack a rebuild must
    /// re-resolve. With `affected` set, a stack whose members are disjoint from
    /// those layers is skipped: the edit changed neither its sublayer edges nor an
    /// authored `${VAR}` expression it resolves, so its members are unchanged.
    /// `None` returns every target, for a full rebuild (a load can extend a stack
    /// with a newly opened member the changed-edge set cannot name).
    pub(crate) fn target_rebuild_specs(
        &self,
        affected: Option<&HashSet<LayerId>>,
    ) -> Vec<(LayerStackId, LayerId, HashMap<String, Value>)> {
        self.instances
            .iter()
            .enumerate()
            .filter_map(|(i, inst)| match inst.key {
                LayerStackKey::Root => None,
                LayerStackKey::Target { root, seed } => {
                    if affected.is_some_and(|affected| inst.member_set.is_disjoint(affected)) {
                        return None;
                    }
                    Some((LayerStackId(i as u32), root, self.seed_vars(seed)))
                }
            })
            .collect()
    }

    /// Replaces a stack's members after a re-resolve, keeping the id stable so a
    /// handle held by a surviving prim index stays valid.
    pub(crate) fn set_members(&mut self, id: LayerStackId, members: Vec<(LayerId, LayerOffset)>) {
        self.instances[id.idx()].member_set = members.iter().map(|&(id, _)| id).collect();
        self.instances[id.idx()].members = members;
    }
}

/// Canonicalizes an expression-variable context to a name-sorted `(name, value)`
/// list, the interning form for an [`ExprVarId`]. Sorting makes the form
/// independent of the source `HashMap`'s iteration order, so two equal contexts
/// canonicalize identically and intern to one id.
fn canonical_seed(vars: &HashMap<String, Value>) -> Vec<(String, Value)> {
    let mut canon: Vec<(String, Value)> = vars.iter().map(|(name, value)| (name.clone(), value.clone())).collect();
    canon.sort_by(|a, b| a.0.cmp(&b.0));
    canon
}

/// Whether two seed values are equal for deduplication, treating two `NaN`s with
/// the same bit pattern as equal so a seed always matches its own re-derived clone.
///
/// [`Value`] derives `PartialEq`, under which `NaN != NaN`, so a seed carrying a
/// float `NaN` — only reachable from non-conformant `expressionVariables`, which
/// the spec restricts to string/bool/int — would otherwise never dedup, leaving
/// [`external_stack_id`](super::layer_graph::LayerGraph::external_stack_id)
/// returning `Demand` and the load barrier interning the same seed forever. A
/// scalar float compares by bit pattern, so a `NaN` equals its clone; a dictionary
/// recurses, matching values by key (order-independently, reaching a `NaN` nested
/// in a dictionary value); every other value uses `==`.
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

    /// A seed carrying a float `NaN` dedups to one id across re-interning, so the
    /// load barrier converges instead of minting an identical seed forever. Under
    /// `Value`'s derived `PartialEq` (`NaN != NaN`) this would return two ids.
    #[test]
    fn nan_seed_dedups() {
        let mut registry = LayerStackRegistry::default();
        let vars = || HashMap::from([("V".to_string(), Value::Double(f64::NAN))]);
        let first = registry.intern_expr_seed(&vars());
        let second = registry.intern_expr_seed(&vars());
        assert_eq!(first, second, "a NaN-valued seed must intern to a single id");
    }
}
