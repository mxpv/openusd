//! Scene-graph instancing: shared prototypes for `instanceable` prims (spec
//! 11.3.3).
//!
//! Instances with the same [`InstanceKey`] — the arc-introduced opinions that
//! define their subtree, independent of stage path — share one composed
//! prototype. [`PrototypeRegistry`] owns that mapping (an [`IndexCache`] holds
//! one as a field); the composition-coupled glue stays on `IndexCache` because
//! it needs the composed indices. The prototype *namespace* is the single
//! composition of a set of identical instances and composes in place: the root
//! from its materialized `/__Prototype_N` index, a descendant by deepening that
//! graph. Every descendant-serving query enters through
//! [`IndexCache::effective_path`], which redirects an instance proxy `/A/tail`
//! onto `/__Prototype_N/tail` so identical instances are composed only once,
//! while an instance root composes in place (it may override property values).
//! Materializing the root independently keeps its shared content addressable
//! without the seeding instance's root-level overrides leaking in.

use std::collections::{HashMap, HashSet};

use anyhow::Result;

use crate::sdf::schema::FieldKey;
use crate::sdf::{Path, PathElement, Value};

use super::index_cache::IndexCache;
use super::layer_graph::LayerGraph;
use super::prim_graph::ArcType;
use super::prim_index::PrimIndex;
use super::LayerId;

/// The shared-prototype registry (spec 11.3.3): maps each instancing key to its
/// prototype and tracks the instances that share it. Owns no composition state
/// — the [`IndexCache`] computes an [`InstanceKey`] from a composed index and
/// hands it to [`register`](Self::register); the registry only dedups by key,
/// mints `/__Prototype_N` identities, and answers prototype/instance queries.
#[derive(Default)]
pub(super) struct PrototypeRegistry {
    /// Prototypes keyed by their `/__Prototype_N` root path. Path-keyed so the
    /// common query direction (path to prototype) is a single lookup.
    by_root: HashMap<Path, Prototype>,
    /// Maps an instancing key to its prototype root, the lookup direction used
    /// only when registering an instance to dedup against an existing key.
    by_key: HashMap<InstanceKey, Path>,
    /// Counter for minting `/__Prototype_N` identities in registration order.
    /// Stays monotonic across [`clear`](Self::clear) so a `/__Prototype_N`
    /// identity is never reused for a different composition within a session.
    count: usize,
}

/// A shared prototype for a set of instances with the same [`InstanceKey`]
/// (spec 11.3.3). The prototype *root* is composed as an independent
/// `/__Prototype_N` index, built from the canonical instance's shared subtree —
/// the instanceable arc, its descendants, and the implied classes — with the
/// instance-local opinions (the local root override and the ancestral references
/// above the instanceable arc) inerted (see
/// [`PrimIndex::mark_instance_local_inert`]) and the namespace re-anchored onto
/// the prototype root (see [`PrimIndex::rebase_root`]). Its descendants compose
/// in place by deepening that graph, and every sharing instance's proxies
/// redirect onto the prototype namespace through [`IndexCache::redirect_anchor`],
/// so identical instances compose once. Materializing the root is what keeps a
/// query on `/__Prototype_N` itself free of the seeding instance's root-level
/// overrides (spec 11.3.3 permits overriding property values at an instance
/// root).
struct Prototype {
    /// Registration order (the `N` in `/__Prototype_N`). Kept so prototypes can
    /// be returned in mint order without parsing the path.
    index: usize,
    /// Instance whose composed subtree seeds this prototype's materialization.
    canonical: Path,
    /// Every instance sharing this prototype.
    instances: Vec<Path>,
}

/// Identity of an instance prim's shared composition (spec 11.3.3): the
/// arc-introduced opinions that determine its subtree, independent of the
/// instance's own stage path. Instances with equal keys share a prototype.
///
/// Variant selections are folded in explicitly via [`selections`](Self::selections)
/// rather than left implicit in the arc paths: each arc's path has its variant
/// selections stripped (so two instances of the same reference produce the same
/// arc path regardless of which variant they pick) and the resolved selection
/// set is carried as a separate, path-independent list. Without the explicit
/// list, two instances of one reference that differ only by a variant selection
/// would collide once the selection is stripped from the path.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct InstanceKey {
    arcs: Vec<InstanceArc>,
    /// The resolved `(variant set, selection)` pairs, in composition order.
    selections: Vec<(String, String)>,
}

/// One arc contribution in an [`InstanceKey`]. Floats are stored as bit
/// patterns so the key is `Hash`/`Eq`.
#[derive(Clone, PartialEq, Eq, Hash)]
struct InstanceArc {
    arc: u8,
    layer: LayerId,
    path: String,
    offset_bits: u64,
    scale_bits: u64,
}

impl PrototypeRegistry {
    /// Registers `instance` against its prototype: dedups by `key`, recording
    /// the instance the first time a key is seen and minting `/__Prototype_N`.
    /// Returns the canonical instance, the prototype path, and whether this call
    /// minted a new prototype (so the caller knows to materialize its index).
    fn register(&mut self, key: InstanceKey, instance: &Path) -> (Path, Path, bool) {
        if let Some(root) = self.by_key.get(&key) {
            let root = root.clone();
            let prototype = self.by_root.get_mut(&root).expect("key index points to a prototype");
            if !prototype.instances.contains(instance) {
                prototype.instances.push(instance.clone());
            }
            return (prototype.canonical.clone(), root, false);
        }

        let index = self.count;
        let path = Path::new(&format!("/__Prototype_{index}")).expect("synthetic prototype path is valid");
        self.count += 1;
        self.by_key.insert(key, path.clone());
        self.by_root.insert(
            path.clone(),
            Prototype {
                index,
                canonical: instance.clone(),
                instances: vec![instance.clone()],
            },
        );
        (instance.clone(), path, true)
    }

    /// The canonical instance backing the prototype at `prototype`, or `None`
    /// for an unknown path. Used by registry tests to assert a prototype's
    /// presence; production composition reaches the prototype directly through
    /// [`register`](Self::register)'s return.
    #[cfg(test)]
    fn canonical_of(&self, prototype: &Path) -> Option<Path> {
        self.by_root.get(prototype).map(|p| p.canonical.clone())
    }

    /// The instances sharing the prototype at `prototype` (a `/__Prototype_N`
    /// path), sorted by namespace path so the result does not depend on the
    /// order instances were queried. Empty for unknown paths.
    fn instances_of(&self, prototype: &Path) -> Vec<Path> {
        let mut instances = self.instances_unsorted(prototype).to_vec();
        instances.sort();
        instances
    }

    /// The instances sharing the prototype at `prototype`, in registration
    /// order, borrowed without the clone-and-sort of [`instances_of`](Self::instances_of).
    /// Used for membership checks (e.g. population-mask gating) where order is
    /// irrelevant. Empty for unknown paths.
    fn instances_unsorted(&self, prototype: &Path) -> &[Path] {
        self.by_root.get(prototype).map_or(&[], |p| &p.instances)
    }

    /// The registered `/__Prototype_N` roots, in registration order.
    fn roots(&self) -> Vec<Path> {
        let mut roots: Vec<(&Path, &Prototype)> = self.by_root.iter().collect();
        roots.sort_by_key(|(_, prototype)| prototype.index);
        roots.into_iter().map(|(root, _)| root.clone()).collect()
    }

    /// Whether `path` is a registered `/__Prototype_N` root.
    fn is_root(&self, path: &Path) -> bool {
        self.by_root.contains_key(path)
    }

    /// Whether `path` lies within a prototype's namespace — i.e. it has a
    /// `/__Prototype_N` ancestor (spec 11.3.3).
    fn is_in_prototype(&self, path: &Path) -> bool {
        self.enclosing_root(path.parent()).is_some()
    }

    /// Walks the chain from `start` toward the root and returns the nearest
    /// `/__Prototype_N` root on it, or `None`. Passing the queried prim starts
    /// the walk inclusively; passing its parent excludes the prim itself.
    fn enclosing_root(&self, start: Option<Path>) -> Option<Path> {
        let mut node = start;
        while let Some(current) = node {
            if self.by_root.contains_key(&current) {
                return Some(current);
            }
            node = current.parent();
        }
        None
    }

    /// Drops every prototype so stale instance-to-prototype mappings do not
    /// survive a composition change; the registry is rebuilt lazily on the next
    /// instancing query. `count` stays monotonic (see its doc).
    pub(super) fn clear(&mut self) {
        self.by_root.clear();
        self.by_key.clear();
    }

    /// Removes every prototype the change set could have invalidated, returning
    /// the dropped `/__Prototype_N` roots so the cache can evict their indices.
    /// A prototype is affected when a changed prim path lies on the ancestor
    /// chain of one of its instances (the instance's `instanceable` opinion,
    /// arcs, or shared content may have changed) or of its prototype root.
    /// Unaffected prototypes keep their instance-to-prototype mapping and
    /// materialized index, so a localized edit no longer forces every key to be
    /// recomputed (spec 11.3.3).
    ///
    /// `count` stays monotonic (see its doc), so a re-registered instance mints
    /// a fresh identity rather than reusing a removed prototype's number.
    //
    // TODO(perf): the affectedness test scans every prototype's instance list
    // against every changed path. A reverse `(instance prefix → prototype)`
    // index would bound it by the change set; left simple while prototype
    // counts are modest.
    fn remove_affected(&mut self, changed: &[Path]) -> Vec<Path> {
        let affected: HashSet<Path> = self
            .by_root
            .iter()
            .filter(|(root, prototype)| {
                changed.iter().any(|p| {
                    p.is_nested_with(root) || prototype.instances.iter().any(|instance| p.is_nested_with(instance))
                })
            })
            .map(|(root, _)| root.clone())
            .collect();
        self.by_root.retain(|root, _| !affected.contains(root));
        self.by_key.retain(|_, root| !affected.contains(root));
        affected.into_iter().collect()
    }
}

/// Computes the instancing key for an already-built instance index: the
/// arc-introduced (shared) opinions that define the prototype subtree,
/// independent of the instance's own stage path (spec 11.3.3).
/// `instance_depth` is the instance prim's own namespace depth, used to
/// partition shared from instance-local nodes
/// ([`PrimIndex::instance_local_nodes`]).
///
/// Each contributing arc's path is stripped of variant selections, and the
/// resolved selection set is folded into the key explicitly (see
/// [`InstanceKey`]), so two instances of one reference share a prototype iff
/// their variant selections also match.
fn instance_key(index: &PrimIndex, instance_depth: u16) -> InstanceKey {
    let local = index.instance_local_nodes(instance_depth);
    let mut arcs = Vec::new();
    let mut selections = Vec::new();
    for (id, node) in index.nodes_with_ids() {
        if local[id.idx()] || node.is_culled() {
            continue;
        }
        if node.arc == ArcType::Variant {
            if let Some(PathElement::Variant { set, selection }) = node.path.last_element() {
                selections.push((set.to_string(), selection.to_string()));
            }
        }
        let offset = node.map_to_root.time_offset();
        arcs.push(InstanceArc {
            arc: node.arc as u8,
            layer: node.layer_id(),
            path: node.path.strip_all_variant_selections().to_string(),
            offset_bits: offset.offset.to_bits(),
            scale_bits: offset.scale.to_bits(),
        });
    }
    InstanceKey { arcs, selections }
}

impl IndexCache {
    /// Evicts only the prototypes a prim-level change touches (spec 11.3.3):
    /// every prototype whose instance subtree or prototype namespace lies on the
    /// ancestor chain of one of the `changed` prim paths is removed from the
    /// registry and has its materialized `/__Prototype_N` index dropped.
    /// Unaffected prototypes keep their mapping and index, so a localized edit
    /// does not recompute every key.
    ///
    /// Pure analysis over the change list (no composition), so it stays
    /// rayon-friendly: see [`PrototypeRegistry::remove_affected`]. A layer-stack
    /// rebuild instead clears the whole registry through
    /// [`Self::clear_all_indices`].
    pub(crate) fn invalidate_prototypes(&mut self, changed: &[Path]) {
        // A prototype's whole namespace composes in place now (the root from its
        // materialized index, descendants by deepening it; see
        // [`Self::redirect_anchor`]), so each affected root's entire subtree must
        // be dropped, not just the root spec.
        //
        // TODO(perf): `drop_index_subtree` is an O(n) cache scan per affected
        // root; batching the affected roots into one prefix-filtered pass (or an
        // `SdfPathTable`-like trie) would bound it by the change set.
        for root in self.prototypes.remove_affected(changed) {
            self.drop_index_subtree(&root);
        }
        // The redirection memo is keyed on instance/prototype structure that the
        // dropped prototypes may have defined, so clear it wholesale; it is
        // repopulated lazily on the next descendant query.
        self.redirected_prims.clear();
    }

    /// Returns `true` if `path` resolves as an instance prim (spec 11.3.3):
    /// the strongest `instanceable` opinion is `true` and the prim has at
    /// least one composition arc.
    ///
    /// Reads `instanceable` off the index that actually composes `path` — for an
    /// instance proxy that is the shared `/__Prototype_N` index, reached through
    /// [`Self::effective_path`], not a throwaway per-instance copy. So checking
    /// instance-ness while walking a deep proxy subtree (every ancestor is tested
    /// by [`Self::enclosing_instance`]) composes the shared subtree once instead
    /// of a literal index per instance. `effective_path` re-enters `is_instance`
    /// on a strict ancestor to find the enclosing instance, but each step moves
    /// to a shorter path and bottoms out at the root, so the recursion
    /// terminates.
    pub(crate) fn is_instance(&mut self, graph: &LayerGraph, path: &Path) -> Result<bool> {
        if path.is_abs_root() {
            return Ok(false);
        }
        let composed = self.effective_path(graph, path)?;
        self.ensure_index(graph, &composed)?;
        let index = self.cached(&composed);
        if !index.has_composition_arc() {
            return Ok(false);
        }
        Ok(matches!(
            index.resolve_field(FieldKey::Instanceable.as_str(), graph, None)?,
            Some(Value::Bool(true))
        ))
    }

    /// Composes `instance`, registers it against its prototype, and materializes
    /// the prototype's index on first use, returning the `(canonical instance,
    /// prototype path)` pair. The first instance registered for a key becomes
    /// canonical and seeds the prototype; later instances with the same key reuse
    /// the already-materialized prototype, so its subtree is composed only once
    /// (spec 11.3.3). Composing the index here (and computing its [`InstanceKey`])
    /// is the cache's job; the dedup is the [`PrototypeRegistry`]'s.
    fn register_prototype(&mut self, graph: &LayerGraph, instance: &Path) -> Result<(Path, Path)> {
        self.ensure_index(graph, instance)?;
        let key = instance_key(self.cached(instance), instance.prim_element_count() as u16);
        let (canonical, prototype, minted) = self.prototypes.register(key, instance);
        // Materialize the prototype's index only when this call minted it. Before
        // it existed, a query on the deterministic `/__Prototype_N` namespace
        // composed the synthetic path in place (no prototype to redirect to), so
        // an earlier query may have cached stale empty indices and identity
        // redirections anywhere under `/__Prototype_N`. Evict both so descendant
        // queries now redirect to the canonical instance; `materialize_prototype`
        // re-caches the root below. Keying off the mint signal (not
        // `indices.contains_key`) is what makes a stale synthetic index a miss
        // rather than a mistaken hit.
        if minted {
            self.drop_index_subtree(&prototype);
            self.redirected_prims.retain(|path, _| !path.has_prefix(&prototype));
            self.materialize_prototype(graph, &canonical, &prototype);
        }
        Ok((canonical, prototype))
    }

    /// Builds and caches the composed index for a freshly minted prototype root
    /// (`/__Prototype_N`) from the canonical instance's shared subtree (spec
    /// 11.3.3). The clone of the canonical index has its instance-local nodes
    /// inerted at the instance root's own depth, so only the instanceable arc,
    /// its descendants, and the implied classes contribute — the local root
    /// override and the ancestral references above the instanceable arc drop out
    /// — and its namespace is re-anchored onto the prototype root.
    ///
    /// The prototype root's child context is seeded as a namespace root with
    /// `instance_depth` cleared (it is not itself an instance — its `instanceable`
    /// opinion is inert), so a descendant built by deepening this graph composes
    /// as prototype content rather than instance-suppressed. Every instance
    /// proxy redirects onto this namespace through [`Self::redirect_anchor`], so
    /// the prototype subtree is the one place a set of identical instances'
    /// descendants compose.
    //
    // TODO(rayon): distinct prototypes (distinct instancing keys) compose
    // independent subtrees, so they can be materialized in parallel. The
    // `Indexer` already takes only `&` references; this needs the cache to build
    // off the `&mut self` path first (compose into per-prototype results, then
    // insert) and the shared `LayerGraph` handed to workers as `&`/`Arc`.
    fn materialize_prototype(&mut self, graph: &LayerGraph, canonical: &Path, prototype: &Path) {
        let mut index = self.cached(canonical).clone();
        index.mark_instance_local_inert(canonical.prim_element_count() as u16);
        // Re-anchor the seeding instance's composed namespace onto the prototype
        // root so the root's own target translation lands in the prototype
        // namespace, not the canonical instance's.
        index.rebase_root(canonical, prototype);

        let mut context = index.context_for_children(graph, &self.root_parent_context());
        context.instance_depth = None;

        // `redirect_anchor` composes a prim in place when it has no enclosing
        // instance, and relies on the prototype root never being one: its
        // `instanceable` opinion must read inert here (the root node is
        // instance-local, so `mark_instance_local_inert` above drops it).
        // Otherwise plain prototype content would wrongly redirect and the root
        // would self-redirect. Guard the invariant against a future change to the
        // instance-local partition.
        debug_assert!(
            !matches!(
                index.resolve_field(FieldKey::Instanceable.as_str(), graph, None),
                Ok(Some(Value::Bool(true)))
            ),
            "materialized prototype root's instanceable must be inert",
        );
        self.cache_index(graph, prototype, index, context);
    }

    /// Returns the synthetic prototype path (`/__Prototype_N`) shared by
    /// `instance`, registering it on first use. `None` when `instance` is not
    /// an instance prim (spec 11.3.3).
    pub(crate) fn prototype_of(&mut self, graph: &LayerGraph, instance: &Path) -> Result<Option<Path>> {
        if !self.is_instance(graph, instance)? {
            return Ok(None);
        }
        Ok(Some(self.register_prototype(graph, instance)?.1))
    }

    /// The instances sharing the prototype at `prototype` (a `/__Prototype_N`
    /// path), sorted by namespace path. Empty for unknown paths.
    pub(crate) fn instances_of(&self, prototype: &Path) -> Vec<Path> {
        self.prototypes.instances_of(prototype)
    }

    /// The registered `/__Prototype_N` roots, in registration order.
    pub(crate) fn prototypes(&self) -> Vec<Path> {
        self.prototypes.roots()
    }

    /// Returns `true` if `path` is a `/__Prototype_N` root.
    pub(crate) fn is_prototype(&self, path: &Path) -> bool {
        self.prototypes.is_root(path)
    }

    /// Returns `true` if `path` lies within a prototype's namespace — i.e. it
    /// has a `/__Prototype_N` ancestor (spec 11.3.3).
    pub(crate) fn is_in_prototype(&self, path: &Path) -> bool {
        self.prototypes.is_in_prototype(path)
    }

    /// Returns the `/__Prototype_N` root enclosing `path` (inclusive of `path`
    /// when it is itself a root), or `None` when `path` is not in a prototype
    /// namespace (spec 11.3.3). Used to gate prototype content against the
    /// population mask through its instances.
    pub(crate) fn prototype_root_of(&self, path: &Path) -> Option<Path> {
        self.prototypes.enclosing_root(Some(path.clone()))
    }

    /// The instances sharing the prototype at `root`, borrowed in registration
    /// order for membership checks (e.g. population-mask gating). Empty for a
    /// path that is not a prototype root.
    pub(crate) fn prototype_instances(&self, root: &Path) -> &[Path] {
        self.prototypes.instances_unsorted(root)
    }

    /// Returns `true` if `path` is an instance proxy — a strict descendant of an
    /// instance prim standing in for a prim in that instance's shared prototype
    /// (spec 11.3.3). This holds both in the ordinary instance namespace
    /// (`/A/child`) and inside a prototype namespace under a *nested* instance
    /// (`/__Prototype_N/.../NestedInstance/child`): each has an enclosing
    /// instance. Prototype content not under a nested instance has no enclosing
    /// instance (the prototype root's `instanceable` opinion is inert), so it is
    /// in a prototype, not a proxy.
    ///
    /// A proxy stands in for a real prim in the shared prototype, so a path under
    /// an instance that composes to no prim (e.g. a misspelled child) is not a
    /// proxy — mirroring the existence check on [`Self::is_instance`] /
    /// `Prim::is_valid`.
    pub(crate) fn is_instance_proxy(&mut self, graph: &LayerGraph, path: &Path) -> Result<bool> {
        if path.is_abs_root() || self.is_prototype(path) {
            return Ok(false);
        }
        if self.enclosing_instance(graph, path)?.is_none() {
            return Ok(false);
        }
        self.has_spec(graph, path)
    }

    /// Returns the prim in the shared prototype an instance proxy stands in for:
    /// a proxy `instance/tail` maps to `/__Prototype_N/tail` (spec 11.3.3).
    /// `None` when `path` is not an instance proxy (including a path under an
    /// instance that composes to no prim).
    pub(crate) fn prim_in_prototype(&mut self, graph: &LayerGraph, path: &Path) -> Result<Option<Path>> {
        if !self.is_instance_proxy(graph, path)? {
            return Ok(None);
        }
        let instance = self
            .enclosing_instance(graph, path)?
            .expect("an instance proxy has an enclosing instance");
        let (_canonical, prototype) = self.register_prototype(graph, &instance)?;
        Ok(path.replace_prefix(&instance, &prototype))
    }

    /// Returns the nearest strict ancestor of `path` that resolves as an
    /// instance prim (spec 11.3.3), or `None` when `path` is not inside an
    /// instance.
    //
    // TODO(perf): each [`is_instance`](Self::is_instance) here itself redirects
    // through `effective_path`, which walks back up via this function — so a cold
    // first query on a depth-d path is O(d²) (cheap path/hashmap ops, no extra
    // composition). The `redirected_prims` memo collapses it to O(d) once the
    // ancestors are warm, which a top-down traversal keeps it; a dedicated
    // `is_instance` memo would remove the cold-cache factor entirely.
    fn enclosing_instance(&mut self, graph: &LayerGraph, path: &Path) -> Result<Option<Path>> {
        let mut ancestor = path.parent();
        while let Some(current) = ancestor {
            if current.is_abs_root() {
                break;
            }
            if self.is_instance(graph, &current)? {
                return Ok(Some(current));
            }
            ancestor = current.parent();
        }
        Ok(None)
    }

    /// Maps a prim path to the path that actually composes it. An instance proxy
    /// — a strict descendant of an instance prim — is redirected into the shared
    /// prototype's namespace, so identical instances share one composed subtree
    /// (spec 11.3.3). Other paths — the prototype namespace itself, an instance
    /// root, and non-instanced prims — pass through unchanged.
    fn redirect_prim(&mut self, graph: &LayerGraph, prim: &Path) -> Result<Path> {
        match self.redirect_anchor(graph, prim)? {
            Some((origin, target)) => Ok(prim.replace_prefix(&origin, &target).unwrap_or_else(|| prim.clone())),
            None => Ok(prim.clone()),
        }
    }

    /// Returns the `(origin, target)` prefixes that map `prim`'s queried
    /// namespace onto the shared prototype's composition, or `None` when `prim`
    /// composes in place (spec 11.3.3).
    ///
    /// `prim` redirects onto the nearest enclosing instance's prototype, so
    /// identical instances share one composed subtree. This is uniform across
    /// namespaces: an ordinary instance proxy (`/A/tail` → `/__Prototype_N/tail`,
    /// including the canonical instance's own descendants) and a nested instance
    /// proxy *inside* a prototype (`/__Prototype_0/Nested/tail`, where `Nested`
    /// is itself an instance → the nested prototype) both map onto the prototype
    /// they stand in for.
    ///
    /// A prim with no enclosing instance composes in place: an instance *root*
    /// (spec 11.3.3 lets it override property values), the prototype root and its
    /// plain content (the materialized prototype root's `instanceable` opinion is
    /// inert, so it is never an enclosing instance — the shared subtree lives
    /// there, composed by deepening the materialized index), and every
    /// non-instanced prim.
    pub(super) fn redirect_anchor(&mut self, graph: &LayerGraph, prim: &Path) -> Result<Option<(Path, Path)>> {
        if let Some(instance) = self.enclosing_instance(graph, prim)? {
            let (_canonical, prototype) = self.register_prototype(graph, &instance)?;
            return Ok(Some((instance, prototype)));
        }
        Ok(None)
    }

    /// Redirects `path` (prim or property) through [`Self::redirect_prim`],
    /// preserving any property suffix. Applied at every descendant-serving
    /// query entry point so an instance proxy's subtree is served from the
    /// shared prototype rather than recomposed per instance.
    ///
    /// The prim-level redirection is memoized in `redirected_prims` (including
    /// the identity result for a non-redirected prim, the common case), so the
    /// ancestor walk that finds an enclosing instance runs once per prim path
    /// rather than once per query; the memo is cleared whenever the prototype
    /// registry is invalidated.
    pub(super) fn effective_path(&mut self, graph: &LayerGraph, path: &Path) -> Result<Path> {
        let prim = path.prim_path();
        let redirected = match self.redirected_prims.get(&prim) {
            Some(hit) => hit.clone(),
            None => {
                let redirected = self.redirect_prim(graph, &prim)?;
                self.redirected_prims.insert(prim.clone(), redirected.clone());
                redirected
            }
        };
        if redirected == prim {
            return Ok(path.clone());
        }
        // Re-anchor any property suffix onto the redirected prim; for a prim
        // path this is the redirected prim itself.
        Ok(path.replace_prefix(&prim, &redirected).unwrap_or(redirected))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(s: &str) -> Path {
        Path::new(s).expect("valid test path")
    }

    /// A key whose identity is a single tagged selection, enough to drive the
    /// registry's dedup without composing a real index.
    fn key(tag: &str) -> InstanceKey {
        InstanceKey {
            arcs: Vec::new(),
            selections: vec![(tag.to_string(), tag.to_string())],
        }
    }

    /// `remove_affected` drops only the prototypes whose instances or root the
    /// change set touches, leaving the rest mapped, and re-registration mints a
    /// fresh identity for a dropped prototype.
    #[test]
    fn remove_affected_targets_touched() {
        let mut reg = PrototypeRegistry::default();
        // /A and /B share one prototype; /C has its own.
        let (_, p0, minted0) = reg.register(key("p"), &path("/A"));
        reg.register(key("p"), &path("/B"));
        let (_, p1, minted1) = reg.register(key("q"), &path("/C"));
        assert!(minted0 && minted1);
        assert_ne!(p0, p1);

        // A change under /C touches only its prototype.
        let dropped = reg.remove_affected(&[path("/C/Child")]);
        assert_eq!(dropped, vec![p1.clone()]);
        assert_eq!(reg.canonical_of(&p0), Some(path("/A")));
        assert!(reg.canonical_of(&p1).is_none());

        // Re-registering /C mints a fresh identity (count stays monotonic).
        let (_, p1b, minted) = reg.register(key("q"), &path("/C"));
        assert!(minted);
        assert_ne!(p1b, p1);
    }

    /// An unrelated change leaves every prototype mapping intact.
    #[test]
    fn remove_affected_keeps_unrelated() {
        let mut reg = PrototypeRegistry::default();
        let (_, p0, _) = reg.register(key("p"), &path("/A"));
        let (_, p1, _) = reg.register(key("q"), &path("/C"));

        assert!(reg.remove_affected(&[path("/Extra")]).is_empty());
        assert!(reg.canonical_of(&p0).is_some());
        assert!(reg.canonical_of(&p1).is_some());
    }

    /// A change at an instance's ancestor (or the prototype root itself) is on
    /// the chain, so it invalidates the prototype.
    #[test]
    fn remove_affected_ancestor_and_root() {
        let mut reg = PrototypeRegistry::default();
        let (_, p0, _) = reg.register(key("p"), &path("/Group/A"));

        // The prototype root itself is on the chain.
        assert_eq!(reg.remove_affected(std::slice::from_ref(&p0)), vec![p0.clone()]);

        // Re-register, then touch an ancestor of the instance.
        let (_, p0b, _) = reg.register(key("p"), &path("/Group/A"));
        assert_eq!(reg.remove_affected(&[path("/Group")]), vec![p0b]);
    }
}
