//! Per-prim composition index storage and its dependency tracking — the Rust
//! analog of C++ `PcpCache`'s index map plus `Pcp_Dependencies`.
//!
//! [`IndexStore`] owns one composed [`PrimEntry`] per prim, keyed by composed
//! path, together with the reverse `(layer, site) → prim-index-path`
//! [`Dependencies`] map that drives surgical invalidation. The two are written
//! and dropped in lockstep — every insert registers dependencies and every
//! removal retracts them — so the store exposes only paired mutations, never raw
//! mutable access to either map. A removal records the dropped prim in the
//! work set ([`IndexStore::release_evicted`]), which keeps the stacks it owned
//! until it is released.
//! [`IndexCache`](super::index_cache::IndexCache) holds one and coordinates the
//! cross-cutting concerns (transient query errors, the prototype registry, the
//! value-clip cache) around the store's index and dependency queries.

use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::mem;
use std::slice;

use crate::sdf::{self, Path};

use super::dependencies::Dependencies;
use super::diagnostics::Diagnostics;
use super::instancing::RetiredPrototype;
use super::layer_graph::{LayerGraph, LayerView};
use super::layer_stack::{LayerStackId, StackMarks};
use super::prim_index::{CompositionContext, NodeRuns, PrimEntry, PrimIndex, TargetMemo, TargetMemoKey};
use super::prim_indexer::ExprVarDeps;
use super::{CompositionDiagnostic, LayerId, QueryError};

/// Per-prim composition index storage with dependency tracking. See the
/// [module docs](self).
#[derive(Default)]
pub(super) struct IndexStore {
    /// Per-prim composition records, keyed by composed path. A [`sdf::PathTable`]
    /// so [`remove_subtrees`](Self::remove_subtrees) erases an invalidated
    /// subtree by a namespace walk.
    entries: sdf::PathTable<PrimEntry>,
    /// Reverse `(layer, site) → prim-index-path` map for surgical invalidation,
    /// kept in lockstep with `entries`.
    deps: Dependencies,
    /// Sentinel returned by [`cached`](Self::cached) for a path left uncached
    /// because its build demanded a not-yet-loaded layer.
    empty_index: PrimIndex,
    /// Cache-owner counts: for each non-root layer stack, how many cached
    /// entries' arenas, and how many work-set entries, reference it.
    /// Incremented by [`insert`](Self::insert) and by each copy
    /// [`transfer_work`](Self::transfer_work) places, kept when a removal
    /// moves an entry into the work set, and decremented when a work-set
    /// entry settles, retires or is released, so the key set is exactly the
    /// stacks the cache keeps alive — the mark set
    /// ([`mark_live_stacks`](Self::mark_live_stacks)) without walking any
    /// arena.
    stack_owners: HashMap<LayerStackId, usize>,
    /// Whether some stack lost its last cache owner since the last sweep —
    /// the signal that schedules a reclamation pass at the next edit seam,
    /// deliberately unthresholded: a single deletion, mute, or unload that
    /// orphans a stack must retire it (and its diagnostics) promptly.
    ownership_lost: bool,
    /// Source of every [`PrimRevision`] this store hands out. Monotonic and
    /// never reset, so a value it minted is never minted again.
    next_revision: u64,
    /// The work set: each cached prim a removal dropped, by path, with the
    /// stacks its index owned, which stay counted as owned until the entry is
    /// released ([`release_evicted`](Self::release_evicted)) or an insert
    /// rebuilds its prim.
    evicted: sdf::PathTable<Unsettled>,
    /// The prototypes an invalidation retired, with the instances that shared
    /// them, kept with the work set until settlement transfers their
    /// descendants' work or the work set is released.
    retired: Vec<RetiredPrototype>,
}

/// A cached prim a removal dropped, waiting in the work set.
#[derive(Debug)]
pub(super) struct Unsettled {
    /// The stacks the dropped index owned, still counted as owned.
    stacks: Box<[LayerStackId]>,
    /// The last attempt to settle the prim, when it failed: the error's
    /// text and the round it failed in.
    failure: Option<(String, u64)>,
}

/// Validity token for a cached answer about one composed prim.
///
/// A cache that resolves something from a prim's composed state — today the
/// [`AttributeValueSource`](super::index_cache::AttributeValueSource) an
/// `AttributeQuery` replays — stamps the prim's revision beside it and rechecks
/// equality before reusing it. The answer is valid exactly while the two
/// compare equal: a rebuilt entry, an entry restaled by a value edit, and a
/// dropped entry (no token at all) each fail the check.
///
/// Values are minted only by [`IndexStore::mint_revision`], which owns the
/// counter behind them; the field is private to this module, so no production
/// seam can forge or reuse one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct PrimRevision(u64);

impl PrimRevision {
    /// A revision for an entry assembled outside an [`IndexStore`], in a
    /// scratch build cache no cached answer reads. Zero is never minted, so it
    /// cannot collide with a stamp any cached answer holds.
    pub(super) fn placeholder() -> Self {
        Self(0)
    }
}

/// One prim's value-tier invalidation: how far it reaches, and which resolved
/// target memos go with it.
///
/// The two travel together because they are found together — a target edit is a
/// value change on the same property — and because normalization must not
/// separate them: absorbing a work item into an ancestor's subtree carries its
/// memo keys along, where dropping the item would silently keep a stale memo.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct ScopedInvalidation {
    /// How far from the recorded path the change reaches.
    pub scope: ValueScope,
    /// Whether the prim's composed property set may have changed, so the
    /// property-derived diagnostics recorded against it no longer describe it.
    /// Set by a property spec appearing or vanishing; a value moving under an
    /// unchanged spec leaves the set alone.
    pub properties: bool,
    /// Resolved-target memos to drop — a `targetPaths` / `connectionPaths` edit
    /// changed a relationship or connection this prim composes in place, or one
    /// it reads through an arc. The prim's other relationships and connections
    /// keep their memos. The graph is intact, so the index survives; the next
    /// query recomposes the targets live.
    pub target_keys: BTreeSet<TargetMemoKey>,
}

/// How far a value-tier invalidation reaches from the prim it is recorded at.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ValueScope {
    /// That prim alone: the change is at a site the prim reads exactly.
    #[default]
    Prim,
    /// The prim and every cached descendant. Ordered above
    /// [`Prim`](Self::Prim), so accumulating the two widens rather than
    /// narrows.
    Subtree,
}

#[cfg(test)]
impl IndexStore {
    /// Every cached entry's path and current stamp, for a test that measures how
    /// far an edit's restaling reached by diffing two snapshots.
    pub(super) fn revisions(&self) -> Vec<(Path, PrimRevision)> {
        self.entries
            .iter()
            .map(|(path, entry)| (path.clone(), entry.revision))
            .collect()
    }
}

impl IndexStore {
    /// Borrows the composed index at `path`, or `None` when no entry is cached.
    pub(super) fn index_at(&self, path: &Path) -> Option<&PrimIndex> {
        self.entries.get(path).map(|entry| &entry.index)
    }

    /// The child-propagation context cached at `path`, if any.
    pub(super) fn context_at(&self, path: &Path) -> Option<&CompositionContext> {
        self.entries.get(path).map(|entry| &entry.context)
    }

    /// Borrows the cached index at `path`, returning the empty index when the
    /// path is uncached — the transient demanded-layer case (see
    /// [`IndexCache::cached`](super::index_cache::IndexCache::cached)).
    pub(super) fn cached(&self, path: &Path) -> &PrimIndex {
        self.index_at(path).unwrap_or(&self.empty_index)
    }

    /// Whether a composed index is currently cached at `path`.
    pub(super) fn is_indexed(&self, path: &Path) -> bool {
        self.entries.contains_key(path)
    }

    /// Number of cached prim indices.
    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }

    /// The whole per-prim table, for the builder and relocate evaluation to read
    /// already-composed indices keyed by stage path.
    pub(super) fn entries(&self) -> &sdf::PathTable<PrimEntry> {
        &self.entries
    }

    /// Read-only access to the dependency map for change-driven invalidation.
    pub(super) fn dependencies(&self) -> &Dependencies {
        &self.deps
    }

    /// Every recoverable build error across all cached entries, for
    /// [`composition_errors`](super::index_cache::IndexCache::composition_errors).
    pub(super) fn errors(&self) -> impl Iterator<Item = &CompositionDiagnostic> {
        self.entries
            .iter()
            .flat_map(|(_, entry)| entry.errors.iter().chain(entry.property_errors.iter()))
    }

    /// Marks every layer stack some cached prim index, or a work-set entry,
    /// owns — the key set of
    /// the maintained owner counts, so no arena is walked. The counts cover
    /// every arena node, inert and culled included, since query paths still
    /// dereference their stacks (the spec-tier refresh reads culled nodes, and
    /// a caller-held [`PrimIndex`] clone reaches every node); prototype
    /// indices are ordinary entries, counted the same way.
    pub(super) fn mark_live_stacks(&self, marks: &mut StackMarks) {
        for &stack in self.stack_owners.keys() {
            marks.mark(stack);
        }
    }

    /// Replaces a cached entry's property-derived diagnostics
    /// ([`PrimEntry::property_errors`]), returning whether an entry was there to
    /// hold them.
    ///
    /// Wholesale replacement, because these are recomputed from the prim's whole
    /// composed property set every time that set may have moved: a conflict the
    /// recomputation no longer finds is one the edit fixed. The build's
    /// graph-derived diagnostics arrive separately, with
    /// [`insert`](Self::insert).
    pub(super) fn replace_property_errors(&mut self, path: &Path, diagnostics: Diagnostics) -> bool {
        match self.entries.get_mut(path) {
            Some(entry) => {
                entry.property_errors = diagnostics;
                true
            }
            None => false,
        }
    }

    /// Clears every entry's recorded build errors in place, keeping the indices —
    /// the test-only reset of accumulated diagnostics.
    #[cfg(test)]
    pub(super) fn clear_errors(&mut self) {
        for (_, entry) in self.entries.iter_mut() {
            entry.errors.clear();
            entry.property_errors.clear();
        }
    }

    /// Caches `index` at `path` with the `context` its children inherit and its
    /// build `errors`, registering its dependencies — the `(layer, site)` map
    /// derived from the index plus the build's per-stack expression-variable
    /// names (`expr_var_deps`). The single insertion point: entries and
    /// dependencies are written together.
    pub(super) fn insert(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
        index: PrimIndex,
        context: CompositionContext,
        errors: Diagnostics,
        expr_var_deps: ExprVarDeps,
    ) {
        // Owner counts pair one increment per entry with one decrement at its
        // removal; a silent overwrite would double-count.
        debug_assert!(!self.entries.contains_key(path), "insert over a cached entry");
        self.own_stacks(owned_stacks(&index));
        // A prim the work set held is rebuilt: the new entry counts its own
        // stacks, so the dropped index's stop being owned.
        self.settle(path);
        self.deps.add(path, &index, graph, expr_var_deps);
        let revision = self.mint_revision();
        self.entries.insert(
            path.clone(),
            PrimEntry {
                index,
                context,
                errors,
                property_errors: Diagnostics::default(),
                resolved_targets: HashMap::new(),
                instanceable: None,
                revision,
            },
        );
    }

    /// The next unused [`PrimRevision`]. Every stamp comes from here, so two
    /// live entries never share one and a rebuilt entry never repeats its
    /// predecessor's.
    ///
    /// Overflow is checked rather than assumed away: the token's whole contract
    /// is that equality means identity, which a wrap would break.
    fn mint_revision(&mut self) -> PrimRevision {
        self.next_revision = self
            .next_revision
            .checked_add(1)
            .expect("prim revision counter exhausted");
        PrimRevision(self.next_revision)
    }

    /// The revision stamped on the entry at `path`, or `None` when none is
    /// cached — which no cached answer may validate against.
    pub(super) fn revision_at(&self, path: &Path) -> Option<PrimRevision> {
        self.entries.get(path).map(|entry| entry.revision)
    }

    /// Stamps a fresh revision on the cached entry at `path`, dropping the
    /// resolved-target memos at `keys` with it — the scoped restale, for a
    /// mutation that changed what the prim composes without changing its graph.
    ///
    /// A path with no cached entry is a no-op: nothing there holds an answer.
    pub(super) fn restale(&mut self, path: &Path, keys: &BTreeSet<TargetMemoKey>) {
        // Minted only once the entry is known to be there: a dependency fanout
        // names plenty of paths nothing is cached at, and a value handed to no
        // entry is a counter step spent on nothing.
        if !self.entries.contains_key(path) {
            return;
        }
        let revision = self.mint_revision();
        if let Some(entry) = self.entries.get_mut(path) {
            entry.revision = revision;
            for key in keys {
                entry.resolved_targets.remove(key);
            }
        }
    }

    /// [`restale`](Self::restale) for `prefix` and every cached descendant — the
    /// reach of a mutation that follows namespace, such as a clip set an
    /// ancestor introduced, or one whose exact composed path an arc's namespace
    /// mapping puts out of reach.
    //
    // TODO(perf): the paths are collected before the walk (a stamp needs `&mut`
    // on the table the iterator borrows), so each is cloned and looked up again.
    // The root prefix makes that the whole cache — every `expressionVariables`
    // edit takes that path, since a value-time `${VAR}` names the root stack's
    // every prim.
    pub(super) fn restale_subtree(&mut self, prefix: &Path, keys: &BTreeSet<TargetMemoKey>) {
        let paths: Vec<Path> = self.entries.subtree(prefix).map(|(path, _)| path.clone()).collect();
        for path in paths {
            self.restale(&path, keys);
        }
    }

    /// The cached prims in `prefix`'s subtree, `prefix` included.
    pub(super) fn subtree_paths(&self, prefix: &Path) -> Vec<Path> {
        self.entries.subtree(prefix).map(|(path, _)| path.clone()).collect()
    }

    /// Records one more ownership of each of `stacks`.
    fn own_stacks(&mut self, stacks: impl IntoIterator<Item = LayerStackId>) {
        for stack in stacks {
            *self.stack_owners.entry(stack).or_default() += 1;
        }
    }

    /// Releases one ownership of each of `stacks`, flagging a reclamation
    /// pass when a stack loses its last cache owner.
    fn release_stacks(&mut self, stacks: impl IntoIterator<Item = LayerStackId>) {
        for stack in stacks {
            match self.stack_owners.entry(stack) {
                Entry::Occupied(mut count) => {
                    *count.get_mut() -= 1;
                    if *count.get() == 0 {
                        count.remove();
                        self.ownership_lost = true;
                    }
                }
                Entry::Vacant(_) => debug_assert!(false, "released a stack with no recorded owner"),
            }
        }
    }

    /// Drops the entry at each of `paths`, retracting their dependency
    /// registrations together and recording each in the work set.
    pub(super) fn remove_all<'p>(&mut self, paths: impl IntoIterator<Item = &'p Path>) {
        let mut victims = Vec::new();
        for path in paths {
            if let Some(entry) = self.entries.remove(path) {
                self.evict(path, &entry.index);
                victims.push(path.clone());
            }
        }
        self.deps.remove_all(&victims);
    }

    /// Drops each of `prefixes` and every namespace descendant, retracting the
    /// removed entries' dependencies together and recording each in the work
    /// set.
    pub(super) fn remove_subtrees<'p>(&mut self, prefixes: impl IntoIterator<Item = &'p Path>) {
        let mut victims = Vec::new();
        for prefix in prefixes {
            // `Path::has_prefix("")` returns `true` for every absolute path, so a
            // default-constructed `Path` would silently wipe the whole store without
            // any layer-stack rebuild — almost certainly a caller bug. Catch it loudly
            // in debug builds; the absolute root (`/`) is the legitimate "blow
            // everything" prefix.
            debug_assert!(
                !prefix.is_empty(),
                "remove_subtrees called with empty prefix — use Path::abs_root() to drop everything",
            );
            for (victim, entry) in self.entries.remove_subtree(prefix) {
                self.evict(&victim, &entry.index);
                victims.push(victim);
            }
        }
        self.deps.remove_all(&victims);
    }

    /// Records `path`'s dropped `index` in the work set with the stacks it
    /// owned, which stay counted as owned. A path is never both cached and in
    /// the work set: an insert settles it, and
    /// [`transfer_work`](Self::transfer_work) places no copy on a cached
    /// path, so dropping it again finds no entry for it there.
    fn evict(&mut self, path: &Path, index: &PrimIndex) {
        let stacks: Box<[LayerStackId]> = owned_stacks(index).into_iter().collect();
        let held = self.evicted.insert(path.clone(), Unsettled { stacks, failure: None });
        debug_assert!(held.is_none(), "a path in the work set was dropped again");
    }

    /// One [`CompositionDiagnostic::SettlementFailed`] per failed work-set
    /// entry.
    pub(super) fn settlement_failures(&self) -> impl Iterator<Item = CompositionDiagnostic> + '_ {
        let work = self.evicted.subtree(&Path::abs_root());
        work.filter_map(|(path, unsettled)| {
            let (reason, _) = unsettled.failure.as_ref()?;
            Some(CompositionDiagnostic::SettlementFailed {
                path: path.clone(),
                reason: reason.clone(),
            })
        })
    }

    /// Releases the whole work set, retired-prototype records included:
    /// every entry's stacks stop being owned, flagging a reclamation pass for
    /// each that loses its last owner.
    ///
    /// TODO: settlement, which rebuilds or retires each prim the work set
    /// holds, replaces this wholesale release.
    pub(super) fn release_evicted(&mut self) {
        self.retired.clear();
        if self.evicted.is_empty() {
            return;
        }
        let evicted = mem::take(&mut self.evicted);
        for (_, unsettled) in evicted.iter() {
            self.release_stacks(unsettled.stacks.iter().copied());
        }
    }

    /// Whether some stack lost its last cache owner since the last sweep.
    pub(super) fn ownership_lost(&self) -> bool {
        self.ownership_lost
    }

    /// Clears the ownership-loss flag after a sweep consumed it.
    pub(super) fn reset_ownership_lost(&mut self) {
        self.ownership_lost = false;
    }

    /// The paths whose entry recorded a [`MalformedLayer`](CompositionDiagnostic::MalformedLayer)
    /// build error — an arc to an unreadable target that may now be readable, so
    /// the index should be dropped and re-demanded. Such an index carries no
    /// dependency on the failed target, so an ordinary layer-stack invalidation
    /// misses it.
    pub(super) fn paths_with_failed_layer(&self) -> Vec<Path> {
        self.entries
            .iter()
            .filter(|(_, entry)| {
                entry.errors.iter().any(|e| {
                    matches!(
                        e,
                        CompositionDiagnostic::MalformedLayer { .. } | CompositionDiagnostic::UnresolvedLayer { .. }
                    )
                })
            })
            .map(|(path, _)| path.clone())
            .collect()
    }

    /// Spec-tier refresh (C++ `Pcp_RescanForSpecs`): for every cached index that
    /// reads `(layer, path)` — the local prim and each dependent, found through
    /// the reverse dependency map — recompute its `has_specs` flags in place from
    /// live layer data, then partition it into `refreshed` (the flags were flipped
    /// in place) or `rebuild` (the in-place refresh cannot make it current).
    ///
    /// An index needs a rebuild when the local prim holds no contributing node at
    /// the site (a prior "no spec here" result), or a dependent had *culled* the
    /// site as an empty arc target that the spec now fills in, which must un-cull
    /// and graft the target's subtree.
    ///
    /// The memoized spec stack is left stale: the refresh keeps each touched
    /// node's fresh run in `refreshed`, and the caller splices them in once per
    /// index via [`splice_spec_stacks`](Self::splice_spec_stacks). An index
    /// reached by several of one round's sites therefore scans each of its nodes
    /// once, and rewrites its stack once.
    ///
    /// `rekeyed` collects every index in which a node an arc introduced gained
    /// or lost its specs ([`SpecRefresh::arc_specs_changed`]), whichever
    /// partition it landed in.
    pub(super) fn refresh_specs(
        &mut self,
        graph: &LayerView<'_>,
        layer: LayerId,
        path: &Path,
        refreshed: &mut sdf::PathMap<NodeRuns>,
        rebuild: &mut sdf::PathSet,
        rekeyed: &mut sdf::PathSet,
    ) {
        for prim in self.deps.exact_lookup(graph, layer, path) {
            // An index this round already condemned recomposes from scratch,
            // flags included, so the rescan leaves it alone.
            if rebuild.contains(&prim) {
                continue;
            }
            let Some(index) = self.entries.get_mut(&prim).map(|entry| &mut entry.index) else {
                continue;
            };
            // Taken out so the refresh sees what earlier sites in this round
            // already scanned, and put back under the owned path. It goes back
            // even when no node was touched, since the entry is also what earns
            // the index its revision stamp and its resync report.
            let mut runs = refreshed.remove(&prim).unwrap_or_default();
            let refresh = index.refresh_has_specs_at(layer, path, graph, &mut runs);
            if refresh.arc_specs_changed {
                rekeyed.insert(prim.clone());
            }
            // The local prim is one of its own dependents (it reads its own
            // site). Rebuild it when it carries no contributing node there; rebuild
            // any index whose culled site the spec just filled in.
            if refresh.needs_rebuild || (prim == *path && !refresh.contributing) {
                rebuild.insert(prim);
            } else {
                refreshed.insert(prim, runs);
            }
        }
        // A prim reached only through an ancestor of the site holds no node for
        // the spec just added: the arc it would compose through was culled and
        // erased in an ancestor's index, so the descendant never deepened a node
        // to here. Rebuild it to pick the spec up (C++ `DidChangeSpecs` adding
        // the prim to `didChangePrims`). A removed spec has no such prim to
        // catch up.
        if !graph.layer(layer).data().has_spec(path) {
            return;
        }
        for prim in self.translated_ancestor_dependents(graph, layer, path) {
            if rebuild.contains(&prim) {
                continue;
            }
            let Some(entry) = self.entries.get(&prim) else {
                continue;
            };
            if entry.index.node_providing_spec(graph, layer, path).is_none() {
                refreshed.remove(&prim);
                rebuild.insert(prim);
            }
        }
    }

    /// Splices each index's refreshed node runs into its memoized spec stack —
    /// what [`refresh_specs`](Self::refresh_specs) collected this change round,
    /// one call per index however many sites reached it — and returns the paths
    /// it consumed, for the caller's resync report. Every path here has a cached
    /// entry: [`refresh_specs`](Self::refresh_specs) records only indices it
    /// found, and the round's dropped set is disjoint from them.
    pub(super) fn splice_spec_stacks(&mut self, graph: &LayerView<'_>, refreshed: sdf::PathMap<NodeRuns>) -> Vec<Path> {
        let mut touched = Vec::with_capacity(refreshed.len());
        for (path, runs) in refreshed {
            debug_assert!(
                self.entries.contains_key(&path),
                "a refreshed index left the cache before its stack was spliced",
            );
            // Flipping `has_specs` changes what the prim composes, so the refresh
            // is a mutation like any rebuild: stamp it once here, where the round
            // reaches each affected index exactly once, rather than per site. The
            // entry above is what earns the token, keeping the rule
            // [`restale`](Self::restale) states: none is minted for nothing.
            let revision = self.mint_revision();
            if let Some(entry) = self.entries.get_mut(&path) {
                entry.index.respec_nodes(runs);
                entry.revision = revision;
                // The splice is a memo nothing downstream can re-derive on read,
                // so debug builds hold it against a full rebuild: this seam owns
                // both halves of that contract, the runs the refresh accumulated
                // and the index they were spliced into. Checked for every touched
                // index, including one the round spliced nothing into, since a
                // node the refresh should have matched and missed shows up only
                // as a stack that stayed put.
                debug_assert!(
                    entry.index.spec_stack_matches_rebuild(graph),
                    "spliced spec stack diverged from a full rebuild at {path}",
                );
            }
            touched.push(path);
        }
        touched
    }

    /// The composed prim paths a change at `(layer_id, site_path)` affects,
    /// through a dependency on that site or on an ancestor of it, each named in
    /// the namespace of the prim it affects.
    ///
    /// Folds in the layer-agnostic self-registrations, which is what keeps an
    /// empty or cache-miss index findable when a spec is first authored at its
    /// path on a layer its graph does not yet touch. Such a registration
    /// observes exactly its own path, so what it contributes is the changed path
    /// itself, whatever depth the registration sits at.
    pub(super) fn lookup_with_ancestors(&self, graph: &LayerGraph, layer_id: LayerId, site_path: &Path) -> Vec<Path> {
        let mut found = self.translated_sites(graph, layer_id, site_path, Ancestry::AtOrAbove);
        if self.deps.has_path_ancestor(site_path) {
            found.push(site_path.clone());
        }
        dedup_owned(found)
    }

    /// [`lookup_with_ancestors`](Self::lookup_with_ancestors) without the
    /// layer-agnostic self-registrations.
    ///
    /// Those exist so a cached prim stays findable on every layer, including
    /// ones its graph never touched, which is right for invalidation and wrong
    /// for a report about one layer's site: a prim merely cached at `/Source`
    /// would answer a question about `/Source` in a layer it does not read.
    pub(super) fn graph_ancestor_lookup(&self, graph: &LayerGraph, layer_id: LayerId, site_path: &Path) -> Vec<Path> {
        dedup_owned(self.translated_sites(graph, layer_id, site_path, Ancestry::AtOrAbove))
    }

    /// The composed paths reached through a graph site *above* `site_path`,
    /// translated into each dependent's own namespace.
    ///
    /// The site itself is left to [`exact_lookup`](Dependencies::exact_lookup),
    /// whose dependents read the change at their own path.
    pub(super) fn translated_ancestor_dependents(
        &self,
        graph: &LayerGraph,
        layer_id: LayerId,
        site_path: &Path,
    ) -> Vec<Path> {
        dedup_owned(self.translated_sites(graph, layer_id, site_path, Ancestry::StrictlyAbove))
    }

    /// Joins each registered `(site, dependent)` pair to the dependent's live
    /// index and translates `site_path` through the nodes that registered it —
    /// the port of C++ `PcpCache::FindSiteDependencies`, which likewise
    /// re-finds the node and maps through it rather than storing a map function
    /// per registration.
    ///
    /// One dependent can be reached through several of its own nodes — two
    /// references to the same prim — and each names its own composed path, so
    /// this yields a path per node rather than one per dependent.
    fn translated_sites(&self, graph: &LayerGraph, layer_id: LayerId, site_path: &Path, reach: Ancestry) -> Vec<Path> {
        let mut out = Vec::new();
        // One scratch buffer for the whole walk: a site typically names a single
        // node, and a fresh vector per pair would be the round's only allocation
        // that scales with the number of dependents.
        let mut nodes = Vec::new();
        for (site, dep) in self.deps.ancestor_sites(graph, layer_id, site_path) {
            if reach == Ancestry::StrictlyAbove && site == site_path {
                continue;
            }
            // A registration and its index are written and dropped together
            // (`insert` / `remove`), so a pair naming no entry is a broken
            // invariant. Silently skipping it would turn that into a missed
            // invalidation — a stale read — so it is loud instead.
            let index = &self
                .entries
                .get(dep)
                .unwrap_or_else(|| panic!("dependency on {dep} has no cached index"))
                .index;
            index.dependency_nodes_at(dep, layer_id, site, graph, &mut nodes);
            out.extend(
                nodes
                    .iter()
                    .filter_map(|&node| index.translate_dependency_path(node, site_path)),
            );
            // A culled node the index erased registered its site too, and
            // translates through what it recorded.
            out.extend(
                index
                    .culled_dependencies()
                    .iter()
                    .filter(|culled| culled.site == *site && graph.stack_contains(culled.layer_stack, layer_id))
                    .filter_map(|culled| culled.translate(site_path)),
            );
        }
        out
    }

    /// The [`TargetMemo`] resolved for `prim`'s property at `key`, or `None` on a
    /// miss. See [`PrimEntry::resolved_targets`].
    pub(super) fn target_memo(&self, prim: &Path, key: &TargetMemoKey) -> Option<&TargetMemo> {
        self.entries.get(prim).and_then(|entry| entry.resolved_targets.get(key))
    }

    /// Memoizes a [`TargetMemo`] for `prim`'s property at `key`. No-op when `prim`
    /// has no cached entry (its index was dropped mid-resolution).
    pub(super) fn set_target_memo(&mut self, prim: &Path, key: TargetMemoKey, memo: TargetMemo) {
        if let Some(entry) = self.entries.get_mut(prim) {
            entry.resolved_targets.insert(key, memo);
        }
    }

    /// [`PrimIndex::is_instanceable`] for the cached index at `prim`, answered
    /// once per entry revision ([`PrimEntry::instanceable`]). A path with no
    /// cached entry answers `false`, as the empty stand-in index
    /// [`cached`](Self::cached) returns would.
    pub(super) fn instanceable(&mut self, graph: &LayerView<'_>, prim: &Path) -> Result<bool, QueryError> {
        let Some(entry) = self.entries.get_mut(prim) else {
            return Ok(false);
        };
        if let Some((revision, instanceable)) = entry.instanceable
            && revision == entry.revision
        {
            return Ok(instanceable);
        }
        let instanceable = entry.index.is_instanceable(graph, prim.prim_element_count() as u16)?;
        entry.instanceable = Some((entry.revision, instanceable));
        Ok(instanceable)
    }

    /// Records `instanceable` as the [`instanceable`](Self::instanceable)
    /// answer for the entry at `prim`, at its current revision. The build that
    /// cached the entry has the answer already.
    pub(super) fn seed_instanceable(&mut self, prim: &Path, instanceable: bool) {
        if let Some(entry) = self.entries.get_mut(prim) {
            entry.instanceable = Some((entry.revision, instanceable));
        }
    }
}

/// The work set's settlement operations: what composing a dropped prim
/// again, or showing it gone, does to its entry.
impl IndexStore {
    /// The work set's paths, parents before children, less those whose
    /// settling failed in `round`.
    pub(super) fn work(&self, round: u64) -> Vec<Path> {
        let work = self.evicted.subtree(&Path::abs_root());
        work.filter(|(_, unsettled)| unsettled.failure.as_ref().is_none_or(|&(_, failed)| failed != round))
            .map(|(path, _)| path.clone())
            .collect()
    }

    /// Whether the work set holds `path`.
    pub(super) fn is_unsettled(&self, path: &Path) -> bool {
        self.evicted.contains_key(path)
    }

    /// Records that settling `path` failed with `reason` in `round`. The
    /// prim keeps its stacks; one failure is kept per prim, the last.
    pub(super) fn fail(&mut self, path: &Path, reason: String, round: u64) {
        if let Some(unsettled) = self.evicted.get_mut(path) {
            unsettled.failure = Some((reason, round));
        }
    }

    /// Records the failure for every work-set entry at and beneath `root`:
    /// what settling them waits on failed.
    pub(super) fn fail_work(&mut self, root: &Path, reason: &str, round: u64) {
        let work: Vec<Path> = self.evicted.subtree(root).map(|(path, _)| path.clone()).collect();
        for path in work {
            self.fail(&path, reason.to_owned(), round);
        }
    }

    /// Settles `path`: its stacks stop being owned and it leaves the work
    /// set.
    pub(super) fn settle(&mut self, path: &Path) {
        if let Some(settled) = self.evicted.remove(path) {
            self.release_stacks(settled.stacks.iter().copied());
        }
    }

    /// Retires `path`, which composes nothing or which the population does
    /// not reach: the cached entry there, built only to decide that, is
    /// dropped without entering the work set, and the work-set entries at
    /// and beneath it leave it. Their stacks stop being owned.
    pub(super) fn retire(&mut self, path: &Path) {
        if let Some(entry) = self.entries.remove(path) {
            self.deps.remove_all(slice::from_ref(path));
            self.release_stacks(owned_stacks(&entry.index));
        }
        for (_, retired) in self.evicted.remove_subtree(path) {
            self.release_stacks(retired.stacks.iter().copied());
        }
    }

    /// Keeps `records` with the work set, for settlement to transfer their
    /// descendants' work.
    pub(super) fn retire_prototypes(&mut self, records: impl IntoIterator<Item = RetiredPrototype>) {
        self.retired.extend(records);
    }

    /// Takes the retired-prototype records out for settlement to transfer.
    pub(super) fn take_retired(&mut self) -> Vec<RetiredPrototype> {
        mem::take(&mut self.retired)
    }

    /// Moves `root`'s work subtree under each of `targets`, re-rooted, each
    /// copy owning its stacks and carrying its failure; with no target, the
    /// work leaves the work set. A copy landing on a path the work set holds
    /// already merges into that entry, which owns each stack once; one
    /// landing on a cached prim is dropped, since that prim composed already.
    pub(super) fn transfer_work(&mut self, root: &Path, targets: &[Path]) {
        let taken = self.evicted.remove_subtree(root);
        for target in targets {
            for (path, unsettled) in &taken {
                let Some(path) = path.replace_prefix(root, target) else {
                    continue;
                };
                if self.entries.contains_key(&path) {
                    continue;
                }
                let held = self.evicted.get(&path).map_or(&[][..], |held| &held.stacks[..]);
                let added: Vec<LayerStackId> = unsettled
                    .stacks
                    .iter()
                    .copied()
                    .filter(|stack| !held.contains(stack))
                    .collect();
                self.own_stacks(added.iter().copied());
                if let Some(held) = self.evicted.get_mut(&path) {
                    held.stacks = held.stacks.iter().chain(&added).copied().collect();
                    if held.failure.is_none() {
                        held.failure.clone_from(&unsettled.failure);
                    }
                } else {
                    let stacks = added.into_boxed_slice();
                    let failure = unsettled.failure.clone();
                    self.evicted.insert(path, Unsettled { stacks, failure });
                }
            }
        }
        // Each copy counted its own stacks, so the taken entries' go.
        for (_, unsettled) in taken {
            self.release_stacks(unsettled.stacks.iter().copied());
        }
    }
}

/// The distinct non-root layer stacks an index's arena references — the
/// stacks a cached entry owns. The full arena counts, inert and culled nodes
/// included, since query paths still dereference their stacks.
fn owned_stacks(index: &PrimIndex) -> HashSet<LayerStackId> {
    index
        .arena()
        .map(|node| node.layer_stack_id())
        .filter(|&stack| stack != LayerStackId::ROOT)
        .collect()
}

/// How far up the namespace a lookup reaches for registered sites.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ancestry {
    /// The changed site and every ancestor of it.
    AtOrAbove,
    /// Ancestors only, leaving the site itself to `Dependencies::exact_lookup`.
    StrictlyAbove,
}

/// Deduplicates translated paths in place, keeping first-seen order.
fn dedup_owned(mut paths: Vec<Path>) -> Vec<Path> {
    let mut seen = sdf::PathSet::default();
    paths.retain(|p| seen.insert(p.clone()));
    paths
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    use crate::pcp::layer_graph::ExternalStack;
    use crate::pcp::mapping::MapFunction;
    use crate::pcp::prim_graph::{ArcType, NodeDesc};
    use crate::pcp::prim_index::CompositionContext;

    fn p(s: &str) -> Path {
        sdf::path(s).expect("valid path")
    }

    fn graph(n: usize) -> LayerGraph {
        let layers = (0..n)
            .map(|i| sdf::Layer::new_in_memory(format!("l{i}.usda")))
            .collect();
        LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default())
    }

    /// A node whose map carries `source -> target`, so a synthetic index can
    /// name exactly what a site translates to.
    fn node(g: &LayerGraph, layer: LayerId, site: &Path, map: MapFunction) -> NodeDesc {
        let stack = match g.external_stack_id(layer, LayerStackId::ROOT) {
            ExternalStack::Ready(id) => id,
            ExternalStack::Demand => panic!("no minted stack for test layer {layer:?}"),
        };
        NodeDesc::new(stack, layer, site.clone(), ArcType::Reference, map)
    }

    /// Registers `index` at `path` so the lookups can join it back.
    fn register(store: &mut IndexStore, g: &LayerGraph, path: &Path, index: PrimIndex) {
        store.insert(
            g,
            path,
            index,
            CompositionContext::default(),
            Diagnostics::default(),
            ExprVarDeps::default(),
        );
    }

    /// A one-layer graph plus a store holding a single index at `/Ref`, whose
    /// nodes all sit at site `/Source` and map it to the given targets — the
    /// shape every translation case below varies.
    fn ref_reading_source(maps: impl IntoIterator<Item = MapFunction>) -> (LayerGraph, LayerId, IndexStore) {
        let g = graph(1);
        let l0 = g.all_ids()[0];
        let site = p("/Source");
        let mut index = PrimIndex::default();
        for map in maps {
            index.push_node(node(&g, l0, &site, map));
        }
        let mut store = IndexStore::default();
        register(&mut store, &g, &p("/Ref"), index);
        (g, l0, store)
    }

    /// The instanceable memo answers only at the revision it was recorded at.
    /// The recorded answer here disagrees with the index, which has no
    /// instanceable node, so the two reads tell the memo from the index: a
    /// restale stamps a new revision, and the next query reads the index.
    #[test]
    fn instanceable_follows_revision() -> Result<(), QueryError> {
        let g = graph(1);
        let prim = p("/Prim");
        let mut store = IndexStore::default();
        register(&mut store, &g, &prim, PrimIndex::default());
        store.seed_instanceable(&prim, true);
        assert!(
            store.instanceable(&g.read_view(), &prim)?,
            "the recorded answer is read"
        );

        store.restale(&prim, &BTreeSet::new());
        assert!(
            !store.instanceable(&g.read_view(), &prim)?,
            "a new revision answers afresh"
        );
        Ok(())
    }

    /// The map a reference-shaped node carries: `source` composes at `target`.
    fn renaming(source: &str, target: &str) -> MapFunction {
        MapFunction::from_pair_identity(p(source), p(target))
    }

    /// The strict-ancestor lookup translates a change *below* an arc's site onto
    /// the dependent's namespace, and reports nothing for the site itself —
    /// which `exact_lookup` covers, at the dependent's own path.
    #[test]
    fn strict_ancestor_translates() {
        let (g, l0, store) = ref_reading_source([renaming("/Source", "/Ref")]);

        assert_eq!(
            store.translated_ancestor_dependents(&g, l0, &p("/Source/Child")),
            vec![p("/Ref/Child")],
            "the change below the arc composes under the dependent"
        );
        assert!(
            store.translated_ancestor_dependents(&g, l0, &p("/Source")).is_empty(),
            "the site itself is `exact_lookup`'s to report"
        );
    }

    /// Every matching node is translated, distinct results survive, and two
    /// nodes translating to one place collapse to a single entry.
    ///
    /// Deliberately not an ordering test: `push_node` appends each handle to
    /// both the arena and the strength order, so a synthetic index built with it
    /// alone cannot tell the two apart. See `translation_follows_strength`.
    #[test]
    fn translation_expands_dedups() {
        let (g, l0, store) = ref_reading_source(["/A", "/B", "/A"].map(|target| renaming("/Source", target)));

        assert_eq!(
            store.translated_ancestor_dependents(&g, l0, &p("/Source/Child")),
            vec![p("/A/Child"), p("/B/Child")],
            "three nodes, two distinct answers, first-seen order"
        );
    }

    /// The walk visits a site's nodes strongest-first, as C++ does through
    /// `PcpPrimIndex::GetNodeRange`. Arena order is a different permutation, so
    /// the weaker node is pushed first and must come back second.
    #[test]
    fn translation_follows_strength() {
        let g = graph(1);
        let l0 = g.all_ids()[0];
        let site = p("/Source");
        let mut index = PrimIndex::default();
        index.push_node(node(&g, l0, &site, renaming("/Source", "/Weak")));
        index.push_node_strongest(node(&g, l0, &site, renaming("/Source", "/Strong")));
        let mut store = IndexStore::default();
        register(&mut store, &g, &p("/Ref"), index);

        assert_eq!(
            store.translated_ancestor_dependents(&g, l0, &p("/Source/Child")),
            vec![p("/Strong/Child"), p("/Weak/Child")],
            "strength order, not the arena order the nodes were pushed in"
        );
    }

    /// A map whose result is shadowed by a closer inverse match is not a
    /// translation at all: `translate_to_target`'s bijection check drops it,
    /// where the bare prefix map would have kept it.
    #[test]
    fn shadowed_match_drops() {
        let g = graph(1);
        let l0 = g.all_ids()[0];
        // `{ / -> /, /_class_Model -> /Model }`: mapping `/Model` through the
        // identity is shadowed by the explicit pair's target.
        let mut index = PrimIndex::default();
        index.push_node(node(&g, l0, &p("/Model"), renaming("/_class_Model", "/Model")));
        let mut store = IndexStore::default();
        register(&mut store, &g, &p("/Ref"), index);

        assert!(
            store
                .translated_ancestor_dependents(&g, l0, &p("/Model/Child"))
                .is_empty(),
            "a non-invertible mapping has no composed image to invalidate"
        );
    }

    /// A blocked mapping — an empty target — carries nothing, so the node
    /// contributes no path rather than falling back to the dependent's root.
    #[test]
    fn unmappable_site_drops() {
        let (g, l0, store) = ref_reading_source([MapFunction::null()]);

        assert!(
            store
                .translated_ancestor_dependents(&g, l0, &p("/Source/Child"))
                .is_empty(),
            "a null map has no image for the changed path"
        );
    }

    /// The layer-agnostic self-registration contributes the *changed* path, not
    /// the ancestor path it was registered at, and only the invalidation lookup
    /// folds it in.
    #[test]
    fn self_path_translates() {
        let g = graph(1);
        let l0 = g.all_ids()[0];
        let own = p("/Foo");
        let mut index = PrimIndex::default();
        index.push_node(node(&g, l0, &own, MapFunction::identity()));
        let mut store = IndexStore::default();
        register(&mut store, &g, &own, index);

        let changed = p("/Foo/Child");
        assert_eq!(
            store.lookup_with_ancestors(&g, l0, &changed),
            vec![changed.clone()],
            "the self-registration answers with the changed path itself"
        );
    }

    /// `lookup_with_ancestors` folds the layer-agnostic self-registration in;
    /// `graph_ancestor_lookup` leaves it out while still returning the genuine
    /// graph readers of that site.
    #[test]
    fn graph_lookup_skips_self() {
        let g = graph(2);
        let (l0, l1) = (g.all_ids()[0], g.all_ids()[1]);
        let site = p("/Source");

        // A prim cached at `/Source` that reads only its own layer.
        let mut bystander = PrimIndex::default();
        bystander.push_node(node(&g, l0, &site, MapFunction::identity()));
        let mut store = IndexStore::default();
        register(&mut store, &g, &site, bystander);

        // A prim whose graph genuinely reads `/Source` on `l1`.
        let user = p("/User");
        let mut reader = PrimIndex::default();
        reader.push_node(node(&g, l1, &site, renaming("/Source", "/User")));
        register(&mut store, &g, &user, reader);

        assert_eq!(store.graph_ancestor_lookup(&g, l1, &site), vec![user.clone()]);
        assert!(
            store.lookup_with_ancestors(&g, l1, &site).contains(&site),
            "the invalidation lookup does fold the self-registration in"
        );
    }
    /// The paths `store`'s work set holds, parents before children.
    pub(crate) fn evicted(store: &IndexStore) -> Vec<String> {
        let evicted = store.evicted.subtree(&Path::abs_root());
        evicted.map(|(path, _)| path.to_string()).collect()
    }

    /// A dropped index's stacks stay owned while it waits in the work set,
    /// so no sweep is scheduled; releasing the work set lets them go.
    #[test]
    fn evicted_holds_stacks() {
        let g = graph(2);
        let referenced = g.all_ids()[1];
        let mut index = PrimIndex::default();
        index.push_node(node(&g, referenced, &p("/Source"), MapFunction::identity()));
        let stack = index.arena().next().expect("one node").layer_stack_id();
        assert_ne!(stack, LayerStackId::ROOT, "the node is in its own stack");
        let mut store = IndexStore::default();
        register(&mut store, &g, &p("/Ref"), index);

        store.remove_all([&p("/Ref")]);
        assert_eq!(evicted(&store), ["/Ref"]);
        assert!(store.stack_owners.contains_key(&stack), "still owned");
        assert!(!store.ownership_lost());

        store.release_evicted();
        assert!(evicted(&store).is_empty());
        assert!(!store.stack_owners.contains_key(&stack));
        assert!(store.ownership_lost(), "the release schedules a sweep");
    }
    /// Transferred work owns its stacks once per copy, a copy merging into a
    /// held entry owns each stack once, and work with no target leaves.
    #[test]
    fn transfer_counts_stacks() {
        let g = graph(2);
        let referenced = g.all_ids()[1];
        let indexed = || {
            let mut index = PrimIndex::default();
            index.push_node(node(&g, referenced, &p("/Source"), MapFunction::identity()));
            index
        };
        let stack = indexed().arena().next().expect("one node").layer_stack_id();
        let mut store = IndexStore::default();
        for path in ["/__Prototype_1", "/__Prototype_1/Part", "/__Prototype_2/Part"] {
            register(&mut store, &g, &p(path), indexed());
        }
        store.remove_subtrees([&p("/__Prototype_1"), &p("/__Prototype_2")]);
        assert_eq!(store.stack_owners[&stack], 3);

        // Two groups, one of them landing on a held entry.
        store.transfer_work(&p("/__Prototype_1"), &[p("/__Prototype_2"), p("/__Prototype_3")]);
        assert_eq!(
            evicted(&store),
            [
                "/__Prototype_2",
                "/__Prototype_2/Part",
                "/__Prototype_3",
                "/__Prototype_3/Part"
            ]
        );
        assert_eq!(store.stack_owners[&stack], 4, "one owner per entry");

        store.transfer_work(&p("/__Prototype_3"), &[]);
        assert_eq!(evicted(&store), ["/__Prototype_2", "/__Prototype_2/Part"]);
        assert_eq!(store.stack_owners[&stack], 2);
        store.release_evicted();
        assert!(!store.stack_owners.contains_key(&stack));
    }
}
