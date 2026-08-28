//! Per-prim composition index storage and its dependency tracking — the Rust
//! analog of C++ `PcpCache`'s index map plus `Pcp_Dependencies`.
//!
//! [`IndexStore`] owns one composed [`PrimEntry`] per prim, keyed by composed
//! path, together with the reverse `(layer, site) → prim-index-path`
//! [`Dependencies`] map that drives surgical invalidation. The two are written
//! and dropped in lockstep — every insert registers dependencies and every
//! removal retracts them — so the store exposes only paired mutations, never raw
//! mutable access to either map.
//! [`IndexCache`](super::index_cache::IndexCache) holds one and coordinates the
//! cross-cutting concerns (transient query errors, the prototype registry, the
//! value-clip cache) around the store's index and dependency queries.

use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap, HashSet};

use crate::sdf::{self, Path};

use super::dependencies::Dependencies;
use super::layer_graph::LayerGraph;
use super::layer_stack::{LayerStackId, StackMarks};
use super::prim_index::{CompositionContext, NodeRuns, PrimEntry, PrimIndex, TargetMemo, TargetMemoKey};
use super::prim_indexer::ExprVarDeps;
use super::{CompositionError, LayerId};

/// Per-prim composition index storage with dependency tracking. See the
/// [module docs](self).
#[derive(Default)]
pub(super) struct IndexStore {
    /// Per-prim composition records, keyed by composed path. A [`sdf::PathTable`]
    /// so [`remove_subtree`](Self::remove_subtree) erases an invalidated subtree
    /// by a namespace walk.
    entries: sdf::PathTable<PrimEntry>,
    /// Reverse `(layer, site) → prim-index-path` map for surgical invalidation,
    /// kept in lockstep with `entries`.
    deps: Dependencies,
    /// Sentinel returned by [`cached`](Self::cached) for a path left uncached
    /// because its build demanded a not-yet-loaded layer.
    empty_index: PrimIndex,
    /// Cache-owner counts: for each non-root layer stack, how many cached
    /// entries' arenas reference it. Incremented by [`insert`](Self::insert)
    /// and decremented by the removals, so the key set is exactly the stacks
    /// the cache keeps alive — the mark set
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

#[cfg(test)]
impl PrimRevision {
    /// A revision for an entry assembled outside an [`IndexStore`] — the
    /// scratch build caches some indexer tests hand-build. Zero is never
    /// minted, so it cannot collide with a stamp any cached answer holds.
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
    pub(super) fn errors(&self) -> impl Iterator<Item = &CompositionError> {
        self.entries.iter().flat_map(|(_, entry)| entry.errors.iter())
    }

    /// Marks every layer stack some cached prim index owns — the key set of
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

    /// Clears every entry's recorded build errors in place, keeping the indices —
    /// the test-only reset of accumulated diagnostics.
    #[cfg(test)]
    pub(super) fn clear_errors(&mut self) {
        for (_, entry) in self.entries.iter_mut() {
            entry.errors.clear();
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
        errors: Vec<CompositionError>,
        expr_var_deps: ExprVarDeps,
    ) {
        // Owner counts pair one increment per entry with one decrement at its
        // removal; a silent overwrite would double-count.
        debug_assert!(!self.entries.contains_key(path), "insert over a cached entry");
        for stack in owned_stacks(&index) {
            *self.stack_owners.entry(stack).or_default() += 1;
        }
        self.deps.add(path, &index, graph, expr_var_deps);
        let revision = self.mint_revision();
        self.entries.insert(
            path.clone(),
            PrimEntry {
                index,
                context,
                errors,
                resolved_targets: HashMap::new(),
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

    /// Releases a removed entry's stack ownership, flagging a reclamation
    /// pass when a stack loses its last cache owner.
    fn release_owned(&mut self, index: &PrimIndex) {
        for stack in owned_stacks(index) {
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

    /// Drops the entry at `path`, retracting its dependency registrations and
    /// releasing its stack ownership.
    pub(super) fn remove(&mut self, path: &Path) {
        if let Some(entry) = self.entries.remove(path) {
            self.release_owned(&entry.index);
        }
        self.deps.remove(path);
    }

    /// Drops `prefix` and every namespace descendant, retracting each removed
    /// entry's dependencies and releasing its stack ownership.
    pub(super) fn remove_subtree(&mut self, prefix: &Path) {
        // `Path::has_prefix("")` returns `true` for every absolute path, so a
        // default-constructed `Path` would silently wipe the whole store without
        // any layer-stack rebuild — almost certainly a caller bug. Catch it loudly
        // in debug builds; the absolute root (`/`) is the legitimate "blow
        // everything" prefix.
        debug_assert!(
            !prefix.is_empty(),
            "remove_subtree called with empty prefix — use Path::abs_root() to drop everything",
        );
        for (victim, entry) in self.entries.remove_subtree(prefix) {
            self.release_owned(&entry.index);
            self.deps.remove(&victim);
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

    /// The paths whose entry recorded a [`MalformedLayer`](CompositionError::MalformedLayer)
    /// build error — an arc to an unreadable target that may now be readable, so
    /// the index should be dropped and re-demanded. Such an index carries no
    /// dependency on the failed target, so an ordinary layer-stack invalidation
    /// misses it.
    pub(super) fn paths_with_malformed_layer(&self) -> Vec<Path> {
        self.entries
            .iter()
            .filter(|(_, entry)| {
                entry
                    .errors
                    .iter()
                    .any(|e| matches!(e, CompositionError::MalformedLayer { .. }))
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
    pub(super) fn refresh_specs(
        &mut self,
        graph: &LayerGraph,
        layer: LayerId,
        path: &Path,
        refreshed: &mut HashMap<Path, NodeRuns>,
        rebuild: &mut HashSet<Path>,
    ) {
        for prim in self.deps.exact_lookup(layer, path) {
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
            // The local prim is one of its own dependents (it reads its own
            // site). Rebuild it when it carries no contributing node there; rebuild
            // any index whose culled site the spec just filled in.
            if refresh.needs_rebuild || (prim == *path && !refresh.contributing) {
                rebuild.insert(prim);
            } else {
                refreshed.insert(prim, runs);
            }
        }
    }

    /// Splices each index's refreshed node runs into its memoized spec stack —
    /// what [`refresh_specs`](Self::refresh_specs) collected this change round,
    /// one call per index however many sites reached it — and returns the paths
    /// it consumed, for the caller's resync report. Every path here has a cached
    /// entry: [`refresh_specs`](Self::refresh_specs) records only indices it
    /// found, and the round's dropped set is disjoint from them.
    pub(super) fn splice_spec_stacks(&mut self, graph: &LayerGraph, refreshed: HashMap<Path, NodeRuns>) -> Vec<Path> {
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
}

/// The distinct non-root layer stacks an index's arena references — the
/// stacks a cached entry owns. The full arena counts, inert and culled nodes
/// included, since query paths still dereference their stacks.
fn owned_stacks(index: &PrimIndex) -> HashSet<LayerStackId> {
    index
        .arena()
        .iter()
        .map(|node| node.layer_stack_id())
        .filter(|&stack| stack != LayerStackId::ROOT)
        .collect()
}
