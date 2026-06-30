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
//! composition revision) around the store's index and dependency queries.

use std::collections::{HashMap, HashSet};

use crate::sdf::{self, Path};

use super::dependencies::Dependencies;
use super::layer_graph::LayerGraph;
use super::prim_index::{CompositionContext, PrimEntry, PrimIndex, TargetMemo, TargetMemoKey};
use super::{Error, LayerId};

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
    pub(super) fn errors(&self) -> impl Iterator<Item = &Error> {
        self.entries.iter().flat_map(|(_, entry)| entry.errors.iter())
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
    /// build `errors`, registering its dependencies. The single insertion point:
    /// entries and dependencies are written together.
    pub(super) fn insert(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
        index: PrimIndex,
        context: CompositionContext,
        errors: Vec<Error>,
    ) {
        self.deps.add(path, &index, graph);
        self.entries.insert(
            path.clone(),
            PrimEntry {
                index,
                context,
                errors,
                resolved_targets: HashMap::new(),
            },
        );
    }

    /// Drops the entry at `path` and retracts its dependency registrations.
    pub(super) fn remove(&mut self, path: &Path) {
        self.entries.remove(path);
        self.deps.remove(path);
    }

    /// Drops `prefix` and every namespace descendant, retracting each removed
    /// entry's dependencies.
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
        for (victim, _) in self.entries.remove_subtree(prefix) {
            self.deps.remove(&victim);
        }
    }

    /// The paths whose entry recorded a [`MalformedLayer`](Error::MalformedLayer)
    /// build error — an arc to an unreadable target that may now be readable, so
    /// the index should be dropped and re-demanded. Such an index carries no
    /// dependency on the failed target, so an ordinary layer-stack invalidation
    /// misses it.
    pub(super) fn paths_with_malformed_layer(&self) -> Vec<Path> {
        self.entries
            .iter()
            .filter(|(_, entry)| entry.errors.iter().any(|e| matches!(e, Error::MalformedLayer { .. })))
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
    /// The memoized spec stack is left stale: the caller finalizes the deduped
    /// `refreshed` set once via [`finalize_spec_stacks`](Self::finalize_spec_stacks),
    /// so an index reached by several of one change round's sites rebuilds its
    /// stack a single time.
    pub(super) fn refresh_specs(
        &mut self,
        graph: &LayerGraph,
        layer: LayerId,
        path: &Path,
        refreshed: &mut HashSet<Path>,
        rebuild: &mut HashSet<Path>,
    ) {
        for prim in self.deps.exact_lookup(layer, path) {
            let Some(index) = self.entries.get_mut(&prim).map(|entry| &mut entry.index) else {
                continue;
            };
            let refresh = index.refresh_has_specs_at(layer, path, graph);
            // The local prim is one of its own dependents (it reads its own
            // site). Rebuild it when it carries no contributing node there; rebuild
            // any index whose culled site the spec just filled in.
            if refresh.needs_rebuild || (prim == *path && !refresh.contributing) {
                rebuild.insert(prim);
            } else {
                refreshed.insert(prim);
            }
        }
    }

    /// Rebuilds the memoized spec stack of each index at `paths`, the deduped set
    /// of indices [`refresh_specs`](Self::refresh_specs) flipped `has_specs` on in
    /// place this change round. Skips a path with no cached entry (one dropped for
    /// rebuild, which recomposes its stack from scratch).
    pub(super) fn finalize_spec_stacks<'p>(&mut self, graph: &LayerGraph, paths: impl IntoIterator<Item = &'p Path>) {
        for path in paths {
            if let Some(entry) = self.entries.get_mut(path) {
                entry.index.finalize_spec_stack(graph);
            }
        }
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

    /// Drops the single memoized property `key` from `prim`'s resolved-target map,
    /// for a `targetPaths` / `connectionPaths` edit that leaves the prim's graph
    /// intact but restales that one property's composed targets — the prim's other
    /// relationships and connections keep their memos. No-op when `prim` has no
    /// cached entry.
    pub(super) fn clear_target_memo(&mut self, prim: &Path, key: &TargetMemoKey) {
        if let Some(entry) = self.entries.get_mut(prim) {
            entry.resolved_targets.remove(key);
        }
    }
}
