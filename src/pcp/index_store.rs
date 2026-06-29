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

use std::collections::HashSet;

use crate::sdf::{self, Path};

use super::dependencies::Dependencies;
use super::layer_graph::LayerGraph;
use super::prim_index::{CompositionContext, PrimEntry, PrimIndex};
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
        self.entries.insert(path.clone(), PrimEntry { index, context, errors });
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
    /// live layer data, and return the paths that cannot be refreshed in place and
    /// must be rebuilt.
    ///
    /// An index needs a rebuild only when the in-place refresh cannot make it
    /// current: the local prim holds no node at the site (a prior "no spec here"
    /// result), or a dependent had *culled* the site as an empty arc target that
    /// the spec now fills in, which must un-cull and graft the target's subtree.
    pub(super) fn refresh_specs(&mut self, graph: &LayerGraph, layer: LayerId, path: &Path) -> Vec<Path> {
        let mut rebuild = Vec::new();
        for prim in self.deps.exact_lookup(layer, path) {
            let Some(index) = self.entries.get_mut(&prim).map(|entry| &mut entry.index) else {
                continue;
            };
            let refresh = index.refresh_has_specs_at(layer, path, graph);
            // The local prim is one of its own dependents (it reads its own
            // site). Drop it when it carries no contributing node there; drop any
            // index whose culled site the spec just filled in.
            if refresh.needs_rebuild || (prim == *path && !refresh.contributing) {
                rebuild.push(prim);
            } else {
                // The `has_specs` flags changed in place, so rebuild the memoized
                // spec stack the same edit shifted — a site that gained or lost
                // its spec — keeping value resolution and introspection current.
                // A dropped index recomposes from scratch, so it needs none here.
                index.finalize_spec_stack(graph);
            }
        }
        rebuild
    }

    /// Every cached prim index whose composition reads one of the `affected`
    /// layers — the victim set for a layer-set invalidation (`invalidate_layers`),
    /// shared by a mute toggle and a `subLayers`/offset/relocate/`timeCodesPerSecond`
    /// edit.
    ///
    /// A mute passes [`mute_fanout`](super::layer_graph::LayerGraph)'s result (the
    /// toggled layer and every layer whose subtree contains it), so a sublayer
    /// stack's root stays present even when the toggle empties the stack. An edit
    /// passes the layers whose composed edges or relocates moved plus the authored
    /// layers, which stay resolvable members of their stacks. A node's layer stack
    /// lists the members it resolved against, so an index whose nodes touch an
    /// `affected` layer is exactly one the change can restructure. An index that
    /// skipped a reference/payload arc because the target root was muted keeps no
    /// node for it, so its recorded muted targets (see
    /// [`PrimIndex::muted_external_targets`]) are checked too — without that,
    /// unmuting the target could not find the index to recompose.
    ///
    /// TODO(perf): this scans every cached index (the reverse [`Dependencies`] map
    /// can't scope it — an index that skipped a muted target registered no
    /// dependency site to find it by). The per-index predicate is independent
    /// (`TODO(rayon)`).
    pub(super) fn indices_touching_layers(&self, graph: &LayerGraph, affected: &HashSet<LayerId>) -> Vec<Path> {
        self.entries
            .iter()
            .filter(|(_, entry)| {
                // A cached node resolves its `LayerStackId` against the
                // already-mutated graph here, so the two prongs are both needed and
                // complementary; correctness rests on the invariant that whenever a
                // node's stack contained a toggled layer, one of these holds:
                //   * the frozen `representative` (the stack's strongest member,
                //     recorded at composition) is in `affected` — this catches a
                //     toggle of a `Sublayer(L)` stack's own root `L`, whose live
                //     stack now resolves empty so the member scan would miss it;
                //   * a surviving resolved member is in `affected` — this catches a
                //     toggle deeper in the stack (e.g. a root sublayer on a stage
                //     with session layers, where the representative is a session
                //     layer outside the fanout but the root layer remains and is in
                //     `affected`).
                // The invariant holds because [`mute_fanout`](super::layer_graph::LayerGraph)'s
                // `ancestors_including` puts every layer whose subtree contains the
                // toggled one into `affected` (so a sublayer stack's root is always
                // in it), and the root anchor covers session-layer mutes. Pinned by
                // `mute_sublayer_drops_root_stack_index` / `mute_keeps_independent_index`;
                // do not narrow to a representative-only check.
                entry.index.dependency_nodes().any(|node| {
                    affected.contains(&node.layer_id())
                        || graph
                            .layer_stack(node.layer_stack_id())
                            .iter()
                            .any(|&(li, _)| affected.contains(&li))
                }) || entry
                    .index
                    .muted_external_targets()
                    .iter()
                    .any(|li| affected.contains(li))
            })
            .map(|(path, _)| path.clone())
            .collect()
    }
}
