//! Three-tier change-processing pipeline for the composition cache.
//!
//! Mirrors C++ `PcpChanges`: a pure-analysis diff phase ([`Changes::did_change`])
//! builds invalidation path-sets keyed by tier; the apply phase
//! ([`Changes::apply`]) surgically blows the affected entries from the
//! cache.
//!
//! Tiers (matching C++ `_didChange{Significantly,Prims,Specs}`):
//!
//! - Significant: graph topology may be wrong — drop the index AND every
//!   namespace descendant.
//! - Prim: this index's graph is wrong but descendants survive — drop only
//!   this index.
//! - Spec: the graph is fine; only whether a site contributes an opinion
//!   changed. An inert spec add or remove authors no arc and no significant
//!   field, so [`IndexCache::rescan_specs`](super::IndexCache::rescan_specs)
//!   (C++ `Pcp_RescanForSpecs`) refreshes the affected nodes' `has_specs`
//!   flag in place instead of rebuilding, dropping the local index only when
//!   it holds no node at the site (a brand-new spec needs a fresh build).

use std::collections::BTreeSet;

use bitflags::bitflags;

use crate::sdf;
use crate::sdf::schema::FieldKey;
use crate::sdf::{ChangeEntry, ChangeList, Path};

use super::layer_graph::LayerGraph;
use super::{IndexCache, LayerId};

/// Plan + apply object for one author round.
///
/// Internal: callers construct a `Changes`, classify the drained
/// [`ChangeList`]s via [`Changes::did_change`], and commit via
/// [`Changes::apply`] against the same cache instance.
#[derive(Debug, Default)]
pub(crate) struct Changes {
    /// Per-cache invalidation path-sets.
    pub cache: CacheChanges,
    /// Per-layer-stack flags.
    pub layer_stack: LayerStackChanges,
}

/// Path-sets identifying which cached prim indices to invalidate.
#[derive(Debug, Default)]
pub struct CacheChanges {
    /// Drop the index AND every namespace descendant.
    pub(crate) did_change_significantly: BTreeSet<Path>,
    /// Drop only this index; descendants survive — for a change that reshapes
    /// this prim's own graph but cannot restructure its namespace children.
    pub(crate) did_change_prims: BTreeSet<Path>,
    /// Refresh `has_specs` at site `(layer, path)` rather than rebuild — for an
    /// inert spec add or remove, which flips only whether a site contributes an
    /// opinion. [`Changes::apply`] feeds each entry to
    /// [`IndexCache::rescan_specs`](super::IndexCache::rescan_specs).
    pub(crate) did_change_specs: BTreeSet<(LayerId, Path)>,
}

impl CacheChanges {
    /// The composed paths whose cached composition changed — the union of the
    /// significant, prim, and spec tiers. These are the paths a consumer must
    /// re-resolve (C++ `PcpCacheChanges` resync set). The spec tier is included
    /// so an inert spec add/remove (e.g. an `over`) is surfaced, not silently
    /// dropped, even though it refreshes `has_specs` in place rather than
    /// rebuilding the index.
    pub(crate) fn resynced_paths(&self) -> impl Iterator<Item = &Path> {
        self.did_change_significantly
            .iter()
            .chain(self.did_change_prims.iter())
            .chain(self.did_change_specs.iter().map(|(_, path)| path))
    }
}

bitflags! {
    /// Layer-stack-level change flags. Drives layer-stack precomputed-state
    /// rebuilds (sublayer ordering, layer offsets, relocates) inside the
    /// cache.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct LayerStackChanges: u8 {
        /// Sublayers were added/removed.
        const LAYERS = 1 << 0;
        /// Per-sublayer offsets were edited.
        const OFFSETS = 1 << 1;
        /// `layerRelocates` was edited.
        const RELOCATES = 1 << 2;
        /// The whole stack should be treated as significantly changed
        /// (every index dropped).
        const SIGNIFICANT = 1 << 3;

        /// Any change that requires recomputing the sublayer ordering /
        /// layer offsets map.
        const NEEDS_LAYER_STACK_REBUILD = Self::LAYERS.bits() | Self::OFFSETS.bits();
        /// Any change that requires recomputing the per-layer relocates
        /// table.
        const NEEDS_RELOCATES_REBUILD = Self::LAYERS.bits() | Self::RELOCATES.bits();
    }
}

impl Changes {
    /// Creates an empty change plan.
    pub fn new() -> Self {
        Self::default()
    }

    /// Diff phase: classify each [`ChangeEntry`] into the appropriate
    /// invalidation tier. Pure analysis — does not mutate `cache`.
    ///
    /// Property-path entries (attribute values, time samples, relationship
    /// targets) are intentionally ignored: those queries read live layer
    /// data on every call, so a newly authored value is visible without
    /// any cache mutation. When the cache memoizes resolved property or
    /// target stacks, a property-tier branch (keyed by property path) will
    /// land here.
    pub fn did_change(&mut self, cache: &IndexCache, changes: &[(LayerId, &ChangeList)]) {
        for (layer_index, cl) in changes {
            for (path, entry) in cl.entries() {
                if path.is_abs_root() {
                    self.classify_root_entry(cache, *layer_index, entry);
                } else if path.is_property_path() {
                    continue;
                } else {
                    self.classify_prim_entry(cache, *layer_index, path, entry);
                }
            }
        }
    }

    fn classify_prim_entry(&mut self, cache: &IndexCache, layer: LayerId, path: &Path, entry: &ChangeEntry) {
        let significant = entry.flags.intersects(sdf::ChangeFlags::NON_INERT_PRIM)
            || entry
                .info_changed
                .iter()
                .any(|k| Self::field_promotes_to_significant(k));

        if significant {
            self.fanout_significant(cache, layer, path);
            // An opinion authored inside a variant (`/Prim{set=sel}child`)
            // composes into the variant-stripped prim (`/Prim/child`). That
            // composed cache key is not on the authored path's ancestor chain
            // (`/Prim{set=sel}child` → `/Prim{set=sel}` → `/Prim` → `/`), so
            // fanning out from the variant path alone leaves a cached miss
            // there stale; invalidate it too.
            let stripped = path.strip_all_variant_selections();
            if stripped != *path {
                self.fanout_significant(cache, layer, &stripped);
            }
        } else if entry.flags.intersects(sdf::ChangeFlags::INERT_PRIM) {
            // An inert add or remove with no significant field flips only whether
            // `(layer, path)` contributes an opinion; the graph structure is
            // untouched. The change record surfaces the structural fields an
            // `over` carries into `info_changed`, so an arc / instancing / activation
            // opinion is already caught by the significant branch above; what
            // reaches here is a genuinely inert change. The spec-tier rescan
            // refreshes the affected nodes' `has_specs` flag across the local prim
            // and every dependent that reads the site, rebuilding only the
            // indices an in-place refresh cannot make current (see
            // [`IndexCache::rescan_specs`](super::IndexCache::rescan_specs)).
            self.cache.did_change_specs.insert((layer, path.clone()));
        }
    }

    fn classify_root_entry(&mut self, _cache: &IndexCache, _layer: LayerId, entry: &ChangeEntry) {
        for key in &entry.info_changed {
            if *key == FieldKey::SubLayers.as_str() {
                self.layer_stack |= LayerStackChanges::LAYERS | LayerStackChanges::SIGNIFICANT;
            } else if *key == FieldKey::SubLayerOffsets.as_str() {
                self.layer_stack |= LayerStackChanges::OFFSETS | LayerStackChanges::SIGNIFICANT;
            } else if *key == FieldKey::LayerRelocates.as_str() {
                self.layer_stack |= LayerStackChanges::RELOCATES | LayerStackChanges::SIGNIFICANT;
            } else if *key == FieldKey::TimeCodesPerSecond.as_str() || *key == FieldKey::FramesPerSecond.as_str() {
                // The effective timeCodesPerSecond (authored rate, else
                // framesPerSecond) retimes reference/payload arcs whose target
                // resolves at a different rate (spec 12.3.2, see
                // `arc_tcps_scale`). Every cached index that folded the old
                // ratio into an arc offset is now stale, so drop the stack.
                self.layer_stack |= LayerStackChanges::SIGNIFICANT;
            } else if *key == FieldKey::DefaultPrim.as_str() {
                self.cache.did_change_significantly.insert(Path::abs_root());
            }
        }
    }

    fn fanout_significant(&mut self, cache: &IndexCache, layer: LayerId, path: &Path) {
        for dep in cache.dependencies().lookup_with_ancestors(layer, path) {
            self.cache.did_change_significantly.insert(dep);
        }
        for dep in cache.dependencies().subtree_lookup(layer, path) {
            self.cache.did_change_significantly.insert(dep);
        }
        // Include the literal path even with no current dependent — a
        // first-time add will need its index built from scratch on next
        // access.
        self.cache.did_change_significantly.insert(path.clone());
    }

    /// Authoring this field on a prim path forces a graph rebuild.
    ///
    /// Mirrors C++ `Pcp_EntryRequiresPrimIndexChange` (changes.cpp:264-298): the
    /// composition-arc, instancing, and activation opinions plus `specifier`,
    /// whose def↔over↔class transitions change whether the prim and its subtree
    /// compose.
    fn field_promotes_to_significant(field: &str) -> bool {
        field == FieldKey::References.as_str()
            || field == FieldKey::Payload.as_str()
            || field == FieldKey::InheritPaths.as_str()
            || field == FieldKey::Specializes.as_str()
            || field == FieldKey::VariantSetNames.as_str()
            || field == FieldKey::VariantSelection.as_str()
            || field == FieldKey::Instanceable.as_str()
            || field == FieldKey::Specifier.as_str()
            || field == FieldKey::Active.as_str()
            // `apiSchemas` is composed off the cached prim index
            // (resolve_token_list_op in IndexCache::api_schemas), so any edit
            // must drop the index. Once registry-driven applied schemas inject
            // composition state, this becomes load-bearing for graph correctness.
            || field == FieldKey::ApiSchemas.as_str()
            // Per-prim `relocates` reshape composition (see `pcp::relocates`). No
            // Stage-tier producer authors this yet, but it matches the C++
            // classifier and forecloses a latent gap.
            || field == FieldKey::Relocates.as_str()
    }

    /// Apply phase: commit the planned invalidations to `cache`.
    pub fn apply(self, cache: &mut IndexCache, graph: &mut LayerGraph) {
        // Advance the composition revision so cached value views rebuild. This
        // is the single funnel for every authoring and layer-stack edit, so a
        // value-only change that drops no index still invalidates them.
        cache.bump_revision();
        // Any index invalidation can change which prims are instances or how
        // they compose, so affected entries in the shared-prototype registry
        // (spec 11.3.3) must be dropped rather than left stale; they are lazily
        // recomposed on the next instancing query. A prim-level change drops only
        // the prototypes whose instances or shared content it touches; a
        // layer-stack rebuild clears the whole registry as part of the
        // `clear_all_indices` below, so it needs no per-prototype work here.
        if !self.layer_stack.contains(LayerStackChanges::SIGNIFICANT)
            && (!self.cache.did_change_significantly.is_empty()
                || !self.cache.did_change_prims.is_empty()
                || !self.cache.did_change_specs.is_empty())
        {
            let changed: Vec<Path> = self
                .cache
                .did_change_significantly
                .iter()
                .chain(self.cache.did_change_prims.iter())
                .map(Path::prim_path)
                .chain(self.cache.did_change_specs.iter().map(|(_, path)| path.prim_path()))
                .collect();
            cache.invalidate_prototypes(&changed);
        }

        // Order matters: clear the index cache BEFORE rebuilding the
        // layer stack's precomputed state. Cached prim graphs were
        // composed against the old composed stacks and relocates; if a
        // future `recompute_*` ever inspects `indices` (e.g. to scope an
        // incremental rebuild) it must not see graphs pinned to the
        // pre-update state. The order is also panic-safe — if a
        // `recompute_*` panics, `indices` is already empty rather than
        // populated with stale entries pointing at the new stack.
        if self.layer_stack.contains(LayerStackChanges::SIGNIFICANT) {
            cache.clear_all_indices();
        }
        // A `subLayers`/`subLayerOffsets` edit rebuilds the graph's sublayer
        // edges (which subsumes the relocate recompute); a `layerRelocates`-only
        // edit refreshes the cached authored relocates. Each refreshes the
        // graph's own diagnostic buckets in place; the cache holds no copy.
        if self
            .layer_stack
            .intersects(LayerStackChanges::NEEDS_LAYER_STACK_REBUILD)
        {
            graph.recompute_sublayers();
        } else if self.layer_stack.intersects(LayerStackChanges::NEEDS_RELOCATES_REBUILD) {
            graph.recompute_relocates();
        }
        if self.layer_stack.contains(LayerStackChanges::SIGNIFICANT) {
            // Cache already cleared above; layer-stack precomputed state
            // is now in sync. Skip the per-path drops below since they'd
            // be no-ops against an empty cache.
            return;
        }
        for path in &self.cache.did_change_significantly {
            cache.drop_index_subtree(path);
        }
        for path in &self.cache.did_change_prims {
            // Subsumed by an ancestor in the significant set?
            if self.cache.did_change_significantly.iter().any(|p| path.has_prefix(p)) {
                continue;
            }
            cache.drop_index(path);
        }
        for (layer, path) in &self.cache.did_change_specs {
            // Subsumed by an ancestor whose subtree was already dropped.
            if self.cache.did_change_significantly.iter().any(|p| path.has_prefix(p)) {
                continue;
            }
            cache.rescan_specs(graph, *layer, path);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcp::VariantFallbackMap;
    use crate::sdf::{ChangeFlags, ChangeList};

    fn p(s: &str) -> Path {
        Path::new(s).expect("valid path")
    }

    /// The first layer id in the graph, or a placeholder for an empty graph.
    fn first_layer(graph: &LayerGraph) -> LayerId {
        graph.all_ids().first().copied().unwrap_or(LayerId::INVALID)
    }

    fn empty_cache() -> (LayerGraph, IndexCache) {
        let graph = LayerGraph::from_layers(Vec::new(), 0, sdf::LayerRegistry::default());
        (graph, IndexCache::new(VariantFallbackMap::new(), true, Vec::new()))
    }

    #[test]
    fn references_promotes_to_significant() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo"))
            .info_changed
            .insert(FieldKey::References.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(first_layer(&graph), &cl)]);
        assert!(changes.cache.did_change_significantly.contains(&p("/Foo")));
    }

    #[test]
    fn variant_selection_promotes_to_significant() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo"))
            .info_changed
            .insert(FieldKey::VariantSelection.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(first_layer(&graph), &cl)]);
        assert!(changes.cache.did_change_significantly.contains(&p("/Foo")));
    }

    /// An inert prim add whose spec authors `instanceable` flips the prim's
    /// instancing composition (spec 11.3.3); the change record surfaces
    /// `instanceable` in `info_changed`, so the classifier promotes it to
    /// significant despite the inert add flag.
    #[test]
    fn inert_add_with_instanceable_is_significant() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        let entry = cl.entry_mut(&p("/X"));
        entry.flags = ChangeFlags::ADD_INERT_PRIM;
        entry.info_changed.insert(FieldKey::Instanceable.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(first_layer(&graph), &cl)]);

        assert!(changes.cache.did_change_significantly.contains(&p("/X")));
    }

    #[test]
    fn inert_add_lands_on_spec_tier() {
        let (graph, cache) = empty_cache();
        let layer = first_layer(&graph);
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo")).flags = ChangeFlags::ADD_INERT_PRIM;
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(layer, &cl)]);
        // An inert add reshapes no graph, so it stays out of the significant
        // tier and lands in the spec tier keyed by its authoring layer.
        assert!(!changes.cache.did_change_significantly.contains(&p("/Foo")));
        assert!(changes.cache.did_change_specs.contains(&(layer, p("/Foo"))));
    }

    #[test]
    fn non_inert_add_is_significant_with_self_path() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo")).flags = ChangeFlags::ADD_NON_INERT_PRIM;
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(first_layer(&graph), &cl)]);
        assert!(changes.cache.did_change_significantly.contains(&p("/Foo")));
    }

    #[test]
    fn sublayers_change_is_layer_stack_significant() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(FieldKey::SubLayers.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(first_layer(&graph), &cl)]);
        assert!(changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
        assert!(changes.layer_stack.contains(LayerStackChanges::LAYERS));
    }

    #[test]
    fn default_prim_change_is_significant_at_root() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(FieldKey::DefaultPrim.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(first_layer(&graph), &cl)]);
        assert!(changes.cache.did_change_significantly.contains(&Path::abs_root()));
        assert!(!changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }

    /// Editing the root layer's `timeCodesPerSecond` (or its `framesPerSecond`
    /// fallback) retimes reference/payload arcs, so it must mark the whole
    /// layer stack significant to drop indices that folded the old ratio.
    #[test]
    fn time_codes_per_second_change_is_significant() {
        for field in [FieldKey::TimeCodesPerSecond, FieldKey::FramesPerSecond] {
            let (graph, cache) = empty_cache();
            let mut cl = ChangeList::new();
            cl.entry_mut(&Path::abs_root())
                .info_changed
                .insert(field.as_str().into());
            let mut changes = Changes::new();
            changes.did_change(&cache, &[(first_layer(&graph), &cl)]);
            assert!(changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
        }
    }

    #[test]
    fn layer_relocates_change_flags_relocates() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(FieldKey::LayerRelocates.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(first_layer(&graph), &cl)]);
        assert!(changes.layer_stack.contains(LayerStackChanges::RELOCATES));
        assert!(changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }

    #[test]
    fn property_changes_no_op() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo.attr")).flags = ChangeFlags::ADD_PROPERTY;
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(first_layer(&graph), &cl)]);
        assert!(changes.cache.did_change_significantly.is_empty());
        assert!(changes.cache.did_change_specs.is_empty());
        assert!(!changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }
}
