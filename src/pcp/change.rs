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

/// Fields whose presence on an `over` makes it structural despite its inert
/// specifier: the composition-arc, instancing, and activation opinions that
/// reshape the graph. A created spec folds its field writes into the inert add
/// flag, so these never reach [`ChangeEntry::info_changed`]; the classifier
/// reads them off the spec instead. `specifier` is deliberately absent — every
/// prim authors one, so it cannot single out a structural `over`.
const STRUCTURAL_INERT_FIELDS: [FieldKey; 10] = [
    FieldKey::References,
    FieldKey::Payload,
    FieldKey::InheritPaths,
    FieldKey::Specializes,
    FieldKey::VariantSetNames,
    FieldKey::VariantSelection,
    FieldKey::Instanceable,
    FieldKey::Active,
    // `apiSchemas` composes off the cached prim index (IndexCache::api_schemas);
    // `relocates` reshapes composition (see `pcp::relocates`). Both are listed
    // for parity with the C++ classifier even though no Stage-tier producer
    // authors `relocates` on a prim yet.
    FieldKey::ApiSchemas,
    FieldKey::Relocates,
];

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
    /// any cache mutation. When the cache memoizes resolved property
    /// stacks, a tier-3 (`did_change_specs`) branch will land here.
    pub fn did_change(&mut self, cache: &IndexCache, graph: &LayerGraph, changes: &[(LayerId, &ChangeList)]) {
        for (layer_index, cl) in changes {
            for (path, entry) in cl.entries() {
                if path.is_abs_root() {
                    self.classify_root_entry(cache, *layer_index, entry);
                } else if path.is_property_path() {
                    continue;
                } else {
                    self.classify_prim_entry(cache, graph, *layer_index, path, entry);
                }
            }
        }
    }

    fn classify_prim_entry(
        &mut self,
        cache: &IndexCache,
        graph: &LayerGraph,
        layer: LayerId,
        path: &Path,
        entry: &ChangeEntry,
    ) {
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
            if self.inert_change_is_structural(cache, graph, layer, path, entry) {
                // An `over` carries no significant field in `info_changed` — a
                // created spec folds its field writes into the inert add flag —
                // yet it may still author (or, when removed, have authored) a
                // composition-arc, instancing, or activation opinion that
                // reshapes the graph despite the inert specifier; recompose the
                // subtree as for any significant change.
                self.fanout_significant(cache, layer, path);
            } else {
                // A non-structural inert add or remove flips only whether
                // `(layer, path)` contributes an opinion; the graph structure is
                // untouched. The spec-tier rescan refreshes the affected nodes'
                // `has_specs` flag in place — across the local prim and every
                // dependent that already reads the site — and drops the local
                // index only when it holds no node there (a brand-new spec needs
                // a fresh build).
                self.cache.did_change_specs.insert((layer, path.clone()));
            }
        }

        // TODO: an inert add at a path whose node a dependent prim culled from
        // its graph (an empty arc target) needs that dependent rebuilt so the
        // now-needed node re-enters. Blocked on culled-node tracking: the
        // `Indexer` culls weaker nodes during composition, and we keep no
        // `culled_dependencies` snapshot to consult, so the spec-tier rescan
        // refreshes only nodes still present in the dependent's graph.
    }

    /// Whether an inert prim add or remove actually reshapes the graph.
    ///
    /// A created spec's field writes fold into its inert add flag (see
    /// [`EditProxy`](crate::sdf::change)), so the significant fields an `over`
    /// carries never reach [`ChangeEntry::info_changed`] for the classifier to
    /// catch. An add is inspected on the spec itself; a remove cannot be (the
    /// spec is gone), so it is treated as structural whenever the cached index
    /// composes any arc the removed spec might have introduced.
    ///
    /// Inferring a removal from arc presence alone is sufficient because the
    /// arc-bearing fields (references / payload / inherits / specializes, and
    /// variantSelection — its selected branch is a `Variant` node) are the only
    /// members of [`STRUCTURAL_INERT_FIELDS`] whose effect is *cached* in the
    /// graph, and all produce a non-`Root` node detected by
    /// [`IndexCache::cached_has_composition_arc`]. The rest resolve live and
    /// need no rebuild on removal: `active` (re-read by `UsdPrim::is_active` /
    /// stage traversal) and `apiSchemas` (re-read by
    /// `PrimIndex::resolve_token_list_op`); `instanceable` is covered separately
    /// because [`Changes::apply`] drops affected prototypes for every spec-tier
    /// path. A future field whose removal mutates cached graph state would have
    /// to extend this check (the principled fix is to record a removed spec's
    /// significant fields at erase time, making the remove path symmetric with
    /// the add).
    fn inert_change_is_structural(
        &self,
        cache: &IndexCache,
        graph: &LayerGraph,
        layer: LayerId,
        path: &Path,
        entry: &ChangeEntry,
    ) -> bool {
        // TODO(perf): each `layer_authors_field` re-resolves the same layer and
        // spec before probing one field; resolving the spec once and testing the
        // fields against it would replace these per-field lookups with one fetch.
        if entry.flags.contains(sdf::ChangeFlags::ADD_INERT_PRIM)
            && STRUCTURAL_INERT_FIELDS
                .iter()
                .any(|k| cache.layer_authors_field(graph, layer, path, k.as_str()))
        {
            return true;
        }
        entry.flags.contains(sdf::ChangeFlags::REMOVE_INERT_PRIM) && cache.cached_has_composition_arc(path)
    }

    fn classify_root_entry(&mut self, _cache: &IndexCache, _layer: LayerId, entry: &ChangeEntry) {
        for key in &entry.info_changed {
            if *key == FieldKey::SubLayers.as_str() {
                self.layer_stack |= LayerStackChanges::LAYERS | LayerStackChanges::SIGNIFICANT;
            } else if *key == FieldKey::SubLayerOffsets.as_str() {
                self.layer_stack |= LayerStackChanges::OFFSETS | LayerStackChanges::SIGNIFICANT;
            } else if *key == FieldKey::LayerRelocates.as_str() {
                self.layer_stack |= LayerStackChanges::RELOCATES | LayerStackChanges::SIGNIFICANT;
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
    /// Mirrors C++ `Pcp_EntryRequiresPrimIndexChange` (changes.cpp:264-298).
    /// All of [`STRUCTURAL_INERT_FIELDS`] qualify — the composition-arc,
    /// instancing, and activation opinions an `over` may carry — plus
    /// `specifier`, whose def↔over↔class transitions change whether the prim
    /// and its subtree compose. (`specifier` is excluded from
    /// [`STRUCTURAL_INERT_FIELDS`] because every prim authors one, so its mere
    /// presence cannot distinguish a structural `over`.)
    fn field_promotes_to_significant(field: &str) -> bool {
        field == FieldKey::Specifier.as_str() || STRUCTURAL_INERT_FIELDS.iter().any(|k| field == k.as_str())
    }

    /// Apply phase: commit the planned invalidations to `cache`.
    pub fn apply(self, cache: &mut IndexCache, graph: &mut LayerGraph) {
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
        // composed against the old `sublayer_stacks`/`Relocates`; if a
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
        // edit refreshes just the validated relocates. Each refreshes the graph's
        // own diagnostic buckets in place; the cache holds no copy.
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
    use crate::ar::DefaultResolver;
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
        let graph = LayerGraph::from_layers(Vec::new(), 0, Box::new(DefaultResolver::new()), true);
        (graph, IndexCache::new(VariantFallbackMap::new(), Vec::new()))
    }

    #[test]
    fn references_promotes_to_significant() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo"))
            .info_changed
            .insert(FieldKey::References.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &graph, &[(first_layer(&graph), &cl)]);
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
        changes.did_change(&cache, &graph, &[(first_layer(&graph), &cl)]);
        assert!(changes.cache.did_change_significantly.contains(&p("/Foo")));
    }

    /// An inert prim add whose spec authors `instanceable` flips the prim's
    /// instancing composition, so it must be promoted to significant even
    /// though the add itself is inert (spec 11.3.3).
    #[test]
    fn inert_add_with_instanceable_is_significant() {
        let mut layer = crate::sdf::Layer::new_anonymous("root.usda");
        crate::sdf::PrimSpec::new(layer.data_mut(), "/X", crate::sdf::Specifier::Over, "")
            .unwrap()
            .set_instanceable(true);
        let graph = LayerGraph::from_layers(vec![layer], 0, Box::new(DefaultResolver::new()), true);
        let cache = IndexCache::new(VariantFallbackMap::new(), Vec::new());

        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/X")).flags = ChangeFlags::ADD_INERT_PRIM;
        let mut changes = Changes::new();
        changes.did_change(&cache, &graph, &[(first_layer(&graph), &cl)]);

        assert!(changes.cache.did_change_significantly.contains(&p("/X")));
    }

    #[test]
    fn inert_add_lands_on_spec_tier() {
        let (graph, cache) = empty_cache();
        let layer = first_layer(&graph);
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo")).flags = ChangeFlags::ADD_INERT_PRIM;
        let mut changes = Changes::new();
        changes.did_change(&cache, &graph, &[(layer, &cl)]);
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
        changes.did_change(&cache, &graph, &[(first_layer(&graph), &cl)]);
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
        changes.did_change(&cache, &graph, &[(first_layer(&graph), &cl)]);
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
        changes.did_change(&cache, &graph, &[(first_layer(&graph), &cl)]);
        assert!(changes.cache.did_change_significantly.contains(&Path::abs_root()));
        assert!(!changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }

    #[test]
    fn layer_relocates_change_flags_relocates() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(FieldKey::LayerRelocates.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &graph, &[(first_layer(&graph), &cl)]);
        assert!(changes.layer_stack.contains(LayerStackChanges::RELOCATES));
        assert!(changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }

    #[test]
    fn property_changes_no_op() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo.attr")).flags = ChangeFlags::ADD_PROPERTY;
        let mut changes = Changes::new();
        changes.did_change(&cache, &graph, &[(first_layer(&graph), &cl)]);
        assert!(changes.cache.did_change_significantly.is_empty());
        assert!(changes.cache.did_change_specs.is_empty());
        assert!(!changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }
}
