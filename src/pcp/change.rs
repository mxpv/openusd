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
//!   this index. Currently dormant: the spec tier subsumes the one case C++
//!   populates it for (see [`CacheChanges::did_change_prims`]).
//! - Spec: the graph is fine; only whether a site contributes an opinion
//!   changed. An inert spec add or remove authors no arc and no significant
//!   field, so [`IndexCache::rescan_specs`](super::IndexCache::rescan_specs)
//!   (C++ `Pcp_RescanForSpecs`) refreshes the affected nodes' `has_specs`
//!   flag in place instead of rebuilding, dropping the local index only when
//!   it holds no node at the site (a brand-new spec needs a fresh build).

use std::collections::{BTreeSet, HashSet};
use std::mem;

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
    /// The layers whose root metadata edit set a [`LayerStackChanges`] flag. A
    /// `subLayers`/offset/relocate/`timeCodesPerSecond` edit keeps its layer a
    /// member of every stack the layer participates in, so dropping the indices
    /// whose composition reads one of these layers ([`IndexCache::invalidate_layers`])
    /// scopes the layer-stack invalidation to exactly the affected stacks.
    layer_stack_layers: HashSet<LayerId>,
}

/// Path-sets identifying which cached prim indices to invalidate.
#[derive(Debug, Default)]
pub struct CacheChanges {
    /// Drop the index AND every namespace descendant.
    pub(crate) did_change_significantly: BTreeSet<Path>,
    /// Drop only this index; descendants survive — for a change that reshapes
    /// this prim's own graph but cannot restructure its namespace children.
    ///
    /// Deliberately never populated, kept (with its [`Changes::apply`] consumer)
    /// as the named third tier so the model stays aligned with C++ `PcpChanges`.
    /// The C++ tier this mirrors (`didChangePrims`) holds one case: an inert prim
    /// spec add that may un-cull a node, where C++ unconditionally rebuilds that
    /// single prim index. The memoized spec stack handles that case here, and more
    /// precisely — [`did_change_specs`](Self::did_change_specs) refreshes
    /// `has_specs` in place and rebuilds the single index (no subtree) only when a
    /// node actually un-culls or loses its last spec (see
    /// [`IndexCache::rescan_specs`](super::IndexCache::rescan_specs)). Every other
    /// prim-index-affecting field — C++ `Pcp_EntryRequiresPrimIndexChange`:
    /// references / payload / inherits / specializes / variants / instanceable /
    /// permission, plus the `active` / `specifier` / `apiSchemas` this cache adds
    /// conservatively — is significant: it can add or drop a subtree, and a
    /// descendant index seeds from its parent's composed graph, so it must
    /// recompose with the parent. A safe population would need a change that
    /// invalidates this prim's graph yet provably leaves untouched the seed and
    /// child context its descendants inherit; no field meets that bar today.
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
        /// The stack changed significantly: every index whose composition reads
        /// one of its layers is dropped and recomposed.
        const SIGNIFICANT = 1 << 3;
        /// `timeCodesPerSecond` / `framesPerSecond` was edited. The effective rate
        /// retimes each sublayer edge offset (spec 12.3.2), so the composed edges
        /// must rebuild even though no sublayer was added or reordered.
        const TIME_CODES = 1 << 4;

        /// Any change that requires recomputing the sublayer ordering, layer
        /// offsets, or the time-codes retiming folded into the edge offsets.
        const NEEDS_LAYER_STACK_REBUILD = Self::LAYERS.bits() | Self::OFFSETS.bits() | Self::TIME_CODES.bits();
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

    fn classify_root_entry(&mut self, _cache: &IndexCache, layer: LayerId, entry: &ChangeEntry) {
        let mut touches_stack = false;
        for key in &entry.info_changed {
            if *key == FieldKey::SubLayers.as_str() {
                self.layer_stack |= LayerStackChanges::LAYERS | LayerStackChanges::SIGNIFICANT;
                touches_stack = true;
            } else if *key == FieldKey::SubLayerOffsets.as_str() {
                self.layer_stack |= LayerStackChanges::OFFSETS | LayerStackChanges::SIGNIFICANT;
                touches_stack = true;
            } else if *key == FieldKey::LayerRelocates.as_str() {
                self.layer_stack |= LayerStackChanges::RELOCATES | LayerStackChanges::SIGNIFICANT;
                touches_stack = true;
            } else if *key == FieldKey::TimeCodesPerSecond.as_str() || *key == FieldKey::FramesPerSecond.as_str() {
                // The effective timeCodesPerSecond (authored rate, else
                // framesPerSecond) retimes each sublayer edge offset by the
                // per-hop ratio (spec 12.3.2, folded into `LayerNode::children` by
                // `build_sublayer_edges`). `TIME_CODES` rebuilds those edges so the
                // stale ratio is refreshed; `SIGNIFICANT` then drops the indices
                // that read the re-offset stack.
                self.layer_stack |= LayerStackChanges::TIME_CODES | LayerStackChanges::SIGNIFICANT;
                touches_stack = true;
            } else if *key == FieldKey::DefaultPrim.as_str() {
                self.cache.did_change_significantly.insert(Path::abs_root());
            }
        }
        // Record the layer behind any layer-stack-tier flag so `apply` can scope the
        // invalidation to the stacks this layer is a member of. Each edited layer in
        // a round is attributed independently, so a multi-layer edit invalidates
        // every affected stack.
        if touches_stack {
            self.layer_stack_layers.insert(layer);
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
    pub fn apply(mut self, cache: &mut IndexCache, graph: &mut LayerGraph) {
        // Advance the composition revision so cached value views rebuild. This
        // is the single funnel for every authoring and layer-stack edit, so a
        // value-only change that drops no index still invalidates them.
        cache.bump_revision();

        // Rebuild the graph's layer-stack precomputed state before the scoped drop
        // below reads it, and collect the affected layer set the drop evicts
        // against. A `subLayers`/`subLayerOffsets`/`timeCodesPerSecond` edit rebuilds
        // the sublayer edges (which subsumes the relocate recompute) and returns the
        // layers whose composed edges shifted, the authored layers, and any whose
        // relocates moved; a `layerRelocates`-only edit refreshes the cached
        // relocates, with the edited layer added to its relocate set. Each refreshes
        // the graph's own diagnostic buckets in place; the cache holds no copy.
        let affected = if self
            .layer_stack
            .intersects(LayerStackChanges::NEEDS_LAYER_STACK_REBUILD)
        {
            graph.recompute_sublayers(Some(&self.layer_stack_layers))
        } else if self.layer_stack.intersects(LayerStackChanges::NEEDS_RELOCATES_REBUILD) {
            let mut relocated = graph.recompute_relocates();
            relocated.extend(self.layer_stack_layers.iter().copied());
            relocated
        } else {
            HashSet::new()
        };

        // Layer-stack-tier change: drop only the indices whose composition reads a
        // stack the rebuild re-resolved. `affected` names every such stack's layers
        // — the edited layers stay members of the stacks they belong to, the edge
        // diff adds a descendant whose inherited context shifted, and the relocate
        // set adds any whose effective relocates moved — so `invalidate_layers`
        // evicts those indices and the prototypes they touch and leaves the rest
        // warm.
        if self.layer_stack.contains(LayerStackChanges::SIGNIFICANT) {
            cache.invalidate_layers(graph, &affected);
        }

        // A prim-tier index invalidation can change which prims are instances or
        // how they compose, so affected entries in the shared-prototype registry
        // (spec 11.3.3) are dropped rather than left stale and lazily recomposed
        // on the next instancing query. The layer-stack path evicted its
        // prototypes through `invalidate_layers` above.
        if !self.cache.did_change_significantly.is_empty()
            || !self.cache.did_change_prims.is_empty()
            || !self.cache.did_change_specs.is_empty()
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
        // Batch the spec-tier rescan: an index reached by several of this round's
        // changed sites refreshes its `has_specs` flags per site but finalizes its
        // spec stack once. Sites subsumed by an ancestor whose subtree was already
        // dropped are skipped. The owned `did_change_specs` is the last read of
        // `self`, so move its sites out rather than cloning each `Path`.
        let sites: Vec<(LayerId, Path)> = mem::take(&mut self.cache.did_change_specs)
            .into_iter()
            .filter(|(_, path)| !self.cache.did_change_significantly.iter().any(|p| path.has_prefix(p)))
            .collect();
        if !sites.is_empty() {
            cache.rescan_specs(graph, &sites);
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
