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
//! - Prim: this index's graph is wrong but descendants survive. Currently
//!   collapsed into significant for safety; the field is reserved for the
//!   future split.
//! - Spec: graph is fine; only which specs contribute changed. No-op while
//!   the cache does not yet memoize per-node spec stacks.

use std::collections::BTreeSet;

use bitflags::bitflags;

use crate::sdf;
use crate::sdf::schema::FieldKey;
use crate::sdf::{ChangeEntry, ChangeList, Path};

use super::Cache;

/// Plan + apply object for one author round.
///
/// Internal: callers route invalidation through
/// [`Cache::process_changes`](super::Cache::process_changes), which
/// constructs a `Changes`, classifies via [`Changes::did_change`], and
/// commits via [`Changes::apply`] against the same cache instance.
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
    /// Drop only this index; descendants survive. Inert spec adds land
    /// here so a cached miss can't stay sticky after `override_prim` /
    /// auto-ancestor creation, without paying the cost of a subtree-wide
    /// invalidation.
    pub(crate) did_change_prims: BTreeSet<Path>,
    /// Reserved — currently NOT consumed by [`Changes::apply`]. A future
    /// tier-3 implementation that refreshes per-node spec stacks (instead
    /// of dropping the prim index) will read this set. The classifier
    /// does not write to it yet either; inert spec adds land in
    /// `did_change_prims` so the cached index is dropped wholesale.
    //
    // TODO: wire producer + consumer together when `Cache` memoizes
    // resolved spec stacks per node. The classifier (`classify_prim_entry`
    // in this file) routes inert spec adds here instead of `did_change_prims`,
    // and `apply` learns to call a `Cache::rescan_specs(path)` (analog of
    // C++ `Pcp_RescanForSpecs`) that walks the existing graph and refreshes
    // which layers contribute opinions, without rebuilding the graph.
    #[allow(dead_code)]
    pub(crate) did_change_specs: BTreeSet<Path>,
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
    pub fn did_change(&mut self, cache: &Cache, changes: &[(usize, ChangeList)]) {
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

    fn classify_prim_entry(&mut self, cache: &Cache, layer: usize, path: &Path, entry: &ChangeEntry) {
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
            if cache.layer_authors_field(layer, path, FieldKey::Instanceable.as_str()) {
                // An inert add whose spec carries `instanceable` flips the
                // prim's instancing composition (spec 11.3.3) even though the
                // add itself is inert; recompose the subtree.
                self.fanout_significant(cache, layer, path);
            } else {
                // Drop the local index so a cached "no spec here" miss can't
                // stay sticky after an inert add. Dependents that already
                // touch `(layer, path)` see the new opinion live through their
                // existing nodes — no rebuild needed for them.
                //
                // The classifier ideally lands this in the spec tier
                // (`did_change_specs`), but apply() can't refresh per-node
                // spec stacks until they're memoized, so dropping is the
                // safe substitute. When the spec tier becomes real, this
                // moves over and the local drop falls out.
                self.cache.did_change_prims.insert(path.clone());
            }
        }

        // TODO: silent promotions of inert spec adds, per C++
        // `Pcp_EntryRequires{Prim,Specs}Change`:
        //   1. Removing the last spec at `path` — promote to significant
        //      because the prim no longer composes anything. Needs a
        //      "does any layer still spec this path?" check, which means
        //      walking every layer for `path` after the mutation.
        //   2. An inert add at a path whose node was previously culled
        //      from a dependent prim's graph — that dependent needs a
        //      tier-2 prim rebuild so the now-needed node re-enters.
        //      Blocked on culled-node tracking: the `Builder` culls
        //      weaker nodes during composition, and we keep no
        //      `culled_dependencies` snapshot to consult.
    }

    fn classify_root_entry(&mut self, _cache: &Cache, _layer: usize, entry: &ChangeEntry) {
        for &key in &entry.info_changed {
            if key == FieldKey::SubLayers.as_str() {
                self.layer_stack |= LayerStackChanges::LAYERS | LayerStackChanges::SIGNIFICANT;
            } else if key == FieldKey::SubLayerOffsets.as_str() {
                self.layer_stack |= LayerStackChanges::OFFSETS | LayerStackChanges::SIGNIFICANT;
            } else if key == FieldKey::LayerRelocates.as_str() {
                self.layer_stack |= LayerStackChanges::RELOCATES | LayerStackChanges::SIGNIFICANT;
            } else if key == FieldKey::DefaultPrim.as_str() {
                self.cache.did_change_significantly.insert(Path::abs_root());
            }
        }
    }

    fn fanout_significant(&mut self, cache: &Cache, layer: usize, path: &Path) {
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
            // (resolve_token_list_op in Cache::api_schemas), so any edit
            // must drop the index. Once registry-driven applied schemas
            // inject composition state, this becomes load-bearing for
            // graph correctness too.
            || field == FieldKey::ApiSchemas.as_str()
            // Per-prim `relocates` reshape composition (see `pcp::rel`).
            // No Stage-tier producer authors this yet, but adding it now
            // matches the C++ classifier and forecloses a latent gap.
            || field == FieldKey::Relocates.as_str()
    }

    /// Apply phase: commit the planned invalidations to `cache`.
    //
    // TODO: tier-2 (`did_change_prims`) currently falls through to
    // `drop_index` per path with no descendant-aware optimization beyond
    // ancestor subsumption. Once the classifier writes prim-tier entries
    // directly (today it collapses them into the significant set in
    // `classify_prim_entry`), this branch becomes load-bearing.
    pub fn apply(self, cache: &mut Cache) {
        // Any index invalidation can change which prims are instances or how
        // they compose, so the shared-prototype registry (spec 11.3.3) must be
        // rebuilt rather than left stale. It is lazily repopulated on the next
        // instancing query.
        if self.layer_stack.contains(LayerStackChanges::SIGNIFICANT)
            || !self.cache.did_change_significantly.is_empty()
            || !self.cache.did_change_prims.is_empty()
        {
            cache.invalidate_prototypes();
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
        if self
            .layer_stack
            .intersects(LayerStackChanges::NEEDS_LAYER_STACK_REBUILD)
        {
            cache.recompute_layer_stack();
        }
        if self.layer_stack.intersects(LayerStackChanges::NEEDS_RELOCATES_REBUILD) {
            cache.recompute_relocates();
        }
        // A `subLayers` edit sets `LAYERS`, which both rebuild masks include, so
        // both recomputes above can run for one edit. Queue the regenerated
        // layer-stack errors once, after both, so each diagnostic is retained
        // exactly once.
        if self
            .layer_stack
            .intersects(LayerStackChanges::NEEDS_LAYER_STACK_REBUILD | LayerStackChanges::NEEDS_RELOCATES_REBUILD)
        {
            cache.queue_layer_stack_errors();
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
        // Tier 3 (spec): no-op until `Cache` memoizes per-node spec stacks.
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::DefaultResolver;
    use crate::pcp::{LayerStack, VariantFallbackMap};
    use crate::sdf::{ChangeFlags, ChangeList};

    fn p(s: &str) -> Path {
        Path::new(s).expect("valid path")
    }

    fn empty_cache() -> Cache {
        let stack = LayerStack::new(Vec::new(), 0, Box::new(DefaultResolver::new()), true);
        Cache::new(stack, VariantFallbackMap::new())
    }

    #[test]
    fn references_promotes_to_significant() {
        let cache = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo"))
            .info_changed
            .insert(FieldKey::References.as_str());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(0, cl)]);
        assert!(changes.cache.did_change_significantly.contains(&p("/Foo")));
    }

    #[test]
    fn variant_selection_promotes_to_significant() {
        let cache = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo"))
            .info_changed
            .insert(FieldKey::VariantSelection.as_str());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(0, cl)]);
        assert!(changes.cache.did_change_significantly.contains(&p("/Foo")));
    }

    /// An inert prim add whose spec authors `instanceable` flips the prim's
    /// instancing composition, so it must be promoted to significant even
    /// though the add itself is inert (spec 11.3.3).
    #[test]
    fn inert_add_with_instanceable_is_significant() {
        let mut layer = crate::sdf::Layer::new_anonymous("root.usda");
        layer
            .create_prim("/X", crate::sdf::Specifier::Over, "")
            .unwrap()
            .set_instanceable(true);
        let stack = LayerStack::new(vec![layer], 0, Box::new(DefaultResolver::new()), true);
        let cache = Cache::new(stack, VariantFallbackMap::new());

        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/X")).flags = ChangeFlags::ADD_INERT_PRIM;
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(0, cl)]);

        assert!(changes.cache.did_change_significantly.contains(&p("/X")));
    }

    #[test]
    fn inert_add_lands_on_spec_tier() {
        let cache = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo")).flags = ChangeFlags::ADD_INERT_PRIM;
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(0, cl)]);
        // No dependent indices exist on an empty cache, so nothing fans out
        // to the spec tier — but the prim itself is NOT in the significant
        // tier either (inert adds don't blow the graph).
        assert!(!changes.cache.did_change_significantly.contains(&p("/Foo")));
        assert!(changes.cache.did_change_specs.is_empty());
    }

    #[test]
    fn non_inert_add_is_significant_with_self_path() {
        let cache = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo")).flags = ChangeFlags::ADD_NON_INERT_PRIM;
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(0, cl)]);
        assert!(changes.cache.did_change_significantly.contains(&p("/Foo")));
    }

    #[test]
    fn sublayers_change_is_layer_stack_significant() {
        let cache = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(FieldKey::SubLayers.as_str());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(0, cl)]);
        assert!(changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
        assert!(changes.layer_stack.contains(LayerStackChanges::LAYERS));
    }

    #[test]
    fn default_prim_change_is_significant_at_root() {
        let cache = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(FieldKey::DefaultPrim.as_str());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(0, cl)]);
        assert!(changes.cache.did_change_significantly.contains(&Path::abs_root()));
        assert!(!changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }

    #[test]
    fn layer_relocates_change_flags_relocates() {
        let cache = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(FieldKey::LayerRelocates.as_str());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(0, cl)]);
        assert!(changes.layer_stack.contains(LayerStackChanges::RELOCATES));
        assert!(changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }

    #[test]
    fn property_changes_no_op() {
        let cache = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo.attr")).flags = ChangeFlags::ADD_PROPERTY;
        let mut changes = Changes::new();
        changes.did_change(&cache, &[(0, cl)]);
        assert!(changes.cache.did_change_significantly.is_empty());
        assert!(changes.cache.did_change_specs.is_empty());
        assert!(!changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }
}
