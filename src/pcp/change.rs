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
//!
//! Edit-type → tier, the audit behind the classifier:
//!
//! - `references`, `payload`, `inheritPaths`, `specializes`, `variantSetNames`,
//!   `variantSelection`, `instanceable`, `permission` → significant: each is a
//!   composition-arc, instancing, or permission opinion that can add or drop a
//!   subtree (C++ `Pcp_EntryRequiresPrimIndexChange`). `specifier`, `active`,
//!   `apiSchemas`, and `relocates` are significant here too, slightly broader
//!   than C++ (which routes `active` / `specifier` through separate
//!   mechanisms).
//! - an inert `over` add or remove carrying no significant field → spec tier.
//! - `subLayers`, `subLayerOffsets`, `layerRelocates`, `timeCodesPerSecond` /
//!   `framesPerSecond`, `expressionVariables` on the root → layer-stack tier.
//! - `defaultPrim` on the root → its own channel: the prims whose builds recorded
//!   consulting the field are evicted, and the dependents of the prim path it used
//!   to name are reported (`apply_default_prim_edits`). Neither half is the
//!   layer-stack tier, and the report is not C++-identical — see the parity notes
//!   in the module docs.
//! - `clips` / `clipSets` → significant, because a prim index caches whether
//!   value clips can source it at all
//!   ([`PrimIndex::may_have_clips`](super::PrimIndex::may_have_clips)) and every
//!   descendant inherits that answer.
//! - non-composition metadata (`kind`, `colorConfiguration`, `customData`, …) →
//!   no index drop. These resolve live through the cached index's spec sites,
//!   and every value view rebuilds against the composition-revision bump
//!   [`apply`](Changes::apply) always makes, so the new opinion is visible
//!   without invalidating the graph.

use std::collections::{BTreeSet, HashSet};
use std::mem;

use bitflags::bitflags;

use crate::sdf;
use crate::sdf::schema::FieldKey;
use crate::sdf::{ChangeEntry, ChangeList, Path};
use crate::tf;

use super::layer_graph::LayerGraph;
use super::layer_stack::StackVarsDelta;
use super::prim_index::{PropertyTargetKind, TargetMemoKey};
use super::{IndexCache, LayerId, LayerStackId};

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
    /// The `defaultPrim` edits this round, each paired with the field's value
    /// before the commit ([`LayerChanges::prior_default_prim`]).
    ///
    /// Deferred to [`apply`](Changes::apply) rather than classified here: both
    /// the eviction and the report need the field's *current* value to skip an
    /// edit that leaves the composed default where it was, and only the apply
    /// phase holds the [`LayerGraph`] to read it from.
    default_prim_edits: Vec<(LayerId, Option<tf::Token>)>,
    /// The layers whose root metadata edit set a [`LayerStackChanges`] flag. A
    /// `subLayers`/offset/relocate/`timeCodesPerSecond`/`expressionVariables` edit
    /// keeps its layer a member of every stack the layer participates in, so
    /// dropping the indices whose composition reads one of these layers
    /// ([`IndexCache::invalidate_layers`]) scopes the layer-stack invalidation to
    /// exactly the affected stacks.
    layer_stack_layers: HashSet<LayerId>,
}

/// One edited layer's committed record, with the prior field values the record
/// itself does not carry.
///
/// [`ChangeList`] names the fields a commit touched, not what they held before
/// (`sdf` reconstructs old values from the pre-edit base at the commit seam
/// instead of snapshotting them). Classification runs after that seam, so the one
/// prior value it needs travels here, captured by the stage's layer sink.
pub(crate) struct LayerChanges<'a> {
    /// The edited layer.
    pub layer: LayerId,
    /// What the commit recorded.
    pub changes: &'a ChangeList,
    /// The layer's `defaultPrim` token before this commit, when the commit
    /// edited that field. `None` means the field named no prim beforehand —
    /// unauthored, or a value that resolves to nothing — which is also the
    /// conservative answer if the value could not be read.
    pub prior_default_prim: Option<tf::Token>,
}

#[cfg(test)]
impl<'a> LayerChanges<'a> {
    /// One layer's record with no prior `defaultPrim` — what a classifier test
    /// needs unless it is exercising that field.
    pub(crate) fn plain(layer: LayerId, changes: &'a ChangeList) -> Self {
        Self {
            layer,
            changes,
            prior_default_prim: None,
        }
    }
}

/// Path-sets identifying which cached prim indices to invalidate.
#[derive(Debug, Default)]
pub struct CacheChanges {
    /// Drop the index AND every namespace descendant, at a composed stage path —
    /// a dependent the change fanned out to. The stage root joins them for a
    /// `defaultPrim` edit, which is namespace-neutral and drops the whole cache.
    pub(crate) did_change_significantly: BTreeSet<Path>,
    /// The same tier for a literal edited path expressed in the *edited layer's*
    /// namespace, which under a variant or arc edit target is not a stage path
    /// (`/Prim{set=sel}child` composes into `/Prim/child`).
    ///
    /// Invalidation reads the two halves together: an authored path can name a
    /// cached index too, and dropping one it does not name costs only warmth.
    /// They stay apart for the report, where a prefix comparison only means
    /// something within one namespace and each half is named in the namespace it
    /// belongs to (see [`usd::Provenance`](crate::usd::Provenance)).
    pub(crate) authored_significant: BTreeSet<Path>,
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
    /// Memoized resolved targets that are stale — a `targetPaths` /
    /// `connectionPaths` edit changed a relationship/connection a prim composes in
    /// place, or one it reads through an arc (so a referenced site's edit fans out
    /// to its dependents). Each entry pairs the dependent prim with the edited
    /// property's [`TargetMemoKey`], so [`Changes::apply`] drops only that one
    /// property's memo
    /// ([`IndexCache::clear_target_memos`](super::IndexCache::clear_target_memos))
    /// and the prim's other relationships and connections keep theirs. The graph is
    /// intact, so the index survives; the next query recomposes the targets live.
    pub(crate) did_change_targets: BTreeSet<(Path, TargetMemoKey)>,
}

impl CacheChanges {
    /// The resynced prim paths that are already composed stage paths — the
    /// significant tier's stage half and the prim tier. These are the paths a
    /// consumer must re-resolve (C++ `PcpCacheChanges` resync set).
    ///
    /// The target tier is deliberately absent: a `targetPaths` / `connectionPaths`
    /// edit drops only a memo, leaving the prim graph intact, so it is a
    /// changed-info edit on the property, not a prim resync. The composed change
    /// notice reports it through the property entry's relationship/connection-
    /// target flag instead.
    pub(crate) fn stage_resynced_paths(&self) -> impl Iterator<Item = &Path> {
        self.did_change_significantly.iter().chain(self.did_change_prims.iter())
    }

    /// The resynced paths expressed in the edited layer's namespace — the
    /// significant tier's authored half and the spec tier, which is authored by
    /// construction (its sites are literal `(layer, path)` pairs).
    ///
    /// The spec tier is reported so an inert spec add/remove (e.g. an `over`) is
    /// surfaced, not silently dropped, even though it refreshes `has_specs` in
    /// place rather than rebuilding the index.
    pub(crate) fn authored_resynced_paths(&self) -> impl Iterator<Item = &Path> {
        self.authored_significant
            .iter()
            .chain(self.did_change_specs.iter().map(|(_, path)| path))
    }

    /// The subset of [`stage_resynced_paths`](Self::stage_resynced_paths) that
    /// stands for a whole subtree — the significant tier, whose entries drop the
    /// index and every namespace descendant.
    ///
    /// Only these may subsume another reported stage path by prefix. The prim
    /// tier drops one index, so it says nothing about the paths beneath it.
    pub(crate) fn stage_subtree_paths(&self) -> impl Iterator<Item = &Path> {
        self.did_change_significantly.iter()
    }

    /// The covering subset of
    /// [`authored_resynced_paths`](Self::authored_resynced_paths). The spec tier
    /// is excluded for the same reason the prim tier is: refreshing `has_specs`
    /// at `/A` says nothing about `/A/B`, so an inert `over` added on the way to
    /// authoring `/A/B.x` must not swallow the attribute's own report.
    pub(crate) fn authored_subtree_paths(&self) -> impl Iterator<Item = &Path> {
        self.authored_significant.iter()
    }

    /// Both halves of the significant tier, for invalidation — which drops every
    /// index either half names, whatever namespace the path came from. Dropping
    /// a path no index is cached at costs nothing, so the union is the
    /// conservative read.
    ///
    /// A path both halves hold is yielded once. An edit to a prim that already
    /// has a cached index puts it in both, since the index self-registers at its
    /// own path and the dependency lookup folds those registrations in, and each
    /// yield costs a prototype-registry walk downstream.
    fn all_significant(&self) -> impl Iterator<Item = &Path> {
        self.did_change_significantly.iter().chain(
            self.authored_significant
                .iter()
                .filter(|path| !self.did_change_significantly.contains(*path)),
        )
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
        /// `expressionVariables` was edited. A `${VAR}` expression in any of the
        /// stack's layers — a sublayer asset path, a reference/payload target, or
        /// a variant selection — may read the changed values, so the expanded
        /// sublayer edges rebuild; [`Changes::apply`] then consumes the rebuild's
        /// per-stack [`StackVarsDelta`]s to drop exactly the prims that recorded
        /// a dependency on a changed name (the C++ five-step
        /// `_DidChangeLayerStackExpressionVariables` diff).
        const EXPRESSION_VARS = 1 << 5;

        /// Any change that requires recomputing the sublayer ordering, layer
        /// offsets, the time-codes retiming folded into the edge offsets, or the
        /// `${VAR}` sublayer-edge expansions.
        const NEEDS_LAYER_STACK_REBUILD =
            Self::LAYERS.bits() | Self::OFFSETS.bits() | Self::TIME_CODES.bits() | Self::EXPRESSION_VARS.bits();
        /// Any change that requires recomputing the per-layer relocates
        /// table.
        const NEEDS_RELOCATES_REBUILD = Self::LAYERS.bits() | Self::RELOCATES.bits();
    }
}

/// What one [`Changes::apply`] must publish beyond the per-path entries the
/// diff phase recorded — the facts only the apply phase can know, since they
/// depend on which layer stacks the rebuild actually moved.
///
/// Every path is in composed stage namespace: each comes from a dependency-table
/// lookup or is the pseudo-root. Both sets stand for whole subtrees, which is
/// what lets a consumer prune its own path-sets by prefix against them.
/// [`asset_paths_resynced`](Self::asset_paths_resynced) is unordered and may
/// name a prim twice, since cascading deltas contribute overlapping victim sets,
/// so a consumer that needs a minimal set normalizes it
/// (`usd::sink::Payload::finish`).
#[derive(Debug, Default)]
pub(crate) struct ApplyOutcome {
    /// Composed prim paths this apply resynced for a layer-stack reason: the
    /// indices a `subLayers`/offset/`timeCodesPerSecond` change or an
    /// `expressionVariables` delta dropped (C++ `DidChangeSignificantly` from
    /// `_DidChangeLayerStackExpressionVariables`). Each drops its index and every
    /// namespace descendant, so an entry stands for its whole subtree; a lone
    /// [`Path::abs_root`] entry means the whole stage resynced. Sorted and
    /// deduplicated.
    ///
    /// An entry is a subtree a consumer must re-resolve, which is not always one
    /// this apply evicted: a `defaultPrim` edit reports C++'s wider fanout while
    /// evicting only the indices that actually compose differently, so a prim
    /// named here may still hold a valid cached index.
    pub(crate) resynced: Vec<Path>,
    /// The subtrees whose `asset` values may now resolve elsewhere, from
    /// [`asset_path_victims`] — the channel that covers what no dependency
    /// record can. Costs a dependency lookup per stack whose composed variables
    /// moved, paid whether or not an observer is installed, since `apply`
    /// cannot see whether the stage wants a notice; C++ collects it
    /// unconditionally too.
    pub(crate) asset_paths_resynced: Vec<Path>,
}

impl Changes {
    /// Creates an empty change plan.
    pub fn new() -> Self {
        Self::default()
    }

    /// Diff phase: classify each [`ChangeEntry`] into the appropriate
    /// invalidation tier. Pure analysis — does not mutate `cache`.
    ///
    /// Most property-path entries (attribute values, time samples) are ignored:
    /// those queries read live layer data on every call, so a newly authored
    /// value is visible without any cache mutation. A `targetPaths` /
    /// `connectionPaths` edit is the exception — the cache memoizes resolved
    /// relationship/connection targets, so it routes through
    /// [`classify_property_entry`](Self::classify_property_entry) to the
    /// [`did_change_targets`](CacheChanges::did_change_targets) set.
    pub fn did_change(&mut self, cache: &IndexCache, changes: &[LayerChanges<'_>]) {
        for edit in changes {
            for (path, entry) in edit.changes.entries() {
                if path.is_abs_root() {
                    self.classify_root_entry(edit, entry);
                } else if path.is_property_path() {
                    self.classify_property_entry(cache, edit.layer, path, entry);
                } else {
                    self.classify_prim_entry(cache, edit.layer, path, entry);
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
            // composed site is not on the authored path's ancestor chain
            // (`/Prim{set=sel}child` → `/Prim{set=sel}` → `/Prim` → `/`), so
            // fanning out from the variant path alone leaves a cached miss
            // there stale; invalidate it too. Stripping the selections keeps the
            // path in the edited layer's namespace — under an arc it is the
            // referenced layer's `/Source/child`, not the stage's.
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

    /// Routes a property-path edit. Only a `targetPaths` / `connectionPaths`
    /// change matters to the cache — it memoizes resolved relationship/connection
    /// targets; every other property edit (attribute value, time samples) reads
    /// live and is ignored. The owning prim's memo is marked stale, as is each
    /// dependent's: a prim that reads the property's site through an arc composes
    /// a translated copy of those targets, so a referenced site's edit restales
    /// them too.
    fn classify_property_entry(&mut self, cache: &IndexCache, layer: LayerId, path: &Path, entry: &ChangeEntry) {
        let is_connection = entry.flags.contains(sdf::ChangeFlags::CHANGE_ATTRIBUTE_CONNECTION)
            || entry
                .info_changed
                .iter()
                .any(|k| *k == FieldKey::ConnectionPaths.as_str());
        let is_relationship = entry.flags.contains(sdf::ChangeFlags::CHANGE_RELATIONSHIP_TARGETS)
            || entry.info_changed.iter().any(|k| *k == FieldKey::TargetPaths.as_str());
        if !is_connection && !is_relationship {
            return;
        }
        let prim = path.prim_path();
        // A target opinion authored inside a variant (`/P{v=x}child.r`) composes
        // into the variant-stripped prim (`/P/child`), whose memo key is not on the
        // authored path's ancestor chain, so the fanout from the variant path alone
        // misses it; restale it too, as the significant tier does for the same reason.
        let stripped = prim.strip_all_variant_selections();
        let suffix = path.property_suffix();
        // The memo is keyed by the edited property within its prim, matching the key
        // `IndexCache::compose_property_paths` files results under. One edit can
        // replace a relationship with a same-named attribute (or the reverse),
        // surfacing both target fields on a single entry, so restale each signalled
        // kind — clearing only one would leave the prior kind's memo stale.
        let keys: Vec<TargetMemoKey> = [
            is_relationship.then_some(PropertyTargetKind::Relationship),
            is_connection.then_some(PropertyTargetKind::Connection),
        ]
        .into_iter()
        .flatten()
        .map(|kind| TargetMemoKey {
            kind,
            property_suffix: suffix.to_owned(),
        })
        .collect();
        self.fanout_targets(cache, layer, &prim, &keys);
        if stripped != prim {
            self.fanout_targets(cache, layer, &stripped, &keys);
        }
    }

    /// Marks every key in `keys` stale on `prim`'s resolved-target memo and on every
    /// prim that composes its targets — anything reading its site, or an ancestor of
    /// it, through an arc. A prim reading a *descendant* of `prim` does not compose
    /// this property, so the fanout stays on the ancestor + self direction. The
    /// literal prim is included via the dependency self-edge, and explicitly for a
    /// prim not yet cached. The dependent set is the same for every key — an arc maps
    /// prim namespaces, not property names — so the ancestor walk runs once and each
    /// dependent is restaled under every key.
    fn fanout_targets(&mut self, cache: &IndexCache, layer: LayerId, prim: &Path, keys: &[TargetMemoKey]) {
        for dep in cache.dependencies().lookup_with_ancestors(layer, prim) {
            self.restale_targets(dep, keys);
        }
        self.restale_targets(prim.clone(), keys);
    }

    /// Records `prim`'s memo as stale under each of `keys`, consuming `prim` on the
    /// final key so the common single-key edit clones it not at all.
    fn restale_targets(&mut self, prim: Path, keys: &[TargetMemoKey]) {
        let Some((last, rest)) = keys.split_last() else {
            return;
        };
        for key in rest {
            self.cache.did_change_targets.insert((prim.clone(), key.clone()));
        }
        self.cache.did_change_targets.insert((prim, last.clone()));
    }

    fn classify_root_entry(&mut self, edit: &LayerChanges<'_>, entry: &ChangeEntry) {
        let layer = edit.layer;
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
            } else if *key == FieldKey::ExpressionVariables.as_str() {
                // An `expressionVariables` edit restales the graph's
                // `${VAR}`-expanded sublayer edges and any reference/payload/
                // variant `${VAR}` expression a layer in the stack resolves
                // against (C++ `PcpChanges::_DidChangeLayerStackExpressionVariables`).
                // `EXPRESSION_VARS` rebuilds the expanded edges — the edited
                // layer joins `layer_stack_layers` to scope that rebuild — and
                // [`apply`](Changes::apply) consumes the rebuild's per-stack
                // [`StackVarsDelta`]s to drop exactly the recorded dependents.
                // A combined edit that also authors a `SIGNIFICANT`-tier field
                // takes the blanket path through that field's own flag.
                self.layer_stack |= LayerStackChanges::EXPRESSION_VARS;
                touches_stack = true;
            } else if *key == FieldKey::DefaultPrim.as_str() {
                // Only a reference or payload naming no target prim resolves
                // through the layer's default, and each such build records the
                // layer it consulted, so nothing here needs the layer-stack tier.
                // Queued for `apply`, which can compare the field's prior value
                // against what it now holds (`apply_default_prim_edits`).
                self.default_prim_edits.push((layer, edit.prior_default_prim.clone()));
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

    /// Drops every index depending on `(layer, path)`, plus the literal `path`
    /// itself.
    ///
    /// The two land in different buckets: a dependency lookup answers in the
    /// cache's composed namespace, while `path` comes from a change list and so
    /// is spelled in `layer`'s namespace — which stripping variant selections
    /// off it does not change.
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
        self.cache.authored_significant.insert(path.clone());
    }

    /// Authoring this field on a prim path forces a graph rebuild.
    ///
    /// Mirrors C++ `Pcp_EntryRequiresPrimIndexChange` (changes.cpp:264-298): the
    /// composition-arc and instancing opinions, and `specifier`, whose
    /// def↔over↔class transitions change whether the prim and its subtree
    /// compose. `active`, `apiSchemas`, and `relocates` are added conservatively
    /// (see the module-level edit-type → tier table).
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
            // (`IndexCache::api_schemas`), so any edit must drop the index.
            // Once registry-driven applied schemas inject composition state,
            // this becomes load-bearing for graph correctness.
            || field == FieldKey::ApiSchemas.as_str()
            // Per-prim `relocates` reshape composition (see `pcp::relocates`). No
            // Stage-tier producer authors this yet, but it matches the C++
            // classifier and forecloses a latent gap.
            || field == FieldKey::Relocates.as_str()
            // Clip presence is cached per prim index and inherited by every
            // descendant (`PrimIndex::may_have_clips`), so authoring or removing
            // clip metadata has to drop the subtree that reads it. `clipSets`
            // joins it because deleting a set through that list op can empty a
            // prim's clips just as removing the dictionary does.
            //
            // TODO: C++ narrows this to an add or a removal, comparing the
            // field's before and after values, so a content-only clip edit stays
            // insignificant. `sdf::ChangeEntry::info_changed` carries field names
            // alone, so every clip edit resyncs the subtree until it carries the
            // values too.
            || field == FieldKey::Clips.as_str()
            || field == FieldKey::ClipSets.as_str()
    }

    /// Apply phase: commit the planned invalidations to `cache`.
    ///
    /// Returns the [`ApplyOutcome`] observers must be told on top of the
    /// per-path entries the diff phase recorded. A layer-stack
    /// [`SIGNIFICANT`](LayerStackChanges::SIGNIFICANT) edit drops the affected
    /// indices wholesale and resyncs the whole stage; an `expressionVariables`
    /// edit resyncs exactly the dependents it dropped and, on the separate
    /// asset-path channel, names the subtrees whose `asset` values may now
    /// resolve elsewhere. A vars edit that changed no composed set (an
    /// identical re-authoring, or variables on a non-root member layer, which
    /// contribute to no stack) reports nothing on either channel, matching the
    /// C++ five-step diff's step-1 no-op.
    /// Whether this pass can change which prims exist, how they are named, or
    /// whether they are active — the question
    /// [`IndexCache::invalidate_population`] answers for. Every tier but the
    /// property one qualifies: a layer-stack edit can swap a stack's members, a
    /// `defaultPrim` edit can move where an arc lands, and the prim and spec
    /// tiers name prims outright. A pass carrying only attribute values, or
    /// only relationship targets, changes none of that.
    fn touches_population(&self) -> bool {
        !self.layer_stack.is_empty()
            || !self.default_prim_edits.is_empty()
            || self.cache.all_significant().next().is_some()
            || !self.cache.did_change_prims.is_empty()
            || !self.cache.did_change_specs.is_empty()
    }

    pub fn apply(mut self, cache: &mut IndexCache, graph: &mut LayerGraph) -> ApplyOutcome {
        // Advance the composition revision so cached value views rebuild. This
        // is the single funnel for every authoring and layer-stack edit, so a
        // value-only change that drops no index still invalidates them.
        cache.bump_revision();
        // The population epoch moves only for a pass that can change which
        // prims exist. Stamped here, before anything is dropped, so it does not
        // depend on the invalidation finding a victim: a structural edit whose
        // victim set comes back empty — nothing cached reads the edited layer
        // yet — still retires the memos that recorded a prim's absence.
        if self.touches_population() {
            cache.invalidate_population();
        }

        // Rebuild the graph's layer-stack precomputed state before the scoped drop
        // below reads it, and collect the affected layer set the drop evicts
        // against. A `subLayers`/`subLayerOffsets`/`timeCodesPerSecond`/`expressionVariables`
        // edit rebuilds the sublayer edges (which subsumes the relocate recompute and
        // re-expands `${VAR}` edges) and returns the layers whose composed edges
        // shifted, the authored layers, and any whose relocates moved — together
        // with the per-stack composed-variable deltas the rebuild emitted; a
        // `layerRelocates`-only edit refreshes the cached relocates, with the edited
        // layer added to its relocate set. Each refreshes the graph's own diagnostic
        // buckets in place; the cache holds no copy.
        let (affected, vars_deltas) = if self
            .layer_stack
            .intersects(LayerStackChanges::NEEDS_LAYER_STACK_REBUILD)
        {
            let recompute = graph.recompute_sublayers(Some(&self.layer_stack_layers));
            (recompute.affected, recompute.vars_deltas)
        } else if self.layer_stack.intersects(LayerStackChanges::NEEDS_RELOCATES_REBUILD) {
            let mut relocated = graph.recompute_relocates();
            relocated.extend(self.layer_stack_layers.iter().copied());
            (relocated, Vec::new())
        } else {
            (HashSet::new(), Vec::new())
        };

        // Layer-stack-tier change: drop only the indices whose composition reads a
        // stack the rebuild re-resolved. `affected` names every such stack's layers
        // — the edited layers stay members of the stacks they belong to, the edge
        // diff adds a descendant whose inherited context shifted, and the relocate
        // set adds any whose effective relocates moved — so `invalidate_layers`
        // evicts those indices and the prototypes they touch and leaves the rest
        // warm. The blanket subsumes the vars deltas: a prim using a stack whose
        // variables cascaded from an edited layer composes that layer's stack
        // somewhere on its arc chain, so the layer fanout already reaches it. A
        // membership change can also admit prims no cached index names yet, so the
        // resync reported is the pseudo-root, not the evicted set.
        //
        // The asset-path channel is collected from the deltas whichever branch runs,
        // matching C++, which records `didChangeExpressionVariables` on a
        // composed-value change alone. It must be gathered before the drop below
        // empties the registrations it reads. On the significant branch the
        // pseudo-root resync stands for every asset value on the stage, so the
        // notice discards what is collected here.
        let asset_paths_resynced = asset_path_victims(cache, &vars_deltas);
        let mut resynced = if self.layer_stack.contains(LayerStackChanges::SIGNIFICANT) {
            cache.invalidate_layers(&affected);
            vec![Path::abs_root()]
        } else {
            apply_vars_deltas(cache, graph, &vars_deltas)
        };

        // `defaultPrim` edits: each evicts the prims that recorded consulting the
        // field and reports the dependents of the prim path it used to name.
        resynced.extend(apply_default_prim_edits(cache, graph, &self.default_prim_edits));

        // A prim-tier index invalidation can change which prims are instances or
        // how they compose, so affected entries in the shared-prototype registry
        // (spec 11.3.3) are dropped rather than left stale and lazily recomposed
        // on the next instancing query. The layer-stack path evicted its
        // prototypes through `invalidate_layers` above.
        let changed: Vec<Path> = self
            .cache
            .all_significant()
            .chain(self.cache.did_change_prims.iter())
            .map(Path::prim_path)
            .chain(self.cache.did_change_specs.iter().map(|(_, path)| path.prim_path()))
            .collect();
        if !changed.is_empty() {
            // The tiers that named `changed` were snapshotted before this pass
            // ran, so the roots it retires reach the notice only here.
            resynced.extend(cache.invalidate_prototypes(&changed));
        }

        for path in self.cache.all_significant() {
            cache.drop_index_subtree(path);
        }
        for path in &self.cache.did_change_prims {
            // Subsumed by an ancestor whose subtree just went? Only the stage half
            // can answer: this tier holds composed paths, and a prefix test against
            // an authored spelling could match by coincidence and skip a live drop.
            if self.cache.did_change_significantly.iter().any(|p| path.has_prefix(p)) {
                continue;
            }
            cache.drop_index(path);
        }
        // Batch the spec-tier rescan: an index reached by several of this round's
        // changed sites refreshes its `has_specs` flags per site but finalizes its
        // spec stack once. Sites subsumed by an ancestor whose subtree was already
        // dropped are skipped — against the authored half alone, the one sharing
        // a spec site's namespace. A site a dependency-derived stage path covers is
        // rescanned anyway and finds nothing: its registrations went with the drop.
        // Nothing reads `did_change_specs` after this, so move its sites out rather
        // than cloning each `Path`.
        let sites: Vec<(LayerId, Path)> = mem::take(&mut self.cache.did_change_specs)
            .into_iter()
            .filter(|(_, path)| !self.cache.authored_significant.iter().any(|p| path.has_prefix(p)))
            .collect();
        if !sites.is_empty() {
            cache.rescan_specs(graph, &sites);
        }

        // Property tier: a `targetPaths` / `connectionPaths` edit leaves the graph
        // intact, so drop only the edited property's resolved-target memo on each
        // affected prim. Every entry is cleared; one naming a prim whose index the
        // significant tier already dropped finds no memo left to clear.
        //
        // TODO: `fanout_targets` puts both namespaces in one set — a dependency
        // result and the literal edited prim — so no prefix test over it is sound
        // against either half of the significant tier. Splitting it on namespace
        // the way that tier is split would let the already-dropped prims be
        // skipped.
        cache.clear_target_memos(self.cache.did_change_targets.iter());

        ApplyOutcome {
            resynced,
            asset_paths_resynced,
        }
    }
}

/// The composed paths whose `asset` values may re-resolve after `deltas`, for
/// the notice's asset-path channel (C++ `assetPathResyncChanges`, gathered by
/// `UsdStage::_HandleLayersDidChange` from each layer stack flagged
/// `didChangeExpressionVariables`).
///
/// A value-time `` `${VAR}` `` expression in an `asset` value is re-evaluated on
/// every access against its opinion's layer stack and never recorded as a
/// dependency, so no index drop can stand in for it: every prim using a stack
/// whose composed variables moved must be named. The gate is the composed
/// *value*, matching C++ `expressionVarsChanged` — a delta that only moved the
/// stack's variable source re-keys arcs without changing what an expression
/// evaluates to.
fn asset_path_victims(cache: &IndexCache, deltas: &[StackVarsDelta]) -> Vec<Path> {
    let mut victims = Vec::new();
    for delta in deltas.iter().filter(|delta| delta.old_expr != delta.new_expr) {
        victims.extend(cache.dependencies().prims_for_stack(delta.stack));
        // What the root stack answers with subsumes every path a later delta in
        // the cascade could add. Every `Stage::set_expression_variables` moves
        // it, so stopping here is the common case, not an edge one.
        if delta.stack == LayerStackId::ROOT {
            break;
        }
    }
    victims
}

/// Applies this round's `defaultPrim` edits, returning the composed prim paths
/// to report as resynced.
///
/// Two different sets, deliberately. The eviction is exactly the prims whose
/// builds recorded consulting the field
/// ([`prims_using_default_prim`](super::dependencies::Dependencies::prims_using_default_prim)),
/// since nothing else composes differently. The report follows C++ `PcpChanges`,
/// which fans out from the prim path the field used to name (`changes.cpp`):
/// that also reaches prims referencing the old path explicitly, which do not
/// need recomposing but which C++ resyncs.
///
/// It reaches them through graph sites only, so it stops one short of C++ in a
/// case C++ answers through `PcpDependencyTypeRoot`: the prim *at* the old
/// default path does not register its own site
/// ([`Dependencies::add`](super::dependencies::Dependencies::add) skips the
/// self-Root edge), so an edit on the layer that owns it leaves it unreported.
/// Its composition is unaffected either way — this is the over-report shrinking,
/// not a missed recompose.
///
/// With no prior prim path the report is the recorded consumers instead. C++ fans
/// out from the pseudo-root site on the layer there, reaching the placeholder arcs
/// it grafts for an unresolved default; this port grafts none and records the
/// dependency directly, so the record names exactly what those placeholders stand
/// for, without the collateral a `/`-site subtree walk would sweep in.
///
/// Both sets are gathered before the drop, which retires the registrations they
/// read.
fn apply_default_prim_edits(
    cache: &mut IndexCache,
    graph: &LayerGraph,
    edits: &[(LayerId, Option<tf::Token>)],
) -> Vec<Path> {
    let mut reported: BTreeSet<Path> = BTreeSet::new();
    let mut victims: BTreeSet<Path> = BTreeSet::new();
    for (layer, prior) in edits {
        let old = prior.as_deref().and_then(sdf::default_prim_path);
        let current = graph
            .default_prim_token(*layer)
            .as_deref()
            .and_then(sdf::default_prim_path);
        // The composed default did not move, so no index composes differently and
        // no dependent resyncs — C++'s equality skip. The value-diff in
        // `ChangeList` already suppresses an identical re-author, so what reaches
        // here is a re-spelling (`"Source"` for `"/Source"`).
        if old == current {
            continue;
        }
        let deps = cache.dependencies();
        // With a prior prim path, C++ fans out from its site; the consumers this
        // evicts are a subset of that, so they need no separate mention.
        if let Some(path) = &old {
            reported.extend(deps.graph_ancestor_lookup(*layer, path));
            reported.extend(deps.subtree_lookup(*layer, path));
        }
        victims.extend(deps.prims_using_default_prim(*layer));
    }
    // One drop for the round, as the expression-variable path batches for the
    // same reason: each pays a prototype scan per victim. It hands back the
    // prototype roots it retired alongside the prims it evicted, and both
    // resynced, so both are reported.
    reported.extend(cache.drop_index_victims(victims.into_iter().collect()));
    reported.into_iter().collect()
}

/// Consumes an `expressionVariables` rebuild's per-stack deltas, dropping their
/// recorded dependents and returning them, with the prototype roots retired
/// alongside, as the resynced paths — the C++
/// five-step `_DidChangeLayerStackExpressionVariables` diff, whose every victim
/// is a `DidChangeSignificantly`. Step 1 (composed variables and source
/// unchanged) emits no delta, so an identical re-authoring costs only the
/// rebuild and the revision bump; step 5 — propagation to stacks whose override
/// source resolves through a changed one — is the rebuild's seed cascade, which
/// emits those stacks' own deltas. Victims accumulate across deltas and drop
/// once, since a cascade's victim sets overlap and each drop pays a per-victim
/// prototype scan.
fn apply_vars_deltas(cache: &mut IndexCache, graph: &LayerGraph, deltas: &[StackVarsDelta]) -> Vec<Path> {
    let mut victims: BTreeSet<Path> = BTreeSet::new();
    for delta in deltas {
        if delta.old_source == delta.new_source {
            let changed = graph.changed_var_names(delta.old_expr, delta.new_expr);
            if graph.stack_sublayer_var_deps(delta.stack).is_disjoint(&changed) {
                // Step 4: a value-only change; resync exactly the prims whose
                // builds recorded reading a changed name from this stack.
                victims.extend(cache.dependencies().prims_using_vars(delta.stack, &changed));
                continue;
            }
            // Step 3: a changed name feeds one of the stack's own `${VAR}`
            // sublayer entries, so its membership may have swapped — as
            // significant as a source change.
        }
        // Step 2 (the variable source changed, so every arc out of the stack
        // keys its target differently) or step 3: resync every prim using the
        // stack. The root stack's users are the whole cache, subsuming every
        // victim any delta could add — prototype roots included, so the roots
        // retired here need no separate mention — so drop it once and stop.
        if delta.stack == LayerStackId::ROOT {
            return cache.drop_index_victims(vec![Path::abs_root()]);
        }
        victims.extend(cache.dependencies().prims_for_stack(delta.stack));
    }
    cache.drop_index_victims(victims.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::pcp::layer_stack::{ExprVarId, ExprVarInterner, VarsSource};
    use crate::pcp::{LoadRules, PopulationMask, VariantFallbackMap};
    use crate::sdf::{ChangeFlags, ChangeList, Value};

    fn p(s: &str) -> Path {
        Path::new(s).expect("valid path")
    }

    /// The first layer id in the graph, or a placeholder for an empty graph.
    fn first_layer(graph: &LayerGraph) -> LayerId {
        graph.all_ids().first().copied().unwrap_or(LayerId::INVALID)
    }

    fn empty_cache() -> (LayerGraph, IndexCache) {
        let graph = LayerGraph::from_layers(Vec::new(), 0, sdf::LayerRegistry::default());
        (
            graph,
            IndexCache::new(
                VariantFallbackMap::new(),
                LoadRules::all(),
                PopulationMask::all(),
                Vec::new(),
            ),
        )
    }

    /// An interned context holding `name = value`, for building the before/after
    /// pair a [`StackVarsDelta`] carries.
    fn intern(interner: &mut ExprVarInterner, name: &str, value: &str) -> ExprVarId {
        interner.intern(&HashMap::from([(name.to_string(), Value::String(value.to_string()))]))
    }

    /// The asset-path channel is gated on the composed *value* moving (C++
    /// `expressionVarsChanged`): a delta that only re-sourced a stack's
    /// variables leaves every expression evaluating to what it did before.
    #[test]
    fn asset_victims_need_value() {
        let (_graph, cache) = empty_cache();
        let mut interner = ExprVarInterner::default();
        let before = intern(&mut interner, "V", "a");
        let after = intern(&mut interner, "V", "b");
        assert_ne!(before, after);

        let changed = StackVarsDelta {
            stack: LayerStackId::ROOT,
            old_expr: before,
            new_expr: after,
            old_source: VarsSource::Root,
            new_source: VarsSource::Root,
        };
        assert_eq!(asset_path_victims(&cache, &[changed]), vec![Path::abs_root()]);

        let source_only = StackVarsDelta {
            stack: LayerStackId::ROOT,
            old_expr: before,
            new_expr: before,
            old_source: VarsSource::Root,
            new_source: VarsSource::Instance(LayerStackId::ROOT),
        };
        assert!(asset_path_victims(&cache, &[source_only]).is_empty());
    }

    #[test]
    fn references_promotes_to_significant() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo"))
            .info_changed
            .insert(FieldKey::References.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        assert!(changes.cache.authored_significant.contains(&p("/Foo")));
    }

    #[test]
    fn variant_selection_promotes_to_significant() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo"))
            .info_changed
            .insert(FieldKey::VariantSelection.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        assert!(changes.cache.authored_significant.contains(&p("/Foo")));
    }

    /// An opinion authored inside a variant is fanned out twice — from the
    /// literal `/Foo{set=sel}Bar` and from the `/Foo/Bar` it composes into — and
    /// both spellings stay in the edited layer's namespace, so an edit target
    /// maps each before the stage names an object by it.
    #[test]
    fn variant_edit_stays_authored() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo{set=sel}Bar"))
            .info_changed
            .insert(FieldKey::References.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        assert_eq!(
            changes.cache.authored_significant.iter().collect::<Vec<_>>(),
            [&p("/Foo/Bar"), &p("/Foo{set=sel}Bar")]
        );
        assert!(
            changes.cache.did_change_significantly.is_empty(),
            "nothing depends on either site, so no stage path is derived"
        );
    }

    /// `permission` is inert metadata for composition (C++ only enforces it for
    /// legacy non-Usd caches), so editing it resolves live against the bumped
    /// revision like any other non-composition field — the over-invalidation
    /// guard mirroring `kind_metadata_drops_nothing`.
    #[test]
    fn permission_metadata_drops_nothing() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo"))
            .info_changed
            .insert(FieldKey::Permission.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        assert!(changes.cache.all_significant().next().is_none());
        assert!(changes.cache.did_change_specs.is_empty());
    }

    /// A non-composition metadata edit (`kind`) on an existing prim resolves
    /// live against the bumped revision, so the classifier drops no index in
    /// either the significant or the spec tier — the over-invalidation guard.
    #[test]
    fn kind_metadata_drops_nothing() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo"))
            .info_changed
            .insert(FieldKey::Kind.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        assert!(changes.cache.all_significant().next().is_none());
        assert!(changes.cache.did_change_specs.is_empty());
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
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);

        assert!(changes.cache.authored_significant.contains(&p("/X")));
    }

    #[test]
    fn inert_add_lands_on_spec_tier() {
        let (graph, cache) = empty_cache();
        let layer = first_layer(&graph);
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo")).flags = ChangeFlags::ADD_INERT_PRIM;
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(layer, &cl)]);
        // An inert add reshapes no graph, so it stays out of the significant
        // tier and lands in the spec tier keyed by its authoring layer.
        assert!(!changes.cache.all_significant().any(|path| *path == p("/Foo")));
        assert!(changes.cache.did_change_specs.contains(&(layer, p("/Foo"))));
    }

    #[test]
    fn non_inert_add_is_significant_with_self_path() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo")).flags = ChangeFlags::ADD_NON_INERT_PRIM;
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        assert!(changes.cache.authored_significant.contains(&p("/Foo")));
    }

    /// The population epoch tracks what can change which prims exist, not every
    /// edit: a value-only change must leave a completed population walk — and
    /// the redirection and eligibility memos derived from it — standing, while
    /// a structural one retires them.
    #[test]
    fn epoch_tracks_structure_only() {
        // A value edit records its property entry with no structural flag; a
        // new `def` spec records one.
        for (path, flags, advances) in [
            ("/Foo.attr", ChangeFlags::empty(), false),
            ("/Foo", ChangeFlags::ADD_NON_INERT_PRIM, true),
        ] {
            let (mut graph, mut cache) = empty_cache();
            let before = cache.population_epoch();
            let revision = cache.revision();
            let mut cl = ChangeList::new();
            cl.entry_mut(&p(path)).flags = flags;
            let mut changes = Changes::new();
            changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
            changes.apply(&mut cache, &mut graph);
            assert_ne!(cache.revision(), revision, "every edit advances the revision");
            assert_eq!(
                cache.population_epoch() != before,
                advances,
                "a change at {path} must {} the population epoch",
                if advances { "advance" } else { "leave" }
            );
        }
    }

    #[test]
    fn sublayers_change_is_layer_stack_significant() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(FieldKey::SubLayers.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        assert!(changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
        assert!(changes.layer_stack.contains(LayerStackChanges::LAYERS));
    }

    #[test]
    fn default_prim_records_edit() {
        let (graph, cache) = empty_cache();
        let layer = first_layer(&graph);
        let mut cl = ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(FieldKey::DefaultPrim.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(
            &cache,
            &[LayerChanges {
                layer,
                changes: &cl,
                prior_default_prim: Some(tf::Token::from("Source")),
            }],
        );

        // The edit is queued with its prior value for `apply` to act on, and
        // decides nothing here: no tier is touched, and in particular the whole
        // cache is not marked for a drop.
        assert_eq!(changes.default_prim_edits, [(layer, Some(tf::Token::from("Source")))]);
        assert!(changes.cache.did_change_significantly.is_empty());
        assert!(changes.cache.authored_significant.is_empty());
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
            changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
            assert!(changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
        }
    }

    /// Editing a layer's `expressionVariables` flags the layer stack for an
    /// edge rebuild (`EXPRESSION_VARS`) without the `SIGNIFICANT` blanket — the
    /// apply phase consumes the rebuild's per-stack deltas to drop only the
    /// recorded dependents.
    #[test]
    fn expression_vars_not_significant() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(FieldKey::ExpressionVariables.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        assert!(changes.layer_stack.contains(LayerStackChanges::EXPRESSION_VARS));
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
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        assert!(changes.layer_stack.contains(LayerStackChanges::RELOCATES));
        assert!(changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }

    #[test]
    fn property_changes_no_op() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        cl.entry_mut(&p("/Foo.attr")).flags = ChangeFlags::ADD_PROPERTY;
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        assert!(changes.cache.all_significant().next().is_none());
        assert!(changes.cache.did_change_specs.is_empty());
        assert!(!changes.layer_stack.contains(LayerStackChanges::SIGNIFICANT));
    }

    /// A `targetPaths` edit authored inside a variant composes into the
    /// variant-stripped prim, so the target tier must restale that stripped prim's
    /// memo (`/P/Child`), not only the variant path's (`/P{v=x}Child`).
    #[test]
    fn variant_target_edit_restales_stripped_prim() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        let entry = cl.entry_mut(&p("/P{v=x}Child.r"));
        entry.flags = ChangeFlags::CHANGE_RELATIONSHIP_TARGETS;
        entry.info_changed.insert(FieldKey::TargetPaths.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        let key = TargetMemoKey {
            kind: PropertyTargetKind::Relationship,
            property_suffix: ".r".to_owned(),
        };
        assert!(changes.cache.did_change_targets.contains(&(p("/P/Child"), key.clone())));
        assert!(changes.cache.did_change_targets.contains(&(p("/P{v=x}Child"), key)));
    }

    /// Replacing a relationship with a same-named attribute in one edit surfaces
    /// both `targetPaths` and `connectionPaths` on the entry; the classifier must
    /// restale both memo kinds, or the prior kind's memo would linger and a later
    /// query could return the stale pre-replacement targets.
    #[test]
    fn property_replace_restales_both_kinds() {
        let (graph, cache) = empty_cache();
        let mut cl = ChangeList::new();
        let entry = cl.entry_mut(&p("/P.x"));
        entry.info_changed.insert(FieldKey::TargetPaths.as_str().into());
        entry.info_changed.insert(FieldKey::ConnectionPaths.as_str().into());
        let mut changes = Changes::new();
        changes.did_change(&cache, &[LayerChanges::plain(first_layer(&graph), &cl)]);
        let key = |kind| TargetMemoKey {
            kind,
            property_suffix: ".x".to_owned(),
        };
        assert!(
            changes
                .cache
                .did_change_targets
                .contains(&(p("/P"), key(PropertyTargetKind::Relationship)))
        );
        assert!(
            changes
                .cache
                .did_change_targets
                .contains(&(p("/P"), key(PropertyTargetKind::Connection)))
        );
    }
}
