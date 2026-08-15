//! Stage-tier change sinks: observers of a [`Stage`]'s composed-scene changes.
//!
//! A [`StageSink`] is the high tier of the two-level change pipeline. The low
//! tier is [`sdf::LayerSink`], fired at each layer's commit seam; the stage
//! installs an aggregating layer sink on every layer it owns, which records the
//! committed edit so the stage can recompose and, once composition is
//! invalidated, deliver a composed [`CommittedChange`] to every `StageSink`.
//! Higher-level features (change notification, undo/redo, replay, validation)
//! are built as sinks; `Stage` installs none by default, so the no-sink path
//! costs nothing extra.
//!
//! Install with [`Stage::add_sink`](super::Stage::add_sink), which returns a
//! [`StageSinkId`] to later [`Stage::remove_sink`](super::Stage::remove_sink). A
//! plain `Fn(&Stage, &CommittedChange)` closure is itself a `StageSink`, so
//! `add_sink` takes either a full sink type or a quick closure observer.

use std::collections::BTreeSet;

use super::stage::Stage;
use crate::{pcp, sdf, tf};

/// A [`sink::Id`](sdf::sink::Id) for a [`StageSink`] installed on a [`Stage`].
pub type StageSinkId = sdf::sink::Id<dyn StageSink>;

/// An observer of a [`Stage`]'s composed-scene changes and lifecycle events.
///
/// All methods default to doing nothing, so a sink implements only the events it
/// cares about. Sinks fire in installation order, after composition has been
/// invalidated and all stage borrows are released — so a sink may read (or
/// further author) the `stage`, but must not add or remove sinks from within a
/// callback (the pool is borrowed for the duration of a fan-out).
pub trait StageSink {
    /// Observe a committed edit in composed (stage) namespace, after composition
    /// has been invalidated and the stage's borrows released — so the callback
    /// may read or re-author the `stage`.
    ///
    /// This is the composed counterpart to [`sdf::LayerSink::after_commit`]:
    /// where a layer sink sees one layer's raw [`ChangeList`](sdf::ChangeList) in
    /// that layer's own namespace the instant it commits, a stage sink sees the
    /// resulting change to the composed scene — the resynced, changed-info, and
    /// asset-path-resynced prim paths in stage namespace, after PCP has
    /// invalidated the affected indices.
    ///
    /// The two are bridged by an aggregating [`sdf::LayerSink`] the stage installs
    /// on each layer it owns: each layer commit records its edit, and the recorded
    /// edits are processed together in one recompose. So an authoring operation
    /// that touches several
    /// layers at once — a batched namespace edit spanning the local layer stack —
    /// fires this once with the union of every layer's effect on the composed
    /// scene, not once per layer. (The single [`change`](CommittedChange) reports
    /// the merged record under the strongest edited layer; see
    /// [`CommittedChange::change_list`].)
    fn after_commit(&self, stage: &Stage, change: &CommittedChange<'_>) {
        let _ = (stage, change);
    }

    /// Inspect a staged edit to one of the stage's layers before it commits,
    /// while the layer's pristine pre-edit values are still readable.
    ///
    /// The stage-tier counterpart to [`sdf::LayerSink::before_commit`], fired
    /// once per edited layer inside the layer's commit seam. It carries the
    /// layer's [`base`](PendingChange::base) — the values as they stood before
    /// this transaction — which is what lets a sink derive an inverse (undo)
    /// record here; after the commit drains, those values are gone. Every
    /// `before_commit` of one atomic transaction fires (in phase order, before
    /// any [`after_commit`](Self::after_commit)) sharing one
    /// [`generation`](PendingChange::generation); a transaction that a later
    /// veto or a panic rolls back fires no `after_commit`, so a sink keys its
    /// per-transaction scratch on the generation to discard the orphaned
    /// captures when the next transaction opens.
    ///
    /// The layer graph is mid-edit for the duration, so a `before_commit` sink
    /// must derive only from the values `change` carries — it must not re-enter
    /// authoring or read composed state on `stage`. Unlike
    /// [`sdf::LayerSink::before_commit`] this cannot veto: it observes.
    fn before_commit(&self, stage: &Stage, change: &PendingChange<'_>) {
        let _ = (stage, change);
    }

    /// Observe an edit-target change (C++ `UsdNotice::StageEditTargetChanged`).
    fn edit_target_changed(&self, stage: &Stage) {
        let _ = stage;
    }

    /// Observe a layer mute/unmute (C++ `UsdNotice::LayerMutingChanged`).
    fn layer_muting_changed(&self, stage: &Stage, layer: &str, muted: bool) {
        let _ = (stage, layer, muted);
    }

    /// Observe a payload load/unload change (C++ `UsdNotice::ObjectsChanged`
    /// fired by `Load`/`Unload`/`LoadAndUnload`/`SetLoadRules`, treating every
    /// reported path as a full resync).
    ///
    /// `resynced` is the bounded set of paths
    /// [`Stage::load`]/[`Stage::unload`]/[`Stage::load_and_unload`]/
    /// [`Stage::set_load_rules`] used to invalidate the cache — never empty,
    /// since a no-op edit fires no notification at all.
    fn load_rules_changed(&self, stage: &Stage, resynced: &[sdf::Path]) {
        let _ = (stage, resynced);
    }
}

/// Where a committed edit originated, which determines the namespace its
/// [`CommittedChange`] paths are reported in.
///
/// Distinguishing the three cases removes the ambiguity of a bare "no mapping"
/// signal: a local edit and a direct non-local edit both translate no paths, but
/// a sink must treat their paths differently — the first are composed (stage)
/// paths, the second are the edited layer's own.
#[derive(Debug, Clone)]
pub enum Provenance {
    /// An edit to a layer of the local (root) layer stack: stage authoring
    /// through the root edit target, a [`Stage::batch_edit`](super::Stage::batch_edit),
    /// or a direct [`Stage::layer_mut`](super::Stage::layer_mut) edit to a local
    /// layer. The local layer stack shares the stage's namespace, so paths are
    /// already composed (stage) paths.
    LocalStack,
    /// Stage authoring through an edit target that remaps paths — a reference,
    /// payload, or variant arc. The carried mapping translates the authored
    /// (layer-namespace) paths to composed stage namespace. This is keyed on the
    /// mapping, not on locality: a variant edit target authors into a local layer
    /// yet still remaps (`/Prim{set=sel}child` to `/Prim/child`), so it is
    /// `EditTarget` too; an identity-mapped target needs no translation and is
    /// instead [`LocalStack`](Self::LocalStack) or [`DirectLayerEdit`](Self::DirectLayerEdit).
    EditTarget(pcp::MapFunction),
    /// A direct [`Stage::layer_mut`](super::Stage::layer_mut) edit to a non-local
    /// (referenced or payload) layer. Nothing is translated
    /// ([`mapping`](Self::mapping) is `None`): the literal authored paths stay in
    /// the edited layer's own namespace, while the dependency-derived
    /// [`resynced`](CommittedChange::resynced) paths (the composed prims that
    /// reference the layer) are already in stage namespace. The two coexist
    /// untranslated in one [`CommittedChange`], reaching the stage through
    /// composition dependencies rather than a single path mapping.
    DirectLayerEdit,
}

impl Provenance {
    /// The namespace mapping that carries this edit's paths to composed stage
    /// namespace, or `None` when paths need no translation — either because they
    /// are already stage paths ([`LocalStack`](Self::LocalStack)) or because they
    /// are reported in the edited layer's own namespace
    /// ([`DirectLayerEdit`](Self::DirectLayerEdit)).
    pub fn mapping(&self) -> Option<&pcp::MapFunction> {
        match self {
            Provenance::EditTarget(m) => Some(m),
            Provenance::LocalStack | Provenance::DirectLayerEdit => None,
        }
    }
}

/// A committed edit handed to [`StageSink::after_commit`] (the data the former
/// `ObjectsChanged` notice carried).
///
/// A flat, borrowed view valid only for the callback. Clone what must outlive it
/// ([`sdf::ChangeList`] is [`Clone`]).
///
/// [`resynced`](Self::resynced) and [`changed_info_only`](Self::changed_info_only)
/// are in composed stage namespace for stage-authored edits and edits to a local
/// layer. A direct edit to a non-local (referenced or payload) layer is reported
/// in the edited layer's own namespace instead; [`provenance`](Self::provenance)
/// says which. [`asset_paths_resynced`](Self::asset_paths_resynced) is stage
/// namespace either way, being derived from composition dependencies rather
/// than from the authored change record.
pub struct CommittedChange<'a> {
    /// Paths whose composition was resynced — the prim index and its namespace
    /// descendants were dropped (C++ `ResyncedPaths`). Composed/stage namespace.
    ///
    /// Minimal in ancestors: an entry stands for its whole subtree, so a
    /// resynced `/foo` appears without `/foo/bar`. The exception is a
    /// [`Provenance::DirectLayerEdit`], whose mixed namespaces (see
    /// [`provenance`](Self::provenance)) leave no sound way to compare paths by
    /// prefix, so its entries are reported as classified.
    pub resynced: &'a [sdf::Path],
    /// Paths that changed only in field or target info, without restructuring
    /// composition (C++ `ChangedInfoOnlyPaths`). Composed/stage namespace.
    ///
    /// Disjoint from [`resynced`](Self::resynced), which already implies
    /// re-reading everything beneath it — with the same
    /// [`Provenance::DirectLayerEdit`] exception, where the two sets are in
    /// different namespaces and may overlap.
    pub changed_info_only: &'a [sdf::Path],
    /// Paths whose subtrees may resolve `asset` values to a different location
    /// even though no authored value changed — an `expressionVariables` edit
    /// re-pointed a value-time `` `${VAR}` `` expression (C++
    /// `ObjectsChanged::GetResolvedAssetPathsResyncedPaths`). Minimal in
    /// ancestors like [`resynced`](Self::resynced), and disjoint from it, since
    /// a resync already implies re-reading everything beneath it.
    ///
    /// Always composed stage namespace, whatever the
    /// [`provenance`](Self::provenance), since these paths are derived from
    /// composition dependencies rather than from the authored change record.
    /// Under a [`Provenance::DirectLayerEdit`] only the dependency-derived half
    /// of `resynced` shares that namespace, so an entry may conservatively
    /// survive a same-spelled resync. An instance's shared composition is named
    /// by its `/__Prototype_N` path, the key it composes under (C++ reports
    /// prototype paths the same way); a proxy reaches it through its instance
    /// root, which is named in its own right, or through
    /// [`Prim::prototype`](super::Prim::prototype).
    pub asset_paths_resynced: &'a [sdf::Path],
    /// Canonical identifier of the layer the edit landed on, and the lookup key
    /// for reading its authored values.
    pub layer_identifier: &'a str,
    /// The recorded change index for the edit, keyed in the edited layer's
    /// namespace (under an arc or variant edit target this differs from the
    /// stage-namespace [`resynced`](Self::resynced) /
    /// [`changed_info_only`](Self::changed_info_only) paths;
    /// [`changed_fields`](Self::changed_fields) bridges the two).
    pub change_list: &'a sdf::ChangeList,
    /// The raw change record per edited layer — each layer's canonical identifier
    /// and the change index keyed in that layer's own namespace. A transaction
    /// that edits several layers (a batch or namespace edit) lists each; the
    /// merged [`change_list`](Self::change_list) is their union attributed to the
    /// strongest layer, which loses which layer authored what. Read per entry to
    /// derive a faithful per-layer diff.
    pub layer_changes: &'a [(String, sdf::ChangeList)],
    /// Where this edit originated, which determines the namespace
    /// [`resynced`](Self::resynced) and
    /// [`changed_info_only`](Self::changed_info_only) are reported in (see
    /// [`Provenance`]).
    pub provenance: &'a Provenance,
    /// The id of the atomic transaction this change is for, matching the
    /// [`generation`](PendingChange::generation) its layers carried at
    /// [`before_commit`](StageSink::before_commit). Each committed transaction
    /// delivers its own `after_commit`, so a sink can correlate a transaction's
    /// pre-commit and post-commit events by it — e.g. an
    /// [`UndoStage`](super::UndoStage) pairs the two to seal one transaction's
    /// captured inverses.
    pub generation: u64,
}

impl CommittedChange<'_> {
    /// The field names authored at `path` by this edit (C++ `GetChangedFields`),
    /// or an empty set if `path` was not touched. `path` is in stage namespace,
    /// the same as the paths in [`resynced`](Self::resynced) and
    /// [`changed_info_only`](Self::changed_info_only); under an arc or variant
    /// edit target it is translated back to the layer-namespace key
    /// [`change_list`](Self::change_list) records it under.
    pub fn changed_fields(&self, path: &sdf::Path) -> &BTreeSet<tf::Token> {
        static EMPTY: BTreeSet<tf::Token> = BTreeSet::new();
        let key = match self.provenance.mapping() {
            Some(m) => match m.map_target_to_source(path) {
                Some(key) => key,
                None => return &EMPTY,
            },
            None => path.clone(),
        };
        self.change_list
            .entries()
            .iter()
            .find(|(p, _)| p == &key)
            .map_or(&EMPTY, |(_, entry)| &entry.info_changed)
    }
}

/// A staged, not-yet-committed edit to one of the stage's layers, handed to
/// [`StageSink::before_commit`] — the stage-tier view of one layer's
/// [`sdf::PendingLayerChange`].
///
/// A borrowed view valid only for the callback. It carries the layer's pre-edit
/// [`base`](Self::base) and the derived [`change_list`](Self::change_list); a
/// sink pairs them to derive the inverse of the edit (the old value of each
/// touched field, the whole state of each removed spec) without committing.
pub struct PendingChange<'a> {
    /// Canonical identifier of the layer being edited — the
    /// [`ApplyMode::ExactLayer`](super::ApplyMode::ExactLayer) key for replaying
    /// a derived diff back onto this same layer.
    pub layer_identifier: &'a str,
    /// The layer's values as they stood before this transaction (the overlay's
    /// base). Reading a field here yields its pre-edit value; a field or spec
    /// absent here was created by this edit.
    pub base: &'a dyn sdf::AbstractData,
    /// The change index derived for this layer's staged edit, keyed in the
    /// layer's own namespace — which specs and fields the edit touched.
    pub change_list: &'a sdf::ChangeList,
    /// The edit target's namespace mapping (layer namespace to composed stage
    /// namespace), or `None` for a local or identity-mapped edit whose paths are
    /// already stage paths. Carried onto a derived [`Diff`](super::Diff) so a
    /// later replay reports composed notice paths.
    pub mapping: Option<&'a pcp::MapFunction>,
    /// The id of the atomic transaction this edit belongs to: shared by every
    /// layer the transaction edits, distinct from the next transaction's, and
    /// monotonically increasing. It equals the
    /// [`generation`](CommittedChange::generation) the matching
    /// [`after_commit`](StageSink::after_commit) carries, so a sink can group a
    /// transaction's per-layer pre-commit events and correlate them with its
    /// commit — e.g. an [`UndoStage`](super::UndoStage) buffers per-layer inverses
    /// by it and seals them when the commit arrives.
    pub generation: u64,
}

/// A bare closure is a [`StageSink`] that only observes committed edits — the
/// ergonomic "just watch changes" case, installed straight through
/// [`Stage::add_sink`](super::Stage::add_sink) with no wrapper type. `Fn` (not
/// `FnMut`) because a sink is invoked through a shared `&self`; capture
/// interior-mutable state (a `Cell`/`RefCell`) to accumulate.
impl<F: Fn(&Stage, &CommittedChange<'_>)> StageSink for F {
    fn after_commit(&self, stage: &Stage, change: &CommittedChange<'_>) {
        self(stage, change);
    }
}

/// The owned backing for one [`CommittedChange`].
///
/// A `CommittedChange` is a borrowed view valid only for the `after_commit`
/// call, so the paths and change record it points at must outlive it. The stage
/// builds a `Payload` from the classified [`pcp::Changes`] and the edit's raw
/// change list, then lends it out through
/// [`committed_change`](Self::committed_change). Built only when a sink is
/// installed, so the no-sink path allocates nothing.
pub(super) struct Payload {
    resynced: Vec<sdf::Path>,
    changed_info_only: Vec<sdf::Path>,
    asset_paths_resynced: Vec<sdf::Path>,
    /// The subset of [`resynced`](Self::resynced) whose entries stand for their
    /// whole subtree, and so are the only sound covering prefixes.
    ///
    /// [`resynced`](Self::resynced) mixes three invalidation tiers (see
    /// [`pcp::CacheChanges::subtree_resynced_paths`]): only the significant tier
    /// and the layer-stack victims drop a subtree, while the spec tier refreshes
    /// a site in place. Pruning by prefix against the whole set would let an
    /// inert `over` at `/A` delete the report of an attribute authored at
    /// `/A/B.x`. Not reported — it is a projection of `resynced`.
    subtree_resynced: Vec<sdf::Path>,
    change_list: sdf::ChangeList,
    layer_changes: Vec<(String, sdf::ChangeList)>,
}

impl Payload {
    /// Classify one edit into the composed path-sets a sink reports.
    ///
    /// `changes` is the edit's invalidation plan and `scratch` its raw change
    /// list, in the edited layer's namespace. `provenance` says how those paths
    /// reach composed stage namespace — its [`mapping`](Provenance::mapping)
    /// translates them, or leaves them untranslated for a local or direct edit.
    ///
    /// [`resynced`](CommittedChange::resynced) is the union of the significant and
    /// prim-tier composed paths; [`changed_info_only`](CommittedChange::changed_info_only)
    /// is every other edited path that authored a field value or edited
    /// relationship/connection targets. `scratch` is the merged change list;
    /// `layer_changes` is the per-layer split retained for
    /// [`layer_changes`](CommittedChange::layer_changes).
    ///
    /// This covers only what the classification phase knows, and the sets it
    /// builds are not yet normalized against each other. The layer-stack tier's
    /// paths land, and the normalization runs, in [`finish`](Self::finish),
    /// which every payload must pass through before it is reported.
    pub(super) fn new(
        changes: &pcp::Changes,
        scratch: &sdf::ChangeList,
        layer_changes: Vec<(String, sdf::ChangeList)>,
        provenance: &Provenance,
    ) -> Self {
        let mapping = provenance.mapping();
        // `resynced_paths` mixes composed dependency paths (already stage
        // namespace) with the literal authored path, which under an arc or
        // variant edit target is in the edited layer's namespace (e.g.
        // `/Prim{set=sel}child`). Map each through the edit target's mapping so
        // the literal path is carried to its composed form. A path already in
        // stage namespace matches no source pair, so it is kept unchanged —
        // mapped to itself by the variant target's root identity, or returned as
        // `None` (and kept) by a restricted arc mapping. A local/root edit has no
        // mapping and keeps every path.
        let mut resynced: Vec<sdf::Path> = changes
            .cache
            .resynced_paths()
            .map(|p| match mapping {
                Some(m) => m.map_source_to_target(p).unwrap_or_else(|| p.clone()),
                None => p.clone(),
            })
            .collect();
        resynced.sort();
        resynced.dedup();
        let mut subtree_resynced: Vec<sdf::Path> = changes
            .cache
            .subtree_resynced_paths()
            .map(|p| match mapping {
                Some(m) => m.map_source_to_target(p).unwrap_or_else(|| p.clone()),
                None => p.clone(),
            })
            .collect();
        subtree_resynced.sort();
        // The `ChangeList` records paths in the edited layer's namespace.
        // Translate each back to stage namespace through the mapping (its
        // source-to-target direction) so the sink sees composed paths; for a
        // local/root edit the mapping is identity (`None`) and paths pass
        // through. A path outside the mapping's domain (one the arc target cannot
        // reach, so it could not have been authored through it) is dropped. The
        // sort/dedup also collapses distinct layer paths the mapping merges onto
        // one stage path. Subsumption against `resynced` is left to
        // [`finish`](Self::finish), which owns the rule once the layer-stack
        // tier's paths have landed.
        let mut changed_info_only: Vec<sdf::Path> = scratch
            .entries()
            .iter()
            .filter(|(_, e)| {
                // A property removal is a structural change, not an info-only edit.
                // A removed relationship/connection surfaces its torn-down
                // `targetPaths` / `connectionPaths` for memo invalidation; that
                // signal must not also report the now-gone property as if its value
                // merely changed. A replacement (removed and re-created in one edit)
                // keeps the property, so it stays an info change.
                let removed = e.flags.contains(sdf::ChangeFlags::REMOVE_PROPERTY)
                    && !e.flags.contains(sdf::ChangeFlags::ADD_PROPERTY);
                !removed
                    && (!e.info_changed.is_empty()
                        || e.flags.intersects(
                            sdf::ChangeFlags::CHANGE_RELATIONSHIP_TARGETS
                                | sdf::ChangeFlags::CHANGE_ATTRIBUTE_CONNECTION,
                        ))
            })
            .filter_map(|(p, _)| match mapping {
                Some(m) => m.map_source_to_target(p),
                None => Some(p.clone()),
            })
            .collect();
        changed_info_only.sort();
        changed_info_only.dedup();
        Self {
            resynced,
            changed_info_only,
            asset_paths_resynced: Vec::new(),
            subtree_resynced,
            change_list: scratch.clone(),
            layer_changes,
        }
    }

    /// Folds the layer-stack tier's [`pcp::ApplyOutcome`] in and normalizes the
    /// notice — the finalizer every payload passes through before it is
    /// reported. The outcome arrives here rather than at construction because
    /// only the apply phase knows it: a vars edit whose rebuild changed no
    /// composed set publishes nothing at all (see [`pcp::Changes::apply`]).
    ///
    /// A subtree resync subsumes every other reported path below it, so the sets
    /// are normalized the way C++ `UsdStage::_ProcessPendingChanges` normalizes
    /// `recomposeChanges` against `otherInfoChanges` and
    /// `assetPathResyncChanges`. Only [`subtree_resynced`](Self::subtree_resynced)
    /// entries may cover, which is why that projection is carried; an exact
    /// match on any resync still suppresses a redundant info entry.
    ///
    /// Comparing paths by prefix only means something within one namespace, and
    /// a [`Provenance::DirectLayerEdit`] payload reports two: the edited layer's
    /// own paths and the dependency-derived stage paths that reach the stage. So
    /// every cross-set pruning is gated on the payload being single-namespace,
    /// except the one the outcome's own paths drive — those are stage paths
    /// whatever the provenance.
    ///
    /// TODO: a direct edit could prune like any other payload if
    /// [`pcp::CacheChanges`] carried each resync's namespace origin, rather than
    /// merging the dependency-derived victims and the literal authored path into
    /// one set. Both are load-bearing for the cache drop, so splitting them is a
    /// `pcp`-tier change.
    pub(super) fn finish(&mut self, outcome: pcp::ApplyOutcome, provenance: &Provenance) {
        let pcp::ApplyOutcome {
            resynced: mut stage_resynced,
            mut asset_paths_resynced,
        } = outcome;
        let single_namespace = !matches!(provenance, Provenance::DirectLayerEdit);

        // The outcome's victims are subtree drops in stage namespace, so they
        // join both the reported set and the covering projection. Kept separately
        // too: they are the only entries a direct edit can safely prune against.
        stage_resynced.sort();
        stage_resynced.dedup();
        self.resynced.extend(stage_resynced.iter().cloned());
        self.resynced.sort();
        self.resynced.dedup();
        self.subtree_resynced.extend(stage_resynced.iter().cloned());
        self.subtree_resynced.sort();
        keep_ancestors(&mut self.subtree_resynced);

        if single_namespace {
            self.resynced.retain(|p| !is_covered_below(&self.subtree_resynced, p));
            self.changed_info_only
                .retain(|p| !is_covered(&self.subtree_resynced, p) && self.resynced.binary_search(p).is_err());
        }

        asset_paths_resynced.sort();
        keep_ancestors(&mut asset_paths_resynced);
        // Prune against whichever subtree resyncs share this set's stage
        // namespace: all of them when the payload is single-namespace, else only
        // the outcome's own.
        let covering = if single_namespace {
            &self.subtree_resynced
        } else {
            keep_ancestors(&mut stage_resynced);
            &stage_resynced
        };
        asset_paths_resynced.retain(|p| !is_covered(covering, p));
        self.asset_paths_resynced = asset_paths_resynced;
    }

    /// Borrow this payload as a [`CommittedChange`] for the `after_commit` call.
    pub(super) fn committed_change<'a>(
        &'a self,
        layer_identifier: &'a str,
        provenance: &'a Provenance,
        generation: u64,
    ) -> CommittedChange<'a> {
        CommittedChange {
            resynced: &self.resynced,
            changed_info_only: &self.changed_info_only,
            asset_paths_resynced: &self.asset_paths_resynced,
            layer_identifier,
            change_list: &self.change_list,
            layer_changes: &self.layer_changes,
            provenance,
            generation,
        }
    }
}

/// Reduces a sorted path set to its ancestors, dropping every entry a shallower
/// entry already stands for (C++ `_RemoveDescendentEntries`). Duplicates fall
/// out with them, since a path covers its own copy.
///
/// A path that prefixes another sorts before it, so one forward pass testing
/// each candidate against what has been kept so far settles the whole set. The
/// scan cannot stop at the last kept entry: lexicographic order is not
/// subtree-contiguous, because a sibling name can sort between an ancestor and
/// a variant-selection descendant (`/A`, `/A0`, `/A{v=s}B`).
///
/// TODO(perf): the kept set is normally a handful of paths, but a stack-wide
/// asset-path set is siblings all the way down, making this quadratic. An
/// [`sdf::PathTable`] covering set would answer each test in O(depth); the same
/// structure would bound [`is_covered`]'s scans.
fn keep_ancestors(paths: &mut Vec<sdf::Path>) {
    let mut kept = 0;
    for i in 0..paths.len() {
        if !is_covered(&paths[..kept], &paths[i]) {
            paths.swap(kept, i);
            kept += 1;
        }
    }
    paths.truncate(kept);
}

/// Whether `path` lies at or beneath one of `covering`'s entries, which report
/// their whole subtree. Both must be in the same namespace for the answer to
/// mean anything.
fn is_covered(covering: &[sdf::Path], path: &sdf::Path) -> bool {
    covering.iter().any(|prefix| path.has_prefix(prefix))
}

/// Whether `path` lies strictly *beneath* one of `covering`'s entries — the form
/// for reducing a set that contains its own covering entries, where an entry
/// must not retire itself.
fn is_covered_below(covering: &[sdf::Path], path: &sdf::Path) -> bool {
    covering.iter().any(|prefix| prefix != path && path.has_prefix(prefix))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(s: &str) -> sdf::Path {
        sdf::Path::new(s).expect("valid path")
    }

    fn paths(paths: &[&str]) -> Vec<sdf::Path> {
        paths.iter().map(|s| p(s)).collect()
    }

    /// Builds a payload whose classification-derived resyncs are `resynced` and
    /// whose info changes are `info`, then folds `outcome` in.
    fn shaped(provenance: Provenance, resynced: &[&str], info: &[&str], outcome: pcp::ApplyOutcome) -> Payload {
        let mut changes = pcp::Changes::new();
        for path in resynced {
            changes.cache.did_change_significantly.insert(p(path));
        }
        let mut scratch = sdf::ChangeList::new();
        for path in info {
            scratch.entry_mut(&p(path)).info_changed.insert(tf::Token::new("kind"));
        }
        let mut payload = Payload::new(&changes, &scratch, Vec::new(), &provenance);
        payload.finish(outcome, &provenance);
        payload
    }

    /// A resync stands for its whole subtree, so the reported sets are reduced
    /// to their ancestors and every path a resync covers — prim or property —
    /// drops off the other channels.
    #[test]
    fn resync_subsumes_subtree() {
        let payload = shaped(
            Provenance::LocalStack,
            &["/A", "/A/B"],
            &["/A/B", "/A.x", "/B.y"],
            pcp::ApplyOutcome::default(),
        );
        assert_eq!(payload.resynced, paths(&["/A"]));
        assert_eq!(payload.changed_info_only, paths(&["/B.y"]));
    }

    /// The asset-path channel is minimized the same way and then yields to the
    /// resyncs, which already imply re-reading everything beneath them.
    #[test]
    fn asset_paths_yield_resync() {
        let outcome = pcp::ApplyOutcome {
            resynced: Vec::new(),
            asset_paths_resynced: paths(&["/A/B", "/B", "/B/C"]),
        };
        let payload = shaped(Provenance::LocalStack, &["/A"], &[], outcome);
        assert_eq!(payload.asset_paths_resynced, paths(&["/B"]));

        let outcome = pcp::ApplyOutcome {
            resynced: paths(&["/"]),
            asset_paths_resynced: paths(&["/A", "/B"]),
        };
        let payload = shaped(Provenance::LocalStack, &[], &[], outcome);
        assert!(payload.asset_paths_resynced.is_empty());
    }

    /// A direct edit to a non-local layer reports that layer's own namespace
    /// alongside dependency-derived stage paths, so an identical spelling is a
    /// different object. Nothing prunes the layer-namespace info changes — not
    /// the mixed-origin classification resyncs, not the outcome's stage
    /// resyncs, not even on an exact match. The asset-path channel is stage
    /// namespace like the outcome's resyncs, so those two still prune.
    #[test]
    fn direct_edit_keeps_namespaces() {
        let outcome = pcp::ApplyOutcome {
            resynced: paths(&["/A"]),
            asset_paths_resynced: paths(&["/A/B", "/C"]),
        };
        let payload = shaped(Provenance::DirectLayerEdit, &["/A"], &["/A", "/A/B", "/A.x"], outcome);
        assert_eq!(payload.changed_info_only, paths(&["/A", "/A.x", "/A/B"]));
        assert_eq!(payload.asset_paths_resynced, paths(&["/C"]));
    }
}
