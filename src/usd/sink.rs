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
use std::mem;

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

    /// Observe a layer mute/unmute (C++ `UsdNotice::LayerMutingChanged`, which
    /// C++ pairs with the `ObjectsChanged` its recompose sends).
    ///
    /// `resynced` is what the toggle invalidated: the cached indices dropped and
    /// the prototype roots retired with them, minimal in ancestors. Unlike
    /// [`load_rules_changed`](Self::load_rules_changed) it may be empty, since
    /// muting an identifier that resolves to nothing loaded still toggles the
    /// muted set, and the toggle is reported either way.
    fn layer_muting_changed(&self, stage: &Stage, layer: &str, muted: bool, resynced: &[sdf::Path]) {
        let _ = (stage, layer, muted, resynced);
    }

    /// Observe a payload load/unload change (C++ `UsdNotice::ObjectsChanged`
    /// fired by `Load`/`Unload`/`LoadAndUnload`/`SetLoadRules`, treating every
    /// reported path as a full resync).
    ///
    /// `resynced` is the bounded set of paths
    /// [`Stage::load`]/[`Stage::unload`]/[`Stage::load_and_unload`]/
    /// [`Stage::set_load_rules`] used to invalidate the cache, together with the
    /// prototype roots retired with them, minimal in ancestors — never empty,
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
    /// resynced `/foo` appears without `/foo/bar`. A
    /// [`Provenance::DirectLayerEdit`] reports two namespaces at once (see
    /// [`provenance`](Self::provenance)), each minimal on its own; only across
    /// the two can one entry lie under another, comparing them by prefix being
    /// meaningless.
    pub resynced: &'a [sdf::Path],
    /// Paths that changed only in field or target info, without restructuring
    /// composition (C++ `ChangedInfoOnlyPaths`). Composed/stage namespace.
    ///
    /// Disjoint from [`resynced`](Self::resynced), which already implies
    /// re-reading everything beneath it. Under a
    /// [`Provenance::DirectLayerEdit`] that holds against the resyncs sharing
    /// this set's namespace; an entry may still coincide with one of the stage
    /// paths reported alongside them, which names a different object.
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
    /// The resyncs in composed stage namespace, and the reported set once
    /// [`finish`](Self::finish) has merged [`authored`](Self::authored) in.
    stage: NamespacedPaths,
    /// The resyncs named in the edited layer's own namespace, which only a
    /// [`Provenance::DirectLayerEdit`] has: a local layer's paths are stage
    /// paths already and an edit target maps its own. Emptied by
    /// [`finish`](Self::finish) into [`stage`](Self::stage).
    authored: NamespacedPaths,
    changed_info_only: Vec<sdf::Path>,
    /// Whether [`changed_info_only`](Self::changed_info_only) is named in the
    /// authored namespace, and so yields to [`authored`](Self::authored) rather
    /// than [`stage`](Self::stage). Recorded where the translation happens, so
    /// the two cannot disagree.
    info_is_authored: bool,
    asset_paths_resynced: Vec<sdf::Path>,
    change_list: sdf::ChangeList,
    layer_changes: Vec<(String, sdf::ChangeList)>,
}

/// A resync set and the covering projection over it, both named in one
/// namespace — the only pairing a prefix comparison means anything across.
#[derive(Default)]
struct NamespacedPaths {
    /// The prim paths whose composition was resynced.
    resynced: Vec<sdf::Path>,
    /// The subset of [`resynced`](Self::resynced) whose entries stand for their
    /// whole subtree, and so are the only sound covering prefixes.
    ///
    /// `resynced` mixes invalidation tiers, and only the significant tier and
    /// the layer-stack victims drop a subtree — the prim tier drops one index,
    /// and the spec tier refreshes a site in place. Pruning by prefix against
    /// the whole set would let an inert `over` at `/A` delete the report of an
    /// attribute authored at `/A/B.x`. Not reported — it is a projection of
    /// `resynced`.
    subtree: Vec<sdf::Path>,
}

impl NamespacedPaths {
    /// Orders both sets, reduces the covering projection to its ancestors, and
    /// drops every resync a shallower one already stands for.
    fn normalize(&mut self) {
        self.resynced.sort();
        self.resynced.dedup();
        keep_ancestors(&mut self.subtree);
        self.resynced.retain(|p| !is_covered_below(&self.subtree, p));
    }

    /// Whether these resyncs already report `path` — covering its subtree, or
    /// naming it exactly. Reads the ordering [`normalize`](Self::normalize)
    /// establishes, so it answers only after that has run.
    fn reports(&self, path: &sdf::Path) -> bool {
        is_covered(&self.subtree, path) || self.resynced.binary_search(path).is_ok()
    }

    /// Folds `other`'s resyncs in, restoring the ordering
    /// [`reports`](Self::reports) reads. The covering projections stay apart:
    /// they are only meaningful against paths in their own namespace, and this
    /// runs once every such comparison is done.
    fn absorb(&mut self, other: &mut Self) {
        if other.resynced.is_empty() {
            return;
        }
        self.resynced.append(&mut other.resynced);
        self.resynced.sort();
        self.resynced.dedup();
    }
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
        // Each provenance carries an authored path to composed stage namespace its
        // own way. An edit target maps it through the arc it authors into; a path
        // outside that mapping's domain — one the arc target cannot reach, so it
        // could not have been authored through it — names no composed object and
        // drops out of the report, though it still drives invalidation, which
        // reads `CacheChanges` directly. A local layer shares the stage's
        // namespace except for the variant selections a spec path carries
        // (`/Prim{set=sel}child` composes into `/Prim/child`), which is the whole
        // of its translation. A direct edit to a non-local layer reports that
        // layer's own paths, variant spellings included. Every one of these can
        // merge distinct layer paths onto one stage path, which the later dedup
        // collapses.
        let to_stage = |path: &sdf::Path| match provenance {
            Provenance::EditTarget(m) => m.map_source_to_target(path),
            Provenance::LocalStack => Some(path.strip_all_variant_selections()),
            Provenance::DirectLayerEdit => Some(path.clone()),
        };
        // The cache's stage half needs no translation: it is what a dependency
        // lookup answered, already in the composed namespace.
        let mut stage = NamespacedPaths {
            resynced: changes.cache.stage_resynced_paths().cloned().collect(),
            subtree: changes.cache.stage_subtree_paths().cloned().collect(),
        };
        let mut authored = NamespacedPaths {
            resynced: changes.cache.authored_resynced_paths().filter_map(&to_stage).collect(),
            subtree: changes.cache.authored_subtree_paths().filter_map(&to_stage).collect(),
        };
        // A direct edit to a non-local layer is the one payload carrying two
        // namespaces: nothing maps its authored paths, and the stage reports them
        // in the edited layer's own namespace. Under any other provenance they
        // are stage paths by now — a local layer shares the stage's namespace,
        // and an edit target has mapped into it — so they join the stage half.
        let info_is_authored = matches!(provenance, Provenance::DirectLayerEdit);
        if !info_is_authored {
            stage.resynced.append(&mut authored.resynced);
            stage.subtree.append(&mut authored.subtree);
        }
        // The `ChangeList` records paths in the edited layer's namespace, so it
        // reaches stage namespace through the same rule, leaving it in whichever
        // namespace the authored resyncs ended in. Subsumption against them is
        // left to [`finish`](Self::finish), which owns the rule once the
        // layer-stack tier's paths have landed.
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
            .filter_map(|(p, _)| to_stage(p))
            .collect();
        changed_info_only.sort();
        changed_info_only.dedup();
        Self {
            stage,
            authored,
            changed_info_only,
            info_is_authored,
            asset_paths_resynced: Vec::new(),
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
    /// `assetPathResyncChanges`.
    ///
    /// Each namespace normalizes on its own, since a prefix comparison across
    /// two means nothing: [`changed_info_only`](Self::changed_info_only) yields
    /// to the half [`new`](Self::new) translated it alongside, recorded there as
    /// [`info_is_authored`](Self::info_is_authored), while the outcome's victims
    /// and [`asset_paths_resynced`](Self::asset_paths_resynced) are stage paths
    /// whatever the provenance. The halves merge only once every comparison is
    /// done.
    pub(super) fn finish(&mut self, outcome: pcp::ApplyOutcome) {
        let pcp::ApplyOutcome {
            resynced: mut stage_resynced,
            mut asset_paths_resynced,
        } = outcome;

        // The outcome's victims are subtree drops in stage namespace, so they
        // join both the reported set and the covering projection.
        self.stage.resynced.extend(stage_resynced.iter().cloned());
        self.stage.subtree.append(&mut stage_resynced);
        self.stage.normalize();
        self.authored.normalize();

        let reported = if self.info_is_authored {
            &self.authored
        } else {
            &self.stage
        };
        self.changed_info_only.retain(|p| !reported.reports(p));

        keep_ancestors(&mut asset_paths_resynced);
        asset_paths_resynced.retain(|p| !is_covered(&self.stage.subtree, p));
        self.asset_paths_resynced = asset_paths_resynced;

        // Every comparison is done, so the two namespaces can share one reported
        // set — the provenance says which namespace a direct edit's entries are
        // in, and nothing distinguishes them from here on. The authored bundle is
        // spent with it, covering projection included.
        let mut authored = mem::take(&mut self.authored);
        self.stage.absorb(&mut authored);
    }

    /// Borrow this payload as a [`CommittedChange`] for the `after_commit` call.
    pub(super) fn committed_change<'a>(
        &'a self,
        layer_identifier: &'a str,
        provenance: &'a Provenance,
        generation: u64,
    ) -> CommittedChange<'a> {
        CommittedChange {
            resynced: &self.stage.resynced,
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

/// Orders a path set and reduces it to its ancestors, dropping every entry a
/// shallower entry already stands for (C++ `_RemoveDescendentEntries`).
/// Duplicates fall out with them, since a path covers its own copy. The kept
/// entries hold their relative order, so the result is sorted.
///
/// A path that prefixes another sorts before it, so one forward pass over the
/// ordered set, testing each candidate against what has been kept so far,
/// settles the whole thing. The scan cannot stop at the last kept entry:
/// lexicographic order is not subtree-contiguous, because a sibling name can
/// sort between an ancestor and a variant-selection descendant (`/A`, `/A0`,
/// `/A{v=s}B`).
///
/// TODO(perf): the kept set is normally a handful of paths, but a stack-wide
/// asset-path set is siblings all the way down, making this quadratic. An
/// [`sdf::PathTable`] covering set would answer each test in O(depth); the same
/// structure would bound [`is_covered`]'s scans.
pub(super) fn keep_ancestors(paths: &mut Vec<sdf::Path>) {
    paths.sort();
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

    /// Builds a payload whose classification-derived resyncs are `stage` (paths a
    /// dependency lookup produced) and `authored` (literal edited paths), and
    /// whose info changes are `info`, then folds `outcome` in.
    fn shaped(
        provenance: Provenance,
        stage: &[&str],
        authored: &[&str],
        info: &[&str],
        outcome: pcp::ApplyOutcome,
    ) -> Payload {
        let mut changes = pcp::Changes::new();
        for path in stage {
            changes.cache.did_change_significantly.insert(p(path));
        }
        for path in authored {
            changes.cache.authored_significant.insert(p(path));
        }
        let mut scratch = sdf::ChangeList::new();
        for path in info {
            scratch.entry_mut(&p(path)).info_changed.insert(tf::Token::new("kind"));
        }
        let mut payload = Payload::new(&changes, &scratch, Vec::new(), &provenance);
        payload.finish(outcome);
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
            &[],
            &["/A/B", "/A.x", "/B.y"],
            pcp::ApplyOutcome::default(),
        );
        assert_eq!(payload.stage.resynced, paths(&["/A"]));
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
        let payload = shaped(Provenance::LocalStack, &["/A"], &[], &[], outcome);
        assert_eq!(payload.asset_paths_resynced, paths(&["/B"]));

        let outcome = pcp::ApplyOutcome {
            resynced: paths(&["/"]),
            asset_paths_resynced: paths(&["/A", "/B"]),
        };
        let payload = shaped(Provenance::LocalStack, &[], &[], &[], outcome);
        assert!(payload.asset_paths_resynced.is_empty());
    }

    /// A direct edit to a non-local layer reports two namespaces at once, so an
    /// identical spelling can be a different object. Each set is pruned only
    /// against the covering resyncs sharing its namespace: the layer-namespace
    /// info changes yield to the authored resyncs and to nothing else, while the
    /// asset-path channel is stage namespace and yields to the stage ones.
    #[test]
    fn direct_edit_keeps_namespaces() {
        let outcome = pcp::ApplyOutcome {
            resynced: paths(&["/A"]),
            asset_paths_resynced: paths(&["/A/B", "/C"]),
        };
        let payload = shaped(
            Provenance::DirectLayerEdit,
            &["/A"],
            &["/S"],
            &["/A", "/A.x", "/S/T", "/D.y"],
            outcome,
        );
        assert_eq!(
            payload.changed_info_only,
            paths(&["/A", "/A.x", "/D.y"]),
            "only the authored resync covers a layer-namespace path"
        );
        assert_eq!(payload.asset_paths_resynced, paths(&["/C"]));
        assert_eq!(
            payload.stage.resynced,
            paths(&["/A", "/S"]),
            "both namespaces are reported"
        );
    }

    /// An edit target carries its authored paths to stage namespace, leaving the
    /// payload single-namespace. One outside the arc's domain names no composed
    /// object, so it is dropped from the report rather than reported as if it
    /// were a stage path — it still drove the cache drop.
    #[test]
    fn edit_target_maps_authored() {
        let mapping = pcp::MapFunction::new(vec![(p("/Ref"), p("/Model"))]);
        let payload = shaped(
            Provenance::EditTarget(mapping),
            &["/Other"],
            &["/Ref/Child", "/Elsewhere"],
            &[],
            pcp::ApplyOutcome::default(),
        );
        assert_eq!(payload.stage.resynced, paths(&["/Model/Child", "/Other"]));
    }
}
