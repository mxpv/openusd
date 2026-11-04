//! Stage-tier change sinks: observers of a [`Stage`]'s composed-scene changes.
//!
//! A [`StageSink`] is the high tier of the two-level change pipeline. The low
//! tier is [`sdf::LayerSink`], fired at each layer's commit seam. The stage
//! subscribes to every layer it holds and records each committed edit as it
//! lands, so it can recompose and, once composition is invalidated, deliver a
//! composed [`CommittedChange`] to every `StageSink`.
//! Higher-level features (change notification, undo/redo, replay, validation)
//! are built as sinks; `Stage` installs none by default, so the no-sink path
//! costs nothing extra.
//!
//! Install with [`Stage::add_sink`](super::Stage::add_sink), which returns a
//! [`StageSinkId`] to later [`Stage::remove_sink`](super::Stage::remove_sink).
//! Both fail with `Busy`, changing nothing, where what is pending cannot be
//! delivered first: inside a read or an edit of the stage's layers. A plain
//! `Fn(&Stage, &CommittedChange)` closure is itself a `StageSink`, so
//! `add_sink` takes either a full sink type or a quick closure observer.

use std::collections::HashSet;
use std::mem;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

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
///
/// Notices arrive in commit order: each transaction's
/// [`after_commit`](Self::after_commit), then what settling its snapshot
/// found ([`recomposed`](Self::recomposed)). A mutation's own notice (load
/// rules, muting, retried loads) comes ahead of the edits its settling
/// reconciled. Nothing is delivered while a read, an edit of a layer or a
/// mutation runs: what reads find waits for the next drained edit, the
/// next mutation (ahead of its own notice) or [`Stage::flush`], and an edit
/// a sink makes is heard after the notices being delivered.
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
    /// The two are bridged by the stage's subscription to each layer it holds:
    /// each layer commit records its edit, and the recorded edits are processed
    /// together in one recompose. So an authoring operation that touches
    /// several layers at once — a batched namespace edit spanning the local
    /// layer stack — fires this once with the union of every layer's effect on
    /// the composed scene, not once per layer. (The single
    /// [`change`](CommittedChange) reports the merged record under the
    /// strongest edited layer; see [`CommittedChange::change_list`].)
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
    /// [`generation`](PendingChange::generation). A transaction that a panic
    /// stops after this, in this sink or a later one, fires no `after_commit`;
    /// the sink hears of it through [`aborted`](Self::aborted) instead.
    ///
    /// The layer graph is mid-edit for the duration, so a `before_commit` sink
    /// must derive only from the values `change` carries — it must not re-enter
    /// authoring or read composed state on `stage`. Unlike
    /// [`sdf::LayerSink::before_commit`] this cannot veto: it observes.
    fn before_commit(&self, stage: &Stage, change: &PendingChange<'_>) {
        let _ = (stage, change);
    }

    /// Observe that the transaction `generation`, whose
    /// [`before_commit`](Self::before_commit) this sink may have seen, did not
    /// land. It arrives in transaction order with the
    /// [`after_commit`](Self::after_commit) notices, and lets a sink drop what
    /// it captured for the transaction.
    fn aborted(&self, stage: &Stage, generation: u64) {
        let _ = (stage, generation);
    }

    /// Observe an edit-target change (C++ `UsdNotice::StageEditTargetChanged`).
    fn edit_target_changed(&self, stage: &Stage) {
        let _ = stage;
    }

    /// Observe a layer mute/unmute (C++ `UsdNotice::LayerMutingChanged`, which
    /// C++ pairs with the `ObjectsChanged` its recompose sends).
    ///
    /// `resynced` names what the toggle invalidated, as subtrees: the cached
    /// indices dropped, the prototype roots retired with them and their
    /// instances, what the
    /// loads settling them ran dropped, and the anchors whose value clips
    /// read a layer those loads joined. Unlike
    /// [`load_rules_changed`](Self::load_rules_changed) it may be empty, since
    /// muting an identifier that resolves to nothing loaded still toggles the
    /// muted set, and the toggle is reported either way.
    fn layer_muting_changed(&self, stage: &Stage, layer: &str, muted: bool, resynced: Resynced<'_>) {
        let _ = (stage, layer, muted, resynced);
    }

    /// Observe a payload load/unload change (C++ `UsdNotice::ObjectsChanged`
    /// fired by `Load`/`Unload`/`LoadAndUnload`/`SetLoadRules`).
    ///
    /// `resynced` names, as subtrees, the paths whose own payload inclusion
    /// [`Stage::load`]/[`Stage::unload`]/[`Stage::load_and_unload`]/
    /// [`Stage::set_load_rules`] changed, with an ancestor whose own payload
    /// it includes or leaves out, the prototype roots retired with them and
    /// their instances;
    /// and, as prims, the ancestors whose loaded state flipped with no
    /// payload to recompose. Loading `/world/element_0` on a stage that loads
    /// nothing names `/world/element_0` as a subtree and, when `/world` has
    /// no payload of its own, `/world` as a prim, leaving `/world/element_1`
    /// out. What the
    /// loads settling the change ran dropped joins the subtrees, with the
    /// anchors whose value clips read a layer they joined.
    /// Never empty, since a no-op edit fires no notification at all.
    fn load_rules_changed(&self, stage: &Stage, resynced: Resynced<'_>) {
        let _ = (stage, resynced);
    }

    /// Observe the loads the stage tried again: at [`Stage::retry_loads`],
    /// or once a reload reached its layers, through [`Stage::reload`] or a
    /// layer handle (C++ `UsdNotice::ObjectsChanged` fired by `Reload` for an
    /// asset that may now load, treating every reported path as a full
    /// resync).
    ///
    /// `resynced` names, as subtrees, the prims that recompose with a
    /// reference, payload or sublayer that failed to load, with what the
    /// loads settling them ran dropped and the anchors whose value clips
    /// read a layer the retry joined. Never empty, since a retry that
    /// resyncs nothing fires no notification.
    fn loads_retried(&self, stage: &Stage, resynced: Resynced<'_>) {
        let _ = (stage, resynced);
    }

    /// Observe what composition found that no other notice carries: as
    /// subtrees, the prims dropped by the layer loads a read, an authoring
    /// call or a drain's settling ran (a joined layer that relocates, a
    /// failed load recorded), and the anchors whose value clips now read a
    /// layer they found missing before, for the values they source below
    /// them. A [`flush`](Stage::flush) delivers it too.
    /// A drain of edits to the stage's layers reports what its snapshot
    /// found, with what was found outside a drain since the last one, after
    /// the snapshot's transaction notices and less what those resynced: a
    /// read delivers nothing. Never empty.
    fn recomposed(&self, stage: &Stage, resynced: Resynced<'_>) {
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
    /// An edit to layers of the local (root) layer stack: stage authoring
    /// through the root edit target, a [`Stage::batch_edit`](super::Stage::batch_edit)
    /// of local layers, or a direct [`Stage::layer_handle`](super::Stage::layer_handle)
    /// edit to a local layer. The local layer stack shares the stage's
    /// namespace, so paths are already composed (stage) paths.
    LocalStack,
    /// Stage authoring through an edit target that remaps paths — a reference,
    /// payload, or variant arc. The carried mapping translates the authored
    /// (layer-namespace) paths to composed stage namespace. This is keyed on the
    /// mapping, not on locality: a variant edit target authors into a local layer
    /// yet still remaps (`/Prim{set=sel}child` to `/Prim/child`), so it is
    /// `EditTarget` too; an identity-mapped target needs no translation and is
    /// instead [`LocalStack`](Self::LocalStack) or [`DirectLayerEdit`](Self::DirectLayerEdit).
    EditTarget(pcp::MapFunction),
    /// An edit reaching a non-local (referenced or payload) layer through no
    /// edit target: a direct [`Stage::layer_handle`](super::Stage::layer_handle)
    /// edit, or a [`Stage::batch_edit`](super::Stage::batch_edit) or reload
    /// that includes one. No mapping translates it ([`mapping`](Self::mapping)
    /// is `None`): a non-local layer's authored paths stay in that layer's own
    /// namespace, while a local layer's edited with it, and the
    /// dependency-derived [`resynced`](CommittedChange::resynced) paths (the
    /// composed prims that reference the layer), are in stage namespace. The
    /// two coexist in one [`CommittedChange`], reaching the stage through
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
/// layer. The paths a direct edit authors in a non-local (referenced or payload)
/// layer are reported in that layer's own namespace instead;
/// [`provenance`](Self::provenance) says when.
/// [`asset_paths_resynced`](Self::asset_paths_resynced) is stage namespace
/// either way, being derived from composition dependencies rather
/// than from the authored change record.
pub struct CommittedChange<'a> {
    /// Paths a consumer must re-resolve outright (C++ `ResyncedPaths`).
    /// Composed/stage namespace.
    ///
    /// A prim path here composes afresh from that prim down: its index and
    /// namespace descendants were dropped, or a spec of it appeared or
    /// vanished. A
    /// *property* path is one whose spec appeared or vanished: the owning prim
    /// composes exactly as it did, but the property itself is a different object
    /// than it was, so a handle to it must be re-resolved rather than re-read.
    /// The prims the transaction's own layer loads dropped are here too;
    /// what settling the drain's work finds reaches
    /// [`StageSink::recomposed`].
    ///
    /// Minimal in ancestors: an entry stands for its whole subtree, so a
    /// resynced `/foo` appears without `/foo/bar`. A
    /// [`Provenance::DirectLayerEdit`] reports two namespaces at once (see
    /// [`provenance`](Self::provenance)), each minimal on its own; only across
    /// the two can one entry lie under another, comparing them by prefix being
    /// meaningless.
    pub resynced: &'a [sdf::Path],
    /// Prims recomposed in place: each prim's own composition was derived
    /// again (its index rebuilt, its metadata or arcs possibly changed), but
    /// the prims beneath it are not implied. Composed/stage namespace.
    ///
    /// Disjoint from [`resynced`](Self::resynced): a prim a resync covers is
    /// left out, and a prim named in both is reported as a resync. Under a
    /// [`Provenance::DirectLayerEdit`] that holds against the resyncs sharing
    /// this set's namespace.
    pub recomposed: &'a [sdf::Path],
    /// Paths that changed only in field or target info, without restructuring
    /// composition (C++ `ChangedInfoOnlyPaths`). Composed/stage namespace.
    ///
    /// Disjoint from [`resynced`](Self::resynced), which already implies
    /// re-reading everything beneath it, and from
    /// [`recomposed`](Self::recomposed). Under a
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
    /// pre-commit and post-commit events by it.
    pub generation: u64,
    /// Whether this stage made the edit (see [`is_own`](Self::is_own)).
    pub(crate) own: bool,
    /// The undo revert this edit replays, when it is one of a revert's
    /// replays (see [`PendingChange::replay`]).
    pub(crate) replay: Option<ReplayId>,
}

impl CommittedChange<'_> {
    /// Whether this stage made the edit, through its authoring methods or
    /// [`Stage::edit_layer`](super::Stage::edit_layer). An edit made through a
    /// [`sdf::LayerHandle`], or by another stage holding the layer, is not.
    pub fn is_own(&self) -> bool {
        self.own
    }

    /// The field names authored at `path` by this edit (C++ `GetChangedFields`),
    /// empty if `path` was not touched. `path` is in stage namespace, the same
    /// as the paths in [`resynced`](Self::resynced) and
    /// [`changed_info_only`](Self::changed_info_only); under an arc or variant
    /// edit target it is translated back to the layer-namespace key
    /// [`change_list`](Self::change_list) records it under.
    ///
    /// To tell a field that appeared or disappeared from one re-authored in
    /// place, read [`sdf::ChangeEntry::presence_changed`] off
    /// [`layer_changes`](Self::layer_changes). Not off
    /// [`change_list`](Self::change_list): that is the cross-layer merge, where
    /// one layer's presence change stands for the whole entry.
    pub fn changed_fields<'a>(&'a self, path: &sdf::Path) -> impl Iterator<Item = &'a tf::Token> + use<'a> {
        let key = self
            .provenance
            .mapping()
            .map_or_else(|| Some(path.clone()), |m| m.map_target_to_source(path));
        self.change_list
            .entries()
            .iter()
            .find(|(p, _)| Some(p) == key.as_ref())
            .into_iter()
            .flat_map(|(_, entry)| entry.info_changed())
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
    /// commit.
    pub generation: u64,
    /// Whether this stage is making the edit (see [`is_own`](Self::is_own)).
    pub(crate) own: bool,
    /// The undo revert this edit replays, when it is one of a revert's
    /// replays: the revert's own undo stage skips it, and every other
    /// observer sees an own edit like any other.
    pub(crate) replay: Option<ReplayId>,
}

impl PendingChange<'_> {
    /// Whether this stage is making the edit, through its authoring methods
    /// or [`Stage::edit_layer`](super::Stage::edit_layer). An edit made
    /// through a [`sdf::LayerHandle`], or by another stage holding the layer,
    /// is not.
    pub fn is_own(&self) -> bool {
        self.own
    }
}

/// The identity of one undo revert, which every transaction it replays
/// carries, so the undo stage running it tells its own replays from the
/// other edits of the stage, a sink's made while it replays among them.
/// Unique process-wide.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReplayId(u64);

impl ReplayId {
    /// A fresh identity.
    pub(crate) fn next() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Self(NEXT.fetch_add(1, Ordering::Relaxed))
    }
}

/// A crate-internal observer of a stage's transaction outcomes, told as each
/// transaction is reconciled, before its notices are delivered. It is current
/// even while a delivery is pending. It runs no user code. It reads
/// the stage's layers as they stand when the transaction reconciles (through
/// `Stage::current_view`): a stage edit reconciles as its authoring call
/// ends, before the next edit, while edits made through a layer handle and
/// drained together are read as the last of them left the layers.
pub(crate) trait TxnObserver {
    /// One layer of a transaction is about to commit, with the pre-edit data
    /// still readable: `change` is the staged edit to the layer `layer`. Runs
    /// with the layer's registry borrowed, ahead of the stage's sinks.
    fn capture(&self, stage: &Stage, change: &PendingChange<'_>, layer: pcp::LayerId) {
        let _ = (stage, change, layer);
    }

    /// The transaction `change` reports landed, which touched each layer in
    /// `footprints` with its footprint.
    fn committed(&self, stage: &Stage, change: &CommittedChange<'_>, footprints: &[(pcp::LayerId, Rc<sdf::Footprint>)]);

    /// The transaction `generation` began committing and did not land.
    fn aborted(&self, generation: u64) {
        let _ = generation;
    }

    /// The layers in `layers` are about to leave the stage's graph, so an
    /// edit to one no longer reaches the stage, or were reloaded from their
    /// assets: what the observer recorded of them is stale. Runs between two
    /// borrows of the stage's composition and touches only the observer's
    /// own state.
    fn departed(&self, layers: &HashSet<pcp::LayerId>) {
        let _ = layers;
    }

    /// Adds to `layers` the layers what the observer recorded still names,
    /// which the reclaim an edit ends with keeps (an undo step's layers).
    fn held_layers(&self, layers: &mut HashSet<pcp::LayerId>) {
        let _ = layers;
    }
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

/// The paths a stage notice reports, apart by what an observer re-reads:
/// each of [`subtrees`](Self::subtrees) with everything beneath it, each of
/// [`prims`](Self::prims) alone.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Resynced<'a> {
    /// Subtree resyncs, minimal in ancestors.
    pub subtrees: &'a [sdf::Path],
    /// Prims recomposed in place, none of them at or under a subtree resync.
    pub prims: &'a [sdf::Path],
}

/// The owned paths behind a [`Resynced`], normalized once they are all in.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(super) struct ResyncPaths {
    /// Subtree resyncs ([`Resynced::subtrees`]).
    pub(super) subtrees: Vec<sdf::Path>,
    /// Prims recomposed in place ([`Resynced::prims`]).
    pub(super) prims: Vec<sdf::Path>,
}

impl ResyncPaths {
    /// The subtree resyncs `paths` name, normalized.
    pub(super) fn from_subtrees(mut paths: Vec<sdf::Path>) -> Self {
        let _ = keep_ancestors(&mut paths);
        Self {
            subtrees: paths,
            prims: Vec::new(),
        }
    }

    /// Keeps [`subtrees`](Self::subtrees) minimal in ancestors and drops a
    /// prim a subtree covers.
    pub(super) fn normalize(&mut self) {
        let covering = keep_ancestors(&mut self.subtrees);
        self.prims.sort();
        self.prims.dedup();
        self.prims.retain(|prim| !covering.covers(prim));
    }

    /// Borrows the paths for a sink.
    pub(super) fn view(&self) -> Resynced<'_> {
        Resynced {
            subtrees: &self.subtrees,
            prims: &self.prims,
        }
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
    /// The prims recomposed in place, in composed stage namespace, which
    /// yield to [`stage`](Self::stage)'s resyncs.
    recomposed: Vec<sdf::Path>,
    /// The changed-info paths in composed stage namespace, which yield to
    /// [`stage`](Self::stage)'s resyncs. Emptied into
    /// [`changed_info_only`](Self::changed_info_only) by
    /// [`finish`](Self::finish).
    stage_info: Vec<sdf::Path>,
    /// The changed-info paths named in the edited layer's own namespace, which
    /// only a [`Provenance::DirectLayerEdit`] has, and which yield to
    /// [`authored`](Self::authored)'s resyncs rather than
    /// [`stage`](Self::stage)'s — a prefix comparison across namespaces means
    /// nothing.
    authored_info: Vec<sdf::Path>,
    /// The two halves above, merged once every comparison that needed them
    /// apart is done.
    changed_info_only: Vec<sdf::Path>,
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
    /// the layer-stack victims drop a subtree; the spec tier refreshes a site
    /// in place. Pruning by prefix against
    /// the whole set would let an inert `over` at `/A` delete the report of an
    /// attribute authored at `/A/B.x`. Not reported — it is a projection of
    /// `resynced`.
    subtree: Vec<sdf::Path>,
    /// [`subtree`](Self::subtree) as an [`sdf::Covering`], which
    /// [`normalize`](Self::normalize) builds; empty until it runs.
    covering: sdf::Covering,
}

impl NamespacedPaths {
    /// Orders both sets, reduces the covering projection to its ancestors, and
    /// drops every resync a shallower one already stands for.
    fn normalize(&mut self) {
        self.resynced.sort();
        self.resynced.dedup();
        self.covering = keep_ancestors(&mut self.subtree);
        self.resynced.retain(|p| !self.covering.covers_below(p));
    }

    /// Whether these resyncs already report `path` — covering its subtree, or
    /// naming it exactly. Reads the ordering [`normalize`](Self::normalize)
    /// establishes, so it answers only after that has run.
    fn reports(&self, path: &sdf::Path) -> bool {
        self.covering.covers(path) || self.resynced.binary_search(path).is_ok()
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
    /// [`resynced`](CommittedChange::resynced) is the union of the significant
    /// and spec-tier composed paths, [`recomposed`](CommittedChange::recomposed)
    /// the prim tier's; [`changed_info_only`](CommittedChange::changed_info_only)
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
        is_local: &dyn Fn(pcp::LayerId) -> bool,
    ) -> Self {
        // An authored path reaches the report by the rule of how it was
        // authored. An edit target maps it through the arc it authors into; a
        // path outside that mapping's domain — one the arc target cannot reach,
        // so it could not have been authored through it — names no composed
        // object and drops out of the report, though it still drives
        // invalidation, which reads `CacheChanges` directly. Otherwise each
        // layer that authored it names it by its own rule. A local layer shares
        // the stage's namespace except for the variant selections a spec path
        // carries (`/Prim{set=sel}child` composes into `/Prim/child`), which is
        // the whole of its translation, and the path joins the stage half. A
        // non-local layer's path stays in that layer's own namespace, variant
        // spellings included, in the authored half. Every translation can merge
        // distinct layer paths onto one stage path, which the later dedup
        // collapses.
        let place = |(path, layers): (&sdf::Path, &[pcp::LayerId]),
                     stage: &mut Vec<sdf::Path>,
                     authored: &mut Vec<sdf::Path>| {
            if let Provenance::EditTarget(m) = provenance {
                stage.extend(m.map_source_to_target(path));
                return;
            }
            // Every layer a local-stack edit names is local, and only a direct
            // edit records the layers that authored each path.
            let (local, other) = match provenance {
                Provenance::LocalStack => (true, false),
                _ => layers.iter().fold((false, false), |(local, other), &layer| {
                    let here = is_local(layer);
                    (local || here, other || !here)
                }),
            };
            if local {
                stage.push(path.strip_variant_selections());
            }
            if other {
                authored.push(path.clone());
            }
        };
        // The cache's stage half needs no translation: it is what a dependency
        // lookup answered, already in the composed namespace.
        let mut stage = NamespacedPaths {
            resynced: changes.cache.stage_resynced_paths().cloned().collect(),
            subtree: changes.cache.stage_subtree_paths().cloned().collect(),
            ..NamespacedPaths::default()
        };
        let mut authored = NamespacedPaths::default();
        for path in changes.cache.authored_resynced_paths() {
            place(path, &mut stage.resynced, &mut authored.resynced);
        }
        for path in changes.cache.authored_subtree_paths() {
            place(path, &mut stage.subtree, &mut authored.subtree);
        }
        // The `ChangeList` records paths in the edited layers' namespaces, so
        // they reach the report through the same rule. Translation can collapse
        // two spellings onto one stage path, which is the only thing here that
        // needs re-ordering: both sets arrive sorted and unique out of their
        // `BTreeSet`s. Subsumption against the resyncs is left to
        // [`finish`](Self::finish), which owns the rule once the layer-stack
        // tier's paths have landed.
        let mut stage_info: Vec<sdf::Path> = changes.cache.reported.stage_info.iter().cloned().collect();
        let mut authored_info = Vec::new();
        for path in changes.cache.reported.authored_info() {
            place(path, &mut stage_info, &mut authored_info);
        }
        stage_info.sort();
        stage_info.dedup();
        Self {
            stage,
            authored,
            recomposed: changes.cache.stage_recomposed_paths().cloned().collect(),
            stage_info,
            authored_info,
            changed_info_only: Vec::new(),
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
    /// two means nothing: [`stage_info`](Self::stage_info) yields to the stage
    /// resyncs and [`authored_info`](Self::authored_info) to the authored ones,
    /// while the outcome's victims and
    /// [`asset_paths_resynced`](Self::asset_paths_resynced) are stage paths
    /// whatever the provenance. The halves merge into
    /// [`changed_info_only`](Self::changed_info_only) only once every comparison
    /// is done.
    ///
    /// `found` is what resolving the sublayers the recompose demanded
    /// discovered: it joins the subtree resyncs.
    pub(super) fn finish(&mut self, outcome: pcp::ApplyOutcome, found: Vec<sdf::Path>) {
        let pcp::ApplyOutcome {
            resynced: mut stage_resynced,
            resynced_prims,
            mut asset_paths_resynced,
            ..
        } = outcome;

        // What the demand resolution found counts as the outcome's own.
        stage_resynced.extend(found);
        // The outcome's victims are subtree drops in stage namespace, so they
        // join both the reported set and the covering projection. Its single-prim
        // resyncs join only the reported set: they cover nothing below them.
        self.stage.resynced.extend(stage_resynced.iter().cloned());
        self.stage.resynced.extend(resynced_prims);
        self.stage.subtree.append(&mut stage_resynced);
        self.stage.normalize();
        self.authored.normalize();
        // A recomposed prim covers only itself, and yields to a resync that
        // reaches it.
        self.recomposed.sort();
        self.recomposed.dedup();
        self.recomposed.retain(|p| !self.stage.reports(p));

        // Each half yields to the resyncs of its own namespace, which is why the
        // two are kept apart until here: a direct edit to a non-local layer
        // carries both, and a prefix test across namespaces means nothing.
        self.stage_info
            .retain(|p| !self.stage.reports(p) && self.recomposed.binary_search(p).is_err());
        self.authored_info.retain(|p| !self.authored.reports(p));

        let _ = keep_ancestors(&mut asset_paths_resynced);
        asset_paths_resynced.retain(|p| !self.stage.covering.covers(p));
        self.asset_paths_resynced = asset_paths_resynced;

        // Every comparison is done, so the two namespaces can share one reported
        // set — the provenance says which namespace a direct edit's entries are
        // in, and nothing distinguishes them from here on. The authored bundles
        // are spent with them, covering projection included.
        let mut authored = mem::take(&mut self.authored);
        self.stage.absorb(&mut authored);
        self.changed_info_only = mem::take(&mut self.stage_info);
        self.changed_info_only.append(&mut self.authored_info);
        self.changed_info_only.sort();
        self.changed_info_only.dedup();
    }

    /// The subtrees the finished payload resyncs in composed stage
    /// namespace, each standing for everything beneath it.
    pub(super) fn covering(&self) -> &[sdf::Path] {
        &self.stage.subtree
    }

    /// Borrow this payload as a [`CommittedChange`] for the `after_commit` call.
    pub(super) fn committed_change<'a>(
        &'a self,
        layer_identifier: &'a str,
        provenance: &'a Provenance,
        generation: u64,
        own: bool,
        replay: Option<ReplayId>,
    ) -> CommittedChange<'a> {
        CommittedChange {
            resynced: &self.stage.resynced,
            recomposed: &self.recomposed,
            changed_info_only: &self.changed_info_only,
            asset_paths_resynced: &self.asset_paths_resynced,
            layer_identifier,
            change_list: &self.change_list,
            layer_changes: &self.layer_changes,
            provenance,
            generation,
            own,
            replay,
        }
    }
}

/// Orders a path set and reduces it to its ancestors, dropping every entry a
/// shallower entry already stands for (C++ `_RemoveDescendentEntries`).
/// Duplicates fall out with them, since a path covers its own copy. The
/// result is sorted, and returned as an [`sdf::Covering`] too.
fn keep_ancestors(paths: &mut Vec<sdf::Path>) -> sdf::Covering {
    // A path sorts before every path it prefixes, so each ancestor is kept
    // before any of its descendants is tested.
    paths.sort();
    let mut kept = sdf::Covering::default();
    paths.retain(|path| {
        let covered = kept.covers(path);
        if !covered {
            kept.insert(path.clone());
        }
        !covered
    });
    kept
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcp::change::Authored;

    fn p(s: &str) -> sdf::Path {
        sdf::Path::new(s).expect("valid path")
    }

    fn paths(paths: &[&str]) -> Vec<sdf::Path> {
        paths.iter().map(|s| p(s)).collect()
    }

    /// Builds a payload whose classification-derived resyncs are `stage` (paths a
    /// dependency lookup produced) and `authored` (literal edited paths), and
    /// whose info changes are `info` — recorded as authored spellings, the half
    /// a provenance decides the namespace of — then folds `outcome` in.
    fn shaped(
        provenance: Provenance,
        stage: &[&str],
        authored: &[&str],
        info: &[&str],
        outcome: pcp::ApplyOutcome,
    ) -> Payload {
        // A direct edit authors in a layer the stage does not hold locally.
        let (local, other) = (pcp::LayerId::from_raw(0), pcp::LayerId::from_raw(1));
        let author = match provenance {
            Provenance::DirectLayerEdit => other,
            _ => local,
        };
        let mut changes = pcp::Changes::reporting();
        for path in stage {
            changes.cache.did_change_significantly.insert(p(path));
        }
        for path in authored {
            changes.cache.authored_significant.insert(p(path));
            authored_in(&mut changes, Authored::Significant, path, author);
        }
        for path in info {
            changes.cache.reported.authored_info.insert(p(path));
            authored_in(&mut changes, Authored::Info, path, author);
        }
        let is_local = |layer| layer == local;
        let mut payload = Payload::new(&changes, &sdf::ChangeList::new(), Vec::new(), &provenance, &is_local);
        payload.finish(outcome, Vec::new());
        payload
    }

    /// Records that `layer` put `path` in the authored `set`.
    fn authored_in(changes: &mut pcp::Changes, set: Authored, path: &str, layer: pcp::LayerId) {
        let authors = changes.cache.reported.authors.entry(p(path)).or_default();
        authors[set as usize].push(layer);
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
            resynced_prims: Vec::new(),
            resynced: Vec::new(),
            asset_paths_resynced: paths(&["/A/B", "/B", "/B/C"]),
            retries_sublayers: false,
        };
        let payload = shaped(Provenance::LocalStack, &["/A"], &[], &[], outcome);
        assert_eq!(payload.asset_paths_resynced, paths(&["/B"]));

        let outcome = pcp::ApplyOutcome {
            resynced_prims: Vec::new(),
            resynced: paths(&["/"]),
            asset_paths_resynced: paths(&["/A", "/B"]),
            retries_sublayers: false,
        };
        let payload = shaped(Provenance::LocalStack, &[], &[], &[], outcome);
        assert!(payload.asset_paths_resynced.is_empty());
    }

    /// A group editing a local and a non-local layer names each path by its
    /// own layer: the local layer's variant spelling reaches stage namespace,
    /// and the other layer's path stays as that layer spells it.
    #[test]
    fn mixed_layers_split() {
        let (local, other) = (pcp::LayerId::from_raw(0), pcp::LayerId::from_raw(1));
        let mut changes = pcp::Changes::reporting();
        for (path, layer) in [("/A{v=x}B", local), ("/S{v=x}T", other)] {
            changes.cache.authored_significant.insert(p(path));
            authored_in(&mut changes, Authored::Significant, path, layer);
        }
        let is_local = |layer| layer == local;
        let payload = Payload::new(
            &changes,
            &sdf::ChangeList::new(),
            Vec::new(),
            &Provenance::DirectLayerEdit,
            &is_local,
        );
        assert_eq!(payload.stage.resynced, paths(&["/A/B"]));
        assert_eq!(payload.authored.resynced, paths(&["/S{v=x}T"]));
    }

    /// A direct edit to a non-local layer reports two namespaces at once, so an
    /// identical spelling can be a different object. Each set is pruned only
    /// against the covering resyncs sharing its namespace: the layer-namespace
    /// info changes yield to the authored resyncs and to nothing else, while the
    /// asset-path channel is stage namespace and yields to the stage ones.
    #[test]
    fn direct_edit_keeps_namespaces() {
        let outcome = pcp::ApplyOutcome {
            resynced_prims: Vec::new(),
            resynced: paths(&["/A"]),
            asset_paths_resynced: paths(&["/A/B", "/C"]),
            retries_sublayers: false,
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
