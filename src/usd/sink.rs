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
    /// resulting change to the composed scene — the resynced and changed-info
    /// prim paths in stage namespace, after PCP has invalidated the affected
    /// indices.
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

    /// Observe an edit-target change (C++ `UsdNotice::StageEditTargetChanged`).
    fn edit_target_changed(&self, stage: &Stage) {
        let _ = stage;
    }

    /// Observe a layer mute/unmute (C++ `UsdNotice::LayerMutingChanged`).
    fn layer_muting_changed(&self, stage: &Stage, layer: &str, muted: bool) {
        let _ = (stage, layer, muted);
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
/// layer. A direct edit to a non-local (referenced or payload) layer through
/// [`Stage::layer_mut`](super::Stage::layer_mut) carries no stage-namespace
/// mapping, so for it those paths are reported in the edited layer's own
/// namespace instead.
pub struct CommittedChange<'a> {
    /// Paths whose composition was resynced — the prim index and its namespace
    /// descendants were dropped (C++ `ResyncedPaths`). Composed/stage namespace.
    pub resynced: &'a [sdf::Path],
    /// Paths that changed only in field or target info, without restructuring
    /// composition (C++ `ChangedInfoOnlyPaths`). Composed/stage namespace.
    pub changed_info_only: &'a [sdf::Path],
    /// Canonical identifier of the layer the edit landed on, and the lookup key
    /// for reading its authored values.
    pub layer_identifier: &'a str,
    /// The recorded change index for the edit, keyed in the edited layer's
    /// namespace (under an arc or variant edit target this differs from the
    /// stage-namespace [`resynced`](Self::resynced) /
    /// [`changed_info_only`](Self::changed_info_only) paths;
    /// [`changed_fields`](Self::changed_fields) bridges the two).
    pub change_list: &'a sdf::ChangeList,
    /// Namespace mapping (layer source to stage target) of the producing edit
    /// target, or `None` for a local/root edit.
    pub mapping: Option<&'a pcp::MapFunction>,
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
        let key = match self.mapping {
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
            .map(|(_, entry)| &entry.info_changed)
            .unwrap_or(&EMPTY)
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
    change_list: sdf::ChangeList,
}

impl Payload {
    /// Classify one edit into the composed path-sets a sink reports.
    ///
    /// `changes` is the edit's invalidation plan and `scratch` its raw change
    /// list, in the edited layer's namespace. `mapping` is the edit target's
    /// namespace mapping (layer source to stage target), or `None` for a
    /// local/root edit that needs no translation.
    ///
    /// [`resynced`](CommittedChange::resynced) is the union of the significant and
    /// prim-tier composed paths; [`changed_info_only`](CommittedChange::changed_info_only)
    /// is every other edited path that authored a field value or edited
    /// relationship/connection targets.
    pub(super) fn new(changes: &pcp::Changes, scratch: &sdf::ChangeList, mapping: Option<&pcp::MapFunction>) -> Self {
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
        // A layer-stack-significant edit (sublayers, layer offsets, relocates, or
        // the effective timeCodesPerSecond) drops every cached index via
        // `clear_all_indices`, which the per-path tiers don't capture. Report it
        // as a stage-wide resync at the pseudo-root, matching C++ `ResyncedPaths`.
        if changes.layer_stack.intersects(pcp::LayerStackChanges::SIGNIFICANT) {
            resynced.push(sdf::Path::abs_root());
        }
        resynced.sort();
        resynced.dedup();
        // The `ChangeList` records paths in the edited layer's namespace.
        // Translate each back to stage namespace through the mapping (its
        // source-to-target direction) so the sink sees composed paths; for a
        // local/root edit the mapping is identity (`None`) and paths pass
        // through. A path outside the mapping's domain (one the arc target cannot
        // reach, so it could not have been authored through it) is dropped. After
        // translation `resynced` and `changed_info_only` share a namespace, so the
        // dedup against `resynced` is meaningful; the sort/dedup also collapses
        // distinct layer paths the mapping merges onto one stage path.
        let mut changed_info_only: Vec<sdf::Path> = scratch
            .entries()
            .iter()
            .filter(|(_, e)| {
                !e.info_changed.is_empty()
                    || e.flags.intersects(
                        sdf::ChangeFlags::CHANGE_RELATIONSHIP_TARGETS | sdf::ChangeFlags::CHANGE_ATTRIBUTE_CONNECTION,
                    )
            })
            .filter_map(|(p, _)| match mapping {
                Some(m) => m.map_source_to_target(p),
                None => Some(p.clone()),
            })
            .filter(|p| resynced.binary_search(p).is_err())
            .collect();
        changed_info_only.sort();
        changed_info_only.dedup();
        Self {
            resynced,
            changed_info_only,
            change_list: scratch.clone(),
        }
    }

    /// Borrow this payload as a [`CommittedChange`] for the `after_commit` call.
    pub(super) fn committed_change<'a>(
        &'a self,
        layer_identifier: &'a str,
        mapping: Option<&'a pcp::MapFunction>,
    ) -> CommittedChange<'a> {
        CommittedChange {
            resynced: &self.resynced,
            changed_info_only: &self.changed_info_only,
            layer_identifier,
            change_list: &self.change_list,
            mapping,
        }
    }
}
