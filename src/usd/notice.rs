//! Stage change notifications, the Rust equivalent of C++ `UsdNotice`.
//!
//! A [`Stage`](super::Stage) with a listener installed through
//! [`Stage::set_listener`](super::Stage::set_listener) delivers a [`Notice`]
//! after every successful edit. [`ObjectsChanged`] reports what the edit
//! touched and feeds [`Stage::extract_diff`](super::Stage::extract_diff), the
//! building block for mirroring a stage's edits onto another stage or machine.

use std::collections::BTreeSet;

use crate::{pcp, sdf, tf};

/// A change notification delivered to a stage listener (C++ `UsdNotice`).
///
/// `#[non_exhaustive]` reserves room for further `UsdNotice` kinds.
#[non_exhaustive]
pub enum Notice<'a> {
    /// Scene objects were added, removed, or changed by an edit.
    ObjectsChanged(ObjectsChanged<'a>),
    /// The stage's edit target changed (C++ `UsdNotice::StageEditTargetChanged`).
    /// The new target is available from
    /// [`Stage::edit_target`](super::Stage::edit_target). Fires on
    /// [`Stage::set_edit_target`](super::Stage::set_edit_target) and on both
    /// entering and leaving an [`EditContext`](super::EditContext) scope (the
    /// latter when its restore changes the target).
    EditTargetChanged,
    /// A layer was muted or unmuted (C++ `UsdNotice::LayerMutingChanged`).
    /// Reports the change to the muted set; suppressing muted opinions during
    /// composition is not yet wired up (see
    /// [`Stage::mute_layer`](super::Stage::mute_layer)).
    LayerMutingChanged(LayerMutingChanged<'a>),
}

/// A layer's muting changed (C++ `UsdNotice::LayerMutingChanged`). The stage
/// mutes one layer per call, so each notice reports a single layer.
pub struct LayerMutingChanged<'a> {
    /// Identifier of the layer whose muting changed.
    pub layer: &'a str,
    /// `true` if the layer is now muted, `false` if it was unmuted.
    pub muted: bool,
}

/// The objects affected by one edit (C++ `UsdNotice::ObjectsChanged`).
///
/// A flat, borrowed view that lives only for the listener callback. It carries
/// both the composed "what to refresh" paths ([`resynced`](Self::resynced) and
/// [`changed_info_only`](Self::changed_info_only)) and the replay index
/// ([`change_list`](Self::change_list) on
/// [`layer_identifier`](Self::layer_identifier)) that
/// [`Stage::extract_diff`](super::Stage::extract_diff) turns into a
/// serializable diff. Clone what you need to retain past the callback
/// ([`sdf::ChangeList`] is [`Clone`]).
pub struct ObjectsChanged<'a> {
    /// Paths whose composition was resynced — the prim index and its namespace
    /// descendants were dropped (C++ `ResyncedPaths`). Composed/stage namespace.
    pub resynced: &'a [sdf::Path],
    /// Paths that changed only in field or target info, without restructuring
    /// composition (C++ `ChangedInfoOnlyPaths`). Composed/stage namespace: a
    /// path authored through an arc or variant edit target is translated back
    /// from the edited layer's namespace through the target's mapping.
    pub changed_info_only: &'a [sdf::Path],
    /// Canonical identifier of the layer the edit landed on, and the lookup
    /// key [`Stage::extract_diff`](super::Stage::extract_diff) uses to read its
    /// authored values.
    pub layer_identifier: &'a str,
    /// The recorded change index for the edit: which `(path, field)` pairs were
    /// authored, plus structural flags. Keyed in the edited layer's namespace
    /// (the same as [`Stage::extract_diff`](super::Stage::extract_diff)); under
    /// an arc or variant edit target this differs from the stage-namespace
    /// [`resynced`](Self::resynced) / [`changed_info_only`](Self::changed_info_only)
    /// paths. [`changed_fields`](Self::changed_fields) bridges the two.
    pub change_list: &'a sdf::ChangeList,
    /// Namespace mapping (layer source to stage target) of the edit target the
    /// edit was authored through, or `None` for a local/root edit that needs no
    /// translation. [`changed_fields`](Self::changed_fields) uses it to map a
    /// stage-namespace query path back to the [`change_list`](Self::change_list)
    /// key.
    pub(crate) mapping: Option<&'a pcp::MapFunction>,
}

impl ObjectsChanged<'_> {
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

/// The owned backing store for one [`ObjectsChanged`] notice.
///
/// [`ObjectsChanged`] is a borrowed view valid only for the listener callback,
/// so the paths and change record it points at must outlive the call. The stage
/// builds a `Payload` from the classified [`pcp::Changes`] and the edit's raw
/// change list, then lends it out as an [`ObjectsChanged`] through
/// [`objects_changed`](Self::objects_changed). Held only while a listener is
/// installed, so the no-listener authoring path allocates nothing.
pub(crate) struct Payload {
    resynced: Vec<sdf::Path>,
    changed_info_only: Vec<sdf::Path>,
    change_list: sdf::ChangeList,
}

impl Payload {
    /// Classify one edit into the composed path-sets a notice reports.
    ///
    /// `changes` is the edit's invalidation plan and `scratch` its raw change
    /// list, in the edited layer's namespace. `mapping` is the edit target's
    /// namespace mapping (layer source to stage target), or `None` for a
    /// local/root edit that needs no translation.
    ///
    /// [`resynced`](ObjectsChanged::resynced) is the union of the significant and
    /// prim-tier composed paths; [`changed_info_only`](ObjectsChanged::changed_info_only)
    /// is every other edited path that authored a field value or edited
    /// relationship/connection targets.
    pub(crate) fn new(changes: &pcp::Changes, scratch: &sdf::ChangeList, mapping: Option<&pcp::MapFunction>) -> Self {
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
        // source-to-target direction) so the listener sees composed paths; for a
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

    /// Borrow this payload as an [`ObjectsChanged`] for the listener callback.
    ///
    /// `layer_identifier` names the layer the edit landed on and `mapping` is the
    /// edit target's mapping (the same one passed to [`new`](Self::new)), which
    /// [`changed_fields`](ObjectsChanged::changed_fields) uses to translate query
    /// paths back to the change-list namespace.
    pub(crate) fn objects_changed<'a>(
        &'a self,
        layer_identifier: &'a str,
        mapping: Option<&'a pcp::MapFunction>,
    ) -> ObjectsChanged<'a> {
        ObjectsChanged {
            resynced: &self.resynced,
            changed_info_only: &self.changed_info_only,
            layer_identifier,
            change_list: &self.change_list,
            mapping,
        }
    }
}
