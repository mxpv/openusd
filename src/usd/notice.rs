//! Stage change notifications, the Rust equivalent of C++ `UsdNotice`.
//!
//! A [`Stage`](super::Stage) with a listener installed through
//! [`Stage::set_listener`](super::Stage::set_listener) delivers a [`Notice`]
//! after every successful edit. [`ObjectsChanged`] reports what the edit
//! touched and feeds [`Stage::extract_diff`](super::Stage::extract_diff), the
//! building block for mirroring a stage's edits onto another stage or machine.

use std::collections::BTreeSet;

use crate::{sdf, tf};

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
    /// composition (C++ `ChangedInfoOnlyPaths`).
    //
    // TODO: these come from the edited layer's `ChangeList`, so they are in
    // edit-target/layer namespace. For a local-layer edit that equals stage
    // namespace, but arc-target edits are not yet translated back.
    pub changed_info_only: &'a [sdf::Path],
    /// Canonical identifier of the layer the edit landed on, and the lookup
    /// key [`Stage::extract_diff`](super::Stage::extract_diff) uses to read its
    /// authored values.
    pub layer_identifier: &'a str,
    /// The recorded change index for the edit: which `(path, field)` pairs were
    /// authored, plus structural flags. Backs [`changed_fields`](Self::changed_fields)
    /// and [`Stage::extract_diff`](super::Stage::extract_diff).
    pub change_list: &'a sdf::ChangeList,
}

impl ObjectsChanged<'_> {
    /// The field names authored at `path` by this edit (C++ `GetChangedFields`),
    /// or an empty set if `path` was not touched.
    pub fn changed_fields(&self, path: &sdf::Path) -> &BTreeSet<tf::Token> {
        static EMPTY: BTreeSet<tf::Token> = BTreeSet::new();
        self.change_list
            .entries()
            .iter()
            .find(|(p, _)| p == path)
            .map(|(_, entry)| &entry.info_changed)
            .unwrap_or(&EMPTY)
    }
}
