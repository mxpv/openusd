//! Per-layer change records and the recording delegate that produces them.
//!
//! A [`ChangeList`] records the edits made to a layer and is handed to
//! [`pcp::Changes`](crate::pcp::Changes) so the composition cache can
//! invalidate surgically instead of dropping every cached prim index.
//!
//! Mirroring C++ `SdfChangeList` + `SdfLayerStateDelegateBase`, the list is
//! produced natively by layer mutations: the recording delegate [`EditProxy`]
//! wraps a layer's backing [`AbstractData`](super::AbstractData), forwards every
//! read and write to it, and appends an entry for every write — so any author,
//! not just `Stage`, yields an authoritative record. Drain it with
//! [`Layer::take_changes`](super::Layer::take_changes).
//
// TODO: add `old_path: Option<Path>` and a `RenameChanges` channel for
// namespace edits once `Layer` exposes a rename API. C++
// `SdfChangeList::Entry::oldPath` + `PcpChanges::_renameChanges` are the
// reference shape. Today no `Layer` method renames a prim, so the field
// would have no producer.

use std::borrow::Cow;
use std::collections::{BTreeSet, HashSet};

use anyhow::Result;
use bitflags::bitflags;

use super::{AbstractData, FieldKey, Path, SpecType, Specifier, Value};
use crate::tf;

/// Per-layer ordered list of authoring changes.
///
/// Each `(Path, ChangeEntry)` pair describes one logical edit at a single
/// scene-graph path. Repeated edits at the same path collapse into one
/// entry via [`entry_mut`](Self::entry_mut).
///
/// An empty list means no mutation happened — for example, an authoring
/// closure that returned `ReadOnly` before touching layer state.
#[derive(Debug, Default, Clone)]
pub struct ChangeList {
    entries: Vec<(Path, ChangeEntry)>,
}

/// Per-path summary of changes.
///
/// Flag fields name shape changes (spec added/removed). `info_changed`
/// names which metadata fields were authored. The combination drives the
/// three-tier classification in [`pcp::Changes`](crate::pcp::Changes).
#[derive(Debug, Default, Clone)]
pub struct ChangeEntry {
    /// Shape changes — adds/removes of specs and relationship/connection edits.
    pub flags: ChangeFlags,
    /// Names of fields whose value was authored at this path. Interned as
    /// [`tf::Token`] so the recording delegate ([`EditProxy`]) can note any
    /// field name — schema `FieldKey`s and custom metadata alike — from the
    /// borrowed `&str` it sees on a write.
    pub info_changed: BTreeSet<tf::Token>,
}

bitflags! {
    /// Shape-change bits mirroring `SdfChangeList::Entry`'s bitfield.
    ///
    /// "Inert" matches C++ usage: an inert prim spec has `specifier = over`
    /// and carries no composition arc fields. Adding or removing it leaves
    /// the composition graph topology unchanged.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct ChangeFlags: u16 {
        /// `over` spec created at a previously-unspecified path.
        const ADD_INERT_PRIM = 1 << 0;
        /// `def`/`class` spec created.
        const ADD_NON_INERT_PRIM = 1 << 1;
        /// `over` spec removed.
        const REMOVE_INERT_PRIM = 1 << 2;
        /// `def`/`class` spec removed.
        const REMOVE_NON_INERT_PRIM = 1 << 3;
        /// Property spec (attribute or relationship) created.
        const ADD_PROPERTY = 1 << 4;
        /// Property spec removed.
        const REMOVE_PROPERTY = 1 << 5;
        /// Relationship targets were edited (added/removed/reordered).
        const CHANGE_RELATIONSHIP_TARGETS = 1 << 6;
        /// Attribute connection targets were edited.
        const CHANGE_ATTRIBUTE_CONNECTION = 1 << 7;

        /// Set bit when the change adds or removes a non-inert prim spec
        /// (anything that may shift composition graph topology).
        const NON_INERT_PRIM = Self::ADD_NON_INERT_PRIM.bits() | Self::REMOVE_NON_INERT_PRIM.bits();
        /// Set bit when the change adds or removes an inert (`over`) prim spec.
        const INERT_PRIM = Self::ADD_INERT_PRIM.bits() | Self::REMOVE_INERT_PRIM.bits();
    }
}

impl ChangeList {
    /// Creates an empty change list.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns `true` if no entries were recorded.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Returns the authored entries in insertion order.
    pub fn entries(&self) -> &[(Path, ChangeEntry)] {
        &self.entries
    }

    /// Returns an iterator over `(path, entry)` pairs.
    pub fn iter(&self) -> std::slice::Iter<'_, (Path, ChangeEntry)> {
        self.entries.iter()
    }

    /// Get or insert the entry at `path`, allowing the caller to set flags
    /// or extend `info_changed`. Linear scan; the entry count is bounded
    /// by the number of distinct paths in one authoring call.
    pub fn entry_mut(&mut self, path: &Path) -> &mut ChangeEntry {
        if let Some(pos) = self.entries.iter().position(|(p, _)| p == path) {
            return &mut self.entries[pos].1;
        }
        self.entries.push((path.clone(), ChangeEntry::default()));
        &mut self.entries.last_mut().expect("just pushed").1
    }

    /// Append every entry of `self` onto `out`, leaving `self` empty but
    /// retaining its backing allocation for reuse. The recording delegate
    /// ([`EditProxy`]) moves its entries into a caller-owned buffer this way so
    /// neither side reallocates across edits.
    pub fn append_to(&mut self, out: &mut ChangeList) {
        out.entries.append(&mut self.entries);
    }

    /// Discard all recorded entries, retaining the backing allocation.
    pub fn clear(&mut self) {
        self.entries.clear();
    }
}

/// A write-recording wrapper around a layer's backing [`AbstractData`].
///
/// Reads forward verbatim to `inner`. Writes record into a [`ChangeList`] and
/// then forward. The recorded shape mirrors what composition needs:
/// spec adds/removes become [`ChangeFlags`] (classified at drain time by the
/// spec's final state) and field writes become `info_changed` entries.
///
/// Idempotence is enforced at the source: a `set_field` that does not change
/// the stored value records nothing, and re-creating an existing spec records
/// no add. Field writes on a spec created within the current (undrained)
/// window are folded into that spec's add rather than recorded separately, so
/// the `over` specifier auto-stamped on an auto-created ancestor does not leak
/// out as a spurious `specifier` change.
pub struct EditProxy {
    /// Changes accumulated since the last drain.
    changes: ChangeList,
    /// Specs created since the last drain. Classified into add flags at drain
    /// time from the inner spec's final state, and used to suppress
    /// `info_changed` for their own field writes.
    created: HashSet<Path>,
    /// The real backend (in-memory [`Data`](super::Data), lazy crate reader, …).
    inner: Box<dyn AbstractData>,
}

impl EditProxy {
    /// Wrap `inner`, starting with an empty change record. Construct the
    /// backend fully *before* wrapping (the "wrap last" rule) so populating it
    /// records nothing — only post-wrap edits are tracked.
    pub fn new(inner: Box<dyn AbstractData>) -> Self {
        Self {
            changes: ChangeList::new(),
            created: HashSet::new(),
            inner,
        }
    }

    /// Borrow the wrapped backend directly, bypassing the recording layer. The
    /// read path ([`Layer::data`](super::Layer::data)) uses this so composition
    /// reads dispatch straight to the backend instead of forwarding through the
    /// proxy. There is deliberately no mutable counterpart — every write goes
    /// through the recording proxy.
    pub fn inner(&self) -> &dyn AbstractData {
        self.inner.as_ref()
    }

    /// Whether any change has been recorded since the last drain. Mirrors C++
    /// `SdfLayer::IsDirty`.
    pub fn is_dirty(&self) -> bool {
        !self.changes.is_empty() || !self.created.is_empty()
    }

    /// Finalize the recorded changes and move them into `out`, leaving this
    /// proxy's buffers empty but allocation-warm for the next edit.
    ///
    /// Finalization classifies each spec created since the last drain by its
    /// inner final state: a `def`/`class` prim is a non-inert add, an `over`
    /// prim an inert add, an attribute/relationship a property add. A spec
    /// created and then erased within the window contributes nothing.
    pub fn take(&mut self, out: &mut ChangeList) {
        self.finalize();
        self.changes.append_to(out);
    }

    /// Discard the recorded changes without applying them.
    pub fn clear(&mut self) {
        self.changes.clear();
        self.created.clear();
    }

    /// Fold the `created` set into add flags on the change record.
    fn finalize(&mut self) {
        for path in &self.created {
            let Some(ty) = self.inner.spec_type(path) else {
                continue;
            };
            let flag = match ty {
                SpecType::Prim => match specifier_of(&*self.inner, path) {
                    Some(Specifier::Over) | None => ChangeFlags::ADD_INERT_PRIM,
                    Some(_) => ChangeFlags::ADD_NON_INERT_PRIM,
                },
                SpecType::Attribute | SpecType::Relationship => ChangeFlags::ADD_PROPERTY,
                _ => continue,
            };
            self.changes.entry_mut(path).flags |= flag;
        }
        self.created.clear();
    }

    /// Record a field write on a pre-existing spec: note the field name and OR
    /// in any shape flag the field implies (relationship-target / connection).
    fn note_field(&mut self, path: &Path, field: &str) {
        let entry = self.changes.entry_mut(path);
        entry.info_changed.insert(tf::Token::from(field));
        entry.flags |= flag_for_field(field);
    }
}

impl AbstractData for EditProxy {
    fn has_spec(&self, path: &Path) -> bool {
        self.inner.has_spec(path)
    }

    fn has_field(&self, path: &Path, field: &str) -> bool {
        self.inner.has_field(path, field)
    }

    fn spec_type(&self, path: &Path) -> Option<SpecType> {
        self.inner.spec_type(path)
    }

    fn try_field(&self, path: &Path, field: &str) -> Result<Option<Cow<'_, Value>>> {
        self.inner.try_field(path, field)
    }

    fn list_fields(&self, path: &Path) -> Option<Vec<String>> {
        self.inner.list_fields(path)
    }

    fn spec_paths(&self) -> Vec<Path> {
        self.inner.spec_paths()
    }

    fn create_spec(&mut self, path: Path, ty: SpecType) {
        // Creating over an existing spec replaces it, clearing its fields:
        // record the removal of the old spec so the change isn't dropped.
        if let Some(flag) = remove_flag(&*self.inner, &path) {
            self.changes.entry_mut(&path).flags |= flag;
        }
        // Only specs that `finalize` classifies into an add flag are tracked, so
        // their own field writes fold into that add. Scaffolding specs (the
        // pseudo-root, variant sets/variants) get no add flag, so suppressing
        // their field writes would drop them — a root-metadata edit that also
        // materializes the pseudo-root must still record `defaultPrim` etc.
        if matches!(ty, SpecType::Prim | SpecType::Attribute | SpecType::Relationship) {
            self.created.insert(path.clone());
        }
        self.inner.create_spec(path, ty);
    }

    fn erase_spec(&mut self, path: &Path) {
        // A spec created and erased within one window never existed before it,
        // so it cancels out rather than recording a removal.
        if self.created.remove(path) {
            self.inner.erase_spec(path);
            return;
        }
        if let Some(flag) = remove_flag(&*self.inner, path) {
            self.changes.entry_mut(path).flags |= flag;
        }
        self.inner.erase_spec(path);
    }

    fn set_field(&mut self, path: &Path, field: &str, value: Value) {
        // A write to a spec created this window folds into its add; skip the
        // value-diff read entirely for it.
        if !self.created.contains(path) {
            let changed = self.inner.try_field(path, field).ok().flatten().as_deref() != Some(&value);
            if changed {
                self.note_field(path, field);
            }
        }
        self.inner.set_field(path, field, value);
    }

    fn erase_field(&mut self, path: &Path, field: &str) {
        if self.inner.has_field(path, field) && !self.created.contains(path) {
            self.note_field(path, field);
        }
        self.inner.erase_field(path, field);
    }
}

/// The prim `specifier` authored at `path`, if any.
fn specifier_of(data: &dyn AbstractData, path: &Path) -> Option<Specifier> {
    match data
        .try_field(path, FieldKey::Specifier.as_str())
        .ok()
        .flatten()
        .as_deref()
    {
        Some(Value::Specifier(s)) => Some(*s),
        _ => None,
    }
}

/// The removal flag for the spec currently at `path`, or `None` for spec types
/// that carry no shape change (variant scaffolding, pseudo-root).
fn remove_flag(data: &dyn AbstractData, path: &Path) -> Option<ChangeFlags> {
    match data.spec_type(path)? {
        SpecType::Prim => Some(match specifier_of(data, path) {
            Some(Specifier::Over) | None => ChangeFlags::REMOVE_INERT_PRIM,
            Some(_) => ChangeFlags::REMOVE_NON_INERT_PRIM,
        }),
        SpecType::Attribute | SpecType::Relationship => Some(ChangeFlags::REMOVE_PROPERTY),
        _ => None,
    }
}

/// The shape flag a field write implies. Target/connection edits set a
/// dedicated bit; ordinary metadata sets none.
fn flag_for_field(field: &str) -> ChangeFlags {
    if field == FieldKey::TargetPaths.as_str() {
        ChangeFlags::CHANGE_RELATIONSHIP_TARGETS
    } else if field == FieldKey::ConnectionPaths.as_str() {
        ChangeFlags::CHANGE_ATTRIBUTE_CONNECTION
    } else {
        ChangeFlags::empty()
    }
}
