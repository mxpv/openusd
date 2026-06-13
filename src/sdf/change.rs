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
//! [`Layer::drain_changes`](super::Layer::drain_changes).
//
// TODO: add `old_path: Option<Path>` and a `RenameChanges` channel for
// namespace edits once `Layer` exposes a rename API. C++
// `SdfChangeList::Entry::oldPath` + `PcpChanges::_renameChanges` are the
// reference shape. Today no `Layer` method renames a prim, so the field
// would have no producer.

use std::borrow::Cow;
use std::collections::{BTreeSet, HashSet};

use bitflags::bitflags;

use super::{AbstractData, DataError, FieldKey, Path, SpecType, Specifier, Value};
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
    /// borrowed `&str` it sees on a write. This is the raw set of touched
    /// fields (including non-composition metadata like `customData` and the
    /// child-name lists); deciding which are significant is the consumer's job
    /// — [`pcp::Changes`](crate::pcp::Changes) filters it against its own
    /// structural-field list, so presence here does not by itself imply a
    /// composition change.
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
        /// Set bit when the change creates a prim or property spec outright.
        const ADD = Self::ADD_NON_INERT_PRIM.bits() | Self::ADD_INERT_PRIM.bits() | Self::ADD_PROPERTY.bits();
        /// Set bit when the change removes a prim or property spec outright.
        const REMOVE =
            Self::REMOVE_NON_INERT_PRIM.bits() | Self::REMOVE_INERT_PRIM.bits() | Self::REMOVE_PROPERTY.bits();
    }
}

impl ChangeEntry {
    /// Whether this entry records only child-name bookkeeping: no structural
    /// flags, and every authored field a child-name list (`primChildren`,
    /// `propertyChildren`, or the variant-chain registration a descendant edit
    /// stamps on its ancestors). Such an entry marks a spec whose own opinions
    /// did not change.
    pub fn is_child_bookkeeping(&self) -> bool {
        self.flags.is_empty() && self.authored_fields().next().is_none()
    }

    /// The fields this entry authored as opinions —
    /// [`info_changed`](Self::info_changed) without the structural child-name
    /// lists.
    pub fn authored_fields(&self) -> impl Iterator<Item = &tf::Token> {
        self.info_changed
            .iter()
            .filter(|f| !super::is_children_field(f.as_str()))
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

    /// Remove the entry at `path`, if present. The recording delegate
    /// ([`EditProxy`]) uses this to drop a spec's partial record when a creation
    /// is cancelled — the spec is created and erased before draining.
    pub(crate) fn discard(&mut self, path: &Path) {
        self.entries.retain(|(p, _)| p != path);
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
/// no add. For a spec created within the current (undrained) window the add
/// flag already covers it, so only its `specifier` write is suppressed — that
/// field is auto-stamped on every created spec (including auto-created
/// ancestors) and would otherwise leak as a spurious `specifier` change; its
/// other field writes are still recorded so the classifier sees the
/// composition-arc / instancing / activation opinions an `over` carries.
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

    /// Note every field currently authored at `path` except the auto-stamped
    /// `specifier`, so a spec removal carries the same `info_changed` signal an
    /// add does. `list_fields` returns owned names, so the inner borrow is
    /// released before the recording writes.
    //
    // TODO(perf): `list_fields` allocates a `Vec<String>` and clones every field
    // name on the `Data` backend, and `note_field` re-interns each survivor; a
    // borrowing field-name iterator on `AbstractData` would drop the Vec and the
    // clones (the token intern stays, since the backend keys are `String`).
    fn note_existing_fields(&mut self, path: &Path) {
        let Some(fields) = self.inner.list_fields(path) else {
            return;
        };
        for field in fields {
            if field != FieldKey::Specifier.as_str() {
                self.note_field(path, &field);
            }
        }
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

    fn try_field(&self, path: &Path, field: &str) -> Result<Option<Cow<'_, Value>>, DataError> {
        self.inner.try_field(path, field)
    }

    fn list_fields(&self, path: &Path) -> Option<Vec<String>> {
        self.inner.list_fields(path)
    }

    fn spec_paths(&self) -> Vec<Path> {
        self.inner.spec_paths()
    }

    fn create_spec(&mut self, path: Path, ty: SpecType) {
        // Creating over an existing spec replaces it, clearing its fields: record
        // the removal of the old spec, and — for a prim — surface its authored
        // fields the way `erase_spec` does, so a structural opinion the replace
        // tears down still reaches the classifier.
        if let Some(flag) = remove_flag(&*self.inner, &path) {
            self.changes.entry_mut(&path).flags |= flag;
            if flag.intersects(ChangeFlags::REMOVE_INERT_PRIM | ChangeFlags::REMOVE_NON_INERT_PRIM) {
                self.note_existing_fields(&path);
            }
        }
        // Only specs that `finalize` classifies into an add flag are tracked, so
        // `set_field` knows to suppress their auto-stamped `specifier`. Scaffolding
        // specs (the pseudo-root, variant sets/variants) get no add flag and are
        // left untracked, so every field write on them is recorded — a
        // root-metadata edit that also materializes the pseudo-root must still
        // record `defaultPrim` etc.
        if matches!(ty, SpecType::Prim | SpecType::Attribute | SpecType::Relationship) {
            self.created.insert(path.clone());
        }
        self.inner.create_spec(path, ty);
    }

    fn erase_spec(&mut self, path: &Path) {
        // A spec created and erased within one window cancels out. A fresh
        // create recorded no removal, so the field writes its `set_field`s
        // accumulated are a net no-op — drop that partial record rather than let
        // it linger as a spurious change. A removal flag means `create_spec`
        // replaced a pre-existing spec, whose removal must outlive the cancel.
        if self.created.remove(path) {
            let replaced = self
                .changes
                .entries()
                .iter()
                .find(|(p, _)| p == path)
                .is_some_and(|(_, e)| {
                    e.flags.intersects(
                        ChangeFlags::REMOVE_INERT_PRIM
                            | ChangeFlags::REMOVE_NON_INERT_PRIM
                            | ChangeFlags::REMOVE_PROPERTY,
                    )
                });
            if !replaced {
                self.changes.discard(path);
            }
            self.inner.erase_spec(path);
            return;
        }
        if let Some(flag) = remove_flag(&*self.inner, path) {
            self.changes.entry_mut(path).flags |= flag;
            // A removed prim spec surfaces its authored fields (except the
            // always-present `specifier`) so the classifier can tell a structural
            // removal — an `over` that carried `references`, `active`, … — from a
            // plain one, symmetric with an add. The flag already distinguishes a
            // prim removal from a property one, whose field signal the classifier
            // ignores.
            if flag.intersects(ChangeFlags::REMOVE_INERT_PRIM | ChangeFlags::REMOVE_NON_INERT_PRIM) {
                self.note_existing_fields(path);
            }
        }
        self.inner.erase_spec(path);
    }

    fn set_field(&mut self, path: &Path, field: &str, value: Value) {
        if self.created.contains(path) {
            // The spec was created this window, so its shape is already carried
            // by the add flag. Record every field except `specifier`: a created
            // `over` may carry a composition-arc / instancing / activation
            // opinion the classifier must see, whereas `specifier` is both
            // already implied by the add flag and itself a significant field
            // stamped on every created spec — recording it would force every
            // created `over` into the significant tier. (Other auto-stamped
            // fields such as `typeName` and the child-name lists are recorded too
            // but are harmless: they do not promote to significant.) A created
            // spec's field is always new, so no value diff is needed.
            if field != FieldKey::Specifier.as_str() {
                self.note_field(path, field);
            }
        } else if self.inner.try_field(path, field).ok().flatten().as_deref() != Some(&value) {
            self.note_field(path, field);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::{Data, ReferenceListOp};

    fn p(s: &str) -> Path {
        Path::new(s).expect("valid path")
    }

    fn references(field: &str) -> bool {
        field == FieldKey::References.as_str()
    }

    fn specifier(field: &str) -> bool {
        field == FieldKey::Specifier.as_str()
    }

    /// Authors an `over` carrying a `references` opinion through `proxy` in one
    /// window, the way `define_prim` / `override_prim` + `add_reference` do.
    fn create_over_with_reference(proxy: &mut EditProxy, path: &Path) {
        proxy.create_spec(path.clone(), SpecType::Prim);
        proxy.set_field(path, FieldKey::Specifier.as_str(), Value::Specifier(Specifier::Over));
        proxy.set_field(
            path,
            FieldKey::References.as_str(),
            Value::ReferenceListOp(ReferenceListOp::default()),
        );
    }

    /// A created `over` surfaces its composition-arc field in `info_changed` so
    /// the classifier sees the structural opinion, but not the auto-stamped
    /// `specifier`.
    #[test]
    fn created_over_records_arc_not_specifier() {
        let mut proxy = EditProxy::new(Box::new(Data::new()));
        create_over_with_reference(&mut proxy, &p("/X"));

        let mut cl = ChangeList::new();
        proxy.take(&mut cl);
        let entry = &cl.entries()[0].1;
        assert!(entry.flags.contains(ChangeFlags::ADD_INERT_PRIM));
        assert!(entry.info_changed.iter().any(|t| references(t)));
        assert!(!entry.info_changed.iter().any(|t| specifier(t)));
    }

    /// A created `over` with only its auto-stamped `specifier` records the add
    /// and no spurious `specifier` change — the auto-created-ancestor case.
    #[test]
    fn created_over_suppresses_specifier() {
        let mut proxy = EditProxy::new(Box::new(Data::new()));
        proxy.create_spec(p("/X"), SpecType::Prim);
        proxy.set_field(
            &p("/X"),
            FieldKey::Specifier.as_str(),
            Value::Specifier(Specifier::Over),
        );

        let mut cl = ChangeList::new();
        proxy.take(&mut cl);
        let entry = &cl.entries()[0].1;
        assert!(entry.flags.contains(ChangeFlags::ADD_INERT_PRIM));
        assert!(entry.info_changed.is_empty());
    }

    /// Erasing an `over` surfaces its authored fields (except `specifier`), so a
    /// structural removal carries the same signal as the matching add.
    #[test]
    fn erased_over_records_fields() {
        // Populate the spec outside a proxy window so the erase sees it as
        // pre-existing rather than created-this-window.
        let mut data = Data::new();
        data.create_spec(p("/X"), SpecType::Prim);
        data.set_field(
            &p("/X"),
            FieldKey::Specifier.as_str(),
            Value::Specifier(Specifier::Over),
        );
        data.set_field(
            &p("/X"),
            FieldKey::References.as_str(),
            Value::ReferenceListOp(ReferenceListOp::default()),
        );

        let mut proxy = EditProxy::new(Box::new(data));
        proxy.erase_spec(&p("/X"));

        let mut cl = ChangeList::new();
        proxy.take(&mut cl);
        let entry = &cl.entries()[0].1;
        assert!(entry.flags.contains(ChangeFlags::REMOVE_INERT_PRIM));
        assert!(entry.info_changed.iter().any(|t| references(t)));
        assert!(!entry.info_changed.iter().any(|t| specifier(t)));
    }

    /// Replacing an existing `over` (which carried a composition arc) by
    /// re-creating it as a plain `over` surfaces the dropped `references` field,
    /// so the teardown is not lost — `create_spec`-as-replace is symmetric with
    /// `erase_spec`.
    #[test]
    fn recreated_over_records_dropped_field() {
        let mut data = Data::new();
        data.create_spec(p("/X"), SpecType::Prim);
        data.set_field(
            &p("/X"),
            FieldKey::Specifier.as_str(),
            Value::Specifier(Specifier::Over),
        );
        data.set_field(
            &p("/X"),
            FieldKey::References.as_str(),
            Value::ReferenceListOp(ReferenceListOp::default()),
        );

        let mut proxy = EditProxy::new(Box::new(data));
        // Re-create /X as a plain `over` with no references, in one window.
        proxy.create_spec(p("/X"), SpecType::Prim);
        proxy.set_field(
            &p("/X"),
            FieldKey::Specifier.as_str(),
            Value::Specifier(Specifier::Over),
        );

        let mut cl = ChangeList::new();
        proxy.take(&mut cl);
        let entry = &cl.entries()[0].1;
        assert!(entry.flags.contains(ChangeFlags::REMOVE_INERT_PRIM));
        assert!(entry.info_changed.iter().any(|t| references(t)));
    }

    /// A spec freshly created (with field writes) and erased before draining
    /// cancels out completely — the partial record does not linger as a spurious
    /// change.
    #[test]
    fn created_then_erased_cancels() {
        let mut proxy = EditProxy::new(Box::new(Data::new()));
        create_over_with_reference(&mut proxy, &p("/X"));
        proxy.erase_spec(&p("/X"));

        assert!(!proxy.is_dirty());
        let mut cl = ChangeList::new();
        proxy.take(&mut cl);
        assert!(cl.is_empty());
    }

    /// Re-creating (replacing) a pre-existing spec and then erasing it in one
    /// window still records the removal: the replace's removal flag outlives the
    /// cancelled re-creation, unlike a fresh create+erase.
    #[test]
    fn recreated_then_erased_records_removal() {
        let mut data = Data::new();
        data.create_spec(p("/X"), SpecType::Prim);
        data.set_field(
            &p("/X"),
            FieldKey::Specifier.as_str(),
            Value::Specifier(Specifier::Over),
        );

        let mut proxy = EditProxy::new(Box::new(data));
        proxy.create_spec(p("/X"), SpecType::Prim);
        proxy.erase_spec(&p("/X"));

        let mut cl = ChangeList::new();
        proxy.take(&mut cl);
        assert!(cl.entries()[0].1.flags.contains(ChangeFlags::REMOVE_INERT_PRIM));
    }
}
