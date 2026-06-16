//! Per-layer change records and the derivation that produces them.
//!
//! A [`ChangeList`] records the edits made to a layer and is handed to
//! [`pcp::Changes`](crate::pcp::Changes) so the composition cache can
//! invalidate surgically instead of dropping every cached prim index.
//!
//! Mirroring C++ `SdfChangeList`, the list is produced natively from a layer's
//! staged edits: [`ChangeList::from_overlay`] walks a
//! [`CowData`](super::CowData) overlay against its still-pristine base and
//! classifies each staged [`Patch`](super::Patch) into the shape flags and
//! authored-field set composition needs. A [`Layer`](super::Layer) calls it
//! before committing the overlay, so any author — not just `Stage` — yields an
//! authoritative record.
//
// TODO: add `old_path: Option<Path>` and a `RenameChanges` channel for
// namespace edits once `Layer` exposes a rename API. C++
// `SdfChangeList::Entry::oldPath` + `PcpChanges::_renameChanges` are the
// reference shape. Today no `Layer` method renames a prim, so the field
// would have no producer.

use std::collections::BTreeSet;

use bitflags::bitflags;

use super::{AbstractData, CowData, FieldKey, Patch, Path, SpecData, SpecType, Specifier, Value};
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
    /// [`tf::Token`] so [`ChangeList::from_overlay`] can note any field name —
    /// schema `FieldKey`s and custom metadata alike — from the borrowed `&str`
    /// it reads off a staged patch. This is the raw set of touched
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
    /// Whether this entry records no change at all — no shape flags and no
    /// authored fields.
    pub fn is_empty(&self) -> bool {
        self.flags.is_empty() && self.info_changed.is_empty()
    }

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

    /// Fold `other` into this list, combining entries at the same path — the
    /// flags are unioned and the authored-field sets merged — rather than
    /// duplicating the path. Used to merge several layers' records into one for
    /// a batched edit's change notice, so a path edited in more than one layer
    /// reports the union of its changes.
    //
    // TODO(perf): each merge is an `entry_mut` linear scan, so this is O(entries
    // × distinct paths). Fine for the notice path (only when a listener is
    // installed), but a path-keyed map would bound it for very large batches.
    pub fn merge_from(&mut self, other: &ChangeList) {
        for (path, entry) in &other.entries {
            let merged = self.entry_mut(path);
            merged.flags |= entry.flags;
            merged.info_changed.extend(entry.info_changed.iter().cloned());
        }
    }

    /// Discard all recorded entries, retaining the backing allocation.
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Derive a composition-invalidation record from `cow`'s staged overlay,
    /// reading each [`Patch`](super::Patch) against the still-pristine
    /// [`base`](super::CowData::base). Call it before
    /// [`CowData::commit`](super::CowData::commit), while the base still holds
    /// the pre-edit values the idempotence and field-surfacing checks compare
    /// against.
    ///
    /// The record is a pure function of the staged state, so it is also a touch
    /// more precise than recording mutations as they happen: an edit that nets
    /// to nothing — a field set back to its base value, or a field added and
    /// then erased within the same window — leaves no entry here, since it never
    /// changes what composition would resolve.
    pub fn from_overlay<T: AbstractData>(cow: &CowData<T>) -> ChangeList {
        let base = cow.base();
        let mut changes = ChangeList::new();
        for (path, patch) in cow.overlay() {
            let mut entry = ChangeEntry::default();
            match patch {
                Patch::Created(spec) => {
                    // A create over a pre-existing spec replaces it: record the
                    // old spec's removal — surfacing a prim's authored fields —
                    // so a structural opinion the replace tears down still
                    // reaches the classifier.
                    if base.has_spec(path) {
                        note_removal(&mut entry, base, path);
                    }
                    match spec.ty {
                        SpecType::Prim | SpecType::Attribute | SpecType::Relationship => {
                            // A created prim/property carries its shape in the add
                            // flag; record every field except the auto-stamped
                            // `specifier` (significant on every spec, and already
                            // implied by the flag). Created fields are new, so no
                            // value diff is needed.
                            entry.flags |= add_flag(spec);
                            for (field, _) in &spec.fields {
                                if field != FieldKey::Specifier.as_str() {
                                    note_field(&mut entry, field);
                                }
                            }
                        }
                        _ => {
                            // Scaffolding (pseudo-root, variant set/variant) gets
                            // no add flag; record each authored field that differs
                            // from the base — all of them on a fresh create.
                            for (field, value) in &spec.fields {
                                if field_changed(base, path, field, value) {
                                    note_field(&mut entry, field);
                                }
                            }
                        }
                    }
                }
                Patch::Tombstone => note_removal(&mut entry, base, path),
                Patch::Edited { set, erased } => {
                    for (field, value) in set {
                        if field_changed(base, path, field, value) {
                            note_field(&mut entry, field);
                        }
                    }
                    // CowData only tombstones a field the base actually held, so
                    // every erased field is a real removal worth recording.
                    for field in erased {
                        note_field(&mut entry, field);
                    }
                }
            }
            // Each overlay path is distinct, so the derived entry is new — push it
            // directly (a patch that nets to nothing leaves an empty entry to drop).
            if !entry.is_empty() {
                changes.entries.push((path.clone(), entry));
            }
        }
        changes
    }
}

/// Note a field write into `entry`: record the field name (interned so any
/// field name — schema `FieldKey` or custom metadata — is captured from a
/// borrowed `&str`) and OR in any shape flag the field implies
/// (relationship-target / connection).
fn note_field(entry: &mut ChangeEntry, field: &str) {
    entry.info_changed.insert(tf::Token::from(field));
    entry.flags |= flag_for_field(field);
}

/// Whether staging `value` at `path`.`field` actually changes the base — the
/// value-diff idempotence check, so re-authoring an unchanged value records no
/// change.
fn field_changed(base: &dyn AbstractData, path: &Path, field: &str, value: &Value) -> bool {
    base.try_field(path, field).ok().flatten().as_deref() != Some(value)
}

/// Record the removal of the spec currently at `path` in `data` into `entry`:
/// OR in its removal flag and, for a prim, surface its authored fields (except
/// the auto-stamped `specifier`) so a structural removal — an `over` that
/// carried `references`, `active`, … — reaches the classifier with the same
/// `info_changed` signal the matching add carries. A property removal carries
/// only its flag, whose field signal the classifier ignores.
//
// TODO(perf): `list_fields` allocates a `Vec<String>` and clones every field
// name on the `Data` backend, and `note_field` re-interns each survivor; a
// borrowing field-name iterator on `AbstractData` would drop the Vec and the
// clones (the token intern stays, since the backend keys are `String`).
fn note_removal(entry: &mut ChangeEntry, data: &dyn AbstractData, path: &Path) {
    let Some(flag) = remove_flag(data, path) else {
        return;
    };
    entry.flags |= flag;
    if flag.intersects(ChangeFlags::REMOVE_INERT_PRIM | ChangeFlags::REMOVE_NON_INERT_PRIM) {
        if let Some(fields) = data.list_fields(path) {
            for field in fields {
                if field != FieldKey::Specifier.as_str() {
                    note_field(entry, &field);
                }
            }
        }
    }
}

/// The add flag a created `spec` implies, by its final type and specifier: a
/// `def`/`class` prim is a non-inert add, an `over` prim an inert add, an
/// attribute/relationship a property add. Scaffolding specs (pseudo-root,
/// variant set/variant) imply no add flag.
fn add_flag(spec: &SpecData) -> ChangeFlags {
    match spec.ty {
        SpecType::Prim => match specifier_of_spec(spec) {
            Some(Specifier::Over) | None => ChangeFlags::ADD_INERT_PRIM,
            Some(_) => ChangeFlags::ADD_NON_INERT_PRIM,
        },
        SpecType::Attribute | SpecType::Relationship => ChangeFlags::ADD_PROPERTY,
        _ => ChangeFlags::empty(),
    }
}

/// The [`Specifier`] a `specifier`-field value holds, if it is one.
fn as_specifier(value: Option<&Value>) -> Option<Specifier> {
    match value {
        Some(Value::Specifier(s)) => Some(*s),
        _ => None,
    }
}

/// The prim `specifier` carried by a created `spec`, if any.
fn specifier_of_spec(spec: &SpecData) -> Option<Specifier> {
    as_specifier(spec.get(FieldKey::Specifier.as_str()))
}

/// The prim `specifier` authored at `path`, if any.
fn specifier_of(data: &dyn AbstractData, path: &Path) -> Option<Specifier> {
    as_specifier(
        data.try_field(path, FieldKey::Specifier.as_str())
            .ok()
            .flatten()
            .as_deref(),
    )
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
    use crate::sdf::{AttributeSpec, ChildrenKey, Data, PathListOp, PrimSpec, ReferenceListOp, Variability};

    fn p(s: &str) -> Path {
        Path::new(s).expect("valid path")
    }

    /// A blank backend carrying just the pseudo-root — the state a freshly
    /// created layer's overlay sits over.
    fn rooted() -> Data {
        let mut data = Data::new();
        data.create_spec(Path::abs_root(), SpecType::PseudoRoot);
        data
    }

    /// Whether the derived entry at `path` carries `flag`.
    fn has_flag(cl: &ChangeList, path: &str, flag: ChangeFlags) -> bool {
        cl.iter().any(|(pp, e)| pp == &p(path) && e.flags.contains(flag))
    }

    fn references(field: &str) -> bool {
        field == FieldKey::References.as_str()
    }

    fn specifier(field: &str) -> bool {
        field == FieldKey::Specifier.as_str()
    }

    /// Stage `author`'s edits in a fresh [`CowData`] overlay over `base`, then
    /// derive the change record from the staged overlay — the path a layer takes
    /// at commit, before flushing the overlay into the backend.
    fn derive(base: Data, author: impl FnOnce(&mut CowData<Data>)) -> ChangeList {
        let mut cow = CowData::new(base);
        author(&mut cow);
        ChangeList::from_overlay(&cow)
    }

    /// Authors an `over` carrying a `references` opinion into `cow` in one
    /// window, the way `define_prim` / `override_prim` + `add_reference` do.
    fn create_over_with_reference(cow: &mut CowData<Data>, path: &Path) {
        cow.create_spec(path.clone(), SpecType::Prim);
        cow.set_field(path, FieldKey::Specifier.as_str(), Value::Specifier(Specifier::Over));
        cow.set_field(
            path,
            FieldKey::References.as_str(),
            Value::ReferenceListOp(ReferenceListOp::default()),
        );
    }

    /// `merge_from` combines entries at the same path rather than duplicating
    /// it: one merged entry whose flags and authored-field set are the union.
    #[test]
    fn merge_combines_same_path() {
        let mut a = ChangeList::new();
        a.entry_mut(&p("/P")).flags |= ChangeFlags::CHANGE_RELATIONSHIP_TARGETS;
        a.entry_mut(&p("/P"))
            .info_changed
            .insert(FieldKey::TargetPaths.as_str().into());

        let mut b = ChangeList::new();
        b.entry_mut(&p("/P")).flags |= ChangeFlags::ADD_PROPERTY;
        b.entry_mut(&p("/P"))
            .info_changed
            .insert(FieldKey::ConnectionPaths.as_str().into());

        a.merge_from(&b);

        let same: Vec<_> = a.entries().iter().filter(|(path, _)| path == &p("/P")).collect();
        assert_eq!(same.len(), 1, "the path is merged, not duplicated");
        let entry = &same[0].1;
        assert!(entry.flags.contains(ChangeFlags::CHANGE_RELATIONSHIP_TARGETS));
        assert!(entry.flags.contains(ChangeFlags::ADD_PROPERTY));
        assert!(entry.info_changed.iter().any(|t| t == FieldKey::TargetPaths.as_str()));
        assert!(entry
            .info_changed
            .iter()
            .any(|t| t == FieldKey::ConnectionPaths.as_str()));
    }

    #[test]
    fn created_over_records_arc_not_specifier() {
        let cl = derive(Data::new(), |c| create_over_with_reference(c, &p("/X")));
        let entry = &cl.entries()[0].1;
        assert!(entry.flags.contains(ChangeFlags::ADD_INERT_PRIM));
        assert!(entry.info_changed.iter().any(|t| references(t)));
        assert!(!entry.info_changed.iter().any(|t| specifier(t)));
    }

    /// A created `over` with only its auto-stamped `specifier` records the add
    /// and no spurious `specifier` change — the auto-created-ancestor case.
    #[test]
    fn created_over_suppresses_specifier() {
        let cl = derive(Data::new(), |c| {
            c.create_spec(p("/X"), SpecType::Prim);
            c.set_field(
                &p("/X"),
                FieldKey::Specifier.as_str(),
                Value::Specifier(Specifier::Over),
            );
        });
        let entry = &cl.entries()[0].1;
        assert!(entry.flags.contains(ChangeFlags::ADD_INERT_PRIM));
        assert!(entry.info_changed.is_empty());
    }

    /// A created `def`/`class` is a non-inert add; an attribute or relationship
    /// is a property add.
    #[test]
    fn add_flag_by_kind() {
        let cl = derive(Data::new(), |c| {
            c.create_spec(p("/D"), SpecType::Prim);
            c.set_field(&p("/D"), FieldKey::Specifier.as_str(), Value::Specifier(Specifier::Def));
            c.create_spec(p("/D.attr"), SpecType::Attribute);
        });
        let prim = cl.iter().find(|(path, _)| path == &p("/D")).expect("prim entry");
        assert!(prim.1.flags.contains(ChangeFlags::ADD_NON_INERT_PRIM));
        let attr = cl.iter().find(|(path, _)| path == &p("/D.attr")).expect("attr entry");
        assert!(attr.1.flags.contains(ChangeFlags::ADD_PROPERTY));
    }

    /// Erasing an `over` surfaces its authored fields (except `specifier`), so a
    /// structural removal carries the same signal as the matching add.
    #[test]
    fn erased_over_records_fields() {
        let mut base = Data::new();
        base.create_spec(p("/X"), SpecType::Prim);
        base.set_field(
            &p("/X"),
            FieldKey::Specifier.as_str(),
            Value::Specifier(Specifier::Over),
        );
        base.set_field(
            &p("/X"),
            FieldKey::References.as_str(),
            Value::ReferenceListOp(ReferenceListOp::default()),
        );

        let cl = derive(base, |c| c.erase_spec(&p("/X")));
        let entry = &cl.entries()[0].1;
        assert!(entry.flags.contains(ChangeFlags::REMOVE_INERT_PRIM));
        assert!(entry.info_changed.iter().any(|t| references(t)));
        assert!(!entry.info_changed.iter().any(|t| specifier(t)));
    }

    /// Replacing an existing `over` (which carried a composition arc) by
    /// re-creating it as a plain `over` surfaces the dropped `references` field,
    /// so the teardown is not lost — a create-over-base is symmetric with an
    /// erase.
    #[test]
    fn recreated_over_records_dropped_field() {
        let mut base = Data::new();
        base.create_spec(p("/X"), SpecType::Prim);
        base.set_field(
            &p("/X"),
            FieldKey::Specifier.as_str(),
            Value::Specifier(Specifier::Over),
        );
        base.set_field(
            &p("/X"),
            FieldKey::References.as_str(),
            Value::ReferenceListOp(ReferenceListOp::default()),
        );

        // Re-create /X as a plain `over` with no references, in one window.
        let cl = derive(base, |c| {
            c.create_spec(p("/X"), SpecType::Prim);
            c.set_field(
                &p("/X"),
                FieldKey::Specifier.as_str(),
                Value::Specifier(Specifier::Over),
            );
        });
        let entry = &cl.entries()[0].1;
        assert!(entry.flags.contains(ChangeFlags::REMOVE_INERT_PRIM));
        assert!(entry.info_changed.iter().any(|t| references(t)));
    }

    /// A spec freshly created (with field writes) and erased in the same window
    /// cancels out completely: it never reaches the base, so nothing is derived.
    #[test]
    fn created_then_erased_cancels() {
        let cl = derive(Data::new(), |c| {
            create_over_with_reference(c, &p("/X"));
            c.erase_spec(&p("/X"));
        });
        assert!(cl.is_empty());
    }

    /// Re-creating (replacing) a pre-existing spec and then erasing it in one
    /// window still records the removal: the overlay tombstones the base spec,
    /// unlike a fresh create+erase that leaves no trace.
    #[test]
    fn recreated_then_erased_records_removal() {
        let mut base = Data::new();
        base.create_spec(p("/X"), SpecType::Prim);
        base.set_field(
            &p("/X"),
            FieldKey::Specifier.as_str(),
            Value::Specifier(Specifier::Over),
        );

        let cl = derive(base, |c| {
            c.create_spec(p("/X"), SpecType::Prim);
            c.erase_spec(&p("/X"));
        });
        assert!(cl.entries()[0].1.flags.contains(ChangeFlags::REMOVE_INERT_PRIM));
    }

    /// Editing relationship targets / attribute connections sets the dedicated
    /// shape flag, keyed off the field name.
    #[test]
    fn target_and_connection_flags() {
        let mut base = Data::new();
        base.create_spec(p("/P.rel"), SpecType::Relationship);
        base.create_spec(p("/P.attr"), SpecType::Attribute);

        let cl = derive(base, |c| {
            c.set_field(
                &p("/P.rel"),
                FieldKey::TargetPaths.as_str(),
                Value::PathListOp(PathListOp::default()),
            );
            c.set_field(
                &p("/P.attr"),
                FieldKey::ConnectionPaths.as_str(),
                Value::PathListOp(PathListOp::default()),
            );
        });
        let rel = cl.iter().find(|(path, _)| path == &p("/P.rel")).expect("rel entry");
        assert!(rel.1.flags.contains(ChangeFlags::CHANGE_RELATIONSHIP_TARGETS));
        let attr = cl.iter().find(|(path, _)| path == &p("/P.attr")).expect("attr entry");
        assert!(attr.1.flags.contains(ChangeFlags::CHANGE_ATTRIBUTE_CONNECTION));
    }

    /// Re-authoring a field with the value the base already holds nets to no
    /// change — the derived record is more precise than a per-write log.
    #[test]
    fn idempotent_set_no_change() {
        let mut base = Data::new();
        base.create_spec(p("/P"), SpecType::Prim);
        base.set_field(
            &p("/P"),
            FieldKey::TypeName.as_str(),
            Value::Token(tf::Token::from("Xform")),
        );

        let cl = derive(base, |c| {
            c.set_field(
                &p("/P"),
                FieldKey::TypeName.as_str(),
                Value::Token(tf::Token::from("Xform")),
            );
        });
        assert!(cl.is_empty());
    }

    /// Adding a field the base lacks and erasing it in the same window nets to
    /// no change.
    #[test]
    fn add_then_erase_field_no_change() {
        let mut base = Data::new();
        base.create_spec(p("/P"), SpecType::Prim);

        let cl = derive(base, |c| {
            c.set_field(
                &p("/P"),
                FieldKey::TypeName.as_str(),
                Value::Token(tf::Token::from("Xform")),
            );
            c.erase_field(&p("/P"), FieldKey::TypeName.as_str());
        });
        assert!(cl.is_empty());
    }

    /// A child-name-only edit is bookkeeping: no shape flags, and its only
    /// authored field is a child-name list.
    #[test]
    fn child_name_only_is_bookkeeping() {
        let mut base = Data::new();
        base.create_spec(p("/P"), SpecType::Prim);

        let cl = derive(base, |c| {
            c.set_field(
                &p("/P"),
                ChildrenKey::PrimChildren.as_str(),
                Value::TokenVec(vec![tf::Token::from("Child")]),
            );
        });
        assert!(cl.entries()[0].1.is_child_bookkeeping());
    }

    /// Authoring a `def` prim tree through [`PrimSpec`] — the real layer path —
    /// records a non-inert add at the leaf, inert adds for the auto-created
    /// `over` ancestors, and a property add for an attribute. The auto-stamped
    /// `specifier` folds into the add; an explicit `typeName` surfaces in
    /// `info_changed`.
    #[test]
    fn records_prim_tree_adds() {
        let cl = derive(rooted(), |c| {
            PrimSpec::new(c, "/A/B/C", Specifier::Def, "Xform").unwrap();
            AttributeSpec::new(c, "/A/B/C.size", "double", Variability::Varying, true).unwrap();
        });
        assert!(has_flag(&cl, "/A", ChangeFlags::ADD_INERT_PRIM));
        assert!(has_flag(&cl, "/A/B", ChangeFlags::ADD_INERT_PRIM));
        assert!(has_flag(&cl, "/A/B/C", ChangeFlags::ADD_NON_INERT_PRIM));
        assert!(has_flag(&cl, "/A/B/C.size", ChangeFlags::ADD_PROPERTY));
        let leaf = &cl.iter().find(|(pp, _)| pp == &p("/A/B/C")).unwrap().1.info_changed;
        assert!(leaf.iter().any(|t| t == FieldKey::TypeName.as_str()));
        assert!(!leaf.iter().any(|t| specifier(t)));
    }

    /// `PrimSpec::over` creates missing specs as `over`, recording inert adds.
    #[test]
    fn over_records_inert() {
        let cl = derive(rooted(), |c| {
            PrimSpec::over(c, "/X/Y").unwrap();
        });
        assert!(has_flag(&cl, "/X", ChangeFlags::ADD_INERT_PRIM));
        assert!(has_flag(&cl, "/X/Y", ChangeFlags::ADD_INERT_PRIM));
    }

    /// A metadata write on a pre-existing prim records the field in
    /// `info_changed` with no add flag.
    #[test]
    fn metadata_on_existing_prim() {
        let mut base = rooted();
        PrimSpec::new(&mut base, "/A", Specifier::Def, "").unwrap();

        let cl = derive(base, |c| {
            c.set_field(&p("/A"), FieldKey::Kind.as_str(), Value::token("component"));
        });
        let e = &cl.iter().find(|(pp, _)| pp == &p("/A")).unwrap().1;
        assert!(e.flags.is_empty());
        assert!(e.info_changed.iter().any(|t| t == FieldKey::Kind.as_str()));
    }

    /// A root-metadata edit that also materializes the pseudo-root spec still
    /// records the field change — the scaffolding create must not swallow the
    /// `defaultPrim` write.
    #[test]
    fn metadata_materializes_pseudo_root() {
        let cl = derive(Data::new(), |c| {
            c.create_spec(Path::abs_root(), SpecType::PseudoRoot);
            c.set_field(&Path::abs_root(), FieldKey::DefaultPrim.as_str(), Value::token("World"));
        });
        let e = &cl.iter().find(|(pp, _)| pp.is_abs_root()).unwrap().1;
        assert!(e.info_changed.iter().any(|t| t == FieldKey::DefaultPrim.as_str()));
    }

    /// Re-defining an existing `def` with the same type, through the real
    /// authoring path, records nothing.
    #[test]
    fn redundant_define_no_change() {
        let mut base = rooted();
        PrimSpec::new(&mut base, "/A", Specifier::Def, "Xform").unwrap();

        let cl = derive(base, |c| {
            PrimSpec::new(c, "/A", Specifier::Def, "Xform").unwrap();
        });
        assert!(cl.is_empty());
    }
}
