//! Per-layer change descriptions consumed by composition invalidation.
//!
//! A [`ChangeList`] is built at the Stage authoring callsite and handed to
//! [`pcp::Changes`](crate::pcp::Changes) so the composition cache can
//! invalidate surgically instead of dropping every cached prim index.
//!
//! Unlike C++ `SdfChangeList`, this is not produced natively by [`Layer`]
//! mutations — sdf authoring methods take no events. Stage (the only
//! current author) synthesizes the list because it knows the path and
//! operation kind statically.
//!
//! [`Layer`]: super::Layer
//
// TODO: push change-list emission into `Layer`/`AbstractData` so anyone
// mutating a layer (not just `Stage`) produces an authoritative change
// record. Until then, direct `Layer::*` writes bypassing `Stage` leave
// any open `Stage` referring to that layer with stale cache state.
//
// TODO: add `old_path: Option<Path>` and a `RenameChanges` channel for
// namespace edits once `Layer` exposes a rename API. C++
// `SdfChangeList::Entry::oldPath` + `PcpChanges::_renameChanges` are the
// reference shape. Today no `Layer` method renames a prim, so the field
// would have no producer.

use std::collections::BTreeSet;

use bitflags::bitflags;

use super::Path;

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
    /// Names of `FieldKey`s whose value was authored at this path.
    pub info_changed: BTreeSet<&'static str>,
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

    /// Record [`ChangeFlags::ADD_INERT_PRIM`] for each path: the inert `over`
    /// prim specs an authoring call auto-created for the edited spec's chain.
    pub fn add_inert_prims(&mut self, paths: impl IntoIterator<Item = Path>) {
        for path in paths {
            self.entry_mut(&path).flags |= ChangeFlags::ADD_INERT_PRIM;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entry_mut_dedups_same_path() {
        let mut cl = ChangeList::new();
        let p = Path::abs_root();
        cl.entry_mut(&p).flags |= ChangeFlags::ADD_NON_INERT_PRIM;
        cl.entry_mut(&p).info_changed.insert("specifier");
        assert_eq!(cl.entries().len(), 1);
        assert!(cl.entries()[0].1.flags.contains(ChangeFlags::ADD_NON_INERT_PRIM));
        assert!(cl.entries()[0].1.info_changed.contains("specifier"));
    }

    #[test]
    fn empty_until_first_entry() {
        let mut cl = ChangeList::new();
        assert!(cl.is_empty());
        cl.entry_mut(&Path::abs_root());
        assert!(!cl.is_empty());
    }
}
