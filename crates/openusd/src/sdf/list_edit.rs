//! A spec's path-list field as it is edited.

use std::ops::DerefMut;

use crate::sdf;

/// A spec's path-list field as it is edited (C++ `SdfPathEditorProxy`, the
/// `SdfListEditorProxy` over `SdfPathKeyPolicy`), which
/// [`AttributeSpec::edit_connections`](sdf::AttributeSpec::edit_connections),
/// [`RelationshipSpec::edit_targets`](sdf::RelationshipSpec::edit_targets),
/// [`PrimSpec::edit_inherits`](sdf::PrimSpec::edit_inherits) and
/// [`PrimSpec::edit_specializes`](sdf::PrimSpec::edit_specializes) hand out.
/// Every path given is made absolute against the prim path the spec hands
/// the edit: its own, less its variant selections for a class arc, which
/// addresses the namespace composition maps it in. The list is written back
/// as [`Spec::edit_list`](sdf::Spec::edit_list) writes one.
///
/// TODO: refuse a path the field does not admit (C++
/// `SdfSchema::IsValidInheritPath` and kin behind
/// `Sdf_ListEditor::_ValidateEdit`) once the per-field `SpecDefinition` table
/// named at `usd::authoring::check_reserved` exists.
pub struct PathListEdit<'s, 'a, B> {
    spec: &'s mut sdf::Spec<'a, B>,
    key: sdf::FieldKey,
    /// The prim path every path of the list is anchored at.
    anchor: sdf::Path,
}

impl<'s, 'a, B> PathListEdit<'s, 'a, B>
where
    B: DerefMut<Target = dyn sdf::AbstractData + 'a>,
{
    /// The edit of the list `key` holds on `spec`, its paths anchored at the
    /// prim path `anchor`.
    pub(crate) fn new(spec: &'s mut sdf::Spec<'a, B>, key: sdf::FieldKey, anchor: sdf::Path) -> Self {
        Self { spec, key, anchor }
    }

    /// Author the list as the explicit list `paths`, which replaces what
    /// weaker layers list (C++ `ClearEditsAndMakeExplicit` with the explicit
    /// items set).
    pub fn set(self, paths: impl IntoIterator<Item: sdf::IntoPath>) -> Result<(), sdf::AuthoringError> {
        let paths = paths
            .into_iter()
            .map(|path| canonical(&self.anchor, path))
            .collect::<Result<Vec<_>, _>>()?;
        self.spec.edit_list(self.key, |op| *op = sdf::ListOp::explicit(paths))
    }

    /// Put `path` first among the prepended paths, as
    /// [`ListOp::prepend`](sdf::ListOp::prepend) puts it (C++ `Prepend`).
    pub fn prepend(self, path: impl sdf::IntoPath) -> Result<(), sdf::AuthoringError> {
        let path = canonical(&self.anchor, path)?;
        self.spec.edit_list(self.key, |op| op.prepend(path))
    }

    /// Put `path` last among the appended paths, as
    /// [`ListOp::append`](sdf::ListOp::append) puts it (C++ `Append`).
    pub fn append(self, path: impl sdf::IntoPath) -> Result<(), sdf::AuthoringError> {
        let path = canonical(&self.anchor, path)?;
        self.spec.edit_list(self.key, |op| op.append(path))
    }

    /// Remove `path` from the composed list, as
    /// [`ListOp::remove`](sdf::ListOp::remove) removes it (C++ `Remove`).
    /// Returns whether an opinion changed.
    pub fn remove(self, path: impl sdf::IntoPath) -> Result<bool, sdf::AuthoringError> {
        let path = canonical(&self.anchor, path)?;
        self.spec.edit_list(self.key, |op| op.remove(&path))
    }

    /// Drop `path` from the lists that contribute it, as
    /// [`ListOp::erase`](sdf::ListOp::erase) drops it (C++ `Erase`). Returns
    /// whether any held it.
    pub fn erase(self, path: impl sdf::IntoPath) -> Result<bool, sdf::AuthoringError> {
        let path = canonical(&self.anchor, path)?;
        self.spec.edit_list(self.key, |op| op.erase(&path))
    }

    /// Author the list as an explicit empty list, which hides what weaker
    /// layers list (C++ `ClearEditsAndMakeExplicit`).
    pub fn block(self) -> Result<(), sdf::AuthoringError> {
        self.spec.edit_list(self.key, |op| *op = sdf::PathListOp::explicit([]))
    }

    /// Drop the field (C++ `ClearEdits`).
    pub fn clear(self) {
        self.spec.erase(self.key.as_str());
    }

    /// Rewrite the list with `f`, as [`Spec::edit_list`](sdf::Spec::edit_list)
    /// rewrites one, over paths `f` has anchored itself.
    pub(crate) fn edit<R>(self, f: impl FnOnce(&mut sdf::PathListOp) -> R) -> Result<R, sdf::AuthoringError> {
        self.spec.edit_list(self.key, f)
    }
}

/// `path` made absolute against the prim path `anchor` (C++
/// `SdfPathKeyPolicy::Canonicalize`). A path left empty by the anchoring,
/// the empty path included, is
/// [`InvalidPath`](sdf::AuthoringError::InvalidPath).
pub(crate) fn canonical(anchor: &sdf::Path, path: impl sdf::IntoPath) -> Result<sdf::Path, sdf::AuthoringError> {
    let path = sdf::try_into_path(path)?;
    let absolute = anchor.make_absolute(&path);
    if absolute.is_empty() {
        return Err(sdf::AuthoringError::InvalidPath {
            path,
            reason: "the path is empty once anchored at the owning prim",
        });
    }
    Ok(absolute)
}

#[cfg(test)]
mod tests {
    use crate::sdf;
    use crate::sdf::path::tests::strings;
    use crate::sdf::spec::tests::data_with_spec;

    /// A relative path is anchored at the owning prim, whichever list it
    /// goes to or is matched against.
    #[test]
    fn relative_paths_anchored() -> Result<(), sdf::AuthoringError> {
        let (mut data, path) = data_with_spec("/A/B.rel", sdf::SpecType::Relationship);
        let mut rel = sdf::RelationshipSpecMut::get(&mut data, path).expect("relationship spec");
        rel.edit_targets().set(["../C", "D.x", "/E"])?;
        let op = rel.target_path_list().expect("authored");
        assert_eq!(strings(op.explicit_items()), ["/A/C", "/A/B/D.x", "/E"]);

        rel.edit_targets().clear();
        rel.edit_targets().prepend("../C")?;
        assert!(rel.edit_targets().remove("/A/C")?);
        let op = rel.target_path_list().expect("authored");
        assert!(op.prepended_items().is_empty());
        assert_eq!(strings(op.deleted_items()), ["/A/C"]);
        Ok(())
    }

    /// A connection anchored at the attribute's prim; the field goes once
    /// nothing contributes, an explicit empty list stays, and a clear drops
    /// either.
    #[test]
    fn erase_drops_field() -> Result<(), sdf::AuthoringError> {
        let (mut data, path) = data_with_spec("/A.in", sdf::SpecType::Attribute);
        let mut attr = sdf::AttributeSpecMut::get(&mut data, path).expect("attribute spec");
        attr.edit_connections().append("../B.out")?;
        let op = attr.connection_path_list().expect("authored");
        assert_eq!(strings(op.appended_items()), ["/B.out"]);

        assert!(attr.edit_connections().erase("/B.out")?);
        assert!(attr.connection_path_list().is_none());
        attr.edit_connections().block()?;
        assert!(attr.connection_path_list().is_some_and(|op| op.is_explicit()));
        attr.edit_connections().clear();
        attr.edit_connections().set([] as [sdf::Path; 0])?;
        assert!(attr.connection_path_list().is_some_and(|op| op.is_explicit()));
        attr.edit_connections().clear();
        assert!(attr.connection_path_list().is_none());
        Ok(())
    }

    /// A property authored in a variant anchors at the prim the variant
    /// belongs to, and a prim's arc lists at the prim less any variant
    /// selection along its path.
    #[test]
    fn variant_and_prim_anchors() -> Result<(), sdf::AuthoringError> {
        let (mut data, path) = data_with_spec("/A{v=x}.rel", sdf::SpecType::Relationship);
        let mut rel = sdf::RelationshipSpecMut::get(&mut data, path).expect("relationship spec");
        rel.edit_targets().set(["C", "../D"])?;
        let op = rel.target_path_list().expect("authored");
        assert_eq!(strings(op.explicit_items()), ["/A/C", "/D"]);

        let (mut data, path) = data_with_spec("/A{v=x}B", sdf::SpecType::Prim);
        let mut prim = sdf::PrimSpecMut::get(&mut data, path).expect("prim spec");
        prim.edit_specializes().append("C")?;
        let specializes: sdf::PathListOp = prim.get(sdf::FieldKey::Specializes).expect("authored");
        assert_eq!(strings(specializes.appended_items()), ["/A/B/C"]);

        let (mut data, path) = data_with_spec("/A/B", sdf::SpecType::Prim);
        let mut prim = sdf::PrimSpecMut::get(&mut data, path).expect("prim spec");
        prim.edit_inherits().prepend("../C")?;
        prim.edit_specializes().append("D")?;
        let inherits: sdf::PathListOp = prim.get(sdf::FieldKey::InheritPaths).expect("authored");
        assert_eq!(strings(inherits.prepended_items()), ["/A/C"]);
        let specializes: sdf::PathListOp = prim.get(sdf::FieldKey::Specializes).expect("authored");
        assert_eq!(strings(specializes.appended_items()), ["/A/B/D"]);
        Ok(())
    }

    /// Removing from a field nothing is authored on records the delete.
    #[test]
    fn remove_authors_delete() -> Result<(), sdf::AuthoringError> {
        let (mut data, path) = data_with_spec("/A.rel", sdf::SpecType::Relationship);
        let mut rel = sdf::RelationshipSpecMut::get(&mut data, path).expect("relationship spec");
        assert!(rel.edit_targets().remove("/B")?);
        let op = rel.target_path_list().expect("authored");
        assert_eq!(strings(op.deleted_items()), ["/B"]);
        assert!(!op.is_explicit());
        Ok(())
    }

    /// An empty path, and one the prim cannot anchor, are refused before
    /// anything is authored.
    #[test]
    fn unanchored_path_refused() {
        let (mut data, path) = data_with_spec("/A.rel", sdf::SpecType::Relationship);
        let mut rel = sdf::RelationshipSpecMut::get(&mut data, path).expect("relationship spec");
        for path in [sdf::Path::default(), sdf::path("../.y").expect("a path")] {
            let refused = rel.edit_targets().append(path);
            assert!(matches!(refused, Err(sdf::AuthoringError::InvalidPath { .. })));
        }
        assert!(rel.target_path_list().is_none());
    }
}
