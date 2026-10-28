//! The list-valued arc fields of a prim as the edit target authors them.

use std::hash::Hash;
use std::marker::PhantomData;

use crate::{sdf, vt};

use super::{Prim, Stage, StageAuthoringError};

/// A list-valued arc field of a prim, edited on the stage's edit target the
/// way C++ `UsdInherits`, `UsdSpecializes`, `UsdReferences` and
/// `UsdPayloads` edit theirs through their shared `Usd_ListEditImpl`; `T` is
/// what the list holds. [`Prim::inherits`], [`Prim::specializes`],
/// [`Prim::references`] and [`Prim::payloads`] hand one out.
pub struct ListEdit<T> {
    prim: Prim,
    field: sdf::FieldKey,
    item: PhantomData<T>,
}

/// What a [`ListEdit`] lists: an item the edit target authors once it is
/// translated (C++ `Usd_ListEditImplBase::_TranslatePath`).
pub trait ListItem: Clone + PartialEq + Hash + Sized {
    /// `self` as the edit target of `stage` authors it.
    fn translate(self, stage: &Stage) -> Result<Self, StageAuthoringError>;
}

/// An argument naming an item of a list field: whatever a path converts from
/// for a path-valued field, and a reference or payload for its own.
pub trait IntoItem<T>: TryInto<T, Error: Into<sdf::PathParseError>> {}

impl<T, I: TryInto<T, Error: Into<sdf::PathParseError>>> IntoItem<T> for I {}

/// Where an item is put in a list op (C++ `UsdListPosition`): the prepended
/// or appended list, at its front or back, or the explicit list where the op
/// is explicit, at the end the position names. The default is the back of
/// the prepended list, where C++ puts an item unless told otherwise.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum ListPosition {
    /// Stronger than every other item the layer prepends.
    FrontOfPrepend,
    /// Weaker than the other items the layer prepends.
    #[default]
    BackOfPrepend,
    /// Stronger than every other item the layer appends.
    FrontOfAppend,
    /// Weaker than the other items the layer appends.
    BackOfAppend,
}

impl<T: ListItem> ListEdit<T>
where
    sdf::ListOp<T>: Into<vt::Value> + TryFrom<vt::Value>,
{
    /// The editor over `field` of `prim`, which the prim's own accessor
    /// hands out.
    pub(super) fn new(prim: Prim, field: sdf::FieldKey) -> Self {
        Self {
            prim,
            field,
            item: PhantomData,
        }
    }

    /// Author the field as the explicit list `items`, strongest first (C++
    /// `SetInherits` and kin), each translated as [`add`](Self::add)
    /// translates one.
    pub fn set(&self, items: impl IntoIterator<Item: IntoItem<T>>) -> Result<(), StageAuthoringError> {
        let items = items
            .into_iter()
            .map(|item| -> Result<T, StageAuthoringError> { into_item(item)?.translate(self.prim.stage()) })
            .collect::<Result<Vec<_>, _>>()?;
        self.prim
            .clone()
            .edit(|spec| Ok(spec.edit_list(self.field, |op| *op = sdf::ListOp::explicit(items))?))?;
        Ok(())
    }

    /// Put `item` at the back of the edit target's prepended list, where C++
    /// `AddInherit` and kin put one unless told otherwise; see
    /// [`add_at`](Self::add_at).
    pub fn add(&self, item: impl IntoItem<T>) -> Result<(), StageAuthoringError> {
        self.add_at(item, ListPosition::default())
    }

    /// Put `item` at `position` in the edit target's list op (C++
    /// `AddInherit` and kin); see [`ListPosition`]. A path is mapped into the
    /// edit target's layer namespace, a root prim's path standing as given,
    /// and one the mapping does not reach is
    /// [`OutsideEditTarget`](StageAuthoringError::OutsideEditTarget); a
    /// reference or payload into another layer is authored as given.
    pub fn add_at(&self, item: impl IntoItem<T>, position: ListPosition) -> Result<(), StageAuthoringError> {
        let item = into_item(item)?.translate(self.prim.stage())?;
        self.prim
            .clone()
            .edit(|spec| Ok(spec.edit_list(self.field, |op| insert(op, item, position))?))?;
        Ok(())
    }

    /// Remove `item` from the composed list (C++ `RemoveInherit` and kin):
    /// dropped from the lists the edit target contributes it through and,
    /// unless its op is explicit, recorded as deleted so a weaker layer's
    /// copy goes too. The item is translated as [`add`](Self::add)
    /// translates one.
    pub fn remove(&self, item: impl IntoItem<T>) -> Result<(), StageAuthoringError> {
        let item = into_item(item)?.translate(self.prim.stage())?;
        self.prim.clone().edit(|spec| {
            Ok(spec.edit_list(self.field, |op| {
                op.remove(&item);
            })?)
        })?;
        Ok(())
    }

    /// Drop the edit target's opinion (C++ `ClearInherits` and kin).
    pub fn clear(&self) -> Result<(), StageAuthoringError> {
        self.prim.clone().clear_metadata(self.field.as_str())?;
        Ok(())
    }
}

impl ListItem for sdf::Path {
    fn translate(self, stage: &Stage) -> Result<Self, StageAuthoringError> {
        translate_prim_path(stage, self)
    }
}

impl ListItem for sdf::Reference {
    fn translate(mut self, stage: &Stage) -> Result<Self, StageAuthoringError> {
        self.prim_path = translate_arc_path(stage, &self.asset_path, self.prim_path)?;
        Ok(self)
    }
}

impl ListItem for sdf::Payload {
    fn translate(mut self, stage: &Stage) -> Result<Self, StageAuthoringError> {
        self.prim_path = translate_arc_path(stage, &self.asset_path, self.prim_path)?;
        Ok(self)
    }
}

/// Puts `item` at `position` in `op` (C++ `Usd_InsertListItem`); see
/// [`ListPosition`]. An item the list holds already is moved there.
pub(super) fn insert<T: Clone + PartialEq + Hash>(op: &mut sdf::ListOp<T>, item: T, position: ListPosition) {
    let list = match (op.is_explicit(), position) {
        (true, _) => sdf::ListOpType::Explicit,
        (false, ListPosition::FrontOfPrepend | ListPosition::BackOfPrepend) => sdf::ListOpType::Prepended,
        (false, ListPosition::FrontOfAppend | ListPosition::BackOfAppend) => sdf::ListOpType::Appended,
    };
    if matches!(position, ListPosition::FrontOfPrepend | ListPosition::FrontOfAppend) {
        op.prepend_to(list, item);
    } else {
        op.append_to(list, item);
    }
}

/// `item` as the item it names, or what parsing it hit.
fn into_item<T>(item: impl IntoItem<T>) -> Result<T, sdf::PathParseError> {
    item.try_into().map_err(Into::into)
}

/// `path` as the edit target of `stage` authors an arc's prim path (C++
/// `Usd_ListEditImplBase::_TranslatePath` over a path C++
/// `SdfSchema::IsValidInheritPath` and kin admit): an absolute prim path
/// less its variant selections, a root prim's as given, any other mapped
/// into the target's layer namespace, and one the mapping does not reach
/// refused as [`OutsideEditTarget`](StageAuthoringError::OutsideEditTarget).
fn translate_prim_path(stage: &Stage, path: sdf::Path) -> Result<sdf::Path, StageAuthoringError> {
    let path = path.strip_variant_selections();
    if !path.is_abs() || !path.is_prim() {
        return Err(sdf::AuthoringError::InvalidPath {
            path,
            reason: "an arc names an absolute prim path",
        }
        .into());
    }
    if path.is_root_prim() {
        return Ok(path);
    }
    stage.map_to_spec_target_path(&path)
}

/// The prim path of a reference or payload to `asset_path` as the edit
/// target of `stage` authors it (the reference overload of C++
/// `Usd_ListEditImplBase::_TranslatePath`): one into another layer, or an
/// empty one, stands as given; an internal arc's is a prim path of this
/// stage, translated as [`translate_prim_path`] translates one.
fn translate_arc_path(stage: &Stage, asset_path: &str, prim_path: sdf::Path) -> Result<sdf::Path, StageAuthoringError> {
    if !asset_path.is_empty() || prim_path.is_empty() {
        return Ok(prim_path);
    }
    translate_prim_path(stage, prim_path)
}

#[cfg(test)]
mod tests {
    use std::slice;

    use super::*;

    use crate::Result;
    use crate::pcp;
    use crate::sdf::path::tests::strings;
    use crate::usd::stage::tests::{authored, reference_scene, stage};

    /// The paths of the nodes `arc` introduces under `prim`.
    fn arcs(prim: &Prim, arc: pcp::ArcType) -> Result<Vec<String>> {
        Ok(prim
            .prim_index()
            .graph()?
            .nodes()
            .filter(|node| node.arc() == arc)
            .map(|node| node.path().to_string())
            .collect())
    }

    #[test]
    fn specializes_round_trip() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/Base")?;
        let child = stage.define_prim("/Child")?;
        child.specializes().set(["/Base"])?;
        assert_eq!(arcs(&child, pcp::ArcType::Specialize)?, ["/Base"]);
        child.specializes().clear()?;
        assert!(arcs(&child, pcp::ArcType::Specialize)?.is_empty());
        Ok(())
    }

    /// A target authored through a reference arc's edit target lands in the
    /// referenced namespace; a root prim's path stands as given, and one the
    /// mapping does not reach is refused.
    #[test]
    fn specializes_through_reference() -> Result<()> {
        let (_dir, stage, child, target) =
            reference_scene("def \"Base\"\n{\n}\n\n", "    def \"Sibling\"\n    {\n    }\n")?;
        child.specializes().set(["/Child/Sibling", "/Base"])?;
        let layer = stage.layer(target.layer_identifier()).expect("the referenced layer");
        let op: sdf::PathListOp = authored(&layer, "/R", sdf::FieldKey::Specializes).expect("authored");
        assert_eq!(strings(op.explicit_items()), ["/R/Sibling", "/Base"]);

        let refused = child.specializes().set(["/Elsewhere/Deep"]);
        assert!(
            matches!(refused, Err(StageAuthoringError::OutsideEditTarget { .. })),
            "{refused:?}"
        );
        Ok(())
    }

    /// A target that is not an absolute prim path is refused.
    #[test]
    fn specializes_refuses_non_prims() -> Result<()> {
        let stage = stage()?;
        let child = stage.define_prim("/Child")?;
        for target in ["/Base.attr", "/", "Base"] {
            assert!(child.specializes().set([target]).is_err(), "{target}");
        }
        Ok(())
    }

    #[test]
    fn inherits_round_trip() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/Class")?;
        let child = stage.define_prim("/Child")?;
        child.inherits().add("/Class")?;
        assert_eq!(arcs(&child, pcp::ArcType::Inherit)?, ["/Class"]);
        child.inherits().remove("/Class")?;
        assert!(arcs(&child, pcp::ArcType::Inherit)?.is_empty());
        let op: sdf::PathListOp =
            authored(&stage.root_layer(), "/Child", sdf::FieldKey::InheritPaths).expect("authored");
        assert_eq!(strings(op.deleted_items()), ["/Class"]);
        Ok(())
    }

    /// Each position names a list and an end of it, an explicit op takes
    /// every addition into its explicit list, and an item held already
    /// moves to the position asked for.
    #[test]
    fn add_positions() -> Result<()> {
        let stage = stage()?;
        let child = stage.define_prim("/Child")?;
        let inherits = child.inherits();
        inherits.add("/B")?;
        inherits.add_at("/A", ListPosition::FrontOfPrepend)?;
        inherits.add_at("/C", ListPosition::BackOfAppend)?;
        inherits.add_at("/D", ListPosition::FrontOfAppend)?;
        inherits.add("/A")?;
        let op: sdf::PathListOp =
            authored(&stage.root_layer(), "/Child", sdf::FieldKey::InheritPaths).expect("authored");
        assert!(!op.is_explicit());
        assert_eq!(strings(op.prepended_items()), ["/B", "/A"]);
        assert_eq!(strings(op.appended_items()), ["/D", "/C"]);

        inherits.set(["/A", "/B"])?;
        inherits.add("/C")?;
        inherits.add_at("/B", ListPosition::FrontOfAppend)?;
        let op: sdf::PathListOp =
            authored(&stage.root_layer(), "/Child", sdf::FieldKey::InheritPaths).expect("authored");
        assert!(op.is_explicit());
        assert_eq!(strings(op.explicit_items()), ["/B", "/A", "/C"]);
        Ok(())
    }

    /// Removing from a non-explicit op records the deletion, with nothing
    /// of its own to drop as well; from an explicit one it drops the item.
    #[test]
    fn remove_records_delete() -> Result<()> {
        let stage = stage()?;
        let child = stage.define_prim("/Child")?;
        let inherits = child.inherits();
        inherits.add("/A")?;
        inherits.remove("/B")?;
        let op: sdf::PathListOp =
            authored(&stage.root_layer(), "/Child", sdf::FieldKey::InheritPaths).expect("authored");
        assert_eq!(strings(op.prepended_items()), ["/A"]);
        assert_eq!(strings(op.deleted_items()), ["/B"]);

        inherits.set(["/A", "/B"])?;
        inherits.remove("/A")?;
        let op: sdf::PathListOp =
            authored(&stage.root_layer(), "/Child", sdf::FieldKey::InheritPaths).expect("authored");
        assert_eq!(strings(op.explicit_items()), ["/B"]);
        assert!(op.deleted_items().is_empty());
        Ok(())
    }

    /// An internal reference's prim path is mapped through the edit target;
    /// one into another layer, or an empty one, is authored as given.
    #[test]
    fn references_through_reference() -> Result<()> {
        let (_dir, stage, child, target) = reference_scene("", "    def \"Sibling\"\n    {\n    }\n")?;
        let internal = sdf::Reference {
            prim_path: sdf::Path::new("/Child/Sibling")?,
            ..Default::default()
        };
        let external = sdf::Reference {
            asset_path: "other.usda".to_owned(),
            prim_path: sdf::Path::new("/Child/Sibling")?,
            ..Default::default()
        };
        child.references().set([internal, external.clone()])?;
        child.references().add(sdf::Reference::default())?;
        let layer = stage.layer(target.layer_identifier()).expect("the referenced layer");
        let op: sdf::ReferenceListOp = authored(&layer, "/R", sdf::FieldKey::References).expect("authored");
        assert_eq!(
            op.explicit_items(),
            [
                sdf::Reference {
                    prim_path: sdf::Path::new("/R/Sibling")?,
                    ..Default::default()
                },
                external,
                sdf::Reference::default(),
            ]
        );

        let refused = child.references().add(sdf::Reference {
            prim_path: sdf::Path::new("/Elsewhere/Deep")?,
            ..Default::default()
        });
        assert!(
            matches!(refused, Err(StageAuthoringError::OutsideEditTarget { .. })),
            "{refused:?}"
        );
        Ok(())
    }

    #[test]
    fn payloads_round_trip() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/Asset")?;
        let child = stage.define_prim("/Child")?;
        let payload = sdf::Payload {
            prim_path: sdf::Path::new("/Asset")?,
            ..Default::default()
        };
        child.payloads().add(payload.clone())?;
        let op: sdf::PayloadListOp = authored(&stage.root_layer(), "/Child", sdf::FieldKey::Payload).expect("authored");
        assert_eq!(op.prepended_items(), slice::from_ref(&payload));
        child.payloads().remove(payload.clone())?;
        let op: sdf::PayloadListOp = authored(&stage.root_layer(), "/Child", sdf::FieldKey::Payload).expect("authored");
        assert_eq!(op.deleted_items(), [payload]);
        child.payloads().clear()?;
        assert!(authored::<sdf::PayloadListOp>(&stage.root_layer(), "/Child", sdf::FieldKey::Payload).is_none());
        Ok(())
    }

    /// A field holding anything but a list op is refused, not overwritten.
    #[test]
    fn refuses_other_type() -> Result<()> {
        let stage = stage()?;
        let child = stage.define_prim("/Child")?;
        child
            .clone()
            .set_metadata(sdf::FieldKey::InheritPaths.as_str(), vt::Value::Int(1))?;
        assert!(child.inherits().add("/A").is_err());
        assert_eq!(
            authored::<vt::Value>(&stage.root_layer(), "/Child", sdf::FieldKey::InheritPaths),
            Some(vt::Value::Int(1))
        );
        Ok(())
    }
}
