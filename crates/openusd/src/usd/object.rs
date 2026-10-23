//! The metadata every composed object carries, and what a property adds.

use std::collections::HashMap;

use crate::{Error, Result, sdf};

use super::{Attribute, Prim, Relationship, Stage, StageAuthoringError};

/// A composed scene object, a prim or a property (C++ `UsdObject`). The
/// fields its provided methods read answer as unauthored where the value
/// held is of another type, as C++ answers with the field's fallback.
pub trait Object: Sized {
    /// The stage the object is on (C++ `UsdObject::GetStage`).
    fn stage(&self) -> &Stage;

    /// The object's composed namespace path (C++ `UsdObject::GetPath`).
    fn path(&self) -> &sdf::Path;

    /// The composed metadata field `key` decoded to `T`, falling back to
    /// what the object's schema declares (C++ `UsdObject::GetMetadata`).
    fn metadata<T>(&self, key: &str) -> Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: Into<Error>;

    /// Author the metadata field `key` on the edit target (C++
    /// `UsdObject::SetMetadata`).
    fn set_metadata(self, key: &'static str, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError>;

    /// Drop the edit target's opinion of the metadata field `key` (C++
    /// `UsdObject::ClearMetadata`).
    fn clear_metadata(self, key: &'static str) -> Result<Self, StageAuthoringError>;

    /// Whether a layer authors the metadata field `key` on the object (C++
    /// `UsdObject::HasAuthoredMetadata`). What the object's schema declares
    /// for the field is not an authored opinion.
    fn has_authored_metadata(&self, key: &str) -> Result<bool> {
        Ok(self.stage().field::<sdf::Value>(self.path(), key)?.is_some())
    }

    /// The composed `doc` field, `None` where neither a layer nor the
    /// object's schema declaration carries one (C++
    /// `UsdObject::GetDocumentation`).
    fn doc(&self) -> Result<Option<String>> {
        field(self, sdf::FieldKey::Documentation, sdf::Value::try_as_string)
    }

    /// Author the `doc` field (C++ `UsdObject::SetDocumentation`).
    fn set_doc(self, doc: impl Into<String>) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::Documentation.as_str(), sdf::Value::String(doc.into()))
    }

    /// Drop the local `doc` opinion (C++ `UsdObject::ClearDocumentation`).
    fn clear_doc(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::Documentation.as_str())
    }

    /// The composed `displayName`, the name a user interface shows (C++
    /// `UsdObject::GetDisplayName`).
    fn display_name(&self) -> Result<Option<String>> {
        field(self, sdf::FieldKey::DisplayName, sdf::Value::try_as_string)
    }

    /// Author the `displayName` (C++ `UsdObject::SetDisplayName`).
    fn set_display_name(self, name: impl Into<String>) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::DisplayName.as_str(), sdf::Value::String(name.into()))
    }

    /// Drop the local `displayName` opinion (C++
    /// `UsdObject::ClearDisplayName`).
    fn clear_display_name(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::DisplayName.as_str())
    }

    /// Whether the object is marked `hidden`, a hint to user interfaces,
    /// `false` where nothing says so (C++ `UsdObject::IsHidden`).
    fn is_hidden(&self) -> Result<bool> {
        Ok(field(self, sdf::FieldKey::Hidden, sdf::Value::try_as_bool)?.unwrap_or(false))
    }

    /// Author the `hidden` flag (C++ `UsdObject::SetHidden`).
    fn set_hidden(self, hidden: bool) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::Hidden.as_str(), sdf::Value::Bool(hidden))
    }

    /// Drop the local `hidden` opinion (C++ `UsdObject::ClearHidden`).
    fn clear_hidden(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::Hidden.as_str())
    }

    /// The composed `customData` dictionary, the user's own data, each key
    /// the strongest layer's (C++ `UsdObject::GetCustomData`).
    fn custom_data(&self) -> Result<Option<HashMap<String, sdf::Value>>> {
        field(self, sdf::FieldKey::CustomData, sdf::Value::try_as_dictionary)
    }

    /// Author the `customData` dictionary (C++ `UsdObject::SetCustomData`).
    fn set_custom_data(self, data: HashMap<String, sdf::Value>) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::CustomData.as_str(), sdf::Value::Dictionary(data))
    }

    /// Drop the local `customData` opinion (C++
    /// `UsdObject::ClearCustomData`).
    fn clear_custom_data(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::CustomData.as_str())
    }

    /// The composed `assetInfo` dictionary, what identifies the asset the
    /// object belongs to, each key the strongest layer's (C++
    /// `UsdObject::GetAssetInfo`).
    fn asset_info(&self) -> Result<Option<HashMap<String, sdf::Value>>> {
        field(self, sdf::FieldKey::AssetInfo, sdf::Value::try_as_dictionary)
    }

    /// Author the `assetInfo` dictionary (C++ `UsdObject::SetAssetInfo`).
    fn set_asset_info(self, info: HashMap<String, sdf::Value>) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::AssetInfo.as_str(), sdf::Value::Dictionary(info))
    }

    /// Drop the local `assetInfo` opinion (C++ `UsdObject::ClearAssetInfo`).
    fn clear_asset_info(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::AssetInfo.as_str())
    }
}

/// A composed property, an attribute or a relationship (C++
/// `UsdProperty`): the group a user interface files it under.
pub trait Property: Object {
    /// The composed `displayGroup`, `None` where none is authored or
    /// declared (C++ `UsdProperty::GetDisplayGroup`). Nested groups are
    /// `:`-joined.
    fn display_group(&self) -> Result<Option<String>> {
        field(self, sdf::FieldKey::DisplayGroup, sdf::Value::try_as_string)
    }

    /// Author the `displayGroup` (C++ `UsdProperty::SetDisplayGroup`).
    fn set_display_group(self, group: impl Into<String>) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::DisplayGroup.as_str(), sdf::Value::String(group.into()))
    }

    /// Drop the local `displayGroup` opinion (C++
    /// `UsdProperty::ClearDisplayGroup`).
    fn clear_display_group(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::DisplayGroup.as_str())
    }

    /// The `displayGroup` as the groups it nests, outermost first, an empty
    /// name between two `:` dropped (C++
    /// `UsdProperty::GetNestedDisplayGroups`).
    fn nested_display_groups(&self) -> Result<Vec<String>> {
        Ok(self
            .display_group()?
            .map(|group| {
                group
                    .split(':')
                    .filter(|name| !name.is_empty())
                    .map(str::to_owned)
                    .collect()
            })
            .unwrap_or_default())
    }

    /// Author the `displayGroup` as `groups` nested outermost first, an
    /// empty name left out (C++ `UsdProperty::SetNestedDisplayGroups`).
    fn set_nested_display_groups(
        self,
        groups: impl IntoIterator<Item: AsRef<str>>,
    ) -> Result<Self, StageAuthoringError> {
        let groups: Vec<String> = groups
            .into_iter()
            .filter(|group| !group.as_ref().is_empty())
            .map(|group| group.as_ref().to_owned())
            .collect();
        self.set_display_group(groups.join(":"))
    }
}

macro_rules! impl_object {
    ($($ty:ty),*) => {$(
        impl Object for $ty {
            fn stage(&self) -> &Stage {
                <$ty>::stage(self)
            }

            fn path(&self) -> &sdf::Path {
                <$ty>::path(self)
            }

            fn metadata<T>(&self, key: &str) -> Result<Option<T>>
            where
                T: TryFrom<sdf::Value>,
                T::Error: Into<Error>,
            {
                <$ty>::metadata(self, key)
            }

            fn set_metadata(self, key: &'static str, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
                <$ty>::set_metadata(self, key, value)
            }

            fn clear_metadata(self, key: &'static str) -> Result<Self, StageAuthoringError> {
                <$ty>::clear_metadata(self, key)
            }
        }
    )*};
}

impl_object!(Prim, Attribute, Relationship);

impl Property for Attribute {}

impl Property for Relationship {}

/// The composed field `key` of `object` as `decode` takes it out of the
/// value held; `None` where the field is unauthored or holds another type.
fn field<O: Object, T>(
    object: &O,
    key: sdf::FieldKey,
    decode: impl FnOnce(sdf::Value) -> Option<T>,
) -> Result<Option<T>> {
    Ok(object.metadata::<sdf::Value>(key.as_str())?.and_then(decode))
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::{Object, Property};
    use crate::usd::stage::tests::stage;
    use crate::{Result, sdf};

    /// The fields every object shares author and read back on a prim and
    /// an attribute alike, and clear to their fallbacks.
    #[test]
    fn object_fields_round_trip() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/A")?;
        let info: HashMap<String, sdf::Value> = [("name".to_owned(), sdf::Value::String("chair".into()))].into();
        let prim = prim
            .set_display_name("Chair")?
            .set_hidden(true)?
            .set_asset_info(info.clone())?
            .set_custom_data(info.clone())?;
        assert_eq!(prim.display_name()?.as_deref(), Some("Chair"));
        assert!(prim.is_hidden()?);
        assert!(prim.has_authored_metadata(sdf::FieldKey::Hidden.as_str())?);
        assert_eq!(prim.asset_info()?, Some(info.clone()));
        assert_eq!(prim.custom_data()?, Some(info));
        let prim = prim.clear_hidden()?.clear_display_name()?.clear_asset_info()?;
        assert!(!prim.is_hidden()?);
        assert_eq!(prim.display_name()?, None);
        assert_eq!(prim.asset_info()?, None);

        let attr = prim.create_attribute("size", "double")?.set_hidden(true)?;
        assert!(attr.is_hidden()?);
        Ok(())
    }

    /// A field holding a value of another type reads as unauthored.
    #[test]
    fn mistyped_field_unauthored() -> Result<()> {
        let stage = stage()?;
        let prim = stage
            .define_prim("/A")?
            .set_metadata(sdf::FieldKey::Hidden.as_str(), sdf::Value::Int(1))?
            .set_metadata(sdf::FieldKey::CustomData.as_str(), sdf::Value::String("oops".into()))?;
        assert!(!prim.is_hidden()?);
        assert_eq!(prim.custom_data()?, None);
        Ok(())
    }

    /// A property's display group splits into the groups it nests, empty
    /// names dropped either way.
    #[test]
    fn nested_display_groups() -> Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .create_attribute("size", "double")?
            .set_nested_display_groups(["Shape", "", "Size"])?;
        assert_eq!(attr.display_group()?.as_deref(), Some("Shape:Size"));
        assert_eq!(attr.nested_display_groups()?, ["Shape", "Size"]);
        let attr = attr.set_display_group(":Shape::Size:")?;
        assert_eq!(attr.nested_display_groups()?, ["Shape", "Size"]);
        assert!(attr.clear_display_group()?.nested_display_groups()?.is_empty());
        Ok(())
    }
}
