//! The metadata every composed object carries, and what a property adds.

use crate::{Error, Result, sdf, vt};

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
        T: TryFrom<vt::Value>,
        T::Error: Into<Error>;

    /// Author the metadata field `key` on the edit target (C++
    /// `UsdObject::SetMetadata`).
    fn set_metadata(self, key: &'static str, value: impl Into<vt::Value>) -> Result<Self, StageAuthoringError>;

    /// Drop the edit target's opinion of the metadata field `key` (C++
    /// `UsdObject::ClearMetadata`).
    fn clear_metadata(self, key: &'static str) -> Result<Self, StageAuthoringError>;

    /// Rewrite with `f` the edit target's own opinion of the metadata field
    /// `key`: `f` sees the local value, and `None` from it erases the field.
    fn update_metadata(
        self,
        key: &'static str,
        f: impl FnOnce(Option<vt::Value>) -> Option<vt::Value>,
    ) -> Result<Self, StageAuthoringError>;

    /// The value the dictionary field `key` holds at `key_path`, as the
    /// layers compose it; the whole field for an empty path (C++
    /// `UsdObject::GetMetadataByDictKey`). See [`vt::Dictionary`] for
    /// key paths.
    fn metadata_by_key(&self, key: &str, key_path: &str) -> Result<Option<vt::Value>> {
        // TODO(perf): this composes and clones the whole dictionary to read one
        // key. A key-path form of `resolve_field` could read only `key_path` in
        // each layer's opinion and stop at the strongest layer holding a value
        // there that is not a dictionary, as C++ hands `keyPath` to its
        // metadata composer.
        Ok(at_key(self.metadata::<vt::Value>(key)?, key_path))
    }

    /// Whether a layer authors a value at `key_path` in the dictionary field
    /// `key`, or the field itself for an empty path (C++
    /// `UsdObject::HasAuthoredMetadataDictKey`).
    fn has_authored_metadata_key(&self, key: &str, key_path: &str) -> Result<bool> {
        let authored = self.stage().field::<vt::Value>(self.path(), key)?;
        Ok(at_key(authored, key_path).is_some())
    }

    /// Author `value` at `key_path` in the edit target's own opinion of the
    /// dictionary field `key`, leaving its other keys and what weaker layers
    /// author as they are; an empty path authors the whole field (C++
    /// `UsdObject::SetMetadataByDictKey`).
    fn set_metadata_by_key(
        self,
        key: &'static str,
        key_path: &str,
        value: impl Into<vt::Value>,
    ) -> Result<Self, StageAuthoringError> {
        if key_path.is_empty() {
            return self.set_metadata(key, value);
        }
        let value = self.stage().map_to_spec_value(self.path(), value);
        self.update_metadata(key, |local| {
            let mut dict = local.and_then(vt::Value::try_as_dictionary).unwrap_or_default();
            dict.set_at(key_path, value);
            Some(vt::Value::Dictionary(dict))
        })
    }

    /// Drop the edit target's own opinion at `key_path` in the dictionary
    /// field `key`, the field itself where nothing is left in it or the path
    /// is empty; a field holding no dictionary stays as it is (C++
    /// `UsdObject::ClearMetadataByDictKey`).
    fn clear_metadata_by_key(self, key: &'static str, key_path: &str) -> Result<Self, StageAuthoringError> {
        if key_path.is_empty() {
            return self.clear_metadata(key);
        }
        self.update_metadata(key, |local| match local {
            Some(vt::Value::Dictionary(mut dict)) => {
                dict.erase_at(key_path);
                (!dict.is_empty()).then_some(vt::Value::Dictionary(dict))
            }
            other => other,
        })
    }

    /// Whether a layer authors the metadata field `key` on the object (C++
    /// `UsdObject::HasAuthoredMetadata`). What the object's schema declares
    /// for the field is not an authored opinion.
    fn has_authored_metadata(&self, key: &str) -> Result<bool> {
        Ok(self.stage().field::<vt::Value>(self.path(), key)?.is_some())
    }

    /// The composed `doc` field, `None` where neither a layer nor the
    /// object's schema declaration carries one (C++
    /// `UsdObject::GetDocumentation`).
    fn doc(&self) -> Result<Option<String>> {
        field(self, sdf::FieldKey::Documentation, vt::Value::try_as_string)
    }

    /// Whether a layer authors the `doc` field (C++
    /// `UsdObject::HasAuthoredDocumentation`).
    fn has_authored_doc(&self) -> Result<bool> {
        self.has_authored_metadata(sdf::FieldKey::Documentation.as_str())
    }

    /// Author the `doc` field (C++ `UsdObject::SetDocumentation`).
    fn set_doc(self, doc: impl Into<String>) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::Documentation.as_str(), vt::Value::String(doc.into()))
    }

    /// Drop the local `doc` opinion (C++ `UsdObject::ClearDocumentation`).
    fn clear_doc(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::Documentation.as_str())
    }

    /// The composed `displayName`, the name a user interface shows (C++
    /// `UsdObject::GetDisplayName`).
    fn display_name(&self) -> Result<Option<String>> {
        field(self, sdf::FieldKey::DisplayName, vt::Value::try_as_string)
    }

    /// Whether a layer authors the `displayName` (C++
    /// `UsdObject::HasAuthoredDisplayName`).
    fn has_authored_display_name(&self) -> Result<bool> {
        self.has_authored_metadata(sdf::FieldKey::DisplayName.as_str())
    }

    /// Author the `displayName` (C++ `UsdObject::SetDisplayName`).
    fn set_display_name(self, name: impl Into<String>) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::DisplayName.as_str(), vt::Value::String(name.into()))
    }

    /// Drop the local `displayName` opinion (C++
    /// `UsdObject::ClearDisplayName`).
    fn clear_display_name(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::DisplayName.as_str())
    }

    /// Whether the object is marked `hidden`, a hint to user interfaces,
    /// `false` where nothing says so (C++ `UsdObject::IsHidden`).
    fn is_hidden(&self) -> Result<bool> {
        Ok(field(self, sdf::FieldKey::Hidden, vt::Value::try_as_bool)?.unwrap_or(false))
    }

    /// Whether a layer authors the `hidden` flag (C++
    /// `UsdObject::HasAuthoredHidden`).
    fn has_authored_hidden(&self) -> Result<bool> {
        self.has_authored_metadata(sdf::FieldKey::Hidden.as_str())
    }

    /// Author the `hidden` flag (C++ `UsdObject::SetHidden`).
    fn set_hidden(self, hidden: bool) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::Hidden.as_str(), vt::Value::Bool(hidden))
    }

    /// Drop the local `hidden` opinion (C++ `UsdObject::ClearHidden`).
    fn clear_hidden(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::Hidden.as_str())
    }

    /// The composed `customData` dictionary, the user's own data, each key
    /// the strongest layer's or else the schema's (C++
    /// `UsdObject::GetCustomData`).
    fn custom_data(&self) -> Result<Option<vt::Dictionary>> {
        field(self, sdf::FieldKey::CustomData, vt::Value::try_as_dictionary)
    }

    /// Whether a layer authors the `customData` dictionary (C++
    /// `UsdObject::HasAuthoredCustomData`).
    fn has_authored_custom_data(&self) -> Result<bool> {
        self.has_authored_metadata(sdf::FieldKey::CustomData.as_str())
    }

    /// Author the `customData` dictionary (C++ `UsdObject::SetCustomData`).
    fn set_custom_data(self, data: vt::Dictionary) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::CustomData.as_str(), vt::Value::Dictionary(data))
    }

    /// Drop the local `customData` opinion (C++
    /// `UsdObject::ClearCustomData`).
    fn clear_custom_data(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::CustomData.as_str())
    }

    /// The `customData` value at `key_path`, as
    /// [`metadata_by_key`](Self::metadata_by_key) reads one (C++
    /// `UsdObject::GetCustomDataByKey`).
    fn custom_data_by_key(&self, key_path: &str) -> Result<Option<vt::Value>> {
        self.metadata_by_key(sdf::FieldKey::CustomData.as_str(), key_path)
    }

    /// Author `value` at `key_path` in `customData` (C++
    /// `UsdObject::SetCustomDataByKey`).
    fn set_custom_data_by_key(self, key_path: &str, value: impl Into<vt::Value>) -> Result<Self, StageAuthoringError> {
        self.set_metadata_by_key(sdf::FieldKey::CustomData.as_str(), key_path, value)
    }

    /// Drop the local opinion at `key_path` in `customData` (C++
    /// `UsdObject::ClearCustomDataByKey`).
    fn clear_custom_data_by_key(self, key_path: &str) -> Result<Self, StageAuthoringError> {
        self.clear_metadata_by_key(sdf::FieldKey::CustomData.as_str(), key_path)
    }

    /// Whether a layer authors a `customData` value at `key_path` (C++
    /// `UsdObject::HasAuthoredCustomDataKey`).
    fn has_authored_custom_data_key(&self, key_path: &str) -> Result<bool> {
        self.has_authored_metadata_key(sdf::FieldKey::CustomData.as_str(), key_path)
    }

    /// The composed `assetInfo` dictionary, what identifies the asset the
    /// object belongs to, each key the strongest layer's or else the schema's
    /// (C++ `UsdObject::GetAssetInfo`).
    fn asset_info(&self) -> Result<Option<vt::Dictionary>> {
        field(self, sdf::FieldKey::AssetInfo, vt::Value::try_as_dictionary)
    }

    /// Whether a layer authors the `assetInfo` dictionary (C++
    /// `UsdObject::HasAuthoredAssetInfo`).
    fn has_authored_asset_info(&self) -> Result<bool> {
        self.has_authored_metadata(sdf::FieldKey::AssetInfo.as_str())
    }

    /// Author the `assetInfo` dictionary (C++ `UsdObject::SetAssetInfo`).
    fn set_asset_info(self, info: vt::Dictionary) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::AssetInfo.as_str(), vt::Value::Dictionary(info))
    }

    /// Drop the local `assetInfo` opinion (C++ `UsdObject::ClearAssetInfo`).
    fn clear_asset_info(self) -> Result<Self, StageAuthoringError> {
        self.clear_metadata(sdf::FieldKey::AssetInfo.as_str())
    }

    /// The `assetInfo` value at `key_path`, as
    /// [`metadata_by_key`](Self::metadata_by_key) reads one (C++
    /// `UsdObject::GetAssetInfoByKey`).
    fn asset_info_by_key(&self, key_path: &str) -> Result<Option<vt::Value>> {
        self.metadata_by_key(sdf::FieldKey::AssetInfo.as_str(), key_path)
    }

    /// Author `value` at `key_path` in `assetInfo` (C++
    /// `UsdObject::SetAssetInfoByKey`).
    fn set_asset_info_by_key(self, key_path: &str, value: impl Into<vt::Value>) -> Result<Self, StageAuthoringError> {
        self.set_metadata_by_key(sdf::FieldKey::AssetInfo.as_str(), key_path, value)
    }

    /// Drop the local opinion at `key_path` in `assetInfo` (C++
    /// `UsdObject::ClearAssetInfoByKey`).
    fn clear_asset_info_by_key(self, key_path: &str) -> Result<Self, StageAuthoringError> {
        self.clear_metadata_by_key(sdf::FieldKey::AssetInfo.as_str(), key_path)
    }

    /// Whether a layer authors an `assetInfo` value at `key_path` (C++
    /// `UsdObject::HasAuthoredAssetInfoKey`).
    fn has_authored_asset_info_key(&self, key_path: &str) -> Result<bool> {
        self.has_authored_metadata_key(sdf::FieldKey::AssetInfo.as_str(), key_path)
    }
}

/// A composed property, an attribute or a relationship (C++
/// `UsdProperty`): the group a user interface files it under.
pub trait Property: Object {
    /// The last part of the property's name, after its namespaces:
    /// `indices` for `primvars:normals:indices` (C++
    /// `UsdProperty::GetBaseName`).
    fn base_name(&self) -> &str {
        let name = property_name(self.path());
        name.rsplit_once(':').map_or(name, |(_, base)| base)
    }

    /// The namespaces of the property's name, `:`-joined, or `""` for a
    /// name with none: `primvars:normals` for `primvars:normals:indices`
    /// (C++ `UsdProperty::GetNamespace`).
    fn namespace(&self) -> &str {
        property_name(self.path())
            .rsplit_once(':')
            .map_or("", |(namespace, _)| namespace)
    }

    /// The parts of the property's name, outermost first (C++
    /// `UsdProperty::SplitName`).
    fn split_name(&self) -> Vec<&str> {
        let name = property_name(self.path());
        if name.is_empty() {
            return Vec::new();
        }
        name.split(':').collect()
    }

    /// The composed `displayGroup`, `None` where none is authored or
    /// declared (C++ `UsdProperty::GetDisplayGroup`). Nested groups are
    /// `:`-joined.
    fn display_group(&self) -> Result<Option<String>> {
        field(self, sdf::FieldKey::DisplayGroup, vt::Value::try_as_string)
    }

    /// Whether a layer authors the `displayGroup` (C++
    /// `UsdProperty::HasAuthoredDisplayGroup`).
    fn has_authored_display_group(&self) -> Result<bool> {
        self.has_authored_metadata(sdf::FieldKey::DisplayGroup.as_str())
    }

    /// Author the `displayGroup` (C++ `UsdProperty::SetDisplayGroup`).
    fn set_display_group(self, group: impl Into<String>) -> Result<Self, StageAuthoringError> {
        self.set_metadata(sdf::FieldKey::DisplayGroup.as_str(), vt::Value::String(group.into()))
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
                T: TryFrom<vt::Value>,
                T::Error: Into<Error>,
            {
                <$ty>::metadata(self, key)
            }

            fn set_metadata(self, key: &'static str, value: impl Into<vt::Value>) -> Result<Self, StageAuthoringError> {
                <$ty>::set_metadata(self, key, value)
            }

            fn clear_metadata(self, key: &'static str) -> Result<Self, StageAuthoringError> {
                <$ty>::clear_metadata(self, key)
            }

            fn update_metadata(
                self,
                key: &'static str,
                f: impl FnOnce(Option<vt::Value>) -> Option<vt::Value>,
            ) -> Result<Self, StageAuthoringError> {
                <$ty>::update_metadata(self, key, f)
            }
        }
    )*};
}

impl_object!(Prim, Attribute, Relationship);

impl Property for Attribute {}

impl Property for Relationship {}

/// The property name `path` ends with, namespaces included, or `""` where
/// it names no property.
fn property_name(path: &sdf::Path) -> &str {
    path.split_property().map_or("", |(_, name)| name)
}

/// The value at `key_path` in the dictionary `value` holds, or `value`
/// itself for an empty path.
fn at_key(value: Option<vt::Value>, key_path: &str) -> Option<vt::Value> {
    if key_path.is_empty() {
        return value;
    }
    value?.try_as_dictionary()?.get_at(key_path).cloned()
}

/// The composed field `key` of `object` as `decode` takes it out of the
/// value held; `None` where the field is unauthored or holds another type.
fn field<O: Object, T>(
    object: &O,
    key: sdf::FieldKey,
    decode: impl FnOnce(vt::Value) -> Option<T>,
) -> Result<Option<T>> {
    Ok(object.metadata::<vt::Value>(key.as_str())?.and_then(decode))
}

#[cfg(test)]
mod tests {
    use super::{Object, Property};
    use crate::usd::stage::tests::stage;
    use crate::usd::{SchemaRegistry, Stage};
    use crate::vt;
    use crate::{Result, sdf};

    /// The fields every object shares author and read back on a prim and
    /// an attribute alike, and clear to their fallbacks.
    #[test]
    fn object_fields_round_trip() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/A")?;
        let info: vt::Dictionary = [("name".to_owned(), vt::Value::String("chair".into()))].into();
        let prim = prim
            .set_display_name("Chair")?
            .set_hidden(true)?
            .set_asset_info(info.clone())?
            .set_custom_data(info.clone())?;
        assert_eq!(prim.display_name()?.as_deref(), Some("Chair"));
        assert!(prim.is_hidden()?);
        assert!(prim.has_authored_hidden()? && prim.has_authored_custom_data()?);
        assert!(!prim.has_authored_doc()?);
        assert_eq!(prim.asset_info()?, Some(info.clone()));
        assert_eq!(prim.custom_data()?, Some(info));
        let prim = prim.clear_hidden()?.clear_display_name()?.clear_asset_info()?;
        assert!(!prim.is_hidden()? && !prim.has_authored_hidden()?);
        assert!(!prim.has_authored_display_name()? && !prim.has_authored_asset_info()?);
        assert_eq!(prim.display_name()?, None);
        assert_eq!(prim.asset_info()?, None);

        let attr = prim.create_attribute("size", "double")?.set_hidden(true)?;
        assert!(attr.is_hidden()?);
        Ok(())
    }

    /// A dictionary field's value at a key path authors beside the field's
    /// other keys, on a prim and on each property, and clears back out,
    /// dropping the field once it holds nothing.
    #[test]
    fn dictionary_by_key() -> Result<()> {
        let stage = stage()?;
        let prim = stage
            .define_prim("/A")?
            .set_custom_data_by_key("render:quality", vt::Value::Int(2))?
            .set_custom_data_by_key("render:pass", vt::Value::String("beauty".into()))?
            .set_asset_info_by_key("name", vt::Value::String("chair".into()))?;
        assert_eq!(prim.custom_data_by_key("render:quality")?, Some(vt::Value::Int(2)));
        assert!(prim.has_authored_custom_data_key("render:pass")?);
        assert!(!prim.has_authored_custom_data_key("render:missing")?);
        assert_eq!(prim.asset_info_by_key("name")?, Some(vt::Value::String("chair".into())));

        let prim = prim.clear_custom_data_by_key("render:quality")?;
        assert_eq!(prim.custom_data_by_key("render:quality")?, None);
        assert!(prim.has_authored_custom_data_key("render:pass")?);
        let prim = prim.clear_custom_data_by_key("render:pass")?;
        assert!(!prim.has_authored_custom_data()?);

        let attr = prim
            .create_attribute("size", "double")?
            .set_custom_data_by_key("a:b", 1.5)?;
        assert_eq!(attr.custom_data_by_key("a:b")?, Some(vt::Value::Double(1.5)));
        let rel = prim
            .create_relationship("r")?
            .set_asset_info_by_key("id", vt::Value::Int(7))?;
        assert!(rel.has_authored_asset_info_key("id")?);
        Ok(())
    }

    /// An empty key path addresses the whole field, and clearing a key of a
    /// field that holds no dictionary leaves the field as it is.
    #[test]
    fn whole_field_by_key() -> Result<()> {
        let stage = stage()?;
        let whole: vt::Dictionary = [("k".to_owned(), vt::Value::Int(1))].into();
        let prim = stage
            .define_prim("/A")?
            .set_custom_data_by_key("", vt::Value::Dictionary(whole.clone()))?;
        assert_eq!(prim.custom_data()?, Some(whole.clone()));
        assert_eq!(prim.custom_data_by_key("")?, Some(vt::Value::Dictionary(whole)));
        assert!(prim.has_authored_custom_data_key("")?);
        let prim = prim.clear_custom_data_by_key("")?;
        assert!(!prim.has_authored_custom_data()?);

        let key = sdf::FieldKey::DisplayName.as_str();
        let prim = prim.set_display_name("Chair")?.clear_metadata_by_key(key, "a:b")?;
        assert_eq!(prim.display_name()?.as_deref(), Some("Chair"));
        Ok(())
    }

    /// A field holding a value of another type reads as unauthored.
    #[test]
    fn mistyped_field_unauthored() -> Result<()> {
        let stage = stage()?;
        let prim = stage
            .define_prim("/A")?
            .set_metadata(sdf::FieldKey::Hidden.as_str(), vt::Value::Int(1))?
            .set_metadata(sdf::FieldKey::CustomData.as_str(), vt::Value::String("oops".into()))?;
        assert!(!prim.is_hidden()?);
        assert_eq!(prim.custom_data()?, None);
        Ok(())
    }

    /// A property's name splits into its namespaces and its base name.
    #[test]
    fn property_name_splits() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/A")?;
        let attr = prim.create_attribute("primvars:normals:indices", "int[]")?;
        assert_eq!(attr.base_name(), "indices");
        assert_eq!(attr.namespace(), "primvars:normals");
        assert_eq!(attr.split_name(), ["primvars", "normals", "indices"]);
        let rel = prim.create_relationship("proxyPrim")?;
        assert_eq!(rel.base_name(), "proxyPrim");
        assert_eq!(rel.namespace(), "");
        assert_eq!(rel.split_name(), ["proxyPrim"]);
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
        assert!(attr.has_authored_display_group()?);
        assert_eq!(attr.nested_display_groups()?, ["Shape", "Size"]);
        let attr = attr.set_display_group(":Shape::Size:")?;
        assert_eq!(attr.nested_display_groups()?, ["Shape", "Size"]);
        assert!(attr.clear_display_group()?.nested_display_groups()?.is_empty());
        Ok(())
    }

    /// A dictionary the schema declares composes under the authored one on a
    /// prim, an attribute and a relationship: a declared key answers where no
    /// layer authors it, nested dictionaries merge, and an authored key wins.
    #[test]
    fn declared_dictionary_under() -> Result<()> {
        const MANIFEST: &str = r#"#usda 1.0

def "Marker"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
        const SCHEMATICS: &str = r#"#usda 1.0

class Marker "Marker" (
    assetInfo = {
        string declared = "schema"
        string shared = "schema"
        dictionary nested = {
            int x = 1
        }
    }
)
{
    float size (
        assetInfo = {
            string declared = "schema"
            string shared = "schema"
        }
    )
    rel link (
        assetInfo = {
            string declared = "schema"
            string shared = "schema"
        }
    )
}
"#;
        /// Authors `shared` on `object`, whose schema declares `declared` and
        /// `shared`, and checks both keys read the strongest opinion.
        fn shared_over_declared<O: Object>(object: O) -> Result<O> {
            let string = |s: &str| vt::Value::String(s.into());
            let object = object.set_asset_info_by_key("shared", string("layer"))?;
            assert_eq!(object.asset_info_by_key("declared")?, Some(string("schema")));
            assert_eq!(object.asset_info_by_key("shared")?, Some(string("layer")));
            Ok(object)
        }

        let stage = Stage::builder()
            .schema_registry(SchemaRegistry::test_family(MANIFEST, SCHEMATICS))
            .in_memory("anon.usda")?;
        let prim = stage.define_prim("/M")?.set_type_name("Marker")?;
        let prim = shared_over_declared(prim)?.set_asset_info_by_key("nested:y", vt::Value::Int(2))?;
        assert_eq!(prim.asset_info_by_key("nested:x")?, Some(vt::Value::Int(1)));
        assert_eq!(prim.asset_info_by_key("nested:y")?, Some(vt::Value::Int(2)));
        shared_over_declared(stage.attribute("/M.size")?)?;
        shared_over_declared(stage.relationship("/M.link")?)?;
        Ok(())
    }
}
