//! Composed UsdShade `NodeDef` source and shader-registry metadata queries.

use std::borrow::Cow;
use std::collections::HashMap;
use std::error::Error;

use anyhow::Result;

use crate::{sdf, tf, usd};

use super::tokens as tok;
use super::{ImplementationSource, Input, Output, Shader};

/// String-valued metadata passed to an Sdr shader or property definition
/// (C++ `SdrTokenMap`).
pub type SdrMetadata = HashMap<tf::Token, String>;

impl Shader {
    /// The active shader implementation family.
    ///
    /// An unauthored, mistyped, or unrecognized
    /// `info:implementationSource` resolves to [`ImplementationSource::Id`],
    /// matching C++ `UsdShadeNodeDefAPI::GetImplementationSource`.
    pub fn implementation_source(&self) -> Result<ImplementationSource> {
        implementation_source(self)
    }

    /// The composed source asset for `source_type` when source-asset mode is
    /// active.
    ///
    /// An empty source type selects universal `info:sourceAsset`. A requested
    /// source type selects `info:<sourceType>:sourceAsset` and falls back to
    /// the universal attribute only when that specific attribute is not
    /// defined. The returned [`sdf::AssetPath`] retains its authored,
    /// evaluated, and resolved paths.
    pub fn source_asset(&self, source_type: impl AsRef<str>) -> Result<Option<sdf::AssetPath>> {
        source_value(
            self,
            ImplementationSource::SourceAsset,
            source_type.as_ref(),
            tok::A_INFO_SOURCE_ASSET,
            tok::IMPL_SOURCE_SOURCE_ASSET,
        )
    }

    /// The composed source-asset sub-identifier for `source_type` when
    /// source-asset mode is active.
    ///
    /// An empty source type selects the universal sub-identifier. A missing
    /// source-type-specific attribute falls back to it.
    pub fn source_asset_subidentifier(&self, source_type: impl AsRef<str>) -> Result<Option<tf::Token>> {
        source_value(
            self,
            ImplementationSource::SourceAsset,
            source_type.as_ref(),
            tok::A_INFO_SOURCE_ASSET_SUBIDENTIFIER,
            tok::SOURCE_ASSET_SUBIDENTIFIER,
        )
    }

    /// The composed inline source for `source_type` when source-code mode is
    /// active.
    ///
    /// An empty source type selects universal `info:sourceCode`. A missing
    /// source-type-specific attribute falls back to it.
    pub fn source_code(&self, source_type: impl AsRef<str>) -> Result<Option<String>> {
        source_value(
            self,
            ImplementationSource::SourceCode,
            source_type.as_ref(),
            tok::A_INFO_SOURCE_CODE,
            tok::IMPL_SOURCE_SOURCE_CODE,
        )
    }

    /// The source types authored for the active source-asset or source-code
    /// family, in composed property order.
    ///
    /// Universal properties have no source type and are not included.
    /// Identifier mode returns an empty list.
    pub fn source_types(&self) -> Result<Vec<tf::Token>> {
        let implementation = implementation_source(self)?;
        let suffix = match implementation {
            ImplementationSource::Id => return Ok(Vec::new()),
            ImplementationSource::SourceAsset => tok::IMPL_SOURCE_SOURCE_ASSET,
            ImplementationSource::SourceCode => tok::IMPL_SOURCE_SOURCE_CODE,
        };

        Ok(self
            .authored_property_names()?
            .into_iter()
            .filter_map(|name| source_type(name.as_str(), suffix).map(tf::Token::from))
            .collect())
    }

    /// The composed shader-level `sdrMetadata` dictionary.
    ///
    /// UsdShade permits string values in this dictionary. Entries of another
    /// value type are malformed and are omitted from the returned map.
    pub fn sdr_metadata(&self) -> Result<SdrMetadata> {
        Ok(metadata_map(prim_metadata_value(self)?))
    }

    /// The composed shader-level `sdrMetadata` value for `key`.
    pub fn sdr_metadata_by_key(&self, key: impl AsRef<str>) -> Result<Option<String>> {
        Ok(metadata_value(prim_metadata_value(self)?, key.as_ref()))
    }

    /// Whether a composed shader-level `sdrMetadata` field exists.
    pub fn has_sdr_metadata(&self) -> Result<bool> {
        Ok(prim_metadata_value(self)?.is_some())
    }

    /// Whether the composed shader-level `sdrMetadata` dictionary contains
    /// `key`, regardless of the entry's value type.
    pub fn has_sdr_metadata_by_key(&self, key: impl AsRef<str>) -> Result<bool> {
        Ok(metadata_has_key(prim_metadata_value(self)?, key.as_ref()))
    }
}

macro_rules! impl_attribute_sdr_metadata {
    ($ty:ty) => {
        impl $ty {
            /// The composed `sdrMetadata` dictionary on this shading
            /// attribute.
            ///
            /// UsdShade permits string values in this dictionary. Entries of
            /// another value type are malformed and are omitted from the
            /// returned map.
            pub fn sdr_metadata(&self) -> Result<SdrMetadata> {
                Ok(metadata_map(
                    self.attribute()
                        .get_metadata::<sdf::Value>(tok::META_SDR_METADATA)?,
                ))
            }

            /// The composed `sdrMetadata` value for `key` on this shading
            /// attribute.
            pub fn sdr_metadata_by_key(&self, key: impl AsRef<str>) -> Result<Option<String>> {
                Ok(metadata_value(
                    self.attribute()
                        .get_metadata::<sdf::Value>(tok::META_SDR_METADATA)?,
                    key.as_ref(),
                ))
            }

            /// Whether a composed `sdrMetadata` field exists on this shading
            /// attribute.
            pub fn has_sdr_metadata(&self) -> Result<bool> {
                Ok(self
                    .attribute()
                    .get_metadata::<sdf::Value>(tok::META_SDR_METADATA)?
                    .is_some())
            }

            /// Whether this shading attribute's composed `sdrMetadata`
            /// dictionary contains `key`, regardless of its value type.
            pub fn has_sdr_metadata_by_key(&self, key: impl AsRef<str>) -> Result<bool> {
                Ok(metadata_has_key(
                    self.attribute()
                        .get_metadata::<sdf::Value>(tok::META_SDR_METADATA)?,
                    key.as_ref(),
                ))
            }
        }
    };
}

impl_attribute_sdr_metadata!(Input);
impl_attribute_sdr_metadata!(Output);

/// Reads an implementation-specific value, with universal fallback when the
/// requested attribute is not defined.
fn source_value<T>(
    prim: &usd::Prim,
    implementation: ImplementationSource,
    source_type: &str,
    universal_name: &'static str,
    suffix: &str,
) -> Result<Option<T>>
where
    T: TryFrom<sdf::Value>,
    T::Error: Error + Send + Sync + 'static,
{
    if implementation_source(prim)? != implementation {
        return Ok(None);
    }

    let name = source_property_name(source_type, universal_name, suffix);
    let attribute = prim.attribute(name.as_ref());
    if source_type.is_empty() || attribute.is_defined()? {
        return attribute.get();
    }
    prim.attribute(universal_name).get()
}

/// Resolves the active implementation family on a `NodeDef` prim.
fn implementation_source(prim: &usd::Prim) -> Result<ImplementationSource> {
    let value = prim.attribute(tok::A_INFO_IMPLEMENTATION_SOURCE).get::<sdf::Value>()?;
    Ok(value
        .and_then(sdf::Value::try_as_token)
        .and_then(ImplementationSource::from_token)
        .unwrap_or_default())
}

/// Builds a universal or source-type-specific `NodeDef` property name.
fn source_property_name(source_type: &str, universal_name: &'static str, suffix: &str) -> Cow<'static, str> {
    if source_type.is_empty() {
        Cow::Borrowed(universal_name)
    } else {
        Cow::Owned(format!("{}{source_type}:{suffix}", tok::NS_INFO))
    }
}

/// Extracts the source type from an exact active-family property name.
fn source_type<'a>(name: &'a str, suffix: &str) -> Option<&'a str> {
    let mut parts = name.split(':');
    match (parts.next(), parts.next(), parts.next(), parts.next()) {
        (Some("info"), Some(source_type), Some(found), None) if !source_type.is_empty() && found == suffix => {
            Some(source_type)
        }
        _ => None,
    }
}

/// The raw composed prim-level shader-registry metadata value.
fn prim_metadata_value(prim: &usd::Prim) -> Result<Option<sdf::Value>> {
    prim.stage().field(prim.path(), tok::META_SDR_METADATA)
}

/// Converts a valid string-valued metadata dictionary to its public map.
fn metadata_map(value: Option<sdf::Value>) -> SdrMetadata {
    let Some(sdf::Value::Dictionary(dictionary)) = value else {
        return SdrMetadata::new();
    };
    dictionary
        .into_iter()
        .filter_map(|(key, value)| value.try_as_string().map(|value| (tf::Token::from(key), value)))
        .collect()
}

/// Extracts one valid string-valued metadata entry.
fn metadata_value(value: Option<sdf::Value>, key: &str) -> Option<String> {
    let sdf::Value::Dictionary(mut dictionary) = value? else {
        return None;
    };
    dictionary.remove(key)?.try_as_string()
}

/// Tests one composed dictionary key without interpreting its value.
fn metadata_has_key(value: Option<sdf::Value>, key: &str) -> bool {
    matches!(value, Some(sdf::Value::Dictionary(dictionary)) if dictionary.contains_key(key))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::shade::Connectable;
    use crate::usd::SchemaBase;

    fn dictionary(entries: &[(&str, &str)]) -> sdf::Value {
        sdf::Value::Dictionary(
            entries
                .iter()
                .map(|&(key, value)| (key.to_string(), sdf::Value::String(value.to_string())))
                .collect(),
        )
    }

    #[test]
    fn implementation_selects_id() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;
        shader.create_id_attr()?.set(sdf::Value::token("Example"))?;

        assert_eq!(shader.implementation_source()?, ImplementationSource::Id);
        assert_eq!(shader.id()?.as_deref(), Some("Example"));

        shader
            .create_implementation_source_attr()?
            .set(sdf::Value::token("invalid"))?;
        assert_eq!(shader.implementation_source()?, ImplementationSource::Id);
        assert_eq!(shader.id()?.as_deref(), Some("Example"));

        shader
            .implementation_source_attr()
            .set(ImplementationSource::SourceAsset)?;
        assert_eq!(shader.id()?, None);
        Ok(())
    }

    #[test]
    fn source_asset_fallback() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;
        shader
            .create_implementation_source_attr()?
            .set(ImplementationSource::SourceAsset)?;
        shader
            .create_source_asset_attr()?
            .set(sdf::Value::AssetPath("./universal.osl".into()))?;
        shader
            .create_attribute("info:osl:sourceAsset", "asset")?
            .set(sdf::Value::AssetPath("./specific.osl".into()))?;
        shader.create_attribute("info:mdl:sourceAsset", "asset")?;
        shader
            .create_attribute("info:osl:sourceAsset:subIdentifier", "token")?
            .set(sdf::Value::token("Specific"))?;
        shader
            .create_source_asset_subidentifier_attr()?
            .set(sdf::Value::token("Universal"))?;
        shader
            .create_attribute("info:ri:sourceCode", "string")?
            .set("inactive")?;

        assert_eq!(
            shader.source_asset("osl")?.expect("OSL asset").authored_path,
            "./specific.osl"
        );
        assert_eq!(
            shader.source_asset("ri")?.expect("fallback asset").authored_path,
            "./universal.osl"
        );
        assert_eq!(
            shader
                .source_asset("bad type")?
                .expect("malformed source type falls back")
                .authored_path,
            "./universal.osl"
        );
        assert_eq!(shader.source_asset("mdl")?, None);
        assert_eq!(shader.source_asset_subidentifier("osl")?.as_deref(), Some("Specific"));
        assert_eq!(shader.source_asset_subidentifier("ri")?.as_deref(), Some("Universal"));
        assert_eq!(
            shader.source_types()?,
            vec![tf::Token::from("osl"), tf::Token::from("mdl")]
        );
        Ok(())
    }

    #[test]
    fn source_code_selection() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;
        shader
            .create_implementation_source_attr()?
            .set(ImplementationSource::SourceCode)?;
        shader.create_source_code_attr()?.set("universal")?;
        shader
            .create_attribute("info:osl:sourceCode", "string")?
            .set("specific")?;
        shader
            .create_attribute("info:mdl:sourceAsset", "asset")?
            .set(sdf::Value::AssetPath("./inactive.mdl".into()))?;

        assert_eq!(shader.source_code("osl")?.as_deref(), Some("specific"));
        assert_eq!(shader.source_code("ri")?.as_deref(), Some("universal"));
        assert_eq!(shader.source_asset("mdl")?, None);
        assert_eq!(shader.source_types()?, vec![tf::Token::from("osl")]);
        Ok(())
    }

    #[test]
    fn metadata_composes() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("root.usda")?;
        let root = stage.root_layer().identifier().to_string();
        let mut weak = sdf::Layer::new_in_memory("weak.usda");
        weak.edit(|edit| {
            let mut shader = sdf::PrimSpec::new(edit.data_mut(), "/Shader", sdf::Specifier::Def, tok::T_SHADER)?;
            shader.set(
                tok::META_SDR_METADATA,
                dictionary(&[("label", "weak"), ("page", "weak")]),
            );
            let mut input = sdf::AttributeSpec::new(
                edit.data_mut(),
                "/Shader.inputs:value",
                "float",
                sdf::Variability::Varying,
                false,
            )?;
            input.set(tok::META_SDR_METADATA, dictionary(&[("widget", "slider")]));
            Ok(())
        })?;
        stage.insert_layer(&root, 0, weak, sdf::LayerOffset::IDENTITY)?;

        let shader = Shader::define(&stage, "/Shader")?;
        let mut strong_metadata = dictionary(&[("page", "strong")])
            .try_as_dictionary()
            .expect("dictionary helper result");
        strong_metadata.insert("malformed".to_string(), sdf::Value::Int(7));
        shader
            .prim()
            .clone()
            .set_metadata(tok::META_SDR_METADATA, sdf::Value::Dictionary(strong_metadata))?;
        let input = shader.create_input("value", "float")?;
        let output = shader.create_output("result", "float")?;
        output
            .clone()
            .into_attribute()
            .set_metadata(tok::META_SDR_METADATA, dictionary(&[("role", "result")]))?;

        let metadata = shader.sdr_metadata()?;
        assert_eq!(
            metadata.get(&tf::Token::from("label")).map(String::as_str),
            Some("weak")
        );
        assert_eq!(
            metadata.get(&tf::Token::from("page")).map(String::as_str),
            Some("strong")
        );
        assert_eq!(shader.sdr_metadata_by_key("page")?.as_deref(), Some("strong"));
        assert_eq!(shader.sdr_metadata_by_key("malformed")?, None);
        assert!(shader.has_sdr_metadata()?);
        assert!(shader.has_sdr_metadata_by_key("label")?);
        assert!(shader.has_sdr_metadata_by_key("malformed")?);

        assert_eq!(input.sdr_metadata_by_key("widget")?.as_deref(), Some("slider"));
        assert!(input.has_sdr_metadata()?);
        assert_eq!(output.sdr_metadata_by_key("role")?.as_deref(), Some("result"));
        assert!(output.has_sdr_metadata_by_key("role")?);
        Ok(())
    }
}
