//! Composed UsdShade `NodeDef` source and shader-registry metadata: the
//! queries that identify which shader implementation is active, and the
//! authoring counterparts that select one.

use std::borrow::Cow;
use std::collections::HashMap;
use std::error::Error;

use anyhow::Result;

use crate::usd::SchemaBase;
use crate::{sdf, tf, usd};

use super::tokens as tok;
use super::{ImplementationSource, Shader};

/// String-valued metadata passed to an Sdr shader or property definition
/// (C++ `SdrTokenMap`).
pub type SdrMetadata = HashMap<tf::Token, String>;

/// One `NodeDef` source family: which implementation selects it, the universal
/// attribute that carries it, and how a source-type-specific one is spelled and
/// typed. `universal_name` is [`NS_INFO`](tok::NS_INFO) joined to `suffix`,
/// which is what a source-type-specific name interposes its type into.
struct SourceAttr {
    implementation: ImplementationSource,
    universal_name: &'static str,
    suffix: &'static str,
    type_name: &'static str,
}

const SOURCE_ASSET: SourceAttr = SourceAttr {
    implementation: ImplementationSource::SourceAsset,
    universal_name: tok::A_INFO_SOURCE_ASSET,
    suffix: tok::IMPL_SOURCE_SOURCE_ASSET,
    type_name: "asset",
};

const SOURCE_ASSET_SUBIDENTIFIER: SourceAttr = SourceAttr {
    implementation: ImplementationSource::SourceAsset,
    universal_name: tok::A_INFO_SOURCE_ASSET_SUBIDENTIFIER,
    suffix: tok::SOURCE_ASSET_SUBIDENTIFIER,
    type_name: "token",
};

const SOURCE_CODE: SourceAttr = SourceAttr {
    implementation: ImplementationSource::SourceCode,
    universal_name: tok::A_INFO_SOURCE_CODE,
    suffix: tok::IMPL_SOURCE_SOURCE_CODE,
    type_name: "string",
};

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
        source_value(self, &SOURCE_ASSET, source_type.as_ref())
    }

    /// Author the source asset for `source_type` and select source-asset mode
    /// (C++ `SetSourceAsset`).
    ///
    /// An empty source type authors the universal `info:sourceAsset`; any other
    /// authors `info:<sourceType>:sourceAsset`. Returns the authored attribute.
    pub fn set_source_asset(
        &self,
        asset: impl Into<sdf::AssetPath>,
        source_type: impl AsRef<str>,
    ) -> Result<usd::Attribute> {
        set_source_value(
            self,
            &SOURCE_ASSET,
            source_type.as_ref(),
            sdf::Value::AssetPath(asset.into()),
        )
    }

    /// The composed source-asset sub-identifier for `source_type` when
    /// source-asset mode is active.
    ///
    /// An empty source type selects the universal sub-identifier. A missing
    /// source-type-specific attribute falls back to it.
    pub fn source_asset_subidentifier(&self, source_type: impl AsRef<str>) -> Result<Option<tf::Token>> {
        source_value(self, &SOURCE_ASSET_SUBIDENTIFIER, source_type.as_ref())
    }

    /// Author the source-asset sub-identifier for `source_type` and select
    /// source-asset mode (C++ `SetSourceAssetSubIdentifier`).
    pub fn set_source_asset_subidentifier(
        &self,
        subidentifier: impl Into<tf::Token>,
        source_type: impl AsRef<str>,
    ) -> Result<usd::Attribute> {
        set_source_value(
            self,
            &SOURCE_ASSET_SUBIDENTIFIER,
            source_type.as_ref(),
            sdf::Value::Token(subidentifier.into()),
        )
    }

    /// The composed inline source for `source_type` when source-code mode is
    /// active.
    ///
    /// An empty source type selects universal `info:sourceCode`. A missing
    /// source-type-specific attribute falls back to it.
    pub fn source_code(&self, source_type: impl AsRef<str>) -> Result<Option<String>> {
        source_value(self, &SOURCE_CODE, source_type.as_ref())
    }

    /// Author the inline source for `source_type` and select source-code mode
    /// (C++ `SetSourceCode`).
    pub fn set_source_code(&self, source: impl Into<String>, source_type: impl AsRef<str>) -> Result<usd::Attribute> {
        set_source_value(
            self,
            &SOURCE_CODE,
            source_type.as_ref(),
            sdf::Value::String(source.into()),
        )
    }

    /// Author `info:id` and select identifier mode (C++ `SetShaderId`).
    ///
    /// `info:implementationSource` is written only when some layer authors one.
    /// Identifier mode is the schema fallback, so a shader that never selected a
    /// family needs no opinion, while one that did has an opinion to correct —
    /// the test C++ applies when it writes the attribute sparsely.
    pub fn set_shader_id(&self, id: impl Into<tf::Token>) -> Result<usd::Attribute> {
        if self.implementation_source_attr().value_source()? == usd::ValueSource::Authored {
            self.create_implementation_source_attr()?
                .set(ImplementationSource::Id)?;
        }
        Ok(self.create_id_attr()?.set(sdf::Value::Token(id.into()))?)
    }

    /// The source types declared for the active source-asset or source-code
    /// family.
    ///
    /// The scan covers every property the prim carries, whether a layer authors
    /// it or a schema declares it, mirroring C++ `GetPropertiesInNamespace`, and
    /// keeps the order [`Prim::property_names`](usd::Prim::property_names)
    /// reports. Universal properties carry no source type and are not included.
    /// Identifier mode returns an empty list.
    pub fn source_types(&self) -> Result<Vec<tf::Token>> {
        let suffix = match implementation_source(self)? {
            ImplementationSource::Id => return Ok(Vec::new()),
            ImplementationSource::SourceAsset => tok::IMPL_SOURCE_SOURCE_ASSET,
            ImplementationSource::SourceCode => tok::IMPL_SOURCE_SOURCE_CODE,
        };

        Ok(self
            .property_names()?
            .into_iter()
            .filter_map(|name| source_type(name.as_str(), suffix).map(tf::Token::from))
            .collect())
    }

    /// The composed shader-level `sdrMetadata` dictionary.
    ///
    /// TODO(perf): every query in this group re-composes and clones the whole
    /// dictionary, so reading N keys costs N compositions. Reading it once into
    /// an [`SdrMetadata`] is what a consumer wants; a composed presence probe
    /// that does not clone the value would serve the `has_*` pair.
    pub fn sdr_metadata(&self) -> Result<SdrMetadata> {
        Ok(metadata_map(self.get_metadata(tok::META_SDR_METADATA)?))
    }

    /// The composed shader-level `sdrMetadata` value for `key`.
    pub fn sdr_metadata_by_key(&self, key: impl AsRef<str>) -> Result<Option<String>> {
        Ok(metadata_value(self.get_metadata(tok::META_SDR_METADATA)?, key.as_ref()))
    }

    /// Whether a composed shader-level `sdrMetadata` field exists.
    pub fn has_sdr_metadata(&self) -> Result<bool> {
        Ok(self.get_metadata::<sdf::Value>(tok::META_SDR_METADATA)?.is_some())
    }

    /// Whether the composed shader-level `sdrMetadata` dictionary contains
    /// `key`, regardless of the entry's value type. An aggregate value has no
    /// text rendering, so a key holding one reports here but reads back as
    /// absent from the value queries.
    pub fn has_sdr_metadata_by_key(&self, key: impl AsRef<str>) -> Result<bool> {
        Ok(metadata_has_key(
            self.get_metadata(tok::META_SDR_METADATA)?,
            key.as_ref(),
        ))
    }

    /// Author `sdrMetadata` entries on the shader (C++ `SetSdrMetadata`).
    ///
    /// Entries merge into the dictionary the edit target already holds, so keys
    /// this call does not name keep composing from wherever they are authored.
    pub fn set_sdr_metadata(&self, metadata: &SdrMetadata) -> Result<(), usd::StageAuthoringError> {
        self.prim()
            .clone()
            .update_metadata(tok::META_SDR_METADATA, |current| merge_metadata_map(current, metadata))?;
        Ok(())
    }

    /// Author one `sdrMetadata` entry on the shader
    /// (C++ `SetSdrMetadataByKey`).
    pub fn set_sdr_metadata_by_key(
        &self,
        key: impl Into<String>,
        value: impl Into<String>,
    ) -> Result<(), usd::StageAuthoringError> {
        let entry = [(key.into(), value.into())];
        self.prim()
            .clone()
            .update_metadata(tok::META_SDR_METADATA, |current| merge_metadata(current, entry))?;
        Ok(())
    }

    /// Drop the shader's whole `sdrMetadata` opinion on the edit-target layer
    /// (C++ `ClearSdrMetadata`).
    pub fn clear_sdr_metadata(&self) -> Result<(), usd::StageAuthoringError> {
        self.prim().clone().clear_metadata(tok::META_SDR_METADATA)?;
        Ok(())
    }

    /// Drop one `sdrMetadata` entry from the shader's opinion on the
    /// edit-target layer (C++ `ClearSdrMetadataByKey`).
    pub fn clear_sdr_metadata_by_key(&self, key: impl AsRef<str>) -> Result<(), usd::StageAuthoringError> {
        self.prim().clone().update_metadata(tok::META_SDR_METADATA, |current| {
            remove_metadata_key(current, key.as_ref())
        })?;
        Ok(())
    }
}

/// Reads an implementation-specific value, with universal fallback when the
/// requested attribute is not defined.
fn source_value<T>(prim: &usd::Prim, attr: &SourceAttr, source_type: &str) -> Result<Option<T>>
where
    T: TryFrom<sdf::Value>,
    T::Error: Error + Send + Sync + 'static,
{
    if implementation_source(prim)? != attr.implementation {
        return Ok(None);
    }

    let name = source_property_name(attr, source_type);
    let attribute = prim.attribute(name.as_ref());
    if source_type.is_empty() || attribute.is_defined()? {
        return attribute.get();
    }
    prim.attribute(attr.universal_name).get()
}

/// Authors a `NodeDef` source attribute together with the implementation
/// source that selects it. Every C++ source setter writes
/// `info:implementationSource` alongside its own value, so authoring a source
/// is what activates it.
///
/// TODO(perf): each step here — the implementation source, then the value
/// attribute's creation, `custom`, variability and value — is its own layer
/// transaction with its own change-list derivation and invalidation pass.
/// Routing the whole setter through one `Stage::batch_edit` would collapse them.
fn set_source_value(
    shader: &Shader,
    attr: &SourceAttr,
    source_type: &str,
    value: sdf::Value,
) -> Result<usd::Attribute> {
    shader.create_implementation_source_attr()?.set(attr.implementation)?;

    let name = source_property_name(attr, source_type);
    Ok(shader
        .create_attribute(name.as_ref(), attr.type_name)?
        .set_custom(false)?
        .set_variability(sdf::Variability::Uniform)?
        .set(value)?)
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
fn source_property_name(attr: &SourceAttr, source_type: &str) -> Cow<'static, str> {
    if source_type.is_empty() {
        Cow::Borrowed(attr.universal_name)
    } else {
        Cow::Owned(format!("{}{source_type}:{}", tok::NS_INFO, attr.suffix))
    }
}

/// Extracts the source type from an exact active-family property name —
/// `info:<sourceType>:<suffix>`, and nothing longer or shorter.
fn source_type<'a>(name: &'a str, suffix: &str) -> Option<&'a str> {
    let (source_type, found) = name.strip_prefix(tok::NS_INFO)?.split_once(':')?;
    (!source_type.is_empty() && found == suffix).then_some(source_type)
}

/// Converts a composed metadata dictionary to its public map.
pub(super) fn metadata_map(value: Option<sdf::Value>) -> SdrMetadata {
    let Some(sdf::Value::Dictionary(dictionary)) = value else {
        return SdrMetadata::new();
    };
    dictionary
        .into_iter()
        .filter_map(|(key, value)| stringify(value).map(|value| (tf::Token::from(key), value)))
        .collect()
}

/// Extracts one metadata entry.
pub(super) fn metadata_value(value: Option<sdf::Value>, key: &str) -> Option<String> {
    let sdf::Value::Dictionary(mut dictionary) = value? else {
        return None;
    };
    stringify(dictionary.remove(key)?)
}

/// Tests one composed dictionary key without interpreting its value.
pub(super) fn metadata_has_key(value: Option<sdf::Value>, key: &str) -> bool {
    matches!(value, Some(sdf::Value::Dictionary(dictionary)) if dictionary.contains_key(key))
}

/// Merges string entries into a metadata dictionary authored on the edit
/// target, keeping whatever keys it already carries. Merging nothing into an
/// unauthored field leaves it unauthored, so an empty map authors no opinion.
pub(super) fn merge_metadata(
    current: Option<sdf::Value>,
    entries: impl IntoIterator<Item = (String, String)>,
) -> Option<sdf::Value> {
    let mut dictionary = match current {
        Some(sdf::Value::Dictionary(dictionary)) => dictionary,
        _ => HashMap::new(),
    };
    dictionary.extend(entries.into_iter().map(|(key, value)| (key, sdf::Value::String(value))));
    (!dictionary.is_empty()).then_some(sdf::Value::Dictionary(dictionary))
}

/// Merges a whole [`SdrMetadata`] map into a metadata dictionary authored on the
/// edit target. The map-shaped counterpart of [`merge_metadata`].
pub(super) fn merge_metadata_map(current: Option<sdf::Value>, metadata: &SdrMetadata) -> Option<sdf::Value> {
    let entries = metadata
        .iter()
        .map(|(key, value)| (key.as_str().to_string(), value.clone()));
    merge_metadata(current, entries)
}

/// Removes one key from a metadata dictionary, dropping the field itself once
/// its last entry is gone.
pub(super) fn remove_metadata_key(current: Option<sdf::Value>, key: &str) -> Option<sdf::Value> {
    match current {
        Some(sdf::Value::Dictionary(mut dictionary)) => {
            dictionary.remove(key);
            (!dictionary.is_empty()).then_some(sdf::Value::Dictionary(dictionary))
        }
        other => other,
    }
}

/// The composed `sdrMetadata` dictionary on a shading attribute.
pub(super) fn attribute_sdr_metadata(attribute: &usd::Attribute) -> Result<SdrMetadata> {
    Ok(metadata_map(attribute.get_metadata(tok::META_SDR_METADATA)?))
}

/// The composed `sdrMetadata` value for `key` on a shading attribute.
pub(super) fn attribute_sdr_metadata_by_key(attribute: &usd::Attribute, key: &str) -> Result<Option<String>> {
    Ok(metadata_value(attribute.get_metadata(tok::META_SDR_METADATA)?, key))
}

/// Whether a composed `sdrMetadata` field exists on a shading attribute.
pub(super) fn attribute_has_sdr_metadata(attribute: &usd::Attribute) -> Result<bool> {
    Ok(attribute.get_metadata::<sdf::Value>(tok::META_SDR_METADATA)?.is_some())
}

/// Whether a shading attribute's composed `sdrMetadata` dictionary holds `key`.
pub(super) fn attribute_has_sdr_metadata_by_key(attribute: &usd::Attribute, key: &str) -> Result<bool> {
    Ok(metadata_has_key(attribute.get_metadata(tok::META_SDR_METADATA)?, key))
}

/// Merges `metadata` into a shading attribute's own `sdrMetadata` opinion.
pub(super) fn set_attribute_sdr_metadata(
    attribute: usd::Attribute,
    metadata: &SdrMetadata,
) -> Result<usd::Attribute, usd::StageAuthoringError> {
    attribute.update_metadata(tok::META_SDR_METADATA, |current| merge_metadata_map(current, metadata))
}

/// Merges one entry into a shading attribute's own `sdrMetadata` opinion.
pub(super) fn set_attribute_sdr_metadata_by_key(
    attribute: usd::Attribute,
    key: String,
    value: String,
) -> Result<usd::Attribute, usd::StageAuthoringError> {
    attribute.update_metadata(tok::META_SDR_METADATA, |current| {
        merge_metadata(current, [(key, value)])
    })
}

/// Drops one entry from a shading attribute's own `sdrMetadata` opinion.
pub(super) fn clear_attribute_sdr_metadata_by_key(
    attribute: usd::Attribute,
    key: &str,
) -> Result<usd::Attribute, usd::StageAuthoringError> {
    attribute.update_metadata(tok::META_SDR_METADATA, |current| remove_metadata_key(current, key))
}

/// Renders a metadata value as the string an Sdr consumer reads, the way C++
/// `TfStringify` does for the scalar types an `sdrMetadata` dictionary carries.
/// The string-like variants defer to [`sdf::Value::cast`], which owns that
/// coercion; only the numeric rendering is stated here.
///
/// TODO: aggregates (arrays, matrices, nested dictionaries) have no rendering
/// here and read back as absent. Full `TfStringify` parity needs a shared
/// value-to-text primitive in `sdf` rather than a wider match here.
fn stringify(value: sdf::Value) -> Option<String> {
    Some(match value {
        sdf::Value::Bool(value) => value.to_string(),
        sdf::Value::Uchar(value) => value.to_string(),
        sdf::Value::Int(value) => value.to_string(),
        sdf::Value::Uint(value) => value.to_string(),
        sdf::Value::Int64(value) => value.to_string(),
        sdf::Value::Uint64(value) => value.to_string(),
        sdf::Value::Half(value) => value.to_string(),
        sdf::Value::Float(value) => value.to_string(),
        sdf::Value::Double(value) => value.to_string(),
        other => other.cast::<String>().ok()?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::shade::Connectable;

    /// Source types sorted, since the order follows the prim's property order
    /// and that depends on what the schema registry declares for the type.
    fn sorted_source_types(shader: &Shader) -> Result<Vec<String>> {
        let mut types = shader.source_types()?;
        types.sort();
        Ok(types.into_iter().map(String::from).collect())
    }

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
        assert_eq!(
            shader.source_asset("")?.expect("universal asset").authored_path,
            "./universal.osl"
        );
        assert_eq!(shader.source_asset_subidentifier("osl")?.as_deref(), Some("Specific"));
        assert_eq!(shader.source_asset_subidentifier("ri")?.as_deref(), Some("Universal"));
        assert_eq!(shader.source_asset_subidentifier("")?.as_deref(), Some("Universal"));
        assert_eq!(sorted_source_types(&shader)?, ["mdl", "osl"]);
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
        // Defined but valueless: authoritative for its source type, so the
        // universal opinion does not answer for `ri`.
        shader.create_attribute("info:ri:sourceCode", "string")?;
        shader
            .create_attribute("info:mdl:sourceAsset", "asset")?
            .set(sdf::Value::AssetPath("./inactive.mdl".into()))?;

        assert_eq!(shader.source_code("osl")?.as_deref(), Some("specific"));
        assert_eq!(shader.source_code("ri")?, None);
        assert_eq!(shader.source_code("glsl")?.as_deref(), Some("universal"));
        assert_eq!(shader.source_code("")?.as_deref(), Some("universal"));
        assert_eq!(shader.source_asset("mdl")?, None);
        assert_eq!(sorted_source_types(&shader)?, ["osl", "ri"]);
        Ok(())
    }

    #[test]
    fn authors_source_selection() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;

        // An id needs no `info:implementationSource`: identifier mode is the
        // schema fallback.
        shader.set_shader_id("Example")?;
        assert_eq!(shader.id()?.as_deref(), Some("Example"));
        assert_eq!(shader.implementation_source_attr().get::<sdf::Value>()?, None);

        shader.set_source_asset("./shader.mdl", "mdl")?;
        assert_eq!(shader.implementation_source()?, ImplementationSource::SourceAsset);
        assert_eq!(
            shader.source_asset("mdl")?.expect("MDL asset").authored_path,
            "./shader.mdl"
        );
        assert_eq!(shader.id()?, None);

        shader.set_source_asset_subidentifier("Main", "mdl")?;
        assert_eq!(shader.source_asset_subidentifier("mdl")?.as_deref(), Some("Main"));

        // Selecting an id again has a stale family to correct, so this time the
        // opinion is authored.
        shader.set_shader_id("Example")?;
        assert_eq!(shader.implementation_source()?, ImplementationSource::Id);
        assert_eq!(shader.id()?.as_deref(), Some("Example"));

        shader.set_source_code("shader Example() {}", "")?;
        assert_eq!(shader.implementation_source()?, ImplementationSource::SourceCode);
        assert_eq!(shader.source_code("")?.as_deref(), Some("shader Example() {}"));
        assert_eq!(shader.source_types()?, Vec::<tf::Token>::new());
        Ok(())
    }

    /// A layer authoring the family leaves an opinion to correct, so selecting
    /// an id writes one into the edit target even when composition already
    /// reads back as identifier mode.
    #[test]
    fn shader_id_corrects_family() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("root.usda")?;
        let root = stage.root_layer().identifier().to_string();
        stage.insert_layer(
            &root,
            0,
            sdf::Layer::new_in_memory("weak.usda"),
            sdf::LayerOffset::IDENTITY,
        )?;

        // The weak sublayer selects source-code mode and the root overrides it
        // back, so composition already reads back as identifier mode.
        stage.set_edit_target(usd::EditTarget::for_layer("weak.usda"))?;
        let shader = Shader::define(&stage, "/Shader")?;
        shader
            .create_implementation_source_attr()?
            .set(ImplementationSource::SourceCode)?;
        stage.set_edit_target(stage.edit_target_root())?;
        shader
            .create_implementation_source_attr()?
            .set(ImplementationSource::Id)?;
        assert_eq!(shader.implementation_source()?, ImplementationSource::Id);

        stage.set_edit_target(usd::EditTarget::for_layer("weak.usda"))?;
        shader.set_shader_id("Example")?;

        let weak = stage.layer("weak.usda").expect("weak layer").export_to_string()?;
        assert!(!weak.contains(tok::IMPL_SOURCE_SOURCE_CODE));
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
        strong_metadata.insert("count".to_string(), sdf::Value::Int(7));
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
        // A scalar entry of another type renders as its text (C++ `TfStringify`),
        // so the keyed query answers for every key the presence query reports.
        assert_eq!(metadata.get(&tf::Token::from("count")).map(String::as_str), Some("7"));
        assert_eq!(shader.sdr_metadata_by_key("page")?.as_deref(), Some("strong"));
        assert_eq!(shader.sdr_metadata_by_key("count")?.as_deref(), Some("7"));
        assert!(shader.has_sdr_metadata()?);
        assert!(shader.has_sdr_metadata_by_key("label")?);
        assert!(shader.has_sdr_metadata_by_key("count")?);
        assert!(!shader.has_sdr_metadata_by_key("absent")?);

        assert_eq!(input.sdr_metadata_by_key("widget")?.as_deref(), Some("slider"));
        assert!(input.has_sdr_metadata()?);
        assert_eq!(output.sdr_metadata_by_key("role")?.as_deref(), Some("result"));
        assert!(output.has_sdr_metadata_by_key("role")?);
        Ok(())
    }

    #[test]
    fn metadata_unauthored() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;
        let input = shader.create_input("value", "float")?;

        assert!(!shader.has_sdr_metadata()?);
        assert!(!shader.has_sdr_metadata_by_key("label")?);
        assert!(shader.sdr_metadata()?.is_empty());
        assert_eq!(shader.sdr_metadata_by_key("label")?, None);
        assert!(!input.has_sdr_metadata()?);
        assert!(input.sdr_metadata()?.is_empty());
        Ok(())
    }

    #[test]
    fn authors_metadata_entries() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;

        shader.set_sdr_metadata_by_key("label", "Diffuse")?;
        shader.set_sdr_metadata_by_key("page", "Basic")?;
        assert_eq!(shader.sdr_metadata_by_key("label")?.as_deref(), Some("Diffuse"));
        assert_eq!(shader.sdr_metadata_by_key("page")?.as_deref(), Some("Basic"));

        // Whole-map authoring merges into the entries already there.
        shader.set_sdr_metadata(&SdrMetadata::from([(tf::Token::from("role"), "surface".to_string())]))?;
        assert_eq!(shader.sdr_metadata()?.len(), 3);

        // An empty map has nothing to merge, so it authors no opinion.
        let empty = Shader::define(&stage, "/Empty")?;
        empty.set_sdr_metadata(&SdrMetadata::new())?;
        assert!(!empty.has_sdr_metadata()?);

        shader.clear_sdr_metadata_by_key("page")?;
        assert_eq!(shader.sdr_metadata_by_key("page")?, None);
        assert!(shader.has_sdr_metadata_by_key("label")?);

        shader.clear_sdr_metadata()?;
        assert!(!shader.has_sdr_metadata()?);

        let input = shader.create_input("value", "float")?;
        let input = input.set_sdr_metadata_by_key("widget", "slider")?;
        assert_eq!(input.sdr_metadata_by_key("widget")?.as_deref(), Some("slider"));
        let input = input.clear_sdr_metadata_by_key("widget")?;
        assert!(!input.has_sdr_metadata()?);
        Ok(())
    }

    /// Clearing the last entry of a shader's own opinion uncovers whatever a
    /// weaker layer authors instead of leaving an empty dictionary behind.
    #[test]
    fn clearing_key_uncovers_weaker() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("root.usda")?;
        let root = stage.root_layer().identifier().to_string();
        let mut weak = sdf::Layer::new_in_memory("weak.usda");
        weak.edit(|edit| {
            let mut shader = sdf::PrimSpec::new(edit.data_mut(), "/Shader", sdf::Specifier::Def, tok::T_SHADER)?;
            shader.set(tok::META_SDR_METADATA, dictionary(&[("label", "weak")]));
            Ok(())
        })?;
        stage.insert_layer(&root, 0, weak, sdf::LayerOffset::IDENTITY)?;

        let shader = Shader::define(&stage, "/Shader")?;
        shader.set_sdr_metadata_by_key("label", "strong")?;
        assert_eq!(shader.sdr_metadata_by_key("label")?.as_deref(), Some("strong"));

        shader.clear_sdr_metadata_by_key("label")?;
        assert_eq!(shader.sdr_metadata_by_key("label")?.as_deref(), Some("weak"));
        Ok(())
    }
}
