//! Composed UsdShade `NodeDef` source and shader-registry metadata: the
//! queries that identify which shader implementation is active, and the
//! authoring counterparts that select one.

use std::borrow::Cow;
use std::collections::HashMap;

use openusd::Result;

use openusd::usd::SchemaBase;
use openusd::{sdf, tf, usd, vt};

use super::tokens;
use super::{ImplementationSource, NodeDefAPI, Shader};

/// The namespace a shader's source is named under. A render context interposes
/// its own name after it, as in `info:<context>:sourceAsset`, and no schema
/// declares those names.
pub const INFO_NAMESPACE: &str = "info:";

/// The tail of the name carrying a source asset's sub-identifier, which
/// [`INFO_NAMESPACE`] and a render context precede.
pub const SUBIDENTIFIER_SUFFIX: &str = "sourceAsset:subIdentifier";

/// The source asset of the universal render context, which is the context a
/// caller reaches without naming one.
pub const INFO_SOURCE_ASSET: &str = "info:sourceAsset";

/// The universal render context's source-asset sub-identifier.
pub const INFO_SOURCE_ASSET_SUBIDENTIFIER: &str = "info:sourceAsset:subIdentifier";

/// The source code of the universal render context.
pub const INFO_SOURCE_CODE: &str = "info:sourceCode";

/// String-valued metadata passed to an Sdr shader or property definition
/// (C++ `SdrTokenMap`).
pub type SdrMetadata = HashMap<tf::Token, String>;

/// One `NodeDef` source family: which implementation selects it, the universal
/// attribute that carries it, and how a source-type-specific one is spelled and
/// typed. `universal_name` is [`INFO_NAMESPACE`] joined to `suffix`,
/// which is what a source-type-specific name interposes its type into.
struct SourceAttr {
    implementation: ImplementationSource,
    universal_name: &'static str,
    suffix: &'static str,
    type_name: sdf::ValueTypeName,
}

const SOURCE_ASSET: SourceAttr = SourceAttr {
    implementation: ImplementationSource::SourceAsset,
    universal_name: INFO_SOURCE_ASSET,
    suffix: tokens::SOURCE_ASSET,
    type_name: sdf::ValueTypeName::ASSET,
};

const SOURCE_ASSET_SUBIDENTIFIER: SourceAttr = SourceAttr {
    implementation: ImplementationSource::SourceAsset,
    universal_name: INFO_SOURCE_ASSET_SUBIDENTIFIER,
    suffix: SUBIDENTIFIER_SUFFIX,
    type_name: sdf::ValueTypeName::TOKEN,
};

const SOURCE_CODE: SourceAttr = SourceAttr {
    implementation: ImplementationSource::SourceCode,
    universal_name: INFO_SOURCE_CODE,
    suffix: tokens::SOURCE_CODE,
    type_name: sdf::ValueTypeName::STRING,
};

impl NodeDefAPI {
    /// The active shader implementation family (C++
    /// `UsdShadeNodeDefAPI::GetImplementationSource`).
    ///
    /// The attribute is read as its raw token: an unauthored, mistyped, or
    /// unrecognized `info:implementationSource` resolves to
    /// [`ImplementationSource::Id`].
    pub fn implementation(&self) -> Result<ImplementationSource> {
        let value = self.implementation_source_attr().get::<vt::Value>()?;
        Ok(value
            .and_then(vt::Value::try_as_token)
            .and_then(ImplementationSource::from_token)
            .unwrap_or_default())
    }

    /// The composed `info:id` when identifier mode is active, and `None` in
    /// the other modes (C++ `UsdShadeNodeDefAPI::GetShaderId`).
    pub fn shader_id(&self) -> Result<Option<tf::Token>> {
        if self.implementation()? != ImplementationSource::Id {
            return Ok(None);
        }
        self.id()
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
            vt::Value::AssetPath(asset.into()),
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
            vt::Value::Token(subidentifier.into()),
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
            vt::Value::String(source.into()),
        )
    }

    /// Author `info:id` and select identifier mode, as one edit (C++
    /// `SetShaderId`).
    ///
    /// `info:implementationSource` is written sparsely, as C++ writes it: an
    /// unauthored attribute whose fallback is already `id` gets no opinion,
    /// and an authored one is corrected.
    pub fn set_shader_id(&self, id: impl Into<tf::Token>) -> Result<usd::Attribute> {
        let source = self.implementation_source_attr();
        let id_mode = vt::Value::token(ImplementationSource::Id.as_token());
        let sparse = !source.has_authored_value()? && source.get::<vt::Value>()? == Some(id_mode);
        Ok(self.stage().edit(|edit| {
            if !sparse {
                self.implementation_source_attr_builder()
                    .set(ImplementationSource::Id)
                    .in_edit(edit)
                    .build()?;
            }
            self.id_attr_builder().set(id.into()).in_edit(edit).build()
        })?)
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
        let suffix = match self.implementation()? {
            ImplementationSource::Id => return Ok(Vec::new()),
            ImplementationSource::SourceAsset => tokens::SOURCE_ASSET,
            ImplementationSource::SourceCode => tokens::SOURCE_CODE,
        };

        Ok(self
            .property_names()?
            .into_iter()
            .filter_map(|name| source_type(name.as_str(), suffix).map(tf::Token::from))
            .collect())
    }
}

impl Shader {
    /// The composed shader-level `sdrMetadata` dictionary.
    ///
    /// TODO(perf): every query in this group re-composes and clones the whole
    /// dictionary, so reading N keys costs N compositions. Reading it once into
    /// an [`SdrMetadata`] is what a consumer wants; a composed presence probe
    /// that does not clone the value would serve the `has_*` pair.
    pub fn sdr_metadata(&self) -> Result<SdrMetadata> {
        Ok(metadata_map(self.metadata(tokens::SDR_METADATA)?))
    }

    /// The composed shader-level `sdrMetadata` value for `key`.
    pub fn sdr_metadata_by_key(&self, key: impl AsRef<str>) -> Result<Option<String>> {
        Ok(metadata_value(self.metadata(tokens::SDR_METADATA)?, key.as_ref()))
    }

    /// Whether a composed shader-level `sdrMetadata` field exists.
    pub fn has_sdr_metadata(&self) -> Result<bool> {
        Ok(self.metadata::<vt::Value>(tokens::SDR_METADATA)?.is_some())
    }

    /// Whether the composed shader-level `sdrMetadata` dictionary contains
    /// `key`, whatever the entry's value type.
    pub fn has_sdr_metadata_by_key(&self, key: impl AsRef<str>) -> Result<bool> {
        Ok(metadata_has_key(self.metadata(tokens::SDR_METADATA)?, key.as_ref()))
    }

    /// Author `sdrMetadata` entries on the shader (C++ `SetSdrMetadata`).
    ///
    /// Entries merge into the dictionary the edit target already holds, so keys
    /// this call does not name keep composing from wherever they are authored.
    pub fn set_sdr_metadata(&self, metadata: &SdrMetadata) -> Result<(), usd::StageAuthoringError> {
        self.prim()
            .clone()
            .update_metadata(tokens::SDR_METADATA, |current| merge_metadata_map(current, metadata))?;
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
            .update_metadata(tokens::SDR_METADATA, |current| merge_metadata(current, entry))?;
        Ok(())
    }

    /// Drop the shader's whole `sdrMetadata` opinion on the edit-target layer
    /// (C++ `ClearSdrMetadata`).
    pub fn clear_sdr_metadata(&self) -> Result<(), usd::StageAuthoringError> {
        self.prim().clone().clear_metadata(tokens::SDR_METADATA)?;
        Ok(())
    }

    /// Drop one `sdrMetadata` entry from the shader's opinion on the
    /// edit-target layer (C++ `ClearSdrMetadataByKey`).
    pub fn clear_sdr_metadata_by_key(&self, key: impl AsRef<str>) -> Result<(), usd::StageAuthoringError> {
        self.prim().clone().update_metadata(tokens::SDR_METADATA, |current| {
            remove_metadata_key(current, key.as_ref())
        })?;
        Ok(())
    }
}

/// Reads an implementation-specific value, with universal fallback when the
/// requested attribute is not defined.
fn source_value<T>(node_def: &NodeDefAPI, attr: &SourceAttr, source_type: &str) -> Result<Option<T>>
where
    T: vt::FromValue,
    T::Error: Into<openusd::Error>,
{
    if node_def.implementation()? != attr.implementation {
        return Ok(None);
    }

    let name = source_property_name(attr, source_type);
    let attribute = node_def.attribute(name.as_ref());
    if source_type.is_empty() || attribute.is_defined()? {
        return attribute.get();
    }
    node_def.attribute(attr.universal_name).get()
}

/// Authors a `NodeDef` source attribute together with the implementation
/// source that selects it. Every C++ source setter writes
/// `info:implementationSource` alongside its own value, so authoring a source
/// is what activates it.
///
/// Both properties are authored as one stage edit. The prim never composes
/// with a source selected and no source to read.
fn set_source_value(
    node_def: &NodeDefAPI,
    attr: &SourceAttr,
    source_type: &str,
    value: vt::Value,
) -> Result<usd::Attribute> {
    let name = source_property_name(attr, source_type);
    Ok(node_def.stage().edit(|edit| {
        node_def
            .implementation_source_attr_builder()
            .set(attr.implementation)
            .in_edit(edit)
            .build()?;
        node_def
            .attribute_builder(name.as_ref(), attr.type_name.clone())
            .custom(false)
            .variability(sdf::Variability::Uniform)
            .set(value)
            .in_edit(edit)
            .build()
    })?)
}

/// Builds a universal or source-type-specific `NodeDef` property name.
fn source_property_name(attr: &SourceAttr, source_type: &str) -> Cow<'static, str> {
    if source_type.is_empty() {
        Cow::Borrowed(attr.universal_name)
    } else {
        Cow::Owned(format!("{INFO_NAMESPACE}{source_type}:{}", attr.suffix))
    }
}

/// Extracts the source type from an exact active-family property name —
/// `info:<sourceType>:<suffix>`, and nothing longer or shorter.
fn source_type<'a>(name: &'a str, suffix: &str) -> Option<&'a str> {
    let (source_type, found) = name.strip_prefix(INFO_NAMESPACE)?.split_once(':')?;
    (!source_type.is_empty() && found == suffix).then_some(source_type)
}

/// Converts a composed metadata dictionary to its public map, each value as
/// the text C++ `TfStringify` makes of it (C++ `_GetSdrMetadata`,
/// `nodeDefAPI.cpp:383-395`).
pub(super) fn metadata_map(value: Option<vt::Value>) -> SdrMetadata {
    let Some(vt::Value::Dictionary(dictionary)) = value else {
        return SdrMetadata::new();
    };
    dictionary
        .into_iter()
        .map(|(key, value)| (tf::Token::from(key), value.to_string()))
        .collect()
}

/// Extracts one metadata entry, as [`metadata_map`] renders it.
pub(super) fn metadata_value(value: Option<vt::Value>, key: &str) -> Option<String> {
    let vt::Value::Dictionary(mut dictionary) = value? else {
        return None;
    };
    Some(dictionary.remove(key)?.to_string())
}

/// Tests one composed dictionary key without interpreting its value.
pub(super) fn metadata_has_key(value: Option<vt::Value>, key: &str) -> bool {
    matches!(value, Some(vt::Value::Dictionary(dictionary)) if dictionary.contains_key(key))
}

/// Merges string entries into a metadata dictionary authored on the edit
/// target, keeping whatever keys it already carries. Merging nothing into an
/// unauthored field leaves it unauthored, so an empty map authors no opinion.
pub(super) fn merge_metadata(
    current: Option<vt::Value>,
    entries: impl IntoIterator<Item = (String, String)>,
) -> Option<vt::Value> {
    let mut dictionary = match current {
        Some(vt::Value::Dictionary(dictionary)) => dictionary,
        _ => vt::Dictionary::new(),
    };
    dictionary.extend(entries.into_iter().map(|(key, value)| (key, vt::Value::String(value))));
    (!dictionary.is_empty()).then_some(vt::Value::Dictionary(dictionary))
}

/// Merges a whole [`SdrMetadata`] map into a metadata dictionary authored on the
/// edit target. The map-shaped counterpart of [`merge_metadata`].
pub(super) fn merge_metadata_map(current: Option<vt::Value>, metadata: &SdrMetadata) -> Option<vt::Value> {
    let entries = metadata
        .iter()
        .map(|(key, value)| (key.as_str().to_string(), value.clone()));
    merge_metadata(current, entries)
}

/// Removes one key from a metadata dictionary, dropping the field itself once
/// its last entry is gone.
pub(super) fn remove_metadata_key(current: Option<vt::Value>, key: &str) -> Option<vt::Value> {
    match current {
        Some(vt::Value::Dictionary(mut dictionary)) => {
            dictionary.remove(key);
            (!dictionary.is_empty()).then_some(vt::Value::Dictionary(dictionary))
        }
        other => other,
    }
}

/// The composed `sdrMetadata` dictionary on a shading attribute.
pub(super) fn attribute_sdr_metadata(attribute: &usd::Attribute) -> Result<SdrMetadata> {
    Ok(metadata_map(attribute.metadata(tokens::SDR_METADATA)?))
}

/// The composed `sdrMetadata` value for `key` on a shading attribute.
pub(super) fn attribute_sdr_metadata_by_key(attribute: &usd::Attribute, key: &str) -> Result<Option<String>> {
    Ok(metadata_value(attribute.metadata(tokens::SDR_METADATA)?, key))
}

/// Whether a composed `sdrMetadata` field exists on a shading attribute.
pub(super) fn attribute_has_sdr_metadata(attribute: &usd::Attribute) -> Result<bool> {
    Ok(attribute.metadata::<vt::Value>(tokens::SDR_METADATA)?.is_some())
}

/// Whether a shading attribute's composed `sdrMetadata` dictionary holds `key`.
pub(super) fn attribute_has_sdr_metadata_by_key(attribute: &usd::Attribute, key: &str) -> Result<bool> {
    Ok(metadata_has_key(attribute.metadata(tokens::SDR_METADATA)?, key))
}

/// Merges `metadata` into a shading attribute's own `sdrMetadata` opinion.
pub(super) fn set_attribute_sdr_metadata(
    attribute: usd::Attribute,
    metadata: &SdrMetadata,
) -> Result<usd::Attribute, usd::StageAuthoringError> {
    attribute.update_metadata(tokens::SDR_METADATA, |current| merge_metadata_map(current, metadata))
}

/// Merges one entry into a shading attribute's own `sdrMetadata` opinion.
pub(super) fn set_attribute_sdr_metadata_by_key(
    attribute: usd::Attribute,
    key: String,
    value: String,
) -> Result<usd::Attribute, usd::StageAuthoringError> {
    attribute.update_metadata(tokens::SDR_METADATA, |current| merge_metadata(current, [(key, value)]))
}

/// Drops one entry from a shading attribute's own `sdrMetadata` opinion.
pub(super) fn clear_attribute_sdr_metadata_by_key(
    attribute: usd::Attribute,
    key: &str,
) -> Result<usd::Attribute, usd::StageAuthoringError> {
    attribute.update_metadata(tokens::SDR_METADATA, |current| remove_metadata_key(current, key))
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::shade::Connectable;
    use openusd::{Result, gf};

    /// Source types sorted, since the order follows the prim's property order
    /// and that depends on what the schema registry declares for the type.
    fn sorted_source_types(shader: &Shader) -> Result<Vec<String>> {
        let mut types = shader.node_def().source_types()?;
        types.sort();
        Ok(types.into_iter().map(String::from).collect())
    }

    fn dictionary(entries: &[(&str, &str)]) -> vt::Value {
        vt::Value::Dictionary(
            entries
                .iter()
                .map(|&(key, value)| (key.to_string(), vt::Value::String(value.to_string())))
                .collect(),
        )
    }

    #[test]
    fn implementation_selects_id() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;
        shader.node_def().create_id_attr()?.set(vt::Value::token("Example"))?;

        assert_eq!(shader.node_def().implementation()?, ImplementationSource::Id);
        assert_eq!(shader.node_def().shader_id()?.as_deref(), Some("Example"));

        shader
            .node_def()
            .create_implementation_source_attr()?
            .set(vt::Value::token("invalid"))?;
        assert_eq!(shader.node_def().implementation()?, ImplementationSource::Id);
        assert_eq!(shader.node_def().shader_id()?.as_deref(), Some("Example"));

        shader
            .node_def()
            .implementation_source_attr()
            .set(ImplementationSource::SourceAsset)?;
        assert_eq!(shader.node_def().shader_id()?, None);
        Ok(())
    }

    #[test]
    fn source_asset_fallback() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;
        let node_def = shader.node_def();
        node_def.set_source_asset("./universal.osl", "")?;
        node_def.set_source_asset_subidentifier("Universal", "")?;
        shader
            .create_attribute("info:osl:sourceAsset", "asset")?
            .set(vt::Value::AssetPath("./specific.osl".into()))?;
        shader.create_attribute("info:mdl:sourceAsset", "asset")?;
        shader
            .create_attribute("info:osl:sourceAsset:subIdentifier", "token")?
            .set(vt::Value::token("Specific"))?;
        shader
            .create_attribute("info:ri:sourceCode", "string")?
            .set("inactive")?;

        let asset = |source_type: &str| -> Result<Option<String>> {
            Ok(node_def.source_asset(source_type)?.map(|asset| asset.authored_path))
        };
        assert_eq!(asset("osl")?.as_deref(), Some("./specific.osl"));
        assert_eq!(asset("ri")?.as_deref(), Some("./universal.osl"), "fallback asset");
        assert_eq!(
            asset("bad type")?.as_deref(),
            Some("./universal.osl"),
            "malformed source type falls back"
        );
        assert_eq!(asset("mdl")?, None);
        assert_eq!(asset("")?.as_deref(), Some("./universal.osl"));
        assert_eq!(node_def.source_asset_subidentifier("osl")?.as_deref(), Some("Specific"));
        assert_eq!(node_def.source_asset_subidentifier("ri")?.as_deref(), Some("Universal"));
        assert_eq!(node_def.source_asset_subidentifier("")?.as_deref(), Some("Universal"));
        assert_eq!(sorted_source_types(&shader)?, ["mdl", "osl"]);
        Ok(())
    }

    #[test]
    fn source_code_selection() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;
        shader.node_def().set_source_code("universal", "")?;
        shader
            .create_attribute("info:osl:sourceCode", "string")?
            .set("specific")?;
        // Defined but valueless: authoritative for its source type, so the
        // universal opinion does not answer for `ri`.
        shader.create_attribute("info:ri:sourceCode", "string")?;
        shader
            .create_attribute("info:mdl:sourceAsset", "asset")?
            .set(vt::Value::AssetPath("./inactive.mdl".into()))?;

        assert_eq!(shader.node_def().source_code("osl")?.as_deref(), Some("specific"));
        assert_eq!(shader.node_def().source_code("ri")?, None);
        assert_eq!(shader.node_def().source_code("glsl")?.as_deref(), Some("universal"));
        assert_eq!(shader.node_def().source_code("")?.as_deref(), Some("universal"));
        assert_eq!(shader.node_def().source_asset("mdl")?, None);
        assert_eq!(sorted_source_types(&shader)?, ["osl", "ri"]);
        Ok(())
    }

    #[test]
    fn authors_source_selection() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;

        // An id needs no authored `info:implementationSource`: identifier mode
        // is the schema's own fallback, which the registry answers with.
        shader.node_def().set_shader_id("Example")?;
        assert_eq!(shader.node_def().shader_id()?.as_deref(), Some("Example"));
        assert_eq!(
            shader.node_def().implementation_source_attr().get()?,
            Some(vt::Value::token("id"))
        );

        shader.node_def().set_source_asset("./shader.mdl", "mdl")?;
        assert_eq!(shader.node_def().implementation()?, ImplementationSource::SourceAsset);
        assert_eq!(
            shader.node_def().source_asset("mdl")?.expect("MDL asset").authored_path,
            "./shader.mdl"
        );
        assert_eq!(shader.node_def().shader_id()?, None);

        shader.node_def().set_source_asset_subidentifier("Main", "mdl")?;
        assert_eq!(
            shader.node_def().source_asset_subidentifier("mdl")?.as_deref(),
            Some("Main")
        );

        // Selecting an id again has a stale family to correct, so this time the
        // opinion is authored.
        shader.node_def().set_shader_id("Example")?;
        assert_eq!(shader.node_def().implementation()?, ImplementationSource::Id);
        assert_eq!(shader.node_def().shader_id()?.as_deref(), Some("Example"));

        shader.node_def().set_source_code("shader Example() {}", "")?;
        assert_eq!(shader.node_def().implementation()?, ImplementationSource::SourceCode);
        assert_eq!(
            shader.node_def().source_code("")?.as_deref(),
            Some("shader Example() {}")
        );
        assert_eq!(shader.node_def().source_types()?, Vec::<tf::Token>::new());
        Ok(())
    }

    /// A prim whose schema gives `info:implementationSource` no fallback gets
    /// the `id` opinion written, as C++'s sparse write does.
    #[test]
    fn shader_id_without_fallback() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let node_def = NodeDefAPI::from_prim_unchecked(stage.define_prim("/Untyped")?);
        node_def.set_shader_id("Example")?;
        assert!(node_def.implementation_source_attr().has_authored_value()?);
        assert_eq!(node_def.shader_id()?.as_deref(), Some("Example"));
        Ok(())
    }

    /// A layer authoring the family leaves an opinion to correct, so selecting
    /// an id writes one into the edit target even when composition already
    /// reads back as identifier mode.
    #[test]
    fn shader_id_corrects_family() -> Result<()> {
        let stage = crate::tests::stage("root.usda")?;
        let root = stage.root_layer().identifier().to_string();
        let weak = sdf::Layer::new_anonymous("weak");
        let weak_id = weak.identifier().to_string();
        stage.insert_layer(&root, 0, weak, sdf::LayerOffset::IDENTITY)?;

        // The weak sublayer selects source-code mode and the root overrides it
        // back, so composition already reads back as identifier mode.
        stage.set_edit_target(usd::EditTarget::for_layer(&weak_id))?;
        let shader = Shader::define(&stage, "/Shader")?;
        shader
            .node_def()
            .create_implementation_source_attr()?
            .set(ImplementationSource::SourceCode)?;
        stage.set_edit_target(stage.edit_target_root())?;
        shader
            .node_def()
            .create_implementation_source_attr()?
            .set(ImplementationSource::Id)?;
        assert_eq!(shader.node_def().implementation()?, ImplementationSource::Id);

        stage.set_edit_target(usd::EditTarget::for_layer(&weak_id))?;
        shader.node_def().set_shader_id("Example")?;

        let weak = stage.layer(&weak_id).expect("weak layer").export_to_string()?;
        assert!(!weak.contains(tokens::SOURCE_CODE));
        Ok(())
    }

    #[test]
    fn metadata_composes() -> Result<()> {
        let stage = crate::tests::stage("root.usda")?;
        let root = stage.root_layer().identifier().to_string();
        let mut weak = sdf::Layer::new_anonymous("weak");
        weak.edit(|edit| {
            let mut shader = sdf::PrimSpec::new(edit.data_mut(), "/Shader", sdf::Specifier::Def, tokens::SHADER)?;
            shader.set(tokens::SDR_METADATA, dictionary(&[("label", "weak"), ("page", "weak")]));
            let mut input = sdf::AttributeSpec::new(
                edit.data_mut(),
                "/Shader.inputs:value",
                "float",
                sdf::Variability::Varying,
                false,
            )?;
            input.set(tokens::SDR_METADATA, dictionary(&[("widget", "slider")]));
            Ok(())
        })?;
        stage.insert_layer(&root, 0, weak, sdf::LayerOffset::IDENTITY)?;

        let shader = Shader::define(&stage, "/Shader")?;
        let mut strong_metadata = dictionary(&[("page", "strong")])
            .try_as_dictionary()
            .expect("dictionary helper result");
        strong_metadata.insert("count".to_string(), vt::Value::Int(7));
        shader
            .prim()
            .clone()
            .set_metadata(tokens::SDR_METADATA, vt::Value::Dictionary(strong_metadata))?;
        let input = shader.create_input("value", "float")?;
        let output = shader.create_output("result", "float")?;
        output
            .clone()
            .into_attribute()
            .set_metadata(tokens::SDR_METADATA, dictionary(&[("role", "result")]))?;

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

    /// Every entry reads back as the text C++ `TfStringify` makes of it,
    /// aggregates and C++'s own forms of scalars included.
    #[test]
    fn metadata_stringified() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Shader")?;
        let entries: vt::Dictionary = [
            ("flag", vt::Value::Bool(true)),
            ("big", vt::Value::Double(1e20)),
            ("list", vt::Value::IntVec(vec![1, 2])),
            ("color", vt::Value::Vec3f(gf::vec3f(1.0, 0.5, 0.0))),
            ("file", vt::Value::AssetPath(sdf::AssetPath::new("a.png"))),
        ]
        .into_iter()
        .map(|(key, value)| (key.to_string(), value))
        .collect();
        shader
            .prim()
            .clone()
            .set_metadata(tokens::SDR_METADATA, vt::Value::Dictionary(entries))?;

        for (key, text) in [
            ("flag", "1"),
            ("big", "1e20"),
            ("list", "[1, 2]"),
            ("color", "(1, 0.5, 0)"),
            ("file", "@a.png@"),
        ] {
            assert_eq!(shader.sdr_metadata_by_key(key)?.as_deref(), Some(text), "{key}");
        }
        assert_eq!(shader.sdr_metadata()?.len(), 5);
        Ok(())
    }

    #[test]
    fn metadata_unauthored() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
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
        let stage = crate::tests::stage("anon.usda")?;
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
        let stage = crate::tests::stage("root.usda")?;
        let root = stage.root_layer().identifier().to_string();
        let mut weak = sdf::Layer::new_anonymous("weak");
        weak.edit(|edit| {
            let mut shader = sdf::PrimSpec::new(edit.data_mut(), "/Shader", sdf::Specifier::Def, tokens::SHADER)?;
            shader.set(tokens::SDR_METADATA, dictionary(&[("label", "weak")]));
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
