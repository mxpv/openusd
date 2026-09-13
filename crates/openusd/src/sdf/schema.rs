use strum::VariantArray;

use super::ValueTypeName;

/// The following fields are pre-registered by Sdf.
///
/// See <https://github.com/PixarAnimationStudios/OpenUSD/blob/release/pxr/usd/sdf/schema.h#L597>
#[derive(Debug, Clone, Copy, VariantArray)]
pub enum FieldKey {
    Active,
    AllowedTokens,
    ApiSchemas,
    AssetInfo,
    Clips,
    ClipSets,
    ColorConfiguration,
    ColorManagementSystem,
    ColorSpace,
    Comment,
    ConnectionPaths,
    Custom,
    CustomData,
    CustomLayerData,
    Default,
    DefaultPrim,
    DisplayGroup,
    DisplayGroupOrder,
    DisplayName,
    DisplayUnit,
    Documentation,
    EndTimeCode,
    ExpressionVariables,
    FallbackPrimTypes,
    FramePrecision,
    FramesPerSecond,
    Hidden,
    HasOwnedSubLayers,
    InheritPaths,
    Instanceable,
    Kind,
    LayerRelocates,
    PrimOrder,
    NoLoadHint,
    Owner,
    Payload,
    Permission,
    Prefix,
    PrefixSubstitutions,
    PropertyOrder,
    References,
    Relocates,
    SessionOwner,
    Specializes,
    Specifier,
    StartTimeCode,
    SubLayers,
    SubLayerOffsets,
    Suffix,
    SuffixSubstitutions,
    SymmetricPeer,
    SymmetryArgs,
    SymmetryArguments,
    SymmetryFunction,
    TargetPaths,
    TimeSamples,
    TimeCodesPerSecond,
    TypeName,
    VariantSelection,
    Variability,
    VariantSetNames,
    EndFrame,
    StartFrame,
}

impl From<FieldKey> for &'static str {
    fn from(key: FieldKey) -> Self {
        key.as_str()
    }
}

impl AsRef<str> for FieldKey {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl FieldKey {
    /// The field `name` denotes, or `None` where this enum does not name it.
    ///
    /// A schema may declare fields of its own, so a `None` here does not mean
    /// the field is unregistered; [`is_registered_field`] answers that.
    pub fn from_name(name: &str) -> Option<Self> {
        FieldKey::VARIANTS.iter().copied().find(|key| key.as_str() == name)
    }

    pub const fn as_str(&self) -> &'static str {
        match self {
            FieldKey::Active => "active",
            FieldKey::AllowedTokens => "allowedTokens",
            FieldKey::ApiSchemas => "apiSchemas",
            FieldKey::AssetInfo => "assetInfo",
            FieldKey::Clips => "clips",
            FieldKey::ClipSets => "clipSets",
            FieldKey::ColorConfiguration => "colorConfiguration",
            FieldKey::ColorManagementSystem => "colorManagementSystem",
            FieldKey::ColorSpace => "colorSpace",
            FieldKey::Comment => "comment",
            FieldKey::ConnectionPaths => "connectionPaths",
            FieldKey::Custom => "custom",
            FieldKey::CustomData => "customData",
            FieldKey::CustomLayerData => "customLayerData",
            FieldKey::Default => "default",
            FieldKey::DefaultPrim => "defaultPrim",
            FieldKey::DisplayGroup => "displayGroup",
            FieldKey::DisplayGroupOrder => "displayGroupOrder",
            FieldKey::DisplayName => "displayName",
            FieldKey::DisplayUnit => "displayUnit",
            FieldKey::Documentation => "documentation",
            FieldKey::EndTimeCode => "endTimeCode",
            FieldKey::ExpressionVariables => "expressionVariables",
            FieldKey::FallbackPrimTypes => "fallbackPrimTypes",
            FieldKey::FramePrecision => "framePrecision",
            FieldKey::FramesPerSecond => "framesPerSecond",
            FieldKey::Hidden => "hidden",
            FieldKey::HasOwnedSubLayers => "hasOwnedSubLayers",
            FieldKey::InheritPaths => "inheritPaths",
            FieldKey::Instanceable => "instanceable",
            FieldKey::Kind => "kind",
            FieldKey::LayerRelocates => "layerRelocates",
            FieldKey::PrimOrder => "primOrder",
            FieldKey::NoLoadHint => "noLoadHint",
            FieldKey::Owner => "owner",
            FieldKey::Payload => "payload",
            FieldKey::Permission => "permission",
            FieldKey::Prefix => "prefix",
            FieldKey::PrefixSubstitutions => "prefixSubstitutions",
            FieldKey::PropertyOrder => "propertyOrder",
            FieldKey::References => "references",
            FieldKey::Relocates => "relocates",
            FieldKey::SessionOwner => "sessionOwner",
            FieldKey::Specializes => "specializes",
            FieldKey::Specifier => "specifier",
            FieldKey::StartTimeCode => "startTimeCode",
            FieldKey::SubLayers => "subLayers",
            FieldKey::SubLayerOffsets => "subLayerOffsets",
            FieldKey::Suffix => "suffix",
            FieldKey::SuffixSubstitutions => "suffixSubstitutions",
            FieldKey::SymmetricPeer => "symmetricPeer",
            FieldKey::SymmetryArgs => "symmetryArgs",
            FieldKey::SymmetryArguments => "symmetryArguments",
            FieldKey::SymmetryFunction => "symmetryFunction",
            FieldKey::TargetPaths => "targetPaths",
            FieldKey::TimeSamples => "timeSamples",
            FieldKey::TimeCodesPerSecond => "timeCodesPerSecond",
            FieldKey::TypeName => "typeName",
            FieldKey::VariantSelection => "variantSelection",
            FieldKey::Variability => "variability",
            FieldKey::VariantSetNames => "variantSetNames",
            FieldKey::EndFrame => "endFrame",
            FieldKey::StartFrame => "startFrame",
        }
    }
}

/// See <https://github.com/PixarAnimationStudios/OpenUSD/blob/2864f3d04f396432f22ec5d6928fc37d34bb4c90/pxr/usd/sdf/schema.h#L652>
#[derive(Clone, Copy)]
pub enum ChildrenKey {
    ConnectionChildren,
    ExpressionChildren,
    MapperArgChildren,
    MapperChildren,
    PrimChildren,
    PropertyChildren,
    RelationshipTargetChildren,
    VariantChildren,
    VariantSetChildren,
}

impl From<ChildrenKey> for &'static str {
    fn from(key: ChildrenKey) -> Self {
        key.as_str()
    }
}

impl AsRef<str> for ChildrenKey {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl ChildrenKey {
    pub const fn as_str(&self) -> &'static str {
        match self {
            ChildrenKey::ConnectionChildren => "connectionChildren",
            ChildrenKey::ExpressionChildren => "expressionChildren",
            ChildrenKey::MapperArgChildren => "mapperArgChildren",
            ChildrenKey::MapperChildren => "mapperChildren",
            ChildrenKey::PrimChildren => "primChildren",
            // The internal/text token is "propertyChildren". The crate (binary)
            // format stores this field under the name "properties"; the usdc
            // reader and writer translate at that boundary (see `usdc`).
            ChildrenKey::PropertyChildren => "propertyChildren",
            ChildrenKey::RelationshipTargetChildren => "targetChildren",
            ChildrenKey::VariantChildren => "variantChildren",
            ChildrenKey::VariantSetChildren => "variantSetChildren",
        }
    }
}

/// The metadata fields the libraries shipped with USD declare, beyond the
/// core fields [`FieldKey`] names, each with the type its declaration gives
/// it.
///
/// C++ discovers these from the `SdfMetadata` block of every plugin's
/// `plugInfo.json` and registers them before any layer is read, so a layer
/// authoring one is authoring a registered field even where nothing has
/// loaded the library that declares it (`SdfSchemaBase::_AddFieldsFromPlugins`).
/// That is why this reaches past the families `openusd-schemas` implements,
/// to `usdImaging` and `execIr`.
///
/// TODO: let a schema family register its own fields, so one defined outside
/// this crate is registered too, and carry the spec types each applies to
/// (C++ `appliesTo`) so a field can be rejected where it does not belong.
/// Until then this is the set the families shipped with USD declare.
const SCHEMA_METADATA: [(&str, &str); 22] = [
    ("bindMaterialAs", "token"),
    ("connectability", "token"),
    ("constraintTargetIdentifier", "token"),
    ("elementSize", "int"),
    ("faceIndexPrimvar", "token"),
    ("faceOffsetPrimvar", "token"),
    ("inactiveIds", "int64listop"),
    ("interpolation", "token"),
    ("irIsInvertible", "bool"),
    ("irRole", "token"),
    ("kilogramsPerUnit", "double"),
    ("metersPerUnit", "double"),
    ("outputName", "token"),
    ("payloadAssetDependencies", "asset[]"),
    ("renderSettingsPrimPath", "string"),
    ("renderType", "token"),
    ("sdrMetadata", "dictionary"),
    ("uiHints", "dictionary"),
    ("unauthoredValuesIndex", "int"),
    ("upAxis", "token"),
    ("uvPrimvar", "token"),
    ("weight", "float"),
];

/// Whether some schema declares `name` as a metadata field.
///
/// A layer may author any identifier in a metadata block. One this answers
/// `false` for is unregistered: nothing gives its literal a type, so a reader
/// carries the text it was written as rather than a value
/// (C++ `SdfSchemaBase::SpecDefinition::IsValidField`).
///
/// Narrower than C++ in one direction, which is the safe one: C++ also
/// rejects a field that is registered but is not metadata for the spec type
/// being read, and without a per-spec-type table this treats such a field as
/// registered rather than misfiling it as opaque.
// TODO(perf): both halves scan their table, once per metadata field read.
// The lookup wants a map, or a `match` the compiler can turn into one; neither
// is worth a third copy of the field names before a profile asks for it.
pub fn is_registered_field(name: &str) -> bool {
    FieldKey::from_name(name).is_some() || schema_field_spelling(name).is_some()
}

/// The type the schema declaring `name` gives that metadata field, or `None`
/// where no schema declares it.
///
/// A spelling the value-type table does not know — `dictionary`, and the
/// list-op types — comes back as an unregistered [`ValueTypeName`] answering
/// no [`kind`](ValueTypeName::kind), so a caller that can only act on a type
/// it recognises skips those without needing a second table.
pub fn schema_field_type(name: &str) -> Option<ValueTypeName> {
    schema_field_spelling(name).map(ValueTypeName::from)
}

/// How the declaring library spells that field's type, without resolving it.
fn schema_field_spelling(name: &str) -> Option<&'static str> {
    SCHEMA_METADATA
        .iter()
        .find(|(field, _)| *field == name)
        .map(|(_, ty)| *ty)
}

/// Whether `field` holds a vector rather than an array of the same element.
///
/// C++ separates `std::vector<T>` from `VtArray<T>`: `subLayers` is a vector
/// of strings, while a `string[]` attribute's value is an array of them.
/// [`Value::TokenVec`](super::Value::TokenVec) and
/// [`Value::StringVec`](super::Value::StringVec) carry both, so a format that
/// encodes them differently has to ask the field which it is looking at.
///
/// These are the fields `SdfSchema` registers with a `std::vector` fallback
/// and whose element has an array spelling too; the path and layer-offset
/// vectors need no entry, having no array form to be confused with.
pub fn is_vector_field(field: &str) -> bool {
    const VECTORS: [&str; 9] = [
        ChildrenKey::ExpressionChildren.as_str(),
        ChildrenKey::MapperArgChildren.as_str(),
        ChildrenKey::PrimChildren.as_str(),
        ChildrenKey::PropertyChildren.as_str(),
        ChildrenKey::VariantChildren.as_str(),
        ChildrenKey::VariantSetChildren.as_str(),
        FieldKey::PrimOrder.as_str(),
        FieldKey::PropertyOrder.as_str(),
        FieldKey::SubLayers.as_str(),
    ];
    VECTORS.contains(&field)
}

/// Whether generic field resolution folds list-op opinions authored for
/// `field` (spec 12.2.6).
///
/// Composition arcs, relationship targets and attribute connections, clip-set
/// ordering, and the value-resolution fields compose through dedicated
/// machinery — arcs during prim indexing, targets with per-node namespace
/// translation, `clipSets` with encoding coercion, values by
/// strongest-opinion resolution — so generic resolution leaves their opinions
/// untouched (C++ `UsdStage::_IsPrivateFieldKey` shields the same fields from
/// its generic metadata path).
pub fn folds_list_ops(field: &str) -> bool {
    const DEDICATED: [FieldKey; 10] = [
        FieldKey::References,
        FieldKey::Payload,
        FieldKey::InheritPaths,
        FieldKey::Specializes,
        FieldKey::VariantSetNames,
        FieldKey::ConnectionPaths,
        FieldKey::TargetPaths,
        FieldKey::ClipSets,
        FieldKey::Default,
        FieldKey::TimeSamples,
    ];
    !DEDICATED.iter().any(|key| key.as_str() == field)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_key_from_name() {
        for key in FieldKey::VARIANTS {
            assert_eq!(
                FieldKey::from_name(key.as_str()).map(|k| k.as_str()),
                Some(key.as_str())
            );
        }
        assert!(FieldKey::from_name("madeUpField").is_none());
    }

    #[test]
    fn vector_fields() {
        assert!(is_vector_field(ChildrenKey::PrimChildren.as_str()));
        assert!(is_vector_field(FieldKey::SubLayers.as_str()));
        // A path-valued children field, and an array-valued metadata field.
        assert!(!is_vector_field(ChildrenKey::ConnectionChildren.as_str()));
        assert!(!is_vector_field(FieldKey::AllowedTokens.as_str()));
    }

    #[test]
    fn registered_fields() {
        assert!(is_registered_field(FieldKey::DisplayUnit.as_str()));
        assert!(is_registered_field("interpolation"));
        assert!(!is_registered_field("hide_in_stage_window"));
    }

    #[test]
    fn schema_field_types() {
        assert_eq!(schema_field_type("interpolation"), Some(ValueTypeName::TOKEN));
        assert_eq!(schema_field_type("elementSize"), Some(ValueTypeName::INT));
        // A spelling the type table does not know still names the field.
        assert!(schema_field_type("sdrMetadata").is_some_and(|ty| ty.kind().is_none()));
        assert_eq!(schema_field_type("hide_in_stage_window"), None);
        // Declared by a library outside the families this workspace builds.
        assert_eq!(schema_field_type("uvPrimvar"), Some(ValueTypeName::TOKEN));
    }

    #[test]
    fn child_key_str() {
        assert_eq!(ChildrenKey::ConnectionChildren.as_str(), "connectionChildren");
        assert_eq!(ChildrenKey::PrimChildren.as_str(), "primChildren");
        assert_eq!(ChildrenKey::VariantSetChildren.as_str(), "variantSetChildren");
    }
}
