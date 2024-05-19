/// The following fields are pre-registered by Sdf.
///
/// See <https://github.com/PixarAnimationStudios/OpenUSD/blob/release/pxr/usd/sdf/schema.h#L597>
#[derive(Debug)]
pub enum FieldKey {
    Active,
    AllowedTokens,
    AssetInfo,
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

impl FieldKey {
    pub fn as_str(self) -> &'static str {
        match self {
            FieldKey::Active => "active",
            FieldKey::AllowedTokens => "allowedTokens",
            FieldKey::AssetInfo => "assetInfo",
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

impl ChildrenKey {
    pub fn as_str(self) -> &'static str {
        match self {
            ChildrenKey::ConnectionChildren => "connectionChildren",
            ChildrenKey::ExpressionChildren => "expressionChildren",
            ChildrenKey::MapperArgChildren => "mapperArgChildren",
            ChildrenKey::MapperChildren => "mapperChildren",
            ChildrenKey::PrimChildren => "primChildren",
            ChildrenKey::PropertyChildren => "properties",
            ChildrenKey::RelationshipTargetChildren => "targetChildren",
            ChildrenKey::VariantChildren => "variantChildren",
            ChildrenKey::VariantSetChildren => "variantSetChildren",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn child_key_str() {
        assert_eq!(ChildrenKey::ConnectionChildren.as_str(), "connectionChildren");
        assert_eq!(ChildrenKey::PrimChildren.as_str(), "primChildren");
        assert_eq!(ChildrenKey::VariantSetChildren.as_str(), "variantSetChildren");
    }
}
