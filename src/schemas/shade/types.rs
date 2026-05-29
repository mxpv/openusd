//! Decoded enums for the [UsdShade](super) schema family.

use super::tokens::*;

/// `info:implementationSource` on a Shader / NodeDefAPI prim — selects
/// which `info:*` attribute carries the shader's implementation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ImplementationSource {
    /// `id` — look the shader up in the Sdr registry by `info:id`.
    #[default]
    Id,
    /// `sourceAsset` — `info:sourceAsset` points at a parsable asset.
    SourceAsset,
    /// `sourceCode` — `info:sourceCode` holds inline source.
    SourceCode,
}

impl ImplementationSource {
    pub fn as_token(self) -> &'static str {
        match self {
            ImplementationSource::Id => IMPL_SOURCE_ID,
            ImplementationSource::SourceAsset => IMPL_SOURCE_SOURCE_ASSET,
            ImplementationSource::SourceCode => IMPL_SOURCE_SOURCE_CODE,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            IMPL_SOURCE_ID => ImplementationSource::Id,
            IMPL_SOURCE_SOURCE_ASSET => ImplementationSource::SourceAsset,
            IMPL_SOURCE_SOURCE_CODE => ImplementationSource::SourceCode,
            _ => return None,
        })
    }
}

/// `connectability` metadata on a UsdShadeInput — restricts what the
/// input may be connected to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Connectability {
    /// Can connect to any input or output (the default).
    #[default]
    Full,
    /// Can only connect to a NodeGraph interface input (or another
    /// `interfaceOnly` input) — not a render-time dataflow source.
    InterfaceOnly,
}

impl Connectability {
    pub fn as_token(self) -> &'static str {
        match self {
            Connectability::Full => CONNECTABILITY_FULL,
            Connectability::InterfaceOnly => CONNECTABILITY_INTERFACE_ONLY,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            CONNECTABILITY_FULL => Connectability::Full,
            CONNECTABILITY_INTERFACE_ONLY => Connectability::InterfaceOnly,
            _ => return None,
        })
    }
}

/// `bindMaterialAs` strength on a material-binding relationship —
/// whether a binding overrides ones authored lower in namespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum BindingStrength {
    /// Bindings on descendant prims win (the spec default when
    /// `bindMaterialAs` is unauthored).
    #[default]
    WeakerThanDescendants,
    /// This binding wins over any authored on descendant prims.
    StrongerThanDescendants,
}

impl BindingStrength {
    pub fn as_token(self) -> &'static str {
        match self {
            BindingStrength::WeakerThanDescendants => STRENGTH_WEAKER_THAN_DESCENDANTS,
            BindingStrength::StrongerThanDescendants => STRENGTH_STRONGER_THAN_DESCENDANTS,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            STRENGTH_WEAKER_THAN_DESCENDANTS => BindingStrength::WeakerThanDescendants,
            STRENGTH_STRONGER_THAN_DESCENDANTS => BindingStrength::StrongerThanDescendants,
            _ => return None,
        })
    }
}
