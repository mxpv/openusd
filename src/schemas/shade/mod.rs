//! UsdShade schema views.
//!
//! Typed value-views over a composed [`crate::usd::Stage`], mirroring Pixar's
//! `UsdShade` family — the material / shading-network schema. Unlike the
//! geometry / lighting families, its substance is *connection topology* rather
//! than a flat set of typed attributes: a [`Material`] contains [`Shader`]
//! prims whose `inputs:` / `outputs:` attributes are wired together by
//! connections ([`connectionPaths`](crate::sdf::FieldKey::ConnectionPaths)).
//!
//! ```text
//! SchemaBase
//!  ├ Connectable (interface; inputs: / outputs:)
//!  │  ├ Shader        (typed; info:id + NodeDefAPI surface)
//!  │  ├ NodeGraph     (typed; a shading-network container)
//!  │  └ Material      (typed; surface / displacement / volume terminals)
//!  └ MaterialBindingAPI (single-apply; direct + collection bindings)
//! ```
//!
//! [`Connectable`] is the shared `inputs:` / `outputs:` surface (C++
//! `UsdShadeConnectableAPI`); connections are wired with
//! [`Attribute::connect_to`](crate::usd::Attribute::connect_to) and read back
//! through [`get_connections`](crate::usd::Attribute::get_connections). The
//! connection-following computation is kept as
//! [`Material::compute_surface_source`] (resolve a Material's surface terminal
//! back to its shader) and [`read_preview_surface`] (decode the canonical
//! `UsdPreviewSurface` / `UsdUVTexture` graph). To find every shading prim on a
//! stage, traverse it and gate each prim through the typed `get` (e.g.
//! [`Material::get`]), mirroring C++ `prim.IsA<UsdShadeMaterial>()`.
//!
//! # Example
//!
//! ```
//! use openusd::schemas::shade::{self, Connectable};
//! use openusd::{sdf, usd};
//!
//! let stage = usd::Stage::builder().in_memory("scene.usda").unwrap();
//!
//! let surface = shade::Shader::define(&stage, "/Mat/Surface").unwrap();
//! surface.create_id_attr().unwrap().set("UsdPreviewSurface".to_string()).unwrap();
//! surface.create_input("roughness", "float").unwrap().set(0.4_f32).unwrap();
//! surface.create_output("surface", "token").unwrap();
//!
//! shade::Material::define(&stage, "/Mat").unwrap()
//!     .create_surface_output().unwrap()
//!     .set_connections([sdf::path("/Mat/Surface.outputs:surface").unwrap()]).unwrap();
//!
//! let mat = shade::Material::get(&stage, "/Mat").unwrap().expect("Material");
//! let resolved = mat.compute_surface_source().unwrap().expect("surface shader");
//! assert_eq!(resolved.id().unwrap().as_deref(), Some("UsdPreviewSurface"));
//! ```

pub mod tokens;

mod binding;
mod connectable;
mod preview;
mod schema;
mod traits;

pub use binding::MaterialBindingAPI;
pub use connectable::base_name;
pub use preview::{read_preview_surface, Channel, ReadPreviewSurface};
pub use schema::{Material, NodeGraph, Shader};
pub use traits::Connectable;

use tokens::*;

/// Implement the schema-trait memberships for a concrete UsdShade view. All
/// trait paths are fully qualified, so the call site only needs the macro in
/// scope.
///
/// - `connectable` is a concrete typed shading prim that carries `inputs:` /
///   `outputs:` ([`Shader`], [`NodeGraph`], [`Material`]).
/// - `single_api` is a single-apply API schema ([`MaterialBindingAPI`]).
macro_rules! impl_shade_schema {
    (connectable $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::ConcreteTyped;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
        impl $crate::schemas::shade::Connectable for $ty {}
    };
    (single_api $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::SingleApplyApi;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
    };
}

pub(crate) use impl_shade_schema;

/// `info:implementationSource` on a Shader — selects which `info:*` attribute
/// carries the shader's implementation. Pixar's fallback is
/// [`ImplementationSource::Id`].
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

/// `connectability` metadata on a UsdShadeInput — restricts what the input may
/// be connected to. Pixar's fallback is [`Connectability::Full`].
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

/// `bindMaterialAs` strength on a material-binding relationship — whether a
/// binding overrides ones authored lower in namespace. Pixar's fallback (when
/// `bindMaterialAs` is unauthored) is [`BindingStrength::WeakerThanDescendants`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum BindingStrength {
    /// Bindings on descendant prims win (the spec default).
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

// `From`/`TryFrom<Value>` for the token-valued enums, so they pass straight to
// `Attribute::set` / `get::<Enum>()`.
crate::schemas::common::impl_token_value!(ImplementationSource, Connectability, BindingStrength);
