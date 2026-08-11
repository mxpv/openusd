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
//! `UsdShadeConnectableAPI`). [`Input`] and [`Output`] are typed views over the
//! underlying [`Attribute`](crate::usd::Attribute). Connections remain core
//! attribute `connectionPaths`, available as raw composed paths through
//! [`Attribute::connections`](crate::usd::Attribute::connections).
//! [`ConnectedSources`] interprets those paths as valid or invalid UsdShade
//! sources, and [`Input::value_producing_attributes`] /
//! [`Output::value_producing_attributes`] follow container interfaces to the
//! logical shader outputs or authored interface values behind an attribute,
//! as far as [`ProducerFilter`] admits. Specialized consumers include
//! [`Material::compute_surface_source`] and [`read_preview_surface`].
//! To find every shading prim on a stage, traverse it and gate each prim
//! through the typed `get` (e.g. [`Material::get`]), mirroring C++
//! `prim.IsA<UsdShadeMaterial>()`.
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
//! surface.create_id_attr().unwrap().set(sdf::Value::token("UsdPreviewSurface")).unwrap();
//! surface.create_input("roughness", "float").unwrap().set(0.4_f32).unwrap();
//! let terminal = surface.create_output("surface", "token").unwrap();
//!
//! shade::Material::define(&stage, "/Mat").unwrap()
//!     .create_surface_output().unwrap()
//!     .connect_to(&terminal).unwrap();
//!
//! let mat = shade::Material::get(&stage, "/Mat").unwrap().expect("Material");
//! let resolved = mat.compute_surface_source().unwrap().expect("surface shader");
//! assert_eq!(resolved.id().unwrap().as_deref(), Some("UsdPreviewSurface"));
//! ```

pub mod tokens;

mod binding;
mod connectable;
mod input;
mod output;
mod preview;
mod schema;
mod traits;
mod utils;

pub use binding::MaterialBindingAPI;
pub use connectable::{
    AttributeType, ConnectedSources, ConnectionSource, ConnectionTarget, ShadingAttribute, base_name,
    base_name_and_type,
};
pub use input::Input;
pub use output::Output;
pub use preview::{Channel, ReadPreviewSurface, read_preview_surface};
pub use schema::{Material, NodeGraph, Shader};
pub use traits::Connectable;
pub use utils::ProducerFilter;

use crate::tf;
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

/// Implement the shading-attribute surface shared by [`Input`] and [`Output`]:
/// the namespace-checked constructors, the fluent authoring setters, and the
/// connection queries. `$prefix` is the namespace prefix every attribute the
/// view wraps carries. All paths are fully qualified, so the call site only
/// needs the macro in scope.
macro_rules! impl_shading_attribute {
    ($ty:ident, $prefix:expr) => {
        impl $ty {
            /// Wrap `attribute` when its name carries this view's namespace
            /// prefix (C++ `UsdShadeInput::IsInput` /
            /// `UsdShadeOutput::IsOutput`).
            pub fn from_attribute(attribute: $crate::usd::Attribute) -> Option<Self> {
                let namespaced = attribute
                    .path()
                    .split_property()?
                    .1
                    .strip_prefix($prefix)
                    .is_some();
                namespaced.then_some(Self { attribute })
            }

            /// The underlying composed USD attribute.
            pub fn attribute(&self) -> &$crate::usd::Attribute {
                &self.attribute
            }

            /// Consume this view and return its underlying USD attribute.
            pub fn into_attribute(self) -> $crate::usd::Attribute {
                self.attribute
            }

            /// The full attribute name, namespace prefix included, or `""`
            /// when the handle addresses no property — what a base name USD
            /// rejects leaves behind.
            pub fn full_name(&self) -> &str {
                self.attribute
                    .path()
                    .split_property()
                    .map_or("", |(_, name)| name)
            }

            /// The base name, with this view's namespace prefix stripped
            /// (C++ `GetBaseName`), or `""` when the handle addresses no
            /// namespaced property.
            pub fn base_name(&self) -> &str {
                self.full_name().strip_prefix($prefix).unwrap_or_default()
            }

            /// Author this attribute's default value.
            pub fn set(self, value: impl Into<$crate::sdf::Value>) -> Result<Self, $crate::usd::StageAuthoringError> {
                Ok(Self {
                    attribute: self.attribute.set(value)?,
                })
            }

            /// Author this attribute's value at a numeric time code.
            pub fn set_at(
                self,
                value: impl Into<$crate::sdf::Value>,
                time: impl Into<Option<$crate::usd::TimeCode>>,
            ) -> Result<Self, $crate::usd::StageAuthoringError> {
                Ok(Self {
                    attribute: self.attribute.set_at(value, time)?,
                })
            }

            /// Replace this attribute's composed connection source paths.
            pub fn set_connections<I>(self, targets: I) -> Result<Self, $crate::usd::StageAuthoringError>
            where
                I: IntoIterator<Item = $crate::sdf::Path>,
            {
                Ok(Self {
                    attribute: self.attribute.set_connections(targets)?,
                })
            }

            /// Connect this attribute to `source`, replacing existing
            /// connections (C++ `UsdShadeConnectableAPI::ConnectToSource`).
            ///
            /// Only a shading attribute can be named as a source, which is
            /// what [`ConnectionTarget`](crate::schemas::shade::ConnectionTarget)
            /// admits. It must already exist: authoring a connection never
            /// creates the attribute it targets, and a path that identifies
            /// none reads back through
            /// [`invalid_source_paths`](crate::schemas::shade::ConnectedSources::invalid_source_paths).
            pub fn connect_to(
                self,
                source: &impl $crate::schemas::shade::ConnectionTarget,
            ) -> Result<Self, $crate::usd::StageAuthoringError> {
                self.set_connections([source.target_path().clone()])
            }

            /// The renderer-specific `renderType` hint, when authored.
            pub fn render_type(&self) -> ::anyhow::Result<Option<$crate::tf::Token>> {
                self.attribute
                    .get_metadata($crate::schemas::shade::tokens::META_RENDER_TYPE)
            }

            /// Author this attribute's renderer-specific `renderType` hint.
            pub fn set_render_type(
                self,
                render_type: impl Into<$crate::tf::Token>,
            ) -> Result<Self, $crate::usd::StageAuthoringError> {
                Ok(Self {
                    attribute: self.attribute.set_metadata(
                        $crate::schemas::shade::tokens::META_RENDER_TYPE,
                        $crate::sdf::Value::Token(render_type.into()),
                    )?,
                })
            }

            /// Valid and invalid upstream connection sources, in composed order
            /// (C++ `UsdShadeConnectableAPI::GetConnectedSources`).
            pub fn connected_sources(&self) -> ::anyhow::Result<$crate::schemas::shade::ConnectedSources> {
                $crate::schemas::shade::connectable::connected_sources(&self.attribute)
            }

            /// The logical attributes that produce this attribute's value,
            /// following connections through NodeGraph and Material interfaces
            /// (C++ `UsdShadeUtils::GetValueProducingAttributes`).
            ///
            /// A connection cycle terminates the walk that entered it, so a
            /// chain that closes on itself contributes no producer.
            pub fn value_producing_attributes(
                &self,
                filter: $crate::schemas::shade::ProducerFilter,
            ) -> ::anyhow::Result<Vec<$crate::schemas::shade::ShadingAttribute>> {
                $crate::schemas::shade::utils::value_producing_attributes(
                    $crate::schemas::shade::ShadingAttribute::from(self.clone()),
                    filter,
                )
            }

            /// Wrap `attribute` without checking its namespace, for the
            /// accessors that build the name themselves.
            pub(super) fn new(attribute: $crate::usd::Attribute) -> Self {
                Self { attribute }
            }
        }
    };
}

pub(crate) use impl_shading_attribute;

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

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
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

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
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

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            STRENGTH_WEAKER_THAN_DESCENDANTS => BindingStrength::WeakerThanDescendants,
            STRENGTH_STRONGER_THAN_DESCENDANTS => BindingStrength::StrongerThanDescendants,
            _ => return None,
        })
    }
}

// `From`/`TryFrom<Value>` for the token-valued enums, so they pass straight to
// `Attribute::set` / `get::<Enum>()`.
crate::schemas::common::impl_token_value!(ImplementationSource, Connectability, BindingStrength);
