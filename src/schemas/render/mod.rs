//! UsdRender schema views.
//!
//! Typed value-views over a composed [`crate::usd::Stage`], mirroring Pixar's
//! `UsdRender` family — the description of *what* to render and *how* the
//! output is framed and split into channels.
//!
//! ```text
//! SchemaBase
//!  ├ RenderSettingsBase  (interface; shared camera + framing attrs)
//!  │  ├ RenderSettings    (typed; top-level config + products)
//!  │  └ RenderProduct     (typed; one output artifact, overrides the base)
//!  ├ RenderVar            (typed; one output channel / AOV)
//!  ├ RenderPass           (typed; a node in a multi-pass graph)
//!  └ RenderDenoisePass    (typed; dev-era denoise marker)
//! ```
//!
//! [`RenderSettingsBase`] carries the camera + image-framing attributes shared
//! by [`RenderSettings`] and [`RenderProduct`]. The centrepiece is the computed
//! *render spec* ([`compute_render_spec`]): a `RenderSettings` prim, its
//! products, vars, and camera are flattened into a self-contained,
//! fallback-resolved [`RenderSpec`](spec::RenderSpec) (product attributes
//! overriding settings, the aspect-ratio conform policy applied, vars
//! de-duplicated). That computation reads through these views and is the
//! spec-faithful crux of the family.
//!
//! # Example
//!
//! ```
//! use openusd::gf;
//! use openusd::schemas::render::{self, RenderSettingsBase};
//! use openusd::usd::Stage;
//!
//! let stage = Stage::builder().in_memory("scene.usda").unwrap();
//!
//! let settings = render::RenderSettings::define(&stage, "/Render/Settings").unwrap();
//! settings.create_resolution_attr().unwrap().set(gf::vec2i(1920, 1080)).unwrap();
//! settings.create_products_rel().unwrap().add_target("/Render/Products/beauty".parse().unwrap()).unwrap();
//!
//! render::RenderProduct::define(&stage, "/Render/Products/beauty").unwrap()
//!     .create_product_name_attr().unwrap()
//!     .set("beauty.exr".to_string()).unwrap();
//!
//! let spec = render::compute_render_spec(&stage, &"/Render/Settings".parse().unwrap(), &[]).unwrap()
//!     .expect("RenderSpec");
//! assert_eq!(spec.products.len(), 1);
//! ```

pub mod spec;
pub mod tokens;

mod compute;
mod conform;
mod schema;
mod traits;

pub use compute::{compute_namespaced_settings, compute_render_spec};
pub use conform::{apply_aspect_ratio_policy, ConformedAperture};
pub use schema::{RenderDenoisePass, RenderPass, RenderProduct, RenderSettings, RenderVar};
pub use traits::RenderSettingsBase;

use tokens::*;

/// Implement the schema-trait memberships for a concrete UsdRender view. All
/// trait paths are fully qualified, so the call site only needs the macro in
/// scope.
///
/// - `typed` is a concrete typed prim ([`RenderVar`], [`RenderPass`],
///   [`RenderDenoisePass`]).
/// - `settings_base` is a typed prim that also implements
///   [`RenderSettingsBase`] ([`RenderSettings`], [`RenderProduct`]).
macro_rules! impl_render_schema {
    (typed $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::ConcreteTyped;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
    };
    (settings_base $ty:ident) => {
        impl_render_schema!(typed $ty);
        impl $crate::schemas::render::RenderSettingsBase for $ty {}
    };
}

pub(crate) use impl_render_schema;

/// `aspectRatioConformPolicy` — how the camera aperture aspect ratio is
/// reconciled with the image aspect ratio (`resolution` ×
/// `pixelAspectRatio`). Pixar's `usdRender/schema.usda` fallback is
/// [`AspectRatioConformPolicy::ExpandAperture`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AspectRatioConformPolicy {
    /// Grow the aperture so nothing is cropped (the spec default).
    #[default]
    ExpandAperture,
    /// Shrink the aperture, cropping content.
    CropAperture,
    /// Keep aperture height; set width from the image aspect.
    AdjustApertureWidth,
    /// Keep aperture width; set height from the image aspect.
    AdjustApertureHeight,
    /// Keep the aperture; change `pixelAspectRatio` to fit.
    AdjustPixelAspectRatio,
}

impl AspectRatioConformPolicy {
    pub fn as_token(self) -> &'static str {
        match self {
            AspectRatioConformPolicy::ExpandAperture => CONFORM_EXPAND_APERTURE,
            AspectRatioConformPolicy::CropAperture => CONFORM_CROP_APERTURE,
            AspectRatioConformPolicy::AdjustApertureWidth => CONFORM_ADJUST_APERTURE_WIDTH,
            AspectRatioConformPolicy::AdjustApertureHeight => CONFORM_ADJUST_APERTURE_HEIGHT,
            AspectRatioConformPolicy::AdjustPixelAspectRatio => CONFORM_ADJUST_PIXEL_ASPECT_RATIO,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            CONFORM_EXPAND_APERTURE => AspectRatioConformPolicy::ExpandAperture,
            CONFORM_CROP_APERTURE => AspectRatioConformPolicy::CropAperture,
            CONFORM_ADJUST_APERTURE_WIDTH => AspectRatioConformPolicy::AdjustApertureWidth,
            CONFORM_ADJUST_APERTURE_HEIGHT => AspectRatioConformPolicy::AdjustApertureHeight,
            CONFORM_ADJUST_PIXEL_ASPECT_RATIO => AspectRatioConformPolicy::AdjustPixelAspectRatio,
            _ => return None,
        })
    }
}

/// `productType` — the kind of artifact a [`RenderProduct`] emits. Pixar's
/// fallback is [`ProductType::Raster`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ProductType {
    /// A 2D raster image (the spec default).
    #[default]
    Raster,
    /// A deep image carrying multiple samples per pixel.
    DeepRaster,
}

impl ProductType {
    pub fn as_token(self) -> &'static str {
        match self {
            ProductType::Raster => PRODUCT_TYPE_RASTER,
            ProductType::DeepRaster => PRODUCT_TYPE_DEEP_RASTER,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            PRODUCT_TYPE_RASTER => ProductType::Raster,
            PRODUCT_TYPE_DEEP_RASTER => ProductType::DeepRaster,
            _ => return None,
        })
    }
}

/// `sourceType` — how a [`RenderVar`]'s `sourceName` is interpreted. Pixar's
/// fallback is [`SourceType::Raw`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SourceType {
    /// `sourceName` is a direct renderer output identifier (the default).
    #[default]
    Raw,
    /// `sourceName` names a primvar to output.
    Primvar,
    /// `sourceName` is a Light Path Expression.
    Lpe,
    /// A renderer-intrinsic quantity (e.g. geometric data, compute time).
    Intrinsic,
}

impl SourceType {
    pub fn as_token(self) -> &'static str {
        match self {
            SourceType::Raw => SOURCE_TYPE_RAW,
            SourceType::Primvar => SOURCE_TYPE_PRIMVAR,
            SourceType::Lpe => SOURCE_TYPE_LPE,
            SourceType::Intrinsic => SOURCE_TYPE_INTRINSIC,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            SOURCE_TYPE_RAW => SourceType::Raw,
            SOURCE_TYPE_PRIMVAR => SourceType::Primvar,
            SOURCE_TYPE_LPE => SourceType::Lpe,
            SOURCE_TYPE_INTRINSIC => SourceType::Intrinsic,
            _ => return None,
        })
    }
}

// `From`/`TryFrom<Value>` for the token-valued enums, so they pass straight to
// `Attribute::set` / `get::<Enum>()`.
crate::schemas::common::impl_token_value!(AspectRatioConformPolicy, ProductType, SourceType);
