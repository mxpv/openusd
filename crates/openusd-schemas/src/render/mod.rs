//! UsdRender schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdRender` family — the description of *what* to render and *how* the
//! output is framed and split into channels.
//!
//! ```text
//! SchemaBase
//!  ├ SettingsBase  (interface; shared camera + framing attrs)
//!  │  ├ Settings    (typed; top-level config + products)
//!  │  └ Product     (typed; one output artifact, overrides the base)
//!  ├ Var            (typed; one output channel / AOV)
//!  ├ Pass           (typed; a node in a multi-pass graph)
//! ```
//!
//! [`SettingsBase`] carries the camera + image-framing attributes shared
//! by [`Settings`] and [`Product`]. The centrepiece is the computed
//! *render spec* ([`compute_render_spec`]): a `Settings` prim, its
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
//! use openusd::sdf;
//! use openusd_schemas::render::{self, ProductSchema, SettingsBase, SettingsSchema};
//! use openusd::usd::Stage;
//!
//! let stage = Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("scene.usda").unwrap();
//!
//! let settings = render::Settings::define(&stage, "/Render/Settings").unwrap();
//! settings.create_resolution_attr().unwrap().set(gf::vec2i(1920, 1080)).unwrap();
//! settings.create_products_rel().unwrap().add_target("/Render/Products/beauty").unwrap();
//!
//! render::Product::define(&stage, "/Render/Products/beauty").unwrap()
//!     .create_product_name_attr().unwrap()
//!     .set(sdf::Value::token("beauty.exr")).unwrap();
//!
//! let spec = render::compute_render_spec(&stage, &"/Render/Settings".parse().unwrap(), &[]).unwrap()
//!     .expect("RenderSpec");
//! assert_eq!(spec.products.len(), 1);
//! ```

openusd::include_schema!("usdRender");

pub mod spec;

mod compute;
mod conform;
mod settings;

pub use compute::{compute_namespaced_settings, compute_render_spec};
pub use conform::{ConformedAperture, apply_aspect_ratio_policy};

use openusd::tf;
use tokens::*;

// The collections a `RenderPass` carries, each an instance name of
// `UsdCollectionAPI` rather than a property of the pass.
pub const COLLECTION_CAMERA_VISIBILITY: &str = "cameraVisibility";
pub const COLLECTION_PRUNE: &str = "prune";
pub const COLLECTION_MATTE: &str = "matte";

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
            AspectRatioConformPolicy::ExpandAperture => EXPAND_APERTURE,
            AspectRatioConformPolicy::CropAperture => CROP_APERTURE,
            AspectRatioConformPolicy::AdjustApertureWidth => ADJUST_APERTURE_WIDTH,
            AspectRatioConformPolicy::AdjustApertureHeight => ADJUST_APERTURE_HEIGHT,
            AspectRatioConformPolicy::AdjustPixelAspectRatio => ADJUST_PIXEL_ASPECT_RATIO,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            EXPAND_APERTURE => AspectRatioConformPolicy::ExpandAperture,
            CROP_APERTURE => AspectRatioConformPolicy::CropAperture,
            ADJUST_APERTURE_WIDTH => AspectRatioConformPolicy::AdjustApertureWidth,
            ADJUST_APERTURE_HEIGHT => AspectRatioConformPolicy::AdjustApertureHeight,
            ADJUST_PIXEL_ASPECT_RATIO => AspectRatioConformPolicy::AdjustPixelAspectRatio,
            _ => return None,
        })
    }
}

/// `productType` — the kind of artifact a [`Product`] emits. Pixar's
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
            ProductType::Raster => RASTER,
            ProductType::DeepRaster => DEEP_RASTER,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            RASTER => ProductType::Raster,
            DEEP_RASTER => ProductType::DeepRaster,
            _ => return None,
        })
    }
}

/// `sourceType` — how a [`Var`]'s `sourceName` is interpreted. Pixar's
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
            SourceType::Raw => RAW,
            SourceType::Primvar => PRIMVAR,
            SourceType::Lpe => LPE,
            SourceType::Intrinsic => INTRINSIC,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            RAW => SourceType::Raw,
            PRIMVAR => SourceType::Primvar,
            LPE => SourceType::Lpe,
            INTRINSIC => SourceType::Intrinsic,
            _ => return None,
        })
    }
}

// `From`/`TryFrom<Value>` for the token-valued enums, so they pass straight to
// `Attribute::set` / `get::<Enum>()`.
crate::token_value::impl_token_value!(AspectRatioConformPolicy, ProductType, SourceType);
