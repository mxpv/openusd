//! Decoded enums for the [UsdRender](super) schema family.
//!
//! Each enum's `Default` matches Pixar's `usdRender/schema.usda`
//! fallback exactly (`expandAperture` / `raster` / `raw`), so a reader
//! can `unwrap_or_default()` for a spec-correct fallback.

use super::tokens::*;

/// `aspectRatioConformPolicy` — how the camera aperture aspect ratio is
/// reconciled with the image aspect ratio (`resolution` ×
/// `pixelAspectRatio`).
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

/// `productType` — the kind of artifact a [`RenderProduct`](super) emits.
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

/// `sourceType` — how a [`RenderVar`](super)'s `sourceName` is interpreted.
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

/// The attributes shared by `RenderSettings` and `RenderProduct` via
/// their common abstract base `RenderSettingsBase` (camera + framing).
///
/// `Default` matches Pixar's `usdRender/schema.usda` fallbacks exactly,
/// so a reader can fall back per-field on an unauthored attribute.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadSettingsBase {
    /// `resolution` — image pixel resolution (default `(2048, 1080)`).
    pub resolution: [i32; 2],
    /// `pixelAspectRatio` — pixel width / height (default `1.0`).
    pub pixel_aspect_ratio: f32,
    /// `aspectRatioConformPolicy` (default `expandAperture`).
    pub aspect_ratio_conform_policy: AspectRatioConformPolicy,
    /// `dataWindowNDC` — render region `(xmin, ymin, xmax, ymax)` in NDC
    /// (default `(0, 0, 1, 1)`).
    pub data_window_ndc: [f32; 4],
    /// `instantaneousShutter` — deprecated in the C++ `UsdRender` schema,
    /// superseded by `disableMotionBlur`. Still read so older assets that
    /// author it round-trip (default `false`).
    pub instantaneous_shutter: bool,
    /// `disableMotionBlur` — force the shutter to `[0, 0]` (default `false`).
    pub disable_motion_blur: bool,
    /// `disableDepthOfField` — force a pinhole camera (default `false`).
    pub disable_depth_of_field: bool,
    /// `camera` relationship — path to the primary `UsdGeomCamera`, if
    /// authored. No fallback.
    pub camera: Option<String>,
}

impl Default for ReadSettingsBase {
    fn default() -> Self {
        Self {
            resolution: [2048, 1080],
            pixel_aspect_ratio: 1.0,
            aspect_ratio_conform_policy: AspectRatioConformPolicy::ExpandAperture,
            data_window_ndc: [0.0, 0.0, 1.0, 1.0],
            instantaneous_shutter: false,
            disable_motion_blur: false,
            disable_depth_of_field: false,
            camera: None,
        }
    }
}

/// A `RenderSettings` prim: the inherited base attributes plus the
/// top-level render configuration.
///
/// `Default` matches Pixar's `usdRender/schema.usda` fallbacks
/// (`includedPurposes = [default, render]`, `materialBindingPurposes =
/// [full, ""]`); `renderingColorSpace` has no fallback.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadRenderSettings {
    /// The inherited `RenderSettingsBase` attributes.
    pub base: ReadSettingsBase,
    /// `products` relationship — `RenderProduct` prims to produce.
    pub products: Vec<String>,
    /// `includedPurposes` (default `["default", "render"]`).
    pub included_purposes: Vec<String>,
    /// `materialBindingPurposes` (default `["full", ""]`).
    pub material_binding_purposes: Vec<String>,
    /// `renderingColorSpace` — the renderer's linear working space. No
    /// fallback (unauthored = renderer default).
    pub rendering_color_space: Option<String>,
}

impl Default for ReadRenderSettings {
    fn default() -> Self {
        Self {
            base: ReadSettingsBase::default(),
            products: Vec::new(),
            included_purposes: vec!["default".to_string(), "render".to_string()],
            material_binding_purposes: vec!["full".to_string(), String::new()],
            rendering_color_space: None,
        }
    }
}

/// A `RenderProduct` prim: the inherited base attributes (which it may
/// override) plus the product-specific configuration.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadRenderProduct {
    /// The inherited `RenderSettingsBase` attributes (per-field fallback;
    /// see the computed render spec for the authored-only override rule).
    pub base: ReadSettingsBase,
    /// `productType` (default `raster`).
    pub product_type: ProductType,
    /// `productName` — output/display-driver name (default `""`).
    pub product_name: String,
    /// `orderedVars` relationship — `RenderVar` prims composited, in order.
    pub ordered_vars: Vec<String>,
}

impl Default for ReadRenderProduct {
    fn default() -> Self {
        Self {
            base: ReadSettingsBase::default(),
            product_type: ProductType::Raster,
            product_name: String::new(),
            ordered_vars: Vec::new(),
        }
    }
}

/// A `RenderVar` prim: one output channel (AOV).
///
/// `Default` matches Pixar's `usdRender/schema.usda` (`dataType =
/// color3f`, `sourceName = ""`, `sourceType = raw`).
#[derive(Debug, Clone, PartialEq)]
pub struct ReadRenderVar {
    /// `dataType` — the channel's USD attribute type (default `color3f`).
    pub data_type: String,
    /// `sourceName` — the name the renderer looks up (default `""`).
    pub source_name: String,
    /// `sourceType` — how `sourceName` is interpreted (default `raw`).
    pub source_type: SourceType,
}

impl Default for ReadRenderVar {
    fn default() -> Self {
        Self {
            data_type: "color3f".to_string(),
            source_name: String::new(),
            source_type: SourceType::Raw,
        }
    }
}

/// A `RenderPass` prim: a node in a multi-pass render graph.
///
/// Covers the scalar attributes and the `renderSource` / `inputPasses`
/// relationships plus the two collection `includeRoot` flags. The
/// `renderVisibility` / `cameraVisibility` / `prune` / `matte`
/// collection-membership relationships (a multi-apply `CollectionAPI`)
/// are not modelled yet — they need collection-membership evaluation.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadRenderPass {
    /// `passType` — categorises the pass within a custom pipeline.
    pub pass_type: Option<String>,
    /// `command` — command + args to generate the pass (`{var}` substituted
    /// by the consumer).
    pub command: Vec<String>,
    /// `fileName` — external asset holding the pass's prims/config.
    pub file_name: Option<String>,
    /// `renderSource` relationship — first target (settings prim or external).
    pub render_source: Option<String>,
    /// `inputPasses` relationship — passes this one depends on.
    pub input_passes: Vec<String>,
    /// `collection:renderVisibility:includeRoot` (default `true`).
    pub render_visibility_include_root: bool,
    /// `collection:cameraVisibility:includeRoot` (default `true`).
    pub camera_visibility_include_root: bool,
}

impl Default for ReadRenderPass {
    fn default() -> Self {
        Self {
            pass_type: None,
            command: Vec::new(),
            file_name: None,
            render_source: None,
            input_passes: Vec::new(),
            render_visibility_include_root: true,
            camera_visibility_include_root: true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conform_policy_round_trips() {
        for p in [
            AspectRatioConformPolicy::ExpandAperture,
            AspectRatioConformPolicy::CropAperture,
            AspectRatioConformPolicy::AdjustApertureWidth,
            AspectRatioConformPolicy::AdjustApertureHeight,
            AspectRatioConformPolicy::AdjustPixelAspectRatio,
        ] {
            assert_eq!(AspectRatioConformPolicy::from_token(p.as_token()), Some(p));
        }
        assert_eq!(AspectRatioConformPolicy::from_token("bogus"), None);
        assert_eq!(
            AspectRatioConformPolicy::default(),
            AspectRatioConformPolicy::ExpandAperture
        );
    }

    #[test]
    fn product_type_round_trips() {
        for p in [ProductType::Raster, ProductType::DeepRaster] {
            assert_eq!(ProductType::from_token(p.as_token()), Some(p));
        }
        assert_eq!(ProductType::from_token("bogus"), None);
        assert_eq!(ProductType::default(), ProductType::Raster);
    }

    #[test]
    fn source_type_round_trips() {
        for s in [
            SourceType::Raw,
            SourceType::Primvar,
            SourceType::Lpe,
            SourceType::Intrinsic,
        ] {
            assert_eq!(SourceType::from_token(s.as_token()), Some(s));
        }
        assert_eq!(SourceType::from_token("bogus"), None);
        assert_eq!(SourceType::default(), SourceType::Raw);
    }
}
