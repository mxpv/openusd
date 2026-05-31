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
