//! The UsdLux interface traits shared across the light views.
//!
//! [`Light`] carries the `UsdLuxLightAPI` attribute surface every light
//! exposes. [`BoundableLight`] and [`NonboundableLight`] are the two abstract
//! bases (C++ `UsdLuxBoundableLightBase` / `UsdLuxNonboundableLightBase`):
//! they pair [`Light`] with the geom trait the light derives from
//! ([`geom::Boundable`] or [`geom::Xformable`]). Concrete light views
//! implement them through the `impl_lux_schema!` macro; the standalone
//! [`LightAPI`](super::LightAPI) applied-schema view implements [`Light`]
//! directly.

use anyhow::Result;

use crate::schemas::geom;
use crate::usd::{Attribute, Relationship, SchemaBase};

use super::tokens as tok;

/// The `UsdLuxLightAPI` interface (C++ `UsdLuxLightAPI`) — the light
/// parameters shared by every UsdLux light. Implemented by every concrete
/// light view through [`BoundableLight`] / [`NonboundableLight`], and by the
/// standalone [`LightAPI`](super::LightAPI) applied-schema view.
pub trait Light: SchemaBase {
    /// Scalar multiplier on the light's emitted power, scaling its overall
    /// brightness linearly (luminance in nits). C++ `UsdLuxLightAPI::GetIntensityAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    fn intensity_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_INTENSITY)
    }

    /// Author `inputs:intensity` (`float`) (C++ `CreateIntensityAttr`).
    fn create_intensity_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_INTENSITY, "float")?
            .set_custom(false)?)
    }

    /// Exponential brightness adjustment applied as a power of 2, like a
    /// camera f-stop: intensity is scaled by `2^exposure`. C++ `UsdLuxLightAPI::GetExposureAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    fn exposure_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_EXPOSURE)
    }

    /// Author `inputs:exposure` (`float`) (C++ `CreateExposureAttr`).
    fn create_exposure_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_EXPOSURE, "float")?
            .set_custom(false)?)
    }

    /// Non-physical multiplier on this light's contribution to material diffuse
    /// response, for artistic control. C++ `UsdLuxLightAPI::GetDiffuseAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    fn diffuse_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_DIFFUSE)
    }

    /// Author `inputs:diffuse` (`float`) (C++ `CreateDiffuseAttr`).
    fn create_diffuse_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_DIFFUSE, "float")?
            .set_custom(false)?)
    }

    /// Non-physical multiplier on this light's contribution to material specular
    /// response, for artistic control. C++ `UsdLuxLightAPI::GetSpecularAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    fn specular_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_SPECULAR)
    }

    /// Author `inputs:specular` (`float`) (C++ `CreateSpecularAttr`).
    fn create_specular_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_SPECULAR, "float")?
            .set_custom(false)?)
    }

    /// Whether to normalize emitted power by the light's surface area, so that
    /// changing the light's size keeps its total illumination constant. C++ `UsdLuxLightAPI::GetNormalizeAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    fn normalize_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_NORMALIZE)
    }

    /// Author `inputs:normalize` (`bool`) (C++ `CreateNormalizeAttr`).
    fn create_normalize_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_NORMALIZE, "bool")?
            .set_custom(false)?)
    }

    /// The emitted light color in the rendering color space, multiplied into the
    /// light's intensity (default `[1, 1, 1]`). C++ `UsdLuxLightAPI::GetColorAttr`.
    ///
    /// Type `color3f`. Fetch with `get::<[f32; 3]>()?`.
    fn color_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_COLOR)
    }

    /// Author `inputs:color` (`color3f`) (C++ `CreateColorAttr`).
    fn create_color_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_COLOR, "color3f")?
            .set_custom(false)?)
    }

    /// Whether color-temperature tinting is active; when true, the chromaticity
    /// from `colorTemperature` multiplies into the light's color. C++ `UsdLuxLightAPI::GetEnableColorTemperatureAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    fn enable_color_temperature_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_ENABLE_COLOR_TEMPERATURE)
    }

    /// Author `inputs:enableColorTemperature` (`bool`)
    /// (C++ `CreateEnableColorTemperatureAttr`).
    fn create_enable_color_temperature_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_ENABLE_COLOR_TEMPERATURE, "bool")?
            .set_custom(false)?)
    }

    /// Color temperature white point in degrees Kelvin (default 6500K, D65),
    /// applied only when `enableColorTemperature` is true. C++ `UsdLuxLightAPI::GetColorTemperatureAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    fn color_temperature_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_COLOR_TEMPERATURE)
    }

    /// Author `inputs:colorTemperature` (`float`)
    /// (C++ `CreateColorTemperatureAttr`).
    fn create_color_temperature_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_COLOR_TEMPERATURE, "float")?
            .set_custom(false)?)
    }

    /// Relationship targeting the LightFilter prims that modify this light's
    /// emission. C++ `UsdLuxLightAPI::GetFiltersRel`.
    fn filters_rel(&self) -> Relationship {
        self.prim().relationship(tok::REL_FILTERS)
    }

    /// Author the `light:filters` relationship (C++ `CreateFiltersRel`).
    fn create_filters_rel(&self) -> Result<Relationship> {
        Ok(self.prim().create_relationship(tok::REL_FILTERS)?.set_custom(false)?)
    }
}

/// A light with a bounded emissive surface (C++ `UsdLuxBoundableLightBase`):
/// a [`geom::Boundable`] gprim that is also a [`Light`]. The marker base every
/// boundable concrete light (`SphereLight`, `RectLight`, …) shares.
pub trait BoundableLight: geom::Boundable + Light {}

/// A light with no bounded emissive surface (C++
/// `UsdLuxNonboundableLightBase`): a [`geom::Xformable`] prim that is also a
/// [`Light`]. The marker base every nonboundable concrete light
/// (`DistantLight`, `DomeLight`, `GeometryLight`) shares.
pub trait NonboundableLight: geom::Xformable + Light {}
