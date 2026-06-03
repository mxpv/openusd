//! The UsdRender interface trait shared by the framing prims.
//!
//! [`RenderSettingsBase`] (C++ `UsdRenderSettingsBase`) is the abstract base
//! carrying the camera + image-framing attributes shared by
//! [`RenderSettings`](super::RenderSettings) and
//! [`RenderProduct`](super::RenderProduct). A product inherits these from the
//! settings it is produced from and may override any of them. Concrete views
//! implement it through the `impl_render_schema!(settings_base ...)` macro arm.

use anyhow::Result;

use crate::sdf::Variability;
use crate::usd::{Attribute, Relationship, SchemaBase};

use super::tokens as tok;

/// The camera + framing attributes shared by `RenderSettings` and
/// `RenderProduct` via their common abstract base (C++
/// `UsdRenderSettingsBase`): the bound camera, image resolution, pixel aspect
/// ratio, aspect-ratio conform policy, data window, and the motion-blur /
/// depth-of-field toggles.
pub trait RenderSettingsBase: SchemaBase {
    /// The image pixel resolution `(width, height)`.
    /// C++ `UsdRenderSettingsBase::GetResolutionAttr`.
    ///
    /// Type `uniform int2`. Fetch with `get::<sdf::Value>()?` (a
    /// [`sdf::Value::Vec2i`](crate::sdf::Value::Vec2i)).
    fn resolution_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_RESOLUTION)
    }

    /// Author `resolution` (`uniform int2`) (C++ `CreateResolutionAttr`).
    fn create_resolution_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_RESOLUTION, "int2")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// The aspect ratio (width / height) of a pixel.
    /// C++ `UsdRenderSettingsBase::GetPixelAspectRatioAttr`.
    ///
    /// Type `uniform float`. Fetch with `get::<f32>()?`.
    fn pixel_aspect_ratio_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_PIXEL_ASPECT_RATIO)
    }

    /// Author `pixelAspectRatio` (`uniform float`)
    /// (C++ `CreatePixelAspectRatioAttr`).
    fn create_pixel_aspect_ratio_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_PIXEL_ASPECT_RATIO, "float")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// How the camera aperture aspect is reconciled with the image aspect.
    /// C++ `UsdRenderSettingsBase::GetAspectRatioConformPolicyAttr`.
    ///
    /// Type `uniform token`. Fetch with
    /// `get::<`[`AspectRatioConformPolicy`](super::AspectRatioConformPolicy)`>()?`.
    fn aspect_ratio_conform_policy_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_ASPECT_RATIO_CONFORM_POLICY)
    }

    /// Author `aspectRatioConformPolicy` (`uniform token`)
    /// (C++ `CreateAspectRatioConformPolicyAttr`). Pass an
    /// [`AspectRatioConformPolicy`](super::AspectRatioConformPolicy) to `set`.
    fn create_aspect_ratio_conform_policy_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_ASPECT_RATIO_CONFORM_POLICY, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// The render region as `(xmin, ymin, xmax, ymax)` in normalized device
    /// coordinates. C++ `UsdRenderSettingsBase::GetDataWindowNDCAttr`.
    ///
    /// Type `uniform float4`. Fetch with `get::<[f32; 4]>()?`.
    fn data_window_ndc_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_DATA_WINDOW_NDC)
    }

    /// Author `dataWindowNDC` (`uniform float4`) (C++ `CreateDataWindowNDCAttr`).
    fn create_data_window_ndc_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_DATA_WINDOW_NDC, "float4")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Whether to render with an instantaneous shutter (no motion blur).
    /// Deprecated in the C++ `UsdRender` schema, superseded by
    /// [`Self::disable_motion_blur_attr`]; still read so older assets
    /// round-trip. C++ `UsdRenderSettingsBase::GetInstantaneousShutterAttr`.
    ///
    /// Type `uniform bool`. Fetch with `get::<bool>()?`.
    fn instantaneous_shutter_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_INSTANTANEOUS_SHUTTER)
    }

    /// Author `instantaneousShutter` (`uniform bool`)
    /// (C++ `CreateInstantaneousShutterAttr`).
    fn create_instantaneous_shutter_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_INSTANTANEOUS_SHUTTER, "bool")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Whether to force the shutter to `[0, 0]`, disabling motion blur.
    /// C++ `UsdRenderSettingsBase::GetDisableMotionBlurAttr`.
    ///
    /// Type `uniform bool`. Fetch with `get::<bool>()?`.
    fn disable_motion_blur_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_DISABLE_MOTION_BLUR)
    }

    /// Author `disableMotionBlur` (`uniform bool`)
    /// (C++ `CreateDisableMotionBlurAttr`).
    fn create_disable_motion_blur_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_DISABLE_MOTION_BLUR, "bool")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Whether to force a pinhole camera, disabling depth of field.
    /// C++ `UsdRenderSettingsBase::GetDisableDepthOfFieldAttr`.
    ///
    /// Type `uniform bool`. Fetch with `get::<bool>()?`.
    fn disable_depth_of_field_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_DISABLE_DEPTH_OF_FIELD)
    }

    /// Author `disableDepthOfField` (`uniform bool`)
    /// (C++ `CreateDisableDepthOfFieldAttr`).
    fn create_disable_depth_of_field_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_DISABLE_DEPTH_OF_FIELD, "bool")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// The `camera` relationship targeting the primary `UsdGeomCamera`.
    /// C++ `UsdRenderSettingsBase::GetCameraRel`.
    fn camera_rel(&self) -> Relationship {
        self.prim().relationship(tok::REL_CAMERA)
    }

    /// Author the `camera` relationship (C++ `CreateCameraRel`).
    fn create_camera_rel(&self) -> Result<Relationship> {
        Ok(self.prim().create_relationship(tok::REL_CAMERA)?.set_custom(false)?)
    }
}
