//! Shared `RenderSettingsBase` authoring.
//!
//! [`SettingsBaseSetters`] is mixed into both the `RenderSettings` and
//! `RenderProduct` author handles (the `*ApiSetters` idiom) — the two
//! concrete schemas that inherit `RenderSettingsBase`, so they share the
//! camera + framing setters.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Prim, Stage};

use crate::schemas::common::{author_rel_targets, author_uniform_token};
use crate::schemas::render::tokens::*;
use crate::schemas::render::types::AspectRatioConformPolicy;

/// Setters for the attributes declared on `RenderSettingsBase`
/// (`resolution`, `pixelAspectRatio`, `aspectRatioConformPolicy`,
/// `dataWindowNDC`, the motion-blur / depth-of-field toggles, and the
/// `camera` relationship). Implementors expose their underlying prim.
pub trait SettingsBaseSetters: Sized {
    /// Borrow the underlying prim handle.
    fn prim(&self) -> &Prim;

    /// Set `resolution` (`uniform int2`).
    fn set_resolution(self, value: [i32; 2]) -> Result<Self> {
        author_uniform_int2(self.prim().stage(), self.prim().path(), A_RESOLUTION, value)?;
        Ok(self)
    }

    /// Set `pixelAspectRatio` (`uniform float`).
    fn set_pixel_aspect_ratio(self, value: f32) -> Result<Self> {
        author_uniform_float(self.prim().stage(), self.prim().path(), A_PIXEL_ASPECT_RATIO, value)?;
        Ok(self)
    }

    /// Set `aspectRatioConformPolicy` (`uniform token`).
    fn set_aspect_ratio_conform_policy(self, value: AspectRatioConformPolicy) -> Result<Self> {
        author_uniform_token(
            self.prim().stage(),
            self.prim().path(),
            A_ASPECT_RATIO_CONFORM_POLICY,
            value.as_token(),
        )?;
        Ok(self)
    }

    /// Set `dataWindowNDC` (`uniform float4`) — `(xmin, ymin, xmax, ymax)`.
    fn set_data_window_ndc(self, value: [f32; 4]) -> Result<Self> {
        author_uniform_float4(self.prim().stage(), self.prim().path(), A_DATA_WINDOW_NDC, value)?;
        Ok(self)
    }

    /// Set `instantaneousShutter` (`uniform bool`) — deprecated in the C++
    /// `UsdRender` schema; prefer [`Self::set_disable_motion_blur`].
    fn set_instantaneous_shutter(self, value: bool) -> Result<Self> {
        author_uniform_bool(self.prim().stage(), self.prim().path(), A_INSTANTANEOUS_SHUTTER, value)?;
        Ok(self)
    }

    /// Set `disableMotionBlur` (`uniform bool`).
    fn set_disable_motion_blur(self, value: bool) -> Result<Self> {
        author_uniform_bool(self.prim().stage(), self.prim().path(), A_DISABLE_MOTION_BLUR, value)?;
        Ok(self)
    }

    /// Set `disableDepthOfField` (`uniform bool`).
    fn set_disable_depth_of_field(self, value: bool) -> Result<Self> {
        author_uniform_bool(self.prim().stage(), self.prim().path(), A_DISABLE_DEPTH_OF_FIELD, value)?;
        Ok(self)
    }

    /// Set the `camera` relationship to the primary `UsdGeomCamera`.
    fn set_camera(self, camera: impl Into<Path>) -> Result<Self> {
        author_rel_targets(self.prim().stage(), self.prim().path(), REL_CAMERA, [camera.into()])?;
        Ok(self)
    }
}

// ── private uniform-attribute helpers ───────────────────────────────

fn author_uniform_int2(stage: &Stage, prim: &Path, name: &str, value: [i32; 2]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "int2")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Vec2i(value))?;
    Ok(())
}

fn author_uniform_float(stage: &Stage, prim: &Path, name: &str, value: f32) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "float")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Float(value))?;
    Ok(())
}

fn author_uniform_float4(stage: &Stage, prim: &Path, name: &str, value: [f32; 4]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "float4")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Vec4f(value))?;
    Ok(())
}

fn author_uniform_bool(stage: &Stage, prim: &Path, name: &str, value: bool) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "bool")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Bool(value))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::render::tokens::T_RENDER_SETTINGS;
    use crate::schemas::render::{read_settings_base, ReadSettingsBase};
    use crate::sdf;

    /// Minimal host for the shared trait so it can be exercised before the
    /// concrete `RenderSettings` / `RenderProduct` handles exist.
    struct TestBase {
        prim: Prim,
    }
    impl SettingsBaseSetters for TestBase {
        fn prim(&self) -> &Prim {
            &self.prim
        }
    }

    #[test]
    fn base_attrs_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let prim = stage
            .define_prim(sdf::path("/Render/Settings")?)?
            .set_type_name(T_RENDER_SETTINGS)?;
        TestBase { prim }
            .set_resolution([1920, 1080])?
            .set_pixel_aspect_ratio(2.0)?
            .set_aspect_ratio_conform_policy(AspectRatioConformPolicy::CropAperture)?
            .set_data_window_ndc([0.1, 0.2, 0.9, 0.8])?
            .set_disable_motion_blur(true)?
            .set_disable_depth_of_field(true)?
            .set_camera(sdf::path("/World/Cam")?)?;

        let base = read_settings_base(&stage, &sdf::path("/Render/Settings")?)?;
        assert_eq!(base.resolution, [1920, 1080]);
        assert!((base.pixel_aspect_ratio - 2.0).abs() < 1e-6);
        assert_eq!(base.aspect_ratio_conform_policy, AspectRatioConformPolicy::CropAperture);
        assert_eq!(base.data_window_ndc, [0.1, 0.2, 0.9, 0.8]);
        assert!(base.disable_motion_blur);
        assert!(base.disable_depth_of_field);
        assert!(!base.instantaneous_shutter);
        assert_eq!(base.camera.as_deref(), Some("/World/Cam"));
        Ok(())
    }

    #[test]
    fn base_attrs_fall_back_to_spec_defaults() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage
            .define_prim(sdf::path("/Render/Settings")?)?
            .set_type_name(T_RENDER_SETTINGS)?;

        let base = read_settings_base(&stage, &sdf::path("/Render/Settings")?)?;
        assert_eq!(base, ReadSettingsBase::default());
        assert_eq!(base.resolution, [2048, 1080]);
        assert_eq!(
            base.aspect_ratio_conform_policy,
            AspectRatioConformPolicy::ExpandAperture
        );
        assert_eq!(base.camera, None);
        Ok(())
    }
}
