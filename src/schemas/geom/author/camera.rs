//! `UsdGeomCamera` authoring.
//!
//! Mirrors the reader in [`super::super::camera`]: all schema attrs
//! (focal length / aperture / fStop / focus distance / clipping range,
//! plus shutter + exposure controls) are exposed as chainable setters.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::usd::{Prim, Stage};

use crate::schemas::geom::tokens::{
    A_CLIPPING_PLANES, A_CLIPPING_RANGE, A_EXPOSURE, A_EXPOSURE_F_STOP, A_EXPOSURE_ISO, A_EXPOSURE_RESPONSIVITY,
    A_EXPOSURE_TIME, A_FOCAL_LENGTH, A_FOCUS_DISTANCE, A_F_STOP, A_HORIZONTAL_APERTURE, A_HORIZONTAL_APERTURE_OFFSET,
    A_PROJECTION, A_SHUTTER_CLOSE, A_SHUTTER_OPEN, A_STEREO_ROLE, A_VERTICAL_APERTURE, A_VERTICAL_APERTURE_OFFSET,
    T_CAMERA,
};
use crate::schemas::geom::types::{Projection, StereoRole};

use super::common::{author_double, author_float, author_uniform_token};

/// Author a `def Camera` prim and return a chainable [`CameraAuthor`].
pub fn define_camera(stage: &Stage, path: impl Into<Path>) -> Result<CameraAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_CAMERA)?;
    Ok(CameraAuthor { prim })
}

pub struct CameraAuthor {
    prim: Prim,
}

impl CameraAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `projection` (uniform token, `perspective` / `orthographic`).
    pub fn set_projection(self, projection: Projection) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_PROJECTION, projection.as_token())?;
        Ok(self)
    }

    /// Set `focalLength` (float, mm).
    pub fn set_focal_length(self, mm: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_FOCAL_LENGTH, mm)?;
        Ok(self)
    }

    /// Set `horizontalAperture` (float, mm).
    pub fn set_horizontal_aperture(self, mm: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_HORIZONTAL_APERTURE, mm)?;
        Ok(self)
    }

    /// Set `verticalAperture` (float, mm).
    pub fn set_vertical_aperture(self, mm: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_VERTICAL_APERTURE, mm)?;
        Ok(self)
    }

    /// Set `horizontalApertureOffset` (float, mm).
    pub fn set_horizontal_aperture_offset(self, mm: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_HORIZONTAL_APERTURE_OFFSET, mm)?;
        Ok(self)
    }

    /// Set `verticalApertureOffset` (float, mm).
    pub fn set_vertical_aperture_offset(self, mm: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_VERTICAL_APERTURE_OFFSET, mm)?;
        Ok(self)
    }

    /// Set `fStop` (float, spec default 0.0 — pinhole). Pixar's
    /// schema uses 0.0 by default per the per-attribute fallback.
    pub fn set_f_stop(self, f_stop: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_F_STOP, f_stop)?;
        Ok(self)
    }

    /// Set `focusDistance` (float, scene units).
    pub fn set_focus_distance(self, distance: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_FOCUS_DISTANCE, distance)?;
        Ok(self)
    }

    /// Set `clippingRange` (float2, `(near, far)`).
    pub fn set_clipping_range(self, range: [f32; 2]) -> Result<Self> {
        let attr = self.prim.path().append_property(A_CLIPPING_RANGE)?;
        self.prim
            .stage()
            .create_attribute(attr, "float2")?
            .set_custom(false)?
            .set(Value::Vec2f(range))?;
        Ok(self)
    }

    /// Set `clippingPlanes` (float4[] — plane equations in camera space).
    pub fn set_clipping_planes(self, planes: Vec<[f32; 4]>) -> Result<Self> {
        let attr = self.prim.path().append_property(A_CLIPPING_PLANES)?;
        self.prim
            .stage()
            .create_attribute(attr, "float4[]")?
            .set_custom(false)?
            .set(Value::Vec4fVec(planes))?;
        Ok(self)
    }

    /// Set `shutter:open` (double, frame-relative seconds before frame).
    pub fn set_shutter_open(self, value: f64) -> Result<Self> {
        author_double(self.prim.stage(), self.prim.path(), A_SHUTTER_OPEN, value)?;
        Ok(self)
    }

    /// Set `shutter:close` (double, frame-relative seconds after frame).
    pub fn set_shutter_close(self, value: f64) -> Result<Self> {
        author_double(self.prim.stage(), self.prim.path(), A_SHUTTER_CLOSE, value)?;
        Ok(self)
    }

    /// Set `exposure` (float, stops).
    pub fn set_exposure(self, value: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_EXPOSURE, value)?;
        Ok(self)
    }

    /// Set `exposure:iso` (float).
    pub fn set_exposure_iso(self, value: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_EXPOSURE_ISO, value)?;
        Ok(self)
    }

    /// Set `exposure:time` (float, seconds).
    pub fn set_exposure_time(self, value: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_EXPOSURE_TIME, value)?;
        Ok(self)
    }

    /// Set `exposure:fStop` (float).
    pub fn set_exposure_f_stop(self, value: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_EXPOSURE_F_STOP, value)?;
        Ok(self)
    }

    /// Set `exposure:responsivity` (float).
    pub fn set_exposure_responsivity(self, value: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_EXPOSURE_RESPONSIVITY, value)?;
        Ok(self)
    }

    /// Set `stereoRole` (uniform token, `mono` / `left` / `right`).
    pub fn set_stereo_role(self, role: StereoRole) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_STEREO_ROLE, role.as_token())?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn camera_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_camera(&stage, sdf::path("/Cam")?)?
            .set_projection(Projection::Perspective)?
            .set_focal_length(50.0)?
            .set_horizontal_aperture(36.0)?
            .set_vertical_aperture(24.0)?
            .set_f_stop(2.8)?
            .set_focus_distance(3.0)?
            .set_clipping_range([0.1, 1000.0])?
            .set_shutter_open(-0.25)?
            .set_shutter_close(0.25)?;

        let cam = crate::schemas::geom::read_camera(&stage, &sdf::path("/Cam")?)?.expect("Camera");
        assert!((cam.focal_length - 50.0).abs() < 1e-3);
        assert!((cam.horizontal_aperture - 36.0).abs() < 1e-3);
        assert_eq!(cam.projection, Projection::Perspective);
        assert!((cam.f_stop - 2.8).abs() < 1e-3);
        assert_eq!(cam.clipping_range, [0.1, 1000.0]);
        assert!((cam.shutter_open - -0.25).abs() < 1e-6);
        Ok(())
    }
}
