//! `UsdGeomCamera` — a camera prim.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, SchemaBase, SchemaKind, Stage};

use super::tokens as tok;
use super::{create, create_uniform_token, get_typed};
use super::{impl_geom_schema, Imageable, Xformable};

/// A camera prim (C++ `UsdGeomCamera`) — an [`Xformable`] exposing the lens /
/// aperture / shutter / exposure attributes. Attribute getters return a
/// handle whose `get()` yields the authored value (or `None`); the
/// projection / stereo-role token values are [`super::Projection`] /
/// [`super::StereoRole`].
#[derive(Clone, derive_more::Deref)]
pub struct Camera(Prim);

impl Camera {
    /// Author a `def Camera` prim at `path` (C++ `UsdGeomCamera::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_CAMERA)?))
    }

    /// Wrap `path` as a `Camera` if it is typed `Camera`
    /// (C++ `UsdGeomCamera::Get`); returns `None` otherwise.
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_CAMERA).map(|o| o.map(Self))
    }

    /// `focalLength` attribute handle (C++ `GetFocalLengthAttr`).
    pub fn focal_length_attr(&self) -> Attribute {
        self.attribute(tok::A_FOCAL_LENGTH)
    }

    /// Author `focalLength` (`float`, mm) (C++ `CreateFocalLengthAttr`).
    pub fn create_focal_length_attr(&self) -> Result<Attribute> {
        create(self, tok::A_FOCAL_LENGTH, "float")
    }

    /// `horizontalAperture` attribute handle (C++ `GetHorizontalApertureAttr`).
    pub fn horizontal_aperture_attr(&self) -> Attribute {
        self.attribute(tok::A_HORIZONTAL_APERTURE)
    }

    /// Author `horizontalAperture` (`float`, mm).
    pub fn create_horizontal_aperture_attr(&self) -> Result<Attribute> {
        create(self, tok::A_HORIZONTAL_APERTURE, "float")
    }

    /// `verticalAperture` attribute handle (C++ `GetVerticalApertureAttr`).
    pub fn vertical_aperture_attr(&self) -> Attribute {
        self.attribute(tok::A_VERTICAL_APERTURE)
    }

    /// Author `verticalAperture` (`float`, mm).
    pub fn create_vertical_aperture_attr(&self) -> Result<Attribute> {
        create(self, tok::A_VERTICAL_APERTURE, "float")
    }

    /// `horizontalApertureOffset` attribute handle.
    pub fn horizontal_aperture_offset_attr(&self) -> Attribute {
        self.attribute(tok::A_HORIZONTAL_APERTURE_OFFSET)
    }

    /// Author `horizontalApertureOffset` (`float`, mm).
    pub fn create_horizontal_aperture_offset_attr(&self) -> Result<Attribute> {
        create(self, tok::A_HORIZONTAL_APERTURE_OFFSET, "float")
    }

    /// `verticalApertureOffset` attribute handle.
    pub fn vertical_aperture_offset_attr(&self) -> Attribute {
        self.attribute(tok::A_VERTICAL_APERTURE_OFFSET)
    }

    /// Author `verticalApertureOffset` (`float`, mm).
    pub fn create_vertical_aperture_offset_attr(&self) -> Result<Attribute> {
        create(self, tok::A_VERTICAL_APERTURE_OFFSET, "float")
    }

    /// `fStop` attribute handle (C++ `GetFStopAttr`).
    pub fn f_stop_attr(&self) -> Attribute {
        self.attribute(tok::A_F_STOP)
    }

    /// Author `fStop` (`float`).
    pub fn create_f_stop_attr(&self) -> Result<Attribute> {
        create(self, tok::A_F_STOP, "float")
    }

    /// `focusDistance` attribute handle (C++ `GetFocusDistanceAttr`).
    pub fn focus_distance_attr(&self) -> Attribute {
        self.attribute(tok::A_FOCUS_DISTANCE)
    }

    /// Author `focusDistance` (`float`, scene units).
    pub fn create_focus_distance_attr(&self) -> Result<Attribute> {
        create(self, tok::A_FOCUS_DISTANCE, "float")
    }

    /// `exposure` attribute handle (C++ `GetExposureAttr`).
    pub fn exposure_attr(&self) -> Attribute {
        self.attribute(tok::A_EXPOSURE)
    }

    /// Author `exposure` (`float`, stops).
    pub fn create_exposure_attr(&self) -> Result<Attribute> {
        create(self, tok::A_EXPOSURE, "float")
    }

    /// `exposure:iso` attribute handle.
    pub fn exposure_iso_attr(&self) -> Attribute {
        self.attribute(tok::A_EXPOSURE_ISO)
    }

    /// Author `exposure:iso` (`float`).
    pub fn create_exposure_iso_attr(&self) -> Result<Attribute> {
        create(self, tok::A_EXPOSURE_ISO, "float")
    }

    /// `exposure:time` attribute handle.
    pub fn exposure_time_attr(&self) -> Attribute {
        self.attribute(tok::A_EXPOSURE_TIME)
    }

    /// Author `exposure:time` (`float`, seconds).
    pub fn create_exposure_time_attr(&self) -> Result<Attribute> {
        create(self, tok::A_EXPOSURE_TIME, "float")
    }

    /// `exposure:fStop` attribute handle.
    pub fn exposure_f_stop_attr(&self) -> Attribute {
        self.attribute(tok::A_EXPOSURE_F_STOP)
    }

    /// Author `exposure:fStop` (`float`).
    pub fn create_exposure_f_stop_attr(&self) -> Result<Attribute> {
        create(self, tok::A_EXPOSURE_F_STOP, "float")
    }

    /// `exposure:responsivity` attribute handle.
    pub fn exposure_responsivity_attr(&self) -> Attribute {
        self.attribute(tok::A_EXPOSURE_RESPONSIVITY)
    }

    /// Author `exposure:responsivity` (`float`).
    pub fn create_exposure_responsivity_attr(&self) -> Result<Attribute> {
        create(self, tok::A_EXPOSURE_RESPONSIVITY, "float")
    }

    /// `shutter:open` attribute handle.
    pub fn shutter_open_attr(&self) -> Attribute {
        self.attribute(tok::A_SHUTTER_OPEN)
    }

    /// Author `shutter:open` (`double`, frame-relative seconds).
    pub fn create_shutter_open_attr(&self) -> Result<Attribute> {
        create(self, tok::A_SHUTTER_OPEN, "double")
    }

    /// `shutter:close` attribute handle.
    pub fn shutter_close_attr(&self) -> Attribute {
        self.attribute(tok::A_SHUTTER_CLOSE)
    }

    /// Author `shutter:close` (`double`, frame-relative seconds).
    pub fn create_shutter_close_attr(&self) -> Result<Attribute> {
        create(self, tok::A_SHUTTER_CLOSE, "double")
    }

    /// `projection` attribute handle — `perspective` / `orthographic`
    /// (C++ `GetProjectionAttr`).
    pub fn projection_attr(&self) -> Attribute {
        self.attribute(tok::A_PROJECTION)
    }

    /// Author `projection` (`uniform token`).
    pub fn create_projection_attr(&self) -> Result<Attribute> {
        create_uniform_token(self, tok::A_PROJECTION)
    }

    /// `stereoRole` attribute handle — `mono` / `left` / `right`.
    pub fn stereo_role_attr(&self) -> Attribute {
        self.attribute(tok::A_STEREO_ROLE)
    }

    /// Author `stereoRole` (`uniform token`).
    pub fn create_stereo_role_attr(&self) -> Result<Attribute> {
        create_uniform_token(self, tok::A_STEREO_ROLE)
    }

    /// `clippingRange` attribute handle — `(near, far)` (`float2`).
    pub fn clipping_range_attr(&self) -> Attribute {
        self.attribute(tok::A_CLIPPING_RANGE)
    }

    /// Author `clippingRange` (`float2`).
    pub fn create_clipping_range_attr(&self) -> Result<Attribute> {
        create(self, tok::A_CLIPPING_RANGE, "float2")
    }

    /// `clippingPlanes` attribute handle — plane equations (`float4[]`).
    pub fn clipping_planes_attr(&self) -> Attribute {
        self.attribute(tok::A_CLIPPING_PLANES)
    }

    /// Author `clippingPlanes` (`float4[]`).
    pub fn create_clipping_planes_attr(&self) -> Result<Attribute> {
        create(self, tok::A_CLIPPING_PLANES, "float4[]")
    }
}

impl_geom_schema!(xformable Camera);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn camera_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let cam = Camera::define(&stage, "/Cam")?;
        cam.create_focal_length_attr()?.set(50.0_f32)?;
        cam.create_projection_attr()?
            .set(sdf::Value::Token("perspective".into()))?;
        cam.create_clipping_range_attr()?
            .set(sdf::Value::Vec2f([0.1, 1000.0]))?;

        let cam = Camera::get(&stage, "/Cam")?.expect("Camera");
        assert_eq!(cam.focal_length_attr().get()?, Some(sdf::Value::Float(50.0)));
        assert_eq!(
            cam.projection_attr().get()?,
            Some(sdf::Value::Token("perspective".into()))
        );
        assert_eq!(cam.clipping_range_attr().get()?, Some(sdf::Value::Vec2f([0.1, 1000.0])));
        assert!(Camera::get(&stage, "/Cam")?.is_some());
        Ok(())
    }
}
