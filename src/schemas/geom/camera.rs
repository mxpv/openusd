//! `UsdGeomCamera` — a camera prim.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, SchemaBase, SchemaKind, Stage};

use super::tokens as tok;
use super::{impl_geom_schema, Imageable, Xformable};
use crate::schemas::common::get_typed;

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

    /// The perspective lens focal length, in tenths of a scene unit (the USD
    /// camera convention) — e.g. 50 for a 50 mm lens when the scene unit is
    /// millimetres. C++ `UsdGeomCamera::GetFocalLengthAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn focal_length_attr(&self) -> Attribute {
        self.attribute(tok::A_FOCAL_LENGTH)
    }

    /// Author `focalLength` (`float`, mm) (C++ `CreateFocalLengthAttr`).
    pub fn create_focal_length_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_FOCAL_LENGTH, "float")?.set_custom(false)?)
    }

    /// The width of the camera's film gate (aperture), in tenths of a scene
    /// unit, which together with the focal length sets the horizontal field of
    /// view. C++ `UsdGeomCamera::GetHorizontalApertureAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn horizontal_aperture_attr(&self) -> Attribute {
        self.attribute(tok::A_HORIZONTAL_APERTURE)
    }

    /// Author `horizontalAperture` (`float`, mm).
    pub fn create_horizontal_aperture_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_HORIZONTAL_APERTURE, "float")?
            .set_custom(false)?)
    }

    /// The height of the camera's film gate (aperture), in tenths of a scene
    /// unit, which together with the focal length sets the vertical field of
    /// view. C++ `UsdGeomCamera::GetVerticalApertureAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn vertical_aperture_attr(&self) -> Attribute {
        self.attribute(tok::A_VERTICAL_APERTURE)
    }

    /// Author `verticalAperture` (`float`, mm).
    pub fn create_vertical_aperture_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_VERTICAL_APERTURE, "float")?
            .set_custom(false)?)
    }

    /// The horizontal offset of the film gate from the lens axis, in the same
    /// tenths-of-a-scene-unit units as `horizontalAperture`, producing an
    /// off-centre (lens-shift) projection. C++
    /// `UsdGeomCamera::GetHorizontalApertureOffsetAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn horizontal_aperture_offset_attr(&self) -> Attribute {
        self.attribute(tok::A_HORIZONTAL_APERTURE_OFFSET)
    }

    /// Author `horizontalApertureOffset` (`float`, mm).
    pub fn create_horizontal_aperture_offset_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_HORIZONTAL_APERTURE_OFFSET, "float")?
            .set_custom(false)?)
    }

    /// The vertical offset of the film gate from the lens axis, in the same
    /// tenths-of-a-scene-unit units as `verticalAperture`, producing an
    /// off-centre (lens-shift) projection. C++
    /// `UsdGeomCamera::GetVerticalApertureOffsetAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn vertical_aperture_offset_attr(&self) -> Attribute {
        self.attribute(tok::A_VERTICAL_APERTURE_OFFSET)
    }

    /// Author `verticalApertureOffset` (`float`, mm).
    pub fn create_vertical_aperture_offset_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_VERTICAL_APERTURE_OFFSET, "float")?
            .set_custom(false)?)
    }

    /// The lens aperture as an f-number, controlling depth of field: smaller
    /// values open the aperture and shrink the in-focus range. Distinct from
    /// the exposure f-stop. C++ `UsdGeomCamera::GetFStopAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn f_stop_attr(&self) -> Attribute {
        self.attribute(tok::A_F_STOP)
    }

    /// Author `fStop` (`float`).
    pub fn create_f_stop_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_F_STOP, "float")?.set_custom(false)?)
    }

    /// The distance from the camera to the focus plane, in scene units, around
    /// which the depth-of-field blur is centred. C++
    /// `UsdGeomCamera::GetFocusDistanceAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn focus_distance_attr(&self) -> Attribute {
        self.attribute(tok::A_FOCUS_DISTANCE)
    }

    /// Author `focusDistance` (`float`, scene units).
    pub fn create_focus_distance_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_FOCUS_DISTANCE, "float")?
            .set_custom(false)?)
    }

    /// Exposure compensation as a log base-2 stop value applied on top of the
    /// physical exposure terms — each whole unit doubles or halves image
    /// brightness. C++ `UsdGeomCamera::GetExposureAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn exposure_attr(&self) -> Attribute {
        self.attribute(tok::A_EXPOSURE)
    }

    /// Author `exposure` (`float`, stops).
    pub fn create_exposure_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_EXPOSURE, "float")?.set_custom(false)?)
    }

    /// The ISO speed rating of the sensor or film used in the physical exposure
    /// computation — higher values brighten the image. C++
    /// `UsdGeomCamera::GetExposureIsoAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn exposure_iso_attr(&self) -> Attribute {
        self.attribute(tok::A_EXPOSURE_ISO)
    }

    /// Author `exposure:iso` (`float`).
    pub fn create_exposure_iso_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_EXPOSURE_ISO, "float")?.set_custom(false)?)
    }

    /// The sensor exposure time in seconds used in the physical exposure
    /// computation — longer times brighten the image. C++
    /// `UsdGeomCamera::GetExposureTimeAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn exposure_time_attr(&self) -> Attribute {
        self.attribute(tok::A_EXPOSURE_TIME)
    }

    /// Author `exposure:time` (`float`, seconds).
    pub fn create_exposure_time_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_EXPOSURE_TIME, "float")?
            .set_custom(false)?)
    }

    /// The aperture f-number used in the physical exposure computation — a
    /// smaller f-stop brightens the image. Separate from the depth-of-field
    /// `fStop`. C++ `UsdGeomCamera::GetExposureFStopAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn exposure_f_stop_attr(&self) -> Attribute {
        self.attribute(tok::A_EXPOSURE_F_STOP)
    }

    /// Author `exposure:fStop` (`float`).
    pub fn create_exposure_f_stop_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_EXPOSURE_F_STOP, "float")?
            .set_custom(false)?)
    }

    /// A scalar multiplier for the overall responsivity of the sensor system
    /// to light in the physical exposure computation. C++
    /// `UsdGeomCamera::GetExposureResponsivityAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn exposure_responsivity_attr(&self) -> Attribute {
        self.attribute(tok::A_EXPOSURE_RESPONSIVITY)
    }

    /// Author `exposure:responsivity` (`float`).
    pub fn create_exposure_responsivity_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_EXPOSURE_RESPONSIVITY, "float")?
            .set_custom(false)?)
    }

    /// The frame-relative time the shutter opens, in `UsdTimeCode` units
    /// (typically negative, i.e. before the frame), defining the start of the
    /// motion-blur interval. C++ `UsdGeomCamera::GetShutterOpenAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn shutter_open_attr(&self) -> Attribute {
        self.attribute(tok::A_SHUTTER_OPEN)
    }

    /// Author `shutter:open` (`double`, frame-relative seconds).
    pub fn create_shutter_open_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHUTTER_OPEN, "double")?
            .set_custom(false)?)
    }

    /// The frame-relative time the shutter closes, in `UsdTimeCode` units,
    /// defining the end of the motion-blur interval. C++
    /// `UsdGeomCamera::GetShutterCloseAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn shutter_close_attr(&self) -> Attribute {
        self.attribute(tok::A_SHUTTER_CLOSE)
    }

    /// Author `shutter:close` (`double`, frame-relative seconds).
    pub fn create_shutter_close_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHUTTER_CLOSE, "double")?
            .set_custom(false)?)
    }

    /// Whether the camera projects in `perspective` or `orthographic` mode.
    /// C++ `UsdGeomCamera::GetProjectionAttr`.
    ///
    /// Type `token`. Fetch with `get::<Projection>()?`.
    pub fn projection_attr(&self) -> Attribute {
        self.attribute(tok::A_PROJECTION)
    }

    /// Author `projection` (`uniform token`).
    pub fn create_projection_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_PROJECTION, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The camera's role in a stereo rig — `mono`, `left`, or `right`; a value
    /// other than `mono` marks it as one eye of a stereo pair. C++
    /// `UsdGeomCamera::GetStereoRoleAttr`.
    ///
    /// Type `token`. Fetch with `get::<StereoRole>()?`.
    pub fn stereo_role_attr(&self) -> Attribute {
        self.attribute(tok::A_STEREO_ROLE)
    }

    /// Author `stereoRole` (`uniform token`).
    pub fn create_stereo_role_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_STEREO_ROLE, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The near and far clipping distances `(near, far)`, in scene units,
    /// bounding the depth range the camera renders. C++
    /// `UsdGeomCamera::GetClippingRangeAttr`.
    ///
    /// Type `float2`. Fetch with `get::<[f32; 2]>()?`.
    pub fn clipping_range_attr(&self) -> Attribute {
        self.attribute(tok::A_CLIPPING_RANGE)
    }

    /// Author `clippingRange` (`float2`).
    pub fn create_clipping_range_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CLIPPING_RANGE, "float2")?
            .set_custom(false)?)
    }

    /// Additional, arbitrarily oriented clipping planes, each a `(a, b, c, d)`
    /// plane equation that clips geometry on its negative side. C++
    /// `UsdGeomCamera::GetClippingPlanesAttr`.
    ///
    /// Type `float4[]`. Fetch with `get::<Vec<gf::Vec4f>>()?`.
    pub fn clipping_planes_attr(&self) -> Attribute {
        self.attribute(tok::A_CLIPPING_PLANES)
    }

    /// Author `clippingPlanes` (`float4[]`).
    pub fn create_clipping_planes_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CLIPPING_PLANES, "float4[]")?
            .set_custom(false)?)
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
            .set(sdf::Value::vec2f(0.1_f32, 1000.0))?;

        let cam = Camera::get(&stage, "/Cam")?.expect("Camera");
        assert_eq!(cam.focal_length_attr().get()?, Some(sdf::Value::Float(50.0)));
        assert_eq!(
            cam.projection_attr().get()?,
            Some(sdf::Value::Token("perspective".into()))
        );
        assert_eq!(
            cam.clipping_range_attr().get()?,
            Some(sdf::Value::vec2f(0.1_f32, 1000.0))
        );
        assert!(Camera::get(&stage, "/Cam")?.is_some());
        Ok(())
    }
}
