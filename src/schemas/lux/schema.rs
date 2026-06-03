//! The UsdLux prim and applied-API views.
//!
//! Concrete lights are typed views over a [`Prim`] exposing the shared
//! [`Light`] inputs (via the `impl_lux_schema!` chain) plus their own
//! geometry. The area lights derive `BoundableLightBase` (C++
//! `UsdLuxBoundableLightBase`) — they are
//! [`geom::Boundable`](crate::schemas::geom::Boundable) gprims — while
//! `DistantLight` / `GeometryLight` / `DomeLight` derive `NonboundableLightBase`
//! (just [`geom::Xformable`](crate::schemas::geom::Xformable)). `LightFilter`
//! is a plain typed [`geom::Xformable`](crate::schemas::geom::Xformable) prim.
//!
//! The applied-API views ([`LightAPI`], [`ShapingAPI`], [`ShadowAPI`],
//! [`LightListAPI`]) are single-apply schemas: `apply` adds the schema to a
//! prim's `apiSchemas`, and `get` gates on it being present. [`LightAPI`]
//! makes an arbitrary prim (a `Mesh`, `Volume`, …) emissive via [`Light`].

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, Relationship, Stage};

use super::tokens as tok;
use super::{impl_lux_schema, Light};
use crate::schemas::common::{get_typed, get_typed_any, get_with_api};

/// A spherical / point area light (C++ `UsdLuxSphereLight`).
#[derive(Clone, derive_more::Deref)]
pub struct SphereLight(Prim);

impl SphereLight {
    /// Author a `def SphereLight` prim at `path`
    /// (C++ `UsdLuxSphereLight::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_SPHERE_LIGHT)?))
    }

    /// Wrap `path` as a `SphereLight` if it is typed `SphereLight`
    /// (C++ `UsdLuxSphereLight::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_SPHERE_LIGHT).map(|o| o.map(Self))
    }

    /// The radius of the spherical light, in scene units; larger radii give
    /// softer shadows. C++ `UsdLuxSphereLight::GetRadiusAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn radius_attr(&self) -> Attribute {
        self.attribute(tok::A_RADIUS)
    }

    /// Author `inputs:radius` (`float`) (C++ `CreateRadiusAttr`).
    pub fn create_radius_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_RADIUS, "float")?.set_custom(false)?)
    }

    /// Whether the light is treated as an ideal point source of zero radius for
    /// the purpose of energy and shadow computation, ignoring `radius`.
    /// C++ `UsdLuxSphereLight::GetTreatAsPointAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    pub fn treat_as_point_attr(&self) -> Attribute {
        self.attribute(tok::A_TREAT_AS_POINT)
    }

    /// Author `treatAsPoint` (`bool`) (C++ `CreateTreatAsPointAttr`).
    pub fn create_treat_as_point_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_TREAT_AS_POINT, "bool")?
            .set_custom(false)?)
    }
}

impl_lux_schema!(boundable_light SphereLight);

/// A circular area light (C++ `UsdLuxDiskLight`).
#[derive(Clone, derive_more::Deref)]
pub struct DiskLight(Prim);

impl DiskLight {
    /// Author a `def DiskLight` prim at `path` (C++ `UsdLuxDiskLight::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_DISK_LIGHT)?))
    }

    /// Wrap `path` as a `DiskLight` if it is typed `DiskLight`
    /// (C++ `UsdLuxDiskLight::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_DISK_LIGHT).map(|o| o.map(Self))
    }

    /// The radius of the disk, in scene units, measured in its local XY plane.
    /// C++ `UsdLuxDiskLight::GetRadiusAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn radius_attr(&self) -> Attribute {
        self.attribute(tok::A_RADIUS)
    }

    /// Author `inputs:radius` (`float`) (C++ `CreateRadiusAttr`).
    pub fn create_radius_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_RADIUS, "float")?.set_custom(false)?)
    }
}

impl_lux_schema!(boundable_light DiskLight);

/// A rectangular area light (C++ `UsdLuxRectLight`). `inputs:texture:file`
/// colours the light from an image.
#[derive(Clone, derive_more::Deref)]
pub struct RectLight(Prim);

impl RectLight {
    /// Author a `def RectLight` prim at `path` (C++ `UsdLuxRectLight::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_RECT_LIGHT)?))
    }

    /// Wrap `path` as a `RectLight` if it is typed `RectLight`
    /// (C++ `UsdLuxRectLight::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_RECT_LIGHT).map(|o| o.map(Self))
    }

    /// The width of the rectangle, in scene units, along its local X axis.
    /// C++ `UsdLuxRectLight::GetWidthAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn width_attr(&self) -> Attribute {
        self.attribute(tok::A_WIDTH)
    }

    /// Author `inputs:width` (`float`) (C++ `CreateWidthAttr`).
    pub fn create_width_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_WIDTH, "float")?.set_custom(false)?)
    }

    /// The height of the rectangle, in scene units, along its local Y axis.
    /// C++ `UsdLuxRectLight::GetHeightAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn height_attr(&self) -> Attribute {
        self.attribute(tok::A_HEIGHT)
    }

    /// Author `inputs:height` (`float`) (C++ `CreateHeightAttr`).
    pub fn create_height_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_HEIGHT, "float")?.set_custom(false)?)
    }

    /// A color texture image mapped across the rectangle to modulate the
    /// emitted light, e.g. a softbox or gobo. C++ `UsdLuxRectLight::GetTextureFileAttr`.
    ///
    /// Type `asset`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::AssetPath`).
    pub fn texture_file_attr(&self) -> Attribute {
        self.attribute(tok::A_TEXTURE_FILE)
    }

    /// Author `inputs:texture:file` (`asset`) (C++ `CreateTextureFileAttr`).
    pub fn create_texture_file_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_TEXTURE_FILE, "asset")?.set_custom(false)?)
    }
}

impl_lux_schema!(boundable_light RectLight);

/// A tube / strip light (C++ `UsdLuxCylinderLight`).
#[derive(Clone, derive_more::Deref)]
pub struct CylinderLight(Prim);

impl CylinderLight {
    /// Author a `def CylinderLight` prim at `path`
    /// (C++ `UsdLuxCylinderLight::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_CYLINDER_LIGHT)?))
    }

    /// Wrap `path` as a `CylinderLight` if it is typed `CylinderLight`
    /// (C++ `UsdLuxCylinderLight::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_CYLINDER_LIGHT).map(|o| o.map(Self))
    }

    /// The length of the cylinder, in scene units, along its local X axis.
    /// C++ `UsdLuxCylinderLight::GetLengthAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn length_attr(&self) -> Attribute {
        self.attribute(tok::A_LENGTH)
    }

    /// Author `inputs:length` (`float`) (C++ `CreateLengthAttr`).
    pub fn create_length_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_LENGTH, "float")?.set_custom(false)?)
    }

    /// The radius of the cylinder, in scene units. C++ `UsdLuxCylinderLight::GetRadiusAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn radius_attr(&self) -> Attribute {
        self.attribute(tok::A_RADIUS)
    }

    /// Author `inputs:radius` (`float`) (C++ `CreateRadiusAttr`).
    pub fn create_radius_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_RADIUS, "float")?.set_custom(false)?)
    }

    /// Whether the cylinder is treated as an ideal line source of zero radius
    /// for energy and shadow computation, ignoring `radius`.
    /// C++ `UsdLuxCylinderLight::GetTreatAsLineAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    pub fn treat_as_line_attr(&self) -> Attribute {
        self.attribute(tok::A_TREAT_AS_LINE)
    }

    /// Author `treatAsLine` (`bool`) (C++ `CreateTreatAsLineAttr`).
    pub fn create_treat_as_line_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_TREAT_AS_LINE, "bool")?.set_custom(false)?)
    }
}

impl_lux_schema!(boundable_light CylinderLight);

/// An aperture for sampling an enclosing `DomeLight`
/// (C++ `UsdLuxPortalLight`).
#[derive(Clone, derive_more::Deref)]
pub struct PortalLight(Prim);

impl PortalLight {
    /// Author a `def PortalLight` prim at `path`
    /// (C++ `UsdLuxPortalLight::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_PORTAL_LIGHT)?))
    }

    /// Wrap `path` as a `PortalLight` if it is typed `PortalLight`
    /// (C++ `UsdLuxPortalLight::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_PORTAL_LIGHT).map(|o| o.map(Self))
    }

    /// The width of the portal aperture, in scene units, along its local X
    /// axis. C++ `UsdLuxPortalLight::GetWidthAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn width_attr(&self) -> Attribute {
        self.attribute(tok::A_WIDTH)
    }

    /// Author `inputs:width` (`float`) (C++ `CreateWidthAttr`).
    pub fn create_width_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_WIDTH, "float")?.set_custom(false)?)
    }

    /// The height of the portal aperture, in scene units, along its local Y
    /// axis. C++ `UsdLuxPortalLight::GetHeightAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn height_attr(&self) -> Attribute {
        self.attribute(tok::A_HEIGHT)
    }

    /// Author `inputs:height` (`float`) (C++ `CreateHeightAttr`).
    pub fn create_height_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_HEIGHT, "float")?.set_custom(false)?)
    }
}

impl_lux_schema!(boundable_light PortalLight);

/// A directional / sun-style parallel light (C++ `UsdLuxDistantLight`).
#[derive(Clone, derive_more::Deref)]
pub struct DistantLight(Prim);

impl DistantLight {
    /// Author a `def DistantLight` prim at `path`
    /// (C++ `UsdLuxDistantLight::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_DISTANT_LIGHT)?))
    }

    /// Wrap `path` as a `DistantLight` if it is typed `DistantLight`
    /// (C++ `UsdLuxDistantLight::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_DISTANT_LIGHT).map(|o| o.map(Self))
    }

    /// The angular size of the light on the sky, in degrees; the apparent
    /// diameter of the sun is about 0.53. Larger values give softer shadow
    /// penumbrae. C++ `UsdLuxDistantLight::GetAngleAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn angle_attr(&self) -> Attribute {
        self.attribute(tok::A_ANGLE)
    }

    /// Author `inputs:angle` (`float`) (C++ `CreateAngleAttr`).
    pub fn create_angle_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_ANGLE, "float")?.set_custom(false)?)
    }
}

impl_lux_schema!(nonboundable_light DistantLight);

/// A light that uses an arbitrary geometric prim as its emissive surface
/// (C++ `UsdLuxGeometryLight`).
#[derive(Clone, derive_more::Deref)]
pub struct GeometryLight(Prim);

impl GeometryLight {
    /// Author a `def GeometryLight` prim at `path`
    /// (C++ `UsdLuxGeometryLight::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_GEOMETRY_LIGHT)?))
    }

    /// Wrap `path` as a `GeometryLight` if it is typed `GeometryLight`
    /// (C++ `UsdLuxGeometryLight::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_GEOMETRY_LIGHT).map(|o| o.map(Self))
    }

    /// `geometry` relationship handle — the emissive source prim
    /// (C++ `GetGeometryRel`).
    pub fn geometry_rel(&self) -> Relationship {
        self.relationship(tok::REL_GEOMETRY)
    }

    /// Author the `geometry` relationship (C++ `CreateGeometryRel`).
    pub fn create_geometry_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::REL_GEOMETRY)?.set_custom(false)?)
    }
}

impl_lux_schema!(nonboundable_light GeometryLight);

/// An image-based environment light (C++ `UsdLuxDomeLight`). The view also
/// covers the versioned `DomeLight_1` typeName (C++ `UsdLuxDomeLight_1`),
/// whose only addition is `poleAxis`; [`DomeLight::get`] accepts either.
#[derive(Clone, derive_more::Deref)]
pub struct DomeLight(Prim);

impl DomeLight {
    /// Author a `def DomeLight` prim at `path` (C++ `UsdLuxDomeLight::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_DOME_LIGHT)?))
    }

    /// Author a `def DomeLight_1` prim at `path` — the versioned form that
    /// also carries `poleAxis` (C++ `UsdLuxDomeLight_1::Define`).
    pub fn define_v1(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_DOME_LIGHT_1)?))
    }

    /// Wrap `path` as a `DomeLight` if it is typed `DomeLight` or
    /// `DomeLight_1` (C++ `UsdLuxDomeLight::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed_any(stage, path, &[tok::T_DOME_LIGHT, tok::T_DOME_LIGHT_1]).map(|o| o.map(Self))
    }

    /// The environment image lighting the scene from the surrounding sphere,
    /// typically a high-dynamic-range lat-long map. C++ `UsdLuxDomeLight::GetTextureFileAttr`.
    ///
    /// Type `asset`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::AssetPath`).
    pub fn texture_file_attr(&self) -> Attribute {
        self.attribute(tok::A_TEXTURE_FILE)
    }

    /// Author `inputs:texture:file` (`asset`) (C++ `CreateTextureFileAttr`).
    pub fn create_texture_file_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_TEXTURE_FILE, "asset")?.set_custom(false)?)
    }

    /// How the texture image is projected onto the dome: `automatic`,
    /// `latlong`, `mirroredBall`, `angular`, or `cubeMapVerticalCross`.
    /// C++ `UsdLuxDomeLight::GetTextureFormatAttr`.
    ///
    /// Type `token`. Fetch with `get::<String>()?` and decode with
    /// [`TextureFormat::from_token`](super::TextureFormat::from_token).
    pub fn texture_format_attr(&self) -> Attribute {
        self.attribute(tok::A_TEXTURE_FORMAT)
    }

    /// Author `inputs:texture:format` (`token`) (C++ `CreateTextureFormatAttr`).
    pub fn create_texture_format_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_TEXTURE_FORMAT, "token")?
            .set_custom(false)?)
    }

    /// The radius, in scene units, of the guide geometry drawn to visualize the
    /// dome in a viewport; it has no effect on rendered light.
    /// C++ `UsdLuxDomeLight::GetGuideRadiusAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn guide_radius_attr(&self) -> Attribute {
        self.attribute(tok::A_GUIDE_RADIUS)
    }

    /// Author `guideRadius` (`float`) (C++ `CreateGuideRadiusAttr`).
    pub fn create_guide_radius_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_GUIDE_RADIUS, "float")?.set_custom(false)?)
    }

    /// Which axis the latitude-longitude texture's poles align to — `scene`
    /// (the stage up-axis), `Y`, or `Z`; only meaningful on `DomeLight_1`.
    /// C++ `UsdLuxDomeLight_1::GetPoleAxisAttr`.
    ///
    /// Type `token`. Fetch with `get::<String>()?` and decode with
    /// [`PoleAxis::from_token`](super::PoleAxis::from_token).
    pub fn pole_axis_attr(&self) -> Attribute {
        self.attribute(tok::A_POLE_AXIS)
    }

    /// Author `poleAxis` (`uniform token`) (C++ `CreatePoleAxisAttr`).
    pub fn create_pole_axis_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_POLE_AXIS, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// `portals` relationship handle — `PortalLight` prims focusing this dome
    /// (C++ `GetPortalsRel`).
    pub fn portals_rel(&self) -> Relationship {
        self.relationship(tok::REL_PORTALS)
    }

    /// Author the `portals` relationship (C++ `CreatePortalsRel`).
    pub fn create_portals_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::REL_PORTALS)?.set_custom(false)?)
    }
}

impl_lux_schema!(nonboundable_light DomeLight);

/// A light filter (C++ `UsdLuxLightFilter`) — a [`geom::Xformable`](crate::schemas::geom::Xformable)
/// prim referenced from a light's `light:filters` relationship to modulate its
/// contribution. It is a typed prim but not itself a [`Light`]; the concrete
/// filter behavior is supplied by a renderer shader keyed off
/// `lightFilter:shaderId`.
#[derive(Clone, derive_more::Deref)]
pub struct LightFilter(Prim);

impl LightFilter {
    /// Author a `def LightFilter` prim at `path`
    /// (C++ `UsdLuxLightFilter::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_LIGHT_FILTER)?))
    }

    /// Wrap `path` as a `LightFilter` if it is typed `LightFilter`
    /// (C++ `UsdLuxLightFilter::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_LIGHT_FILTER).map(|o| o.map(Self))
    }
}

impl_lux_schema!(xformable LightFilter);

/// The `UsdLuxLightAPI` single-apply API schema as a standalone view
/// (C++ `UsdLuxLightAPI`). Apply it to make an arbitrary prim — a `Mesh`,
/// `Volume`, or other gprim — emissive, then drive the [`Light`] attributes.
/// Concrete light prims carry `LightAPI` implicitly through their typeName, so
/// use their own views (`SphereLight`, …) instead.
#[derive(Clone, derive_more::Deref)]
pub struct LightAPI(Prim);

impl LightAPI {
    /// Apply `LightAPI` to the prim at `path` (C++ `UsdLuxLightAPI::Apply`).
    /// The prim is opened as `over`; author its typeName separately if it does
    /// not exist yet.
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.override_prim(path)?.add_applied_schema(tok::API_LIGHT)?))
    }

    /// Wrap `path` as a `LightAPI` if it carries `LightAPI`, `MeshLightAPI`,
    /// or `VolumeLightAPI` in its `apiSchemas` (C++ `UsdLuxLightAPI::Get`);
    /// returns `None` otherwise. The two derived APIs apply the same inputs to
    /// meshes and volumes.
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(
            stage,
            path,
            &[tok::API_LIGHT, tok::API_MESH_LIGHT, tok::API_VOLUME_LIGHT],
        )
        .map(|o| o.map(Self))
    }
}

impl_lux_schema!(applied_api LightAPI);
impl Light for LightAPI {}

/// Directional shaping for a light — focus, spot cone, and IES profile
/// (C++ `UsdLuxShapingAPI`).
#[derive(Clone, derive_more::Deref)]
pub struct ShapingAPI(Prim);

impl ShapingAPI {
    /// Apply `ShapingAPI` to the prim at `path` (C++ `UsdLuxShapingAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.override_prim(path)?.add_applied_schema(tok::API_SHAPING)?))
    }

    /// Wrap `path` as a `ShapingAPI` if it carries `ShapingAPI` in its
    /// `apiSchemas` (C++ `UsdLuxShapingAPI::Get`); returns `None` otherwise.
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_SHAPING]).map(|o| o.map(Self))
    }

    /// A focusing exponent that concentrates emission toward the light's center
    /// of illumination; higher values give a tighter falloff, `0` is uniform.
    /// C++ `UsdLuxShapingAPI::GetShapingFocusAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn focus_attr(&self) -> Attribute {
        self.attribute(tok::A_SHAPING_FOCUS)
    }

    /// Author `inputs:shaping:focus` (`float`) (C++ `CreateShapingFocusAttr`).
    pub fn create_focus_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHAPING_FOCUS, "float")?
            .set_custom(false)?)
    }

    /// A color tint mixed into the off-axis region as `focus` narrows the beam,
    /// letting the edges of the cone shade differently from the center.
    /// C++ `UsdLuxShapingAPI::GetShapingFocusTintAttr`.
    ///
    /// Type `color3f`. Fetch with `get::<[f32; 3]>()?`.
    pub fn focus_tint_attr(&self) -> Attribute {
        self.attribute(tok::A_SHAPING_FOCUS_TINT)
    }

    /// Author `inputs:shaping:focusTint` (`color3f`)
    /// (C++ `CreateShapingFocusTintAttr`).
    pub fn create_focus_tint_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHAPING_FOCUS_TINT, "color3f")?
            .set_custom(false)?)
    }

    /// The half-angle of the spotlight cone, in degrees, measured from the
    /// light's primary axis; emission outside the cone is cut off.
    /// C++ `UsdLuxShapingAPI::GetShapingConeAngleAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn cone_angle_attr(&self) -> Attribute {
        self.attribute(tok::A_SHAPING_CONE_ANGLE)
    }

    /// Author `inputs:shaping:cone:angle` (`float`)
    /// (C++ `CreateShapingConeAngleAttr`).
    pub fn create_cone_angle_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHAPING_CONE_ANGLE, "float")?
            .set_custom(false)?)
    }

    /// How gradually emission falls off at the edge of the spotlight cone, as a
    /// fraction of the cone angle; `0` is a hard edge, `1` fades across the
    /// whole cone. C++ `UsdLuxShapingAPI::GetShapingConeSoftnessAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn cone_softness_attr(&self) -> Attribute {
        self.attribute(tok::A_SHAPING_CONE_SOFTNESS)
    }

    /// Author `inputs:shaping:cone:softness` (`float`)
    /// (C++ `CreateShapingConeSoftnessAttr`).
    pub fn create_cone_softness_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHAPING_CONE_SOFTNESS, "float")?
            .set_custom(false)?)
    }

    /// An IES photometric profile (`.ies`) describing the light's real-world
    /// angular intensity distribution. C++ `UsdLuxShapingAPI::GetShapingIesFileAttr`.
    ///
    /// Type `asset`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::AssetPath`).
    pub fn ies_file_attr(&self) -> Attribute {
        self.attribute(tok::A_SHAPING_IES_FILE)
    }

    /// Author `inputs:shaping:ies:file` (`asset`)
    /// (C++ `CreateShapingIesFileAttr`).
    pub fn create_ies_file_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHAPING_IES_FILE, "asset")?
            .set_custom(false)?)
    }

    /// A scale factor that rescales the angular extent of the IES profile,
    /// widening or narrowing the emitted distribution.
    /// C++ `UsdLuxShapingAPI::GetShapingIesAngleScaleAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn ies_angle_scale_attr(&self) -> Attribute {
        self.attribute(tok::A_SHAPING_IES_ANGLE_SCALE)
    }

    /// Author `inputs:shaping:ies:angleScale` (`float`)
    /// (C++ `CreateShapingIesAngleScaleAttr`).
    pub fn create_ies_angle_scale_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHAPING_IES_ANGLE_SCALE, "float")?
            .set_custom(false)?)
    }

    /// Whether to normalize the IES profile so its overall power matches the
    /// light's other intensity controls rather than the absolute values baked
    /// into the file. C++ `UsdLuxShapingAPI::GetShapingIesNormalizeAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    pub fn ies_normalize_attr(&self) -> Attribute {
        self.attribute(tok::A_SHAPING_IES_NORMALIZE)
    }

    /// Author `inputs:shaping:ies:normalize` (`bool`)
    /// (C++ `CreateShapingIesNormalizeAttr`).
    pub fn create_ies_normalize_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHAPING_IES_NORMALIZE, "bool")?
            .set_custom(false)?)
    }
}

impl_lux_schema!(applied_api ShapingAPI);

/// Shadow-casting controls for a light (C++ `UsdLuxShadowAPI`).
#[derive(Clone, derive_more::Deref)]
pub struct ShadowAPI(Prim);

impl ShadowAPI {
    /// Apply `ShadowAPI` to the prim at `path` (C++ `UsdLuxShadowAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.override_prim(path)?.add_applied_schema(tok::API_SHADOW)?))
    }

    /// Wrap `path` as a `ShadowAPI` if it carries `ShadowAPI` in its
    /// `apiSchemas` (C++ `UsdLuxShadowAPI::Get`); returns `None` otherwise.
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_SHADOW]).map(|o| o.map(Self))
    }

    /// Whether the light casts shadows; set to `false` to let the light pass
    /// through occluders. C++ `UsdLuxShadowAPI::GetShadowEnableAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    pub fn enable_attr(&self) -> Attribute {
        self.attribute(tok::A_SHADOW_ENABLE)
    }

    /// Author `inputs:shadow:enable` (`bool`) (C++ `CreateShadowEnableAttr`).
    pub fn create_enable_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_SHADOW_ENABLE, "bool")?.set_custom(false)?)
    }

    /// The color of the cast shadow, allowing artistically tinted (rather than
    /// physically black) shadows. C++ `UsdLuxShadowAPI::GetShadowColorAttr`.
    ///
    /// Type `color3f`. Fetch with `get::<[f32; 3]>()?`.
    pub fn color_attr(&self) -> Attribute {
        self.attribute(tok::A_SHADOW_COLOR)
    }

    /// Author `inputs:shadow:color` (`color3f`) (C++ `CreateShadowColorAttr`).
    pub fn create_color_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHADOW_COLOR, "color3f")?
            .set_custom(false)?)
    }

    /// The maximum distance, in scene units, that shadows are cast from the
    /// light; `-1` means unlimited. C++ `UsdLuxShadowAPI::GetShadowDistanceAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn distance_attr(&self) -> Attribute {
        self.attribute(tok::A_SHADOW_DISTANCE)
    }

    /// Author `inputs:shadow:distance` (`float`)
    /// (C++ `CreateShadowDistanceAttr`).
    pub fn create_distance_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHADOW_DISTANCE, "float")?
            .set_custom(false)?)
    }

    /// The distance, in scene units, over which the shadow fades out as it
    /// approaches `distance`; `-1` disables the falloff.
    /// C++ `UsdLuxShadowAPI::GetShadowFalloffAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn falloff_attr(&self) -> Attribute {
        self.attribute(tok::A_SHADOW_FALLOFF)
    }

    /// Author `inputs:shadow:falloff` (`float`)
    /// (C++ `CreateShadowFalloffAttr`).
    pub fn create_falloff_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHADOW_FALLOFF, "float")?
            .set_custom(false)?)
    }

    /// A gamma exponent shaping the curve of the shadow falloff, controlling how
    /// quickly the shadow fades across the falloff region.
    /// C++ `UsdLuxShadowAPI::GetShadowFalloffGammaAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn falloff_gamma_attr(&self) -> Attribute {
        self.attribute(tok::A_SHADOW_FALLOFF_GAMMA)
    }

    /// Author `inputs:shadow:falloffGamma` (`float`)
    /// (C++ `CreateShadowFalloffGammaAttr`).
    pub fn create_falloff_gamma_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SHADOW_FALLOFF_GAMMA, "float")?
            .set_custom(false)?)
    }
}

impl_lux_schema!(applied_api ShadowAPI);

/// A pre-computed list of lights beneath a prim, usually authored on an asset
/// root so consumers can discover lights without traversing (C++
/// `UsdLuxLightListAPI`).
#[derive(Clone, derive_more::Deref)]
pub struct LightListAPI(Prim);

impl LightListAPI {
    /// Apply `LightListAPI` to the prim at `path`
    /// (C++ `UsdLuxLightListAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.override_prim(path)?.add_applied_schema(tok::API_LIGHT_LIST)?,
        ))
    }

    /// Wrap `path` as a `LightListAPI` if it carries `LightListAPI` in its
    /// `apiSchemas` (C++ `UsdLuxLightListAPI::Get`); returns `None` otherwise.
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_LIGHT_LIST]).map(|o| o.map(Self))
    }

    /// `lightList` relationship handle — the cached set of lights
    /// (C++ `GetLightListRel`).
    pub fn light_list_rel(&self) -> Relationship {
        self.relationship(tok::REL_LIGHT_LIST)
    }

    /// Author the `lightList` relationship (C++ `CreateLightListRel`).
    pub fn create_light_list_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::REL_LIGHT_LIST)?.set_custom(false)?)
    }

    /// How a consumer should treat the cached `lightList` relationship while
    /// traversing: `consumeAndContinue` (use it, then keep descending),
    /// `consumeAndHalt` (use it and stop descending), or `ignore` (always
    /// traverse for lights). C++ `UsdLuxLightListAPI::GetLightListCacheBehaviorAttr`.
    ///
    /// Type `token`. Fetch with `get::<String>()?` and decode with
    /// [`LightListCacheBehavior::from_token`](super::LightListCacheBehavior::from_token).
    pub fn cache_behavior_attr(&self) -> Attribute {
        self.attribute(tok::A_LIGHT_LIST_CACHE_BEHAVIOR)
    }

    /// Author `lightList:cacheBehavior` (`uniform token`)
    /// (C++ `CreateLightListCacheBehaviorAttr`).
    pub fn create_cache_behavior_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_LIGHT_LIST_CACHE_BEHAVIOR, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_lux_schema!(applied_api LightListAPI);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::geom::Xformable;
    use crate::usd::SchemaBase;

    #[test]
    fn sphere_light_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let s = SphereLight::define(&stage, "/Bulb")?;
        s.create_radius_attr()?.set(0.25_f32)?;
        s.create_treat_as_point_attr()?.set(true)?;
        s.create_intensity_attr()?.set(800.0_f32)?;

        let s = SphereLight::get(&stage, "/Bulb")?.expect("SphereLight");
        assert_eq!(s.radius_attr().get()?, Some(sdf::Value::Float(0.25)));
        assert_eq!(s.treat_as_point_attr().get()?, Some(sdf::Value::Bool(true)));
        assert_eq!(s.intensity_attr().get()?, Some(sdf::Value::Float(800.0)));
        assert!(SphereLight::get(&stage, "/Missing")?.is_none());
        Ok(())
    }

    #[test]
    fn rect_light_texture_and_filters() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let r = RectLight::define(&stage, "/Rect")?;
        r.create_width_attr()?.set(2.0_f32)?;
        r.create_texture_file_attr()?
            .set(sdf::Value::AssetPath("./softbox.exr".into()))?;
        r.create_filters_rel()?.set_targets([sdf::path("/Filter")?])?;

        let r = RectLight::get(&stage, "/Rect")?.expect("RectLight");
        assert_eq!(r.width_attr().get()?, Some(sdf::Value::Float(2.0)));
        assert_eq!(r.filters_rel().get_targets()?, vec![sdf::path("/Filter")?]);
        Ok(())
    }

    #[test]
    fn distant_light_unauthored_intensity_is_none() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let d = DistantLight::define(&stage, "/Sun")?;
        d.create_angle_attr()?.set(0.53_f32)?;
        assert_eq!(d.angle_attr().get()?, Some(sdf::Value::Float(0.53)));
        // No schema registry yet, so DistantLight's documented 50000 fallback
        // is not synthesized.
        assert_eq!(d.intensity_attr().get::<sdf::Value>()?, None);
        Ok(())
    }

    #[test]
    fn geometry_light_links_mesh() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Emitter")?.set_type_name("Mesh")?;
        let g = GeometryLight::define(&stage, "/Light")?;
        g.create_geometry_rel()?.set_targets([sdf::path("/Emitter")?])?;

        let g = GeometryLight::get(&stage, "/Light")?.expect("GeometryLight");
        assert_eq!(g.geometry_rel().get_targets()?, vec![sdf::path("/Emitter")?]);
        Ok(())
    }

    #[test]
    fn dome_light_and_v1() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let d = DomeLight::define(&stage, "/Dome")?;
        d.create_texture_format_attr()?
            .set(sdf::Value::Token("latlong".into()))?;
        d.create_portals_rel()?.set_targets([sdf::path("/Dome/Portal")?])?;
        assert_eq!(
            DomeLight::get(&stage, "/Dome")?
                .expect("DomeLight")
                .texture_format_attr()
                .get()?,
            Some(sdf::Value::Token("latlong".into()))
        );

        let v1 = DomeLight::define_v1(&stage, "/Dome1")?;
        v1.create_pole_axis_attr()?.set(sdf::Value::Token("Y".into()))?;
        assert_eq!(
            DomeLight::get(&stage, "/Dome1")?
                .expect("DomeLight_1")
                .pole_axis_attr()
                .get()?,
            Some(sdf::Value::Token("Y".into()))
        );
        Ok(())
    }

    #[test]
    fn light_filter_is_typed_xformable() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        LightFilter::define(&stage, "/Filter")?;
        let f = LightFilter::get(&stage, "/Filter")?.expect("LightFilter");
        // Inherited Xformable accessor is available on the handle.
        assert!(f.xform_op_order()?.is_none());
        assert!(LightFilter::get(&stage, "/Missing")?.is_none());
        Ok(())
    }

    #[test]
    fn light_api_apply_and_get() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Emitter")?.set_type_name("Mesh")?;
        let light = LightAPI::apply(&stage, "/Emitter")?;
        light.create_intensity_attr()?.set(1500.0_f32)?;

        assert!(stage
            .api_schemas(&sdf::path("/Emitter")?)?
            .iter()
            .any(|s| s == "LightAPI"));
        let light = LightAPI::get(&stage, "/Emitter")?.expect("LightAPI");
        assert_eq!(light.intensity_attr().get()?, Some(sdf::Value::Float(1500.0)));
        assert!(light.is_applied_api_schema());
        Ok(())
    }

    #[test]
    fn shaping_and_shadow_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Spot")?.set_type_name("RectLight")?;
        ShapingAPI::apply(&stage, "/Spot")?
            .create_cone_angle_attr()?
            .set(45.0_f32)?;
        ShadowAPI::apply(&stage, "/Spot")?
            .create_distance_attr()?
            .set(10.0_f32)?;

        assert_eq!(
            ShapingAPI::get(&stage, "/Spot")?
                .expect("ShapingAPI")
                .cone_angle_attr()
                .get()?,
            Some(sdf::Value::Float(45.0))
        );
        assert_eq!(
            ShadowAPI::get(&stage, "/Spot")?
                .expect("ShadowAPI")
                .distance_attr()
                .get()?,
            Some(sdf::Value::Float(10.0))
        );
        Ok(())
    }

    #[test]
    fn light_list_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/World")?.set_type_name("Xform")?;
        let list = LightListAPI::apply(&stage, "/World")?;
        list.create_light_list_rel()?.set_targets([sdf::path("/World/Sun")?])?;
        list.create_cache_behavior_attr()?
            .set(sdf::Value::Token("consumeAndContinue".into()))?;

        let list = LightListAPI::get(&stage, "/World")?.expect("LightListAPI");
        assert_eq!(list.light_list_rel().get_targets()?, vec![sdf::path("/World/Sun")?]);
        assert_eq!(
            list.cache_behavior_attr().get()?,
            Some(sdf::Value::Token("consumeAndContinue".into()))
        );
        Ok(())
    }
}
