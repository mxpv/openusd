//! Intrinsic primitive shapes — `Cube`, `Sphere`, `Cone`, `Cylinder`,
//! `Capsule`, `Plane`.
//!
//! Each is a concrete [`Gprim`] view over a [`Prim`] (C++ `UsdGeomCube` and
//! friends). They `Deref` to their prim, so the prim/attribute accessors and
//! the inherited `Imageable → Xformable → Boundable → Gprim` methods are
//! available directly on the handle. Attribute getters return a handle whose
//! `get()` yields the authored value (or `None`); unauthored fallbacks come
//! from the schema registry, which is not yet implemented.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, SchemaBase, SchemaKind, Stage};

use super::tokens as tok;
use super::{impl_geom_schema, Boundable, Gprim, Imageable, Xformable};
use crate::schemas::common::get_typed;

/// A cube centered at the prim origin (C++ `UsdGeomCube`). Its one intrinsic
/// attribute is `size` — the edge length (default 2.0).
#[derive(Clone, derive_more::Deref)]
pub struct Cube(Prim);

impl Cube {
    /// Author a `def Cube` prim at `path` (C++ `UsdGeomCube::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_CUBE)?))
    }

    /// Wrap `path` as a `Cube` if it is typed `Cube` (C++ `UsdGeomCube::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_CUBE).map(|o| o.map(Self))
    }

    /// The cube's edge length in local space (default 2.0), so the cube spans
    /// from `-size/2` to `+size/2` on each axis before the prim's transform.
    /// C++ `UsdGeomCube::GetSizeAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn size_attr(&self) -> Attribute {
        self.attribute(tok::A_SIZE)
    }

    /// Author `size` (`double`, default 2.0) (C++ `CreateSizeAttr`).
    pub fn create_size_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_SIZE, "double")?.set_custom(false)?)
    }
}

impl_geom_schema!(gprim Cube);

/// A sphere centered at the prim origin (C++ `UsdGeomSphere`). Its one
/// intrinsic attribute is `radius` (default 1.0).
#[derive(Clone, derive_more::Deref)]
pub struct Sphere(Prim);

impl Sphere {
    /// Author a `def Sphere` prim at `path` (C++ `UsdGeomSphere::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_SPHERE)?))
    }

    /// Wrap `path` as a `Sphere` if it is typed `Sphere`
    /// (C++ `UsdGeomSphere::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_SPHERE).map(|o| o.map(Self))
    }

    /// The sphere's radius in local space (default 1.0); the prim's transform
    /// then scales it. C++ `UsdGeomSphere::GetRadiusAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn radius_attr(&self) -> Attribute {
        self.attribute(tok::A_RADIUS)
    }

    /// Author `radius` (`double`, default 1.0) (C++ `CreateRadiusAttr`).
    pub fn create_radius_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_RADIUS, "double")?.set_custom(false)?)
    }
}

impl_geom_schema!(gprim Sphere);

/// A cone centered at the prim origin (C++ `UsdGeomCone`). Intrinsic
/// attributes: `radius`, `height`, `axis`.
#[derive(Clone, derive_more::Deref)]
pub struct Cone(Prim);

impl Cone {
    /// Author a `def Cone` prim at `path` (C++ `UsdGeomCone::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_CONE)?))
    }

    /// Wrap `path` as a `Cone` if it is typed `Cone` (C++ `UsdGeomCone::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_CONE).map(|o| o.map(Self))
    }

    /// The radius of the cone's circular base, measured perpendicular to its
    /// [`axis`](Self::axis_attr) in local space. C++ `UsdGeomCone::GetRadiusAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn radius_attr(&self) -> Attribute {
        self.attribute(tok::A_RADIUS)
    }

    /// Author `radius` (`double`) (C++ `CreateRadiusAttr`).
    pub fn create_radius_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_RADIUS, "double")?.set_custom(false)?)
    }

    /// The cone's extent along its [`axis`](Self::axis_attr), centered on the
    /// prim origin. C++ `UsdGeomCone::GetHeightAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn height_attr(&self) -> Attribute {
        self.attribute(tok::A_HEIGHT)
    }

    /// Author `height` (`double`) (C++ `CreateHeightAttr`).
    pub fn create_height_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_HEIGHT, "double")?.set_custom(false)?)
    }

    /// The local-space axis the cone's spine runs along: `X`, `Y`, or `Z`
    /// (default `Z`). C++ `UsdGeomCone::GetAxisAttr`.
    ///
    /// Type `token`. Fetch with `get::<Axis>()?`.
    pub fn axis_attr(&self) -> Attribute {
        self.attribute(tok::A_AXIS)
    }

    /// Author `axis` (`uniform token`, default `Z`) (C++ `CreateAxisAttr`).
    pub fn create_axis_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_AXIS, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_geom_schema!(gprim Cone);

/// A cylinder centered at the prim origin (C++ `UsdGeomCylinder`). Intrinsic
/// attributes: `radius`, `height`, `axis`.
#[derive(Clone, derive_more::Deref)]
pub struct Cylinder(Prim);

impl Cylinder {
    /// Author a `def Cylinder` prim at `path` (C++ `UsdGeomCylinder::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_CYLINDER)?))
    }

    /// Wrap `path` as a `Cylinder` if it is typed `Cylinder`
    /// (C++ `UsdGeomCylinder::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_CYLINDER).map(|o| o.map(Self))
    }

    /// The radius of the cylinder's circular cross-section, measured
    /// perpendicular to its [`axis`](Self::axis_attr) in local space.
    /// C++ `UsdGeomCylinder::GetRadiusAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn radius_attr(&self) -> Attribute {
        self.attribute(tok::A_RADIUS)
    }

    /// Author `radius` (`double`) (C++ `CreateRadiusAttr`).
    pub fn create_radius_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_RADIUS, "double")?.set_custom(false)?)
    }

    /// The cylinder's extent along its [`axis`](Self::axis_attr), centered on
    /// the prim origin. C++ `UsdGeomCylinder::GetHeightAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn height_attr(&self) -> Attribute {
        self.attribute(tok::A_HEIGHT)
    }

    /// Author `height` (`double`) (C++ `CreateHeightAttr`).
    pub fn create_height_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_HEIGHT, "double")?.set_custom(false)?)
    }

    /// The local-space axis the cylinder's spine runs along: `X`, `Y`, or `Z`
    /// (default `Z`). C++ `UsdGeomCylinder::GetAxisAttr`.
    ///
    /// Type `token`. Fetch with `get::<Axis>()?`.
    pub fn axis_attr(&self) -> Attribute {
        self.attribute(tok::A_AXIS)
    }

    /// Author `axis` (`uniform token`, default `Z`) (C++ `CreateAxisAttr`).
    pub fn create_axis_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_AXIS, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_geom_schema!(gprim Cylinder);

/// A capsule — a cylinder capped by hemispheres — centered at the prim
/// origin (C++ `UsdGeomCapsule`). Intrinsic attributes: `radius`, `height`,
/// `axis`.
#[derive(Clone, derive_more::Deref)]
pub struct Capsule(Prim);

impl Capsule {
    /// Author a `def Capsule` prim at `path` (C++ `UsdGeomCapsule::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_CAPSULE)?))
    }

    /// Wrap `path` as a `Capsule` if it is typed `Capsule`
    /// (C++ `UsdGeomCapsule::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_CAPSULE).map(|o| o.map(Self))
    }

    /// The radius of the capsule's cylindrical body and its hemispherical caps,
    /// measured perpendicular to the [`axis`](Self::axis_attr) in local space.
    /// C++ `UsdGeomCapsule::GetRadiusAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn radius_attr(&self) -> Attribute {
        self.attribute(tok::A_RADIUS)
    }

    /// Author `radius` (`double`) (C++ `CreateRadiusAttr`).
    pub fn create_radius_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_RADIUS, "double")?.set_custom(false)?)
    }

    /// The length of the capsule's cylindrical section along its
    /// [`axis`](Self::axis_attr), excluding the two hemispherical caps, centered
    /// on the prim origin. C++ `UsdGeomCapsule::GetHeightAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn height_attr(&self) -> Attribute {
        self.attribute(tok::A_HEIGHT)
    }

    /// Author `height` (`double`) (C++ `CreateHeightAttr`).
    pub fn create_height_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_HEIGHT, "double")?.set_custom(false)?)
    }

    /// The local-space axis the capsule's spine runs along: `X`, `Y`, or `Z`
    /// (default `Z`). C++ `UsdGeomCapsule::GetAxisAttr`.
    ///
    /// Type `token`. Fetch with `get::<Axis>()?`.
    pub fn axis_attr(&self) -> Attribute {
        self.attribute(tok::A_AXIS)
    }

    /// Author `axis` (`uniform token`, default `Z`) (C++ `CreateAxisAttr`).
    pub fn create_axis_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_AXIS, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_geom_schema!(gprim Capsule);

/// A flat plane primitive (C++ `UsdGeomPlane`). Intrinsic attributes are
/// `width`, `length`, and `axis` (its normal); `doubleSided` is inherited
/// from [`Gprim`].
#[derive(Clone, derive_more::Deref)]
pub struct Plane(Prim);

impl Plane {
    /// Author a `def Plane` prim at `path` (C++ `UsdGeomPlane::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_PLANE)?))
    }

    /// Wrap `path` as a `Plane` if it is typed `Plane`
    /// (C++ `UsdGeomPlane::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_PLANE).map(|o| o.map(Self))
    }

    /// The plane's extent along the first of the two in-plane axes orthogonal to
    /// its [`axis`](Self::axis_attr) normal, in local space.
    /// C++ `UsdGeomPlane::GetWidthAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn width_attr(&self) -> Attribute {
        self.attribute(tok::A_WIDTH)
    }

    /// Author `width` (`double`) (C++ `CreateWidthAttr`).
    pub fn create_width_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_WIDTH, "double")?.set_custom(false)?)
    }

    /// The plane's extent along the second of the two in-plane axes orthogonal
    /// to its [`axis`](Self::axis_attr) normal, in local space.
    /// C++ `UsdGeomPlane::GetLengthAttr`.
    ///
    /// Type `double`. Fetch with `get::<f64>()?`.
    pub fn length_attr(&self) -> Attribute {
        self.attribute(tok::A_LENGTH)
    }

    /// Author `length` (`double`) (C++ `CreateLengthAttr`).
    pub fn create_length_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_LENGTH, "double")?.set_custom(false)?)
    }

    /// The local-space axis the plane's normal points along: `X`, `Y`, or `Z`
    /// (default `Z`); the plane itself lies in the other two axes.
    /// C++ `UsdGeomPlane::GetAxisAttr`.
    ///
    /// Type `token`. Fetch with `get::<Axis>()?`.
    pub fn axis_attr(&self) -> Attribute {
        self.attribute(tok::A_AXIS)
    }

    /// Author `axis` (`uniform token`, default `Z`) (C++ `CreateAxisAttr`).
    pub fn create_axis_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_AXIS, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_geom_schema!(gprim Plane);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::geom::Purpose;

    #[test]
    fn cube_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        Cube::define(&stage, "/Box")?.create_size_attr()?.set(0.5_f64)?;

        let cube = Cube::get(&stage, "/Box")?.expect("Cube");
        assert_eq!(cube.size_attr().get()?, Some(sdf::Value::Double(0.5)));
        assert!(Cube::get(&stage, "/Missing")?.is_none());
        Ok(())
    }

    #[test]
    fn sphere_roundtrip_and_chain() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let sphere = Sphere::define(&stage, "/Ball")?;
        sphere.create_radius_attr()?.set(2.5_f64)?;
        // Inherited through the Gprim → … → Imageable chain.
        sphere.create_purpose_attr()?.set(sdf::Value::Token("render".into()))?;
        sphere.create_double_sided_attr()?.set(true)?;

        let sphere = Sphere::get(&stage, "/Ball")?.expect("Sphere");
        assert_eq!(sphere.radius_attr().get()?, Some(sdf::Value::Double(2.5)));
        assert_eq!(sphere.compute_purpose()?, Purpose::Render);
        assert_eq!(sphere.double_sided_attr().get()?, Some(sdf::Value::Bool(true)));
        assert_eq!(Sphere::KIND, SchemaKind::ConcreteTyped);
        Ok(())
    }

    #[test]
    fn axial_shapes_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let cyl = Cylinder::define(&stage, "/Pipe")?;
        cyl.create_radius_attr()?.set(0.3_f64)?;
        cyl.create_height_attr()?.set(2.0_f64)?;
        cyl.create_axis_attr()?.set(sdf::Value::Token("X".into()))?;

        let cyl = Cylinder::get(&stage, "/Pipe")?.expect("Cylinder");
        assert_eq!(cyl.radius_attr().get()?, Some(sdf::Value::Double(0.3)));
        assert_eq!(cyl.axis_attr().get()?, Some(sdf::Value::Token("X".into())));

        Cone::define(&stage, "/Pyramid")?.create_height_attr()?.set(2.0_f64)?;
        assert!(Cone::get(&stage, "/Pyramid")?.is_some());
        Capsule::define(&stage, "/Pill")?.create_radius_attr()?.set(0.5_f64)?;
        assert!(Capsule::get(&stage, "/Pill")?.is_some());
        Ok(())
    }

    #[test]
    fn plane_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let plane = Plane::define(&stage, "/Ground")?;
        plane.create_width_attr()?.set(10.0_f64)?;
        plane.create_length_attr()?.set(20.0_f64)?;
        plane.create_axis_attr()?.set(sdf::Value::Token("Y".into()))?;
        plane.create_double_sided_attr()?.set(false)?;

        let plane = Plane::get(&stage, "/Ground")?.expect("Plane");
        assert_eq!(plane.width_attr().get()?, Some(sdf::Value::Double(10.0)));
        assert_eq!(plane.double_sided_attr().get()?, Some(sdf::Value::Bool(false)));
        Ok(())
    }
}
