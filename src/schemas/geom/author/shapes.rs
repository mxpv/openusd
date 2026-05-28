//! Intrinsic shape authoring: `Xform`, `Scope`, plus the six
//! Boundable gprims (Cube, Sphere, Capsule, Cone, Cylinder, Plane).
//!
//! Per `usdGeom/schema.usda`, each gprim has a small fixed set of
//! attributes — radius / height / axis / size — with documented
//! defaults. The helpers below only author values the caller passes;
//! relying on the schema-registry default when unauthored.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::geom::tokens::{
    A_AXIS, A_DOUBLE_SIDED, A_HEIGHT, A_LENGTH, A_RADIUS, A_SIZE, A_WIDTH, T_CAPSULE, T_CONE, T_CUBE, T_CYLINDER,
    T_PLANE, T_SCOPE, T_SPHERE, T_XFORM,
};
use crate::schemas::geom::types::Axis;

use super::common::{author_bool, author_double, author_uniform_token};

/// Author a `def Xform` prim — a transformable grouping prim, no
/// geometry of its own. Combine with [`super::set_translate`] / friends
/// to compose a transform stack.
pub fn define_xform<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<Prim<'s>> {
    Ok(stage.define_prim(path)?.set_type_name(T_XFORM)?)
}

/// Author a `def Scope` prim — a pure grouping prim (not transformable).
pub fn define_scope<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<Prim<'s>> {
    Ok(stage.define_prim(path)?.set_type_name(T_SCOPE)?)
}

// ── Cube ────────────────────────────────────────────────────────────

pub fn define_cube<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<CubeAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_CUBE)?;
    Ok(CubeAuthor { prim })
}

pub struct CubeAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> CubeAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `size` (double, spec default 2.0 — edge length).
    pub fn set_size(self, size: f64) -> Result<Self> {
        author_double(self.prim.stage(), self.prim.path(), A_SIZE, size)?;
        Ok(self)
    }
}

// ── Sphere ──────────────────────────────────────────────────────────

pub fn define_sphere<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<SphereAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_SPHERE)?;
    Ok(SphereAuthor { prim })
}

pub struct SphereAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> SphereAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `radius` (double, spec default 1.0).
    pub fn set_radius(self, radius: f64) -> Result<Self> {
        author_double(self.prim.stage(), self.prim.path(), A_RADIUS, radius)?;
        Ok(self)
    }
}

// ── Cylinder / Capsule / Cone — same attribute set ──────────────────

macro_rules! axial_shape {
    ($author:ident, $define_fn:ident, $type_name:expr) => {
        pub fn $define_fn<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<$author<'s>> {
            let prim = stage.define_prim(path)?.set_type_name($type_name)?;
            Ok($author { prim })
        }

        pub struct $author<'s> {
            prim: Prim<'s>,
        }

        impl<'s> $author<'s> {
            pub fn into_prim(self) -> Prim<'s> {
                self.prim
            }

            /// Set `radius` (double).
            pub fn set_radius(self, radius: f64) -> Result<Self> {
                author_double(self.prim.stage(), self.prim.path(), A_RADIUS, radius)?;
                Ok(self)
            }

            /// Set `height` (double).
            pub fn set_height(self, height: f64) -> Result<Self> {
                author_double(self.prim.stage(), self.prim.path(), A_HEIGHT, height)?;
                Ok(self)
            }

            /// Set `axis` token (`X` / `Y` / `Z`). Spec default `Z`.
            pub fn set_axis(self, axis: Axis) -> Result<Self> {
                author_uniform_token(self.prim.stage(), self.prim.path(), A_AXIS, axis.as_token())?;
                Ok(self)
            }
        }
    };
}

axial_shape!(CylinderAuthor, define_cylinder, T_CYLINDER);
axial_shape!(CapsuleAuthor, define_capsule, T_CAPSULE);
axial_shape!(ConeAuthor, define_cone, T_CONE);

// ── Plane ───────────────────────────────────────────────────────────

pub fn define_plane<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<PlaneAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_PLANE)?;
    Ok(PlaneAuthor { prim })
}

pub struct PlaneAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> PlaneAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `width` (double, spec default 1.0).
    pub fn set_width(self, width: f64) -> Result<Self> {
        author_double(self.prim.stage(), self.prim.path(), A_WIDTH, width)?;
        Ok(self)
    }

    /// Set `length` (double, spec default 1.0).
    pub fn set_length(self, length: f64) -> Result<Self> {
        author_double(self.prim.stage(), self.prim.path(), A_LENGTH, length)?;
        Ok(self)
    }

    /// Set `axis` — normal direction of the plane (`X` / `Y` / `Z`).
    pub fn set_axis(self, axis: Axis) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_AXIS, axis.as_token())?;
        Ok(self)
    }

    /// Set `doubleSided` (bool, Plane's spec default true).
    pub fn set_double_sided(self, double_sided: bool) -> Result<Self> {
        author_bool(self.prim.stage(), self.prim.path(), A_DOUBLE_SIDED, double_sided)?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn cube_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_cube(&stage, sdf::path("/Box")?)?.set_size(0.5)?;

        let cube = crate::schemas::geom::read_cube(&stage, &sdf::path("/Box")?)?.expect("Cube");
        assert!((cube.size - 0.5).abs() < 1e-6);
        Ok(())
    }

    #[test]
    fn sphere_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_sphere(&stage, sdf::path("/Ball")?)?.set_radius(2.5)?;

        let sphere = crate::schemas::geom::read_sphere(&stage, &sdf::path("/Ball")?)?.expect("Sphere");
        assert!((sphere.radius - 2.5).abs() < 1e-6);
        Ok(())
    }

    #[test]
    fn cylinder_roundtrip_with_axis() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_cylinder(&stage, sdf::path("/Pipe")?)?
            .set_radius(0.3)?
            .set_height(2.0)?
            .set_axis(Axis::X)?;

        let cyl = crate::schemas::geom::read_cylinder(&stage, &sdf::path("/Pipe")?)?.expect("Cylinder");
        assert!((cyl.radius - 0.3).abs() < 1e-6);
        assert!((cyl.height - 2.0).abs() < 1e-6);
        assert_eq!(cyl.axis, Axis::X);
        Ok(())
    }

    #[test]
    fn capsule_and_cone_share_axial_attrs() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_capsule(&stage, sdf::path("/Pill")?)?
            .set_radius(0.5)?
            .set_height(2.0)?;
        define_cone(&stage, sdf::path("/Pyramid")?)?
            .set_radius(1.0)?
            .set_height(2.0)?;

        let cap = crate::schemas::geom::read_capsule(&stage, &sdf::path("/Pill")?)?.expect("Capsule");
        assert!((cap.radius - 0.5).abs() < 1e-6);
        let cone = crate::schemas::geom::read_cone(&stage, &sdf::path("/Pyramid")?)?.expect("Cone");
        assert!((cone.height - 2.0).abs() < 1e-6);
        Ok(())
    }

    #[test]
    fn plane_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_plane(&stage, sdf::path("/Ground")?)?
            .set_width(10.0)?
            .set_length(20.0)?
            .set_axis(Axis::Y)?
            .set_double_sided(false)?;

        let plane = crate::schemas::geom::read_plane(&stage, &sdf::path("/Ground")?)?.expect("Plane");
        assert!((plane.width - 10.0).abs() < 1e-6);
        assert!((plane.length - 20.0).abs() < 1e-6);
        assert_eq!(plane.axis, Axis::Y);
        Ok(())
    }

    #[test]
    fn xform_and_scope_are_pure_typed_prims() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_xform(&stage, sdf::path("/Group")?)?;
        define_scope(&stage, sdf::path("/Stage")?)?;

        assert_eq!(stage.type_name(&sdf::path("/Group")?)?.as_deref(), Some("Xform"),);
        assert_eq!(stage.type_name(&sdf::path("/Stage")?)?.as_deref(), Some("Scope"),);
        Ok(())
    }
}
