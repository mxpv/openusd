//! `UsdGeomPointBased` — gprims whose geometry is a point cloud.

use anyhow::Result;

use crate::usd::Attribute;

use super::tokens as tok;
use super::Gprim;

/// A gprim whose geometry is expressed as an array of points (C++
/// `UsdGeomPointBased`) — the base for meshes, curves, point clouds, and
/// NURBS patches. Inherits [`Gprim`] and adds the shared `points` /
/// `normals` / `velocities` / `accelerations` attributes.
///
/// `normals` is primvar-like: author its `interpolation` metadata (via
/// [`Attribute::set_metadata`](crate::usd::Attribute::set_metadata) with
/// [`tok::META_INTERPOLATION`](super::tokens::META_INTERPOLATION)) to describe
/// whether the values are per-point, per-face, or face-varying.
pub trait PointBased: Gprim {
    /// The local-space positions of the gprim's vertices; all other point-based
    /// topology (faces, curves, tets) indexes into this array.
    /// C++ `UsdGeomPointBased::GetPointsAttr`.
    ///
    /// Type `point3f[]`. Fetch with `get::<Vec<[f32; 3]>>()?`.
    fn points_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_POINTS)
    }

    /// Author `points` (`point3f[]`), returning its handle
    /// (C++ `CreatePointsAttr`).
    fn create_points_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_POINTS, "point3f[]")?
            .set_custom(false)?)
    }

    /// Surface normals used for shading, whose `interpolation` metadata says
    /// whether they are per-point, per-face, or face-varying; a mesh's
    /// `subdivisionScheme` may override them. C++ `UsdGeomPointBased::GetNormalsAttr`.
    ///
    /// Type `normal3f[]`. Fetch with `get::<Vec<[f32; 3]>>()?`.
    fn normals_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_NORMALS)
    }

    /// Author `normals` (`normal3f[]`), returning its handle
    /// (C++ `CreateNormalsAttr`).
    fn create_normals_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_NORMALS, "normal3f[]")?
            .set_custom(false)?)
    }

    /// Per-point linear velocities in local units per second, used to motion-blur
    /// and interpolate [`points`](Self::points_attr) between samples instead of
    /// relying on neighboring time samples. C++ `UsdGeomPointBased::GetVelocitiesAttr`.
    ///
    /// Type `vector3f[]`. Fetch with `get::<Vec<[f32; 3]>>()?`.
    fn velocities_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_VELOCITIES)
    }

    /// Author `velocities` (`vector3f[]`), returning its handle
    /// (C++ `CreateVelocitiesAttr`).
    fn create_velocities_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_VELOCITIES, "vector3f[]")?
            .set_custom(false)?)
    }

    /// Per-point accelerations in local units per second squared, refining the
    /// [`velocities`](Self::velocities_attr)-based motion model to a quadratic
    /// position estimate within a frame. C++ `UsdGeomPointBased::GetAccelerationsAttr`.
    ///
    /// Type `vector3f[]`. Fetch with `get::<Vec<[f32; 3]>>()?`.
    fn accelerations_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_ACCELERATIONS)
    }

    /// Author `accelerations` (`vector3f[]`), returning its handle
    /// (C++ `CreateAccelerationsAttr`).
    fn create_accelerations_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_ACCELERATIONS, "vector3f[]")?
            .set_custom(false)?)
    }
}
