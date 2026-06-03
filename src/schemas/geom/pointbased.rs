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
    /// `points` attribute handle — vertex positions, `point3f[]`
    /// (C++ `GetPointsAttr`).
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

    /// `normals` attribute handle — `normal3f[]` (C++ `GetNormalsAttr`).
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

    /// `velocities` attribute handle — per-point linear velocity, `vector3f[]`
    /// (C++ `GetVelocitiesAttr`).
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

    /// `accelerations` attribute handle — per-point acceleration, `vector3f[]`
    /// (C++ `GetAccelerationsAttr`).
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
