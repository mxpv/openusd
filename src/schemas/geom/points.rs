//! Point-cloud and tetrahedral-mesh views — `Points` and `TetMesh`.
//!
//! Both are [`PointBased`] gprims: `Points` is a cloud of per-point widths
//! and ids, `TetMesh` is a volumetric mesh of tetrahedra indexing a shared
//! point pool. Each is a concrete view over a [`Prim`] mirroring the matching
//! C++ `UsdGeom` class.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, SchemaBase, SchemaKind, Stage};

use super::tokens as tok;
use super::{impl_geom_schema, Boundable, Gprim, Imageable, PointBased, Xformable};
use crate::schemas::common::get_typed;

/// A point cloud (C++ `UsdGeomPoints`) — a [`PointBased`] with per-point
/// `widths` and stable `ids`.
#[derive(Clone, derive_more::Deref)]
pub struct Points(Prim);

impl Points {
    /// Author a `def Points` prim at `path` (C++ `UsdGeomPoints::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_POINTS)?))
    }

    /// Wrap `path` as a `Points` if it is typed `Points`
    /// (C++ `UsdGeomPoints::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_POINTS).map(|o| o.map(Self))
    }

    /// The diameter of each point in local space, sized so the cloud renders as
    /// disks or spheres; its `interpolation` metadata says whether one width
    /// covers all points or one is given per point. C++ `UsdGeomPoints::GetWidthsAttr`.
    ///
    /// Type `float[]`. Fetch with `get::<Vec<f32>>()?`.
    pub fn widths_attr(&self) -> Attribute {
        self.attribute(tok::A_WIDTHS)
    }

    /// Author `widths` (`float[]`) (C++ `CreateWidthsAttr`).
    pub fn create_widths_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_WIDTHS, "float[]")?.set_custom(false)?)
    }

    /// Optional persistent identifiers that track each point across time samples
    /// even as points are added or removed, letting renderers maintain motion
    /// correspondence. C++ `UsdGeomPoints::GetIdsAttr`.
    ///
    /// Type `int64[]`. Fetch with `get::<sdf::Value>()?` (a [`sdf::Value::Int64Vec`]).
    pub fn ids_attr(&self) -> Attribute {
        self.attribute(tok::A_IDS)
    }

    /// Author `ids` (`int64[]`) (C++ `CreateIdsAttr`).
    pub fn create_ids_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_IDS, "int64[]")?.set_custom(false)?)
    }
}

impl_geom_schema!(pointbased Points);

/// A tetrahedral mesh (C++ `UsdGeomTetMesh`) — a [`PointBased`] whose
/// `tetVertexIndices` (`int4[]`) index its `points` into tetrahedra, with an
/// optional cached `surfaceFaceVertexIndices` (`int3[]`) boundary
/// triangulation.
#[derive(Clone, derive_more::Deref)]
pub struct TetMesh(Prim);

impl TetMesh {
    /// Author a `def TetMesh` prim at `path` (C++ `UsdGeomTetMesh::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_TET_MESH)?))
    }

    /// Wrap `path` as a `TetMesh` if it is typed `TetMesh`
    /// (C++ `UsdGeomTetMesh::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_TET_MESH).map(|o| o.map(Self))
    }

    /// The four [`points`](PointBased::points_attr) indices forming each
    /// tetrahedron, ordered so the first three wind counter-clockwise as seen
    /// from the fourth. C++ `UsdGeomTetMesh::GetTetVertexIndicesAttr`.
    ///
    /// Type `int4[]`. Fetch with `get::<sdf::Value>()?` (a [`sdf::Value::Vec4iVec`]).
    pub fn tet_vertex_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_TET_VERTEX_INDICES)
    }

    /// Author `tetVertexIndices` (`int4[]`)
    /// (C++ `CreateTetVertexIndicesAttr`).
    pub fn create_tet_vertex_indices_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_TET_VERTEX_INDICES, "int4[]")?
            .set_custom(false)?)
    }

    /// An optional precomputed triangulation of the mesh's exterior boundary,
    /// each triple indexing [`points`](PointBased::points_attr) and wound so its
    /// normal points outward. C++ `UsdGeomTetMesh::GetSurfaceFaceVertexIndicesAttr`.
    ///
    /// Type `int3[]`. Fetch with `get::<sdf::Value>()?` (a [`sdf::Value::Vec3iVec`]).
    pub fn surface_face_vertex_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_SURFACE_FACE_VERTEX_INDICES)
    }

    /// Author `surfaceFaceVertexIndices` (`int3[]`)
    /// (C++ `CreateSurfaceFaceVertexIndicesAttr`).
    pub fn create_surface_face_vertex_indices_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SURFACE_FACE_VERTEX_INDICES, "int3[]")?
            .set_custom(false)?)
    }
}

impl_geom_schema!(pointbased TetMesh);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn points_widths_and_ids() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let p = Points::define(&stage, "/Cloud")?;
        p.create_points_attr()?.set(sdf::Value::Vec3fVec(vec![
            [0.0_f32, 0.0, 0.0].into(),
            [1.0, 0.0, 0.0].into(),
        ]))?;
        p.create_widths_attr()?.set(sdf::Value::FloatVec(vec![0.1, 0.1]))?;
        p.create_ids_attr()?.set(sdf::Value::Int64Vec(vec![10, 20]))?;

        let p = Points::get(&stage, "/Cloud")?.expect("Points");
        assert_eq!(p.widths_attr().get()?, Some(sdf::Value::FloatVec(vec![0.1, 0.1])));
        assert_eq!(p.ids_attr().get()?, Some(sdf::Value::Int64Vec(vec![10, 20])));
        Ok(())
    }

    #[test]
    fn tet_mesh_indices() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let t = TetMesh::define(&stage, "/Soft")?;
        t.create_tet_vertex_indices_attr()?
            .set(sdf::Value::Vec4iVec(vec![[0_i32, 1, 2, 3].into()]))?;

        let t = TetMesh::get(&stage, "/Soft")?.expect("TetMesh");
        assert_eq!(
            t.tet_vertex_indices_attr().get()?,
            Some(sdf::Value::Vec4iVec(vec![[0_i32, 1, 2, 3].into()]))
        );
        assert!(t.surface_face_vertex_indices_attr().get::<sdf::Value>()?.is_none());
        Ok(())
    }
}
