//! `UsdGeomMesh` and `UsdGeomSubset` views.
//!
//! [`Mesh`] is the workhorse [`PointBased`] gprim — polygonal topology plus
//! the subdivision-surface controls (scheme, boundary interpolation, creases,
//! corners, holes). [`GeomSubset`] is a typed-but-not-imageable schema (C++
//! `UsdGeomSubset` derives `UsdTyped` directly) that enumerates a subset of a
//! parent mesh's elements, e.g. for per-face material binding.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, SchemaBase, SchemaKind, Stage};

use super::tokens as tok;
use super::{impl_geom_schema, Boundable, Gprim, Imageable, PointBased, Xformable};
use crate::schemas::common::get_typed;

/// A polygonal / subdivision-surface mesh (C++ `UsdGeomMesh`) — a
/// [`PointBased`] whose `faceVertexCounts` / `faceVertexIndices` define the
/// topology over the inherited `points`. Subdivision behavior is governed by
/// `subdivisionScheme` and the crease / corner / hole controls.
#[derive(Clone, derive_more::Deref)]
pub struct Mesh(Prim);

impl Mesh {
    /// Author a `def Mesh` prim at `path` (C++ `UsdGeomMesh::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_MESH)?))
    }

    /// Wrap `path` as a `Mesh` if it is typed `Mesh` (C++ `UsdGeomMesh::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_MESH).map(|o| o.map(Self))
    }

    /// The number of vertices in each face of the mesh; its length is the face
    /// count and the values index into runs of `faceVertexIndices`.
    /// C++ `UsdGeomMesh::GetFaceVertexCountsAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::IntVec`).
    pub fn face_vertex_counts_attr(&self) -> Attribute {
        self.attribute(tok::A_FACE_VERTEX_COUNTS)
    }

    /// Author `faceVertexCounts` (`int[]`) (C++ `CreateFaceVertexCountsAttr`).
    pub fn create_face_vertex_counts_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_FACE_VERTEX_COUNTS, "int[]")?
            .set_custom(false)?)
    }

    /// The flat list of point indices for every face, grouped by the per-face
    /// counts in `faceVertexCounts`; each value indexes into the `points`.
    /// C++ `UsdGeomMesh::GetFaceVertexIndicesAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::IntVec`).
    pub fn face_vertex_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_FACE_VERTEX_INDICES)
    }

    /// Author `faceVertexIndices` (`int[]`)
    /// (C++ `CreateFaceVertexIndicesAttr`).
    pub fn create_face_vertex_indices_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_FACE_VERTEX_INDICES, "int[]")?
            .set_custom(false)?)
    }

    /// The subdivision algorithm applied to the mesh: `catmullClark` (the
    /// default), `loop`, `bilinear`, or `none` to treat it as a polygonal
    /// mesh with no subdivision.
    /// C++ `UsdGeomMesh::GetSubdivisionSchemeAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<SubdivisionScheme>()?`.
    pub fn subdivision_scheme_attr(&self) -> Attribute {
        self.attribute(tok::A_SUBDIVISION_SCHEME)
    }

    /// Author `subdivisionScheme` (`uniform token`)
    /// (C++ `CreateSubdivisionSchemeAttr`).
    pub fn create_subdivision_scheme_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SUBDIVISION_SCHEME, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// How the subdivision surface behaves at boundary edges and corners:
    /// `none`, `edgeOnly`, or `edgeAndCorner` (the default).
    /// C++ `UsdGeomMesh::GetInterpolateBoundaryAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<InterpolateBoundary>()?`.
    pub fn interpolate_boundary_attr(&self) -> Attribute {
        self.attribute(tok::A_INTERPOLATE_BOUNDARY)
    }

    /// Author `interpolateBoundary` (`uniform token`)
    /// (C++ `CreateInterpolateBoundaryAttr`).
    pub fn create_interpolate_boundary_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_INTERPOLATE_BOUNDARY, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// How face-varying primvars (such as UVs) are interpolated and smoothed
    /// across the surface; one of `all`, `none`, `boundaries`, `cornersOnly`,
    /// `cornersPlus1` (the default), or `cornersPlus2`.
    /// C++ `UsdGeomMesh::GetFaceVaryingLinearInterpolationAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<FaceVaryingLinearInterpolation>()?`.
    pub fn face_varying_linear_interpolation_attr(&self) -> Attribute {
        self.attribute(tok::A_FACE_VARYING_LINEAR_INTERPOLATION)
    }

    /// Author `faceVaryingLinearInterpolation` (`uniform token`)
    /// (C++ `CreateFaceVaryingLinearInterpolationAttr`).
    pub fn create_face_varying_linear_interpolation_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_FACE_VARYING_LINEAR_INTERPOLATION, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The weighting rule used when subdividing triangles under the
    /// Catmull-Clark scheme: `catmullClark` (the default) or `smooth`.
    /// C++ `UsdGeomMesh::GetTriangleSubdivisionRuleAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<TriangleSubdivisionRule>()?`.
    pub fn triangle_subdivision_rule_attr(&self) -> Attribute {
        self.attribute(tok::A_TRIANGLE_SUBDIVISION_RULE)
    }

    /// Author `triangleSubdivisionRule` (`uniform token`)
    /// (C++ `CreateTriangleSubdivisionRuleAttr`).
    pub fn create_triangle_subdivision_rule_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_TRIANGLE_SUBDIVISION_RULE, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The sorted indices of faces that should be made invisible (treated as
    /// holes) for both display and subdivision.
    /// C++ `UsdGeomMesh::GetHoleIndicesAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::IntVec`).
    pub fn hole_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_HOLE_INDICES)
    }

    /// Author `holeIndices` (`int[]`) (C++ `CreateHoleIndicesAttr`).
    pub fn create_hole_indices_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_HOLE_INDICES, "int[]")?.set_custom(false)?)
    }

    /// The point indices marked as sharp corners during subdivision; pairs
    /// element-wise with `cornerSharpnesses`.
    /// C++ `UsdGeomMesh::GetCornerIndicesAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::IntVec`).
    pub fn corner_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_CORNER_INDICES)
    }

    /// Author `cornerIndices` (`int[]`) (C++ `CreateCornerIndicesAttr`).
    pub fn create_corner_indices_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CORNER_INDICES, "int[]")?
            .set_custom(false)?)
    }

    /// The sharpness assigned to each point in `cornerIndices`; higher values
    /// pull the surface toward a sharp corner, with the `10` convention
    /// denoting an infinitely sharp corner.
    /// C++ `UsdGeomMesh::GetCornerSharpnessesAttr`.
    ///
    /// Type `float[]`. Fetch with `get::<Vec<f32>>()?`.
    pub fn corner_sharpnesses_attr(&self) -> Attribute {
        self.attribute(tok::A_CORNER_SHARPNESSES)
    }

    /// Author `cornerSharpnesses` (`float[]`)
    /// (C++ `CreateCornerSharpnessesAttr`).
    pub fn create_corner_sharpnesses_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CORNER_SHARPNESSES, "float[]")?
            .set_custom(false)?)
    }

    /// The flat list of point indices forming the creased edge chains, grouped
    /// by the per-crease counts in `creaseLengths`.
    /// C++ `UsdGeomMesh::GetCreaseIndicesAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::IntVec`).
    pub fn crease_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_CREASE_INDICES)
    }

    /// Author `creaseIndices` (`int[]`) (C++ `CreateCreaseIndicesAttr`).
    pub fn create_crease_indices_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CREASE_INDICES, "int[]")?
            .set_custom(false)?)
    }

    /// The number of points in each crease, partitioning `creaseIndices` into
    /// separate edge chains; each length must be at least two.
    /// C++ `UsdGeomMesh::GetCreaseLengthsAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::IntVec`).
    pub fn crease_lengths_attr(&self) -> Attribute {
        self.attribute(tok::A_CREASE_LENGTHS)
    }

    /// Author `creaseLengths` (`int[]`) (C++ `CreateCreaseLengthsAttr`).
    pub fn create_crease_lengths_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CREASE_LENGTHS, "int[]")?
            .set_custom(false)?)
    }

    /// The sharpness of each crease, supplied either once per crease or once
    /// per crease edge; the `10` convention denotes an infinitely sharp crease.
    /// C++ `UsdGeomMesh::GetCreaseSharpnessesAttr`.
    ///
    /// Type `float[]`. Fetch with `get::<Vec<f32>>()?`.
    pub fn crease_sharpnesses_attr(&self) -> Attribute {
        self.attribute(tok::A_CREASE_SHARPNESSES)
    }

    /// Author `creaseSharpnesses` (`float[]`)
    /// (C++ `CreateCreaseSharpnessesAttr`).
    pub fn create_crease_sharpnesses_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CREASE_SHARPNESSES, "float[]")?
            .set_custom(false)?)
    }
}

impl_geom_schema!(pointbased Mesh);

/// A subset of a parent mesh's elements (C++ `UsdGeomSubset`). Unlike the
/// gprims, it derives `UsdTyped` directly — it is a typed prim but not
/// [`Imageable`], so it has no transform or visibility of its own.
#[derive(Clone, derive_more::Deref)]
pub struct GeomSubset(Prim);

impl GeomSubset {
    /// Author a `def GeomSubset` prim at `path`
    /// (C++ `UsdGeomSubset::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_GEOM_SUBSET)?))
    }

    /// Wrap `path` as a `GeomSubset` if it is typed `GeomSubset`
    /// (C++ `UsdGeomSubset::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_GEOM_SUBSET).map(|o| o.map(Self))
    }

    /// The kind of mesh element that `indices` enumerates: `face` (the
    /// default), `point`, `edge`, or `tetrahedron`.
    /// C++ `UsdGeomSubset::GetElementTypeAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<ElementType>()?`.
    pub fn element_type_attr(&self) -> Attribute {
        self.attribute(tok::A_ELEMENT_TYPE)
    }

    /// Author `elementType` (`uniform token`) (C++ `CreateElementTypeAttr`).
    pub fn create_element_type_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_ELEMENT_TYPE, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The name of the family this subset belongs to; subsets sharing a family
    /// (e.g. `materialBind`) form a logical grouping whose members can be
    /// constrained to partition the parent geometry without overlap.
    /// C++ `UsdGeomSubset::GetFamilyNameAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<String>()?`.
    pub fn family_name_attr(&self) -> Attribute {
        self.attribute(tok::A_FAMILY_NAME)
    }

    /// Author `familyName` (`uniform token`) (C++ `CreateFamilyNameAttr`).
    pub fn create_family_name_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_FAMILY_NAME, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The indices of the parent geometry's elements (of kind `elementType`)
    /// that belong to this subset; may be time-sampled for animated subsets.
    /// C++ `UsdGeomSubset::GetIndicesAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::IntVec`).
    pub fn indices_attr(&self) -> Attribute {
        self.attribute(tok::A_INDICES)
    }

    /// Author `indices` (`int[]`) (C++ `CreateIndicesAttr`).
    pub fn create_indices_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_INDICES, "int[]")?.set_custom(false)?)
    }
}

impl_geom_schema!(typed GeomSubset);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mesh_topology_and_subdiv() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let m = Mesh::define(&stage, "/M")?;
        m.create_points_attr()?.set(sdf::Value::Vec3fVec(vec![
            [0.0, 0.0, 0.0],
            [1.0, 0.0, 0.0],
            [1.0, 1.0, 0.0],
            [0.0, 1.0, 0.0],
        ]))?;
        m.create_face_vertex_counts_attr()?.set(sdf::Value::IntVec(vec![4]))?;
        m.create_face_vertex_indices_attr()?
            .set(sdf::Value::IntVec(vec![0, 1, 2, 3]))?;
        m.create_subdivision_scheme_attr()?
            .set(sdf::Value::Token("none".into()))?;
        m.create_orientation_attr()?
            .set(sdf::Value::Token("leftHanded".into()))?;
        m.create_display_color_attr()?
            .set(sdf::Value::Vec3fVec(vec![[1.0, 0.0, 0.0]]))?;

        let m = Mesh::get(&stage, "/M")?.expect("Mesh");
        assert_eq!(m.face_vertex_counts_attr().get()?, Some(sdf::Value::IntVec(vec![4])));
        assert_eq!(
            m.face_vertex_indices_attr().get()?,
            Some(sdf::Value::IntVec(vec![0, 1, 2, 3]))
        );
        assert_eq!(
            m.subdivision_scheme_attr().get()?,
            Some(sdf::Value::Token("none".into()))
        );
        // Inherited Gprim / PointBased accessors are available on the handle.
        assert_eq!(
            m.orientation_attr().get()?,
            Some(sdf::Value::Token("leftHanded".into()))
        );
        assert_eq!(
            m.points_attr()
                .get::<sdf::Value>()?
                .and_then(|v| v.try_as_vec_3f_vec())
                .map(|v| v.len()),
            Some(4)
        );
        assert_eq!(
            m.display_color_attr().get()?,
            Some(sdf::Value::Vec3fVec(vec![[1.0, 0.0, 0.0]]))
        );
        Ok(())
    }

    #[test]
    fn geom_subset_is_typed_not_imageable() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let s = GeomSubset::define(&stage, "/M/RedFaces")?;
        s.create_element_type_attr()?.set(sdf::Value::Token("face".into()))?;
        s.create_family_name_attr()?
            .set(sdf::Value::Token("materialBind".into()))?;
        s.create_indices_attr()?.set(sdf::Value::IntVec(vec![0]))?;

        let s = GeomSubset::get(&stage, "/M/RedFaces")?.expect("GeomSubset");
        assert_eq!(s.element_type_attr().get()?, Some(sdf::Value::Token("face".into())));
        assert_eq!(s.indices_attr().get()?, Some(sdf::Value::IntVec(vec![0])));
        assert!(s.is_concrete());
        Ok(())
    }
}
