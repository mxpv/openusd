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

    /// `faceVertexCounts` attribute handle — vertices per face, `int[]`
    /// (C++ `GetFaceVertexCountsAttr`).
    pub fn face_vertex_counts_attr(&self) -> Attribute {
        self.attribute(tok::A_FACE_VERTEX_COUNTS)
    }

    /// Author `faceVertexCounts` (`int[]`) (C++ `CreateFaceVertexCountsAttr`).
    pub fn create_face_vertex_counts_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_FACE_VERTEX_COUNTS, "int[]")?
            .set_custom(false)?)
    }

    /// `faceVertexIndices` attribute handle — the index buffer, `int[]`
    /// (C++ `GetFaceVertexIndicesAttr`).
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

    /// `subdivisionScheme` attribute handle — `catmullClark` / `loop` /
    /// `bilinear` / `none` (C++ `GetSubdivisionSchemeAttr`).
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

    /// `interpolateBoundary` attribute handle
    /// (C++ `GetInterpolateBoundaryAttr`).
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

    /// `faceVaryingLinearInterpolation` attribute handle
    /// (C++ `GetFaceVaryingLinearInterpolationAttr`).
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

    /// `triangleSubdivisionRule` attribute handle
    /// (C++ `GetTriangleSubdivisionRuleAttr`).
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

    /// `holeIndices` attribute handle — faces to treat as holes, `int[]`
    /// (C++ `GetHoleIndicesAttr`).
    pub fn hole_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_HOLE_INDICES)
    }

    /// Author `holeIndices` (`int[]`) (C++ `CreateHoleIndicesAttr`).
    pub fn create_hole_indices_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_HOLE_INDICES, "int[]")?.set_custom(false)?)
    }

    /// `cornerIndices` attribute handle — sharpened corner points, `int[]`
    /// (C++ `GetCornerIndicesAttr`).
    pub fn corner_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_CORNER_INDICES)
    }

    /// Author `cornerIndices` (`int[]`) (C++ `CreateCornerIndicesAttr`).
    pub fn create_corner_indices_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CORNER_INDICES, "int[]")?
            .set_custom(false)?)
    }

    /// `cornerSharpnesses` attribute handle — per-corner sharpness, `float[]`
    /// (C++ `GetCornerSharpnessesAttr`).
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

    /// `creaseIndices` attribute handle — point indices of crease edges,
    /// `int[]` (C++ `GetCreaseIndicesAttr`).
    pub fn crease_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_CREASE_INDICES)
    }

    /// Author `creaseIndices` (`int[]`) (C++ `CreateCreaseIndicesAttr`).
    pub fn create_crease_indices_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CREASE_INDICES, "int[]")?
            .set_custom(false)?)
    }

    /// `creaseLengths` attribute handle — point count per crease, `int[]`
    /// (C++ `GetCreaseLengthsAttr`).
    pub fn crease_lengths_attr(&self) -> Attribute {
        self.attribute(tok::A_CREASE_LENGTHS)
    }

    /// Author `creaseLengths` (`int[]`) (C++ `CreateCreaseLengthsAttr`).
    pub fn create_crease_lengths_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CREASE_LENGTHS, "int[]")?
            .set_custom(false)?)
    }

    /// `creaseSharpnesses` attribute handle — per-crease sharpness, `float[]`
    /// (C++ `GetCreaseSharpnessesAttr`).
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

    /// `elementType` attribute handle — `face` / `point` / `edge` /
    /// `tetrahedron` (C++ `GetElementTypeAttr`).
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

    /// `familyName` attribute handle — groups subsets that partition the mesh
    /// (C++ `GetFamilyNameAttr`).
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

    /// `indices` attribute handle — selected element indices, `int[]`
    /// (C++ `GetIndicesAttr`).
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
