//! `UsdGeomMesh` + `UsdGeomSubset` authoring, plus `primvars:*` helpers.
//!
//! Mesh is the workhorse gprim in USD — the helpers here cover the
//! required topology (points / faceVertexCounts / faceVertexIndices),
//! the common Pixar primvars (`primvars:displayColor`,
//! `primvars:st`, normals), and `subdivisionScheme`.
//!
//! `define_subset` authors a face-subset prim with its
//! `elementType` / `familyName` / `indices`, which Pixar uses for
//! per-face material binding and similar.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::Stage;

use crate::schemas::geom::tokens::{
    A_ELEMENT_TYPE, A_FACE_VERTEX_COUNTS, A_FACE_VERTEX_INDICES, A_FAMILY_NAME, A_INDICES, A_NORMALS, A_ORIENTATION,
    A_POINTS, A_SUBDIVISION_SCHEME, T_GEOM_SUBSET, T_MESH,
};
use crate::schemas::geom::types::{ElementType, Orientation};

use super::common::{
    author_color3f_array, author_float_array, author_int_vec, author_point3f_array, author_uniform_token,
    author_vec3f_array,
};

/// Author a `def Mesh` prim and return a chainable [`MeshAuthor`].
pub fn define_mesh<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<MeshAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_MESH)?;
    Ok(MeshAuthor {
        stage,
        path: prim.path().clone(),
    })
}

pub struct MeshAuthor<'s> {
    stage: &'s Stage,
    path: Path,
}

impl MeshAuthor<'_> {
    /// Set `points` — vertex positions.
    pub fn set_points(self, points: Vec<[f32; 3]>) -> Result<Self> {
        author_point3f_array(self.stage, &self.path, A_POINTS, points)?;
        Ok(self)
    }

    /// Set `faceVertexCounts` — vertices per face.
    pub fn set_face_vertex_counts(self, counts: Vec<i32>) -> Result<Self> {
        author_int_vec(self.stage, &self.path, A_FACE_VERTEX_COUNTS, counts)?;
        Ok(self)
    }

    /// Set `faceVertexIndices` — index buffer.
    pub fn set_face_vertex_indices(self, indices: Vec<i32>) -> Result<Self> {
        author_int_vec(self.stage, &self.path, A_FACE_VERTEX_INDICES, indices)?;
        Ok(self)
    }

    /// Set `normals` (varying vector3f[]). Per UsdGeomPointBased, the
    /// builtin `normals` attribute is varying — `primvars:normals` is
    /// the primvar form for per-face/face-varying normals.
    pub fn set_normals(self, normals: Vec<[f32; 3]>) -> Result<Self> {
        author_vec3f_array(self.stage, &self.path, A_NORMALS, normals)?;
        Ok(self)
    }

    /// Set `subdivisionScheme` (uniform token, `catmullClark` / `loop`
    /// / `bilinear` / `none`).
    pub fn set_subdivision_scheme(self, scheme: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.stage, &self.path, A_SUBDIVISION_SCHEME, scheme)?;
        Ok(self)
    }

    /// Set `orientation` (uniform token, `rightHanded` / `leftHanded`).
    pub fn set_orientation(self, orientation: Orientation) -> Result<Self> {
        author_uniform_token(self.stage, &self.path, A_ORIENTATION, orientation.as_token())?;
        Ok(self)
    }

    /// Set `primvars:displayColor` (color3f[]) — the most commonly
    /// authored display primvar. The reader exposes this directly on
    /// the curves / mesh `Read*` structs.
    pub fn set_display_color(self, colors: Vec<[f32; 3]>) -> Result<Self> {
        author_color3f_array(self.stage, &self.path, "primvars:displayColor", colors)?;
        Ok(self)
    }

    /// Set `primvars:st` (texCoord2f[]) — texture coordinates.
    pub fn set_st(self, uvs: Vec<[f32; 2]>) -> Result<Self> {
        let attr = self.path.append_property("primvars:st")?;
        self.stage
            .create_attribute(attr, "texCoord2f[]")?
            .set_custom(false)?
            .set(Value::Vec2fVec(uvs))?;
        Ok(self)
    }

    /// Set `primvars:widths` (float[]) — per-point widths, mainly
    /// used by curves but also valid on PointBased prims.
    pub fn set_widths(self, widths: Vec<f32>) -> Result<Self> {
        author_float_array(self.stage, &self.path, "primvars:widths", widths)?;
        Ok(self)
    }
}

/// Author a `def GeomSubset` prim under a Mesh.
pub fn define_subset<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<SubsetAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_GEOM_SUBSET)?;
    Ok(SubsetAuthor {
        stage,
        path: prim.path().clone(),
    })
}

pub struct SubsetAuthor<'s> {
    stage: &'s Stage,
    path: Path,
}

impl SubsetAuthor<'_> {
    /// Set `elementType` (uniform token, `face` / `point` / `edge` /
    /// `tetrahedron`). Spec default `face`.
    pub fn set_element_type(self, element_type: ElementType) -> Result<Self> {
        author_uniform_token(self.stage, &self.path, A_ELEMENT_TYPE, element_type.as_token())?;
        Ok(self)
    }

    /// Set `familyName` (uniform token) — groups related subsets.
    pub fn set_family_name(self, family_name: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.stage, &self.path, A_FAMILY_NAME, family_name)?;
        Ok(self)
    }

    /// Set `indices` (int[]) — selected element indices into the
    /// owning Mesh.
    pub fn set_indices(self, indices: Vec<i32>) -> Result<Self> {
        let attr = self.path.append_property(A_INDICES)?;
        self.stage
            .create_attribute(attr, "int[]")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::IntVec(indices))?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn mesh_roundtrip_quad() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_mesh(&stage, sdf::path("/M")?)?
            .set_points(vec![[0.0, 0.0, 0.0], [1.0, 0.0, 0.0], [1.0, 1.0, 0.0], [0.0, 1.0, 0.0]])?
            .set_face_vertex_counts(vec![4])?
            .set_face_vertex_indices(vec![0, 1, 2, 3])?
            .set_subdivision_scheme("none")?
            .set_orientation(Orientation::RightHanded)?
            .set_display_color(vec![[1.0, 0.0, 0.0]])?
            .set_st(vec![[0.0, 0.0], [1.0, 0.0], [1.0, 1.0], [0.0, 1.0]])?;

        let mesh = crate::schemas::geom::read_mesh(&stage, &sdf::path("/M")?)?.expect("Mesh");
        assert_eq!(mesh.points.len(), 4);
        assert_eq!(mesh.face_vertex_counts, vec![4]);
        assert_eq!(mesh.face_vertex_indices, vec![0, 1, 2, 3]);
        assert_eq!(mesh.orientation, Orientation::RightHanded);
        Ok(())
    }

    #[test]
    fn subset_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_mesh(&stage, sdf::path("/M")?)?
            .set_points(vec![[0.0, 0.0, 0.0]])?
            .set_face_vertex_counts(vec![3])?
            .set_face_vertex_indices(vec![0, 0, 0])?;
        define_subset(&stage, sdf::path("/M/RedFaces")?)?
            .set_element_type(ElementType::Face)?
            .set_family_name("materialBinding")?
            .set_indices(vec![0])?;

        let subset = crate::schemas::geom::read_subset(&stage, &sdf::path("/M/RedFaces")?)?.expect("Subset");
        assert_eq!(subset.element_type, ElementType::Face);
        assert_eq!(subset.family_name.as_deref(), Some("materialBinding"));
        assert_eq!(subset.indices, vec![0]);
        Ok(())
    }
}
