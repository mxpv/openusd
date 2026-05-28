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

use crate::sdf::{Path, Value};
use crate::usd::{Prim, Stage};

use crate::schemas::geom::tokens::{
    A_ELEMENT_TYPE, A_FACE_VERTEX_COUNTS, A_FACE_VERTEX_INDICES, A_FAMILY_NAME, A_INDICES, A_NORMALS, A_ORIENTATION,
    A_POINTS, A_SUBDIVISION_SCHEME, T_GEOM_SUBSET, T_MESH,
};
use crate::schemas::geom::types::{ElementType, Interpolation, Orientation};

use super::common::{author_int_vec, author_point3f_array, author_primvar, author_uniform_token};

/// Author a `def Mesh` prim and return a chainable [`MeshAuthor`].
pub fn define_mesh<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<MeshAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_MESH)?;
    Ok(MeshAuthor { prim })
}

pub struct MeshAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> MeshAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `points` — vertex positions.
    pub fn set_points(self, points: Vec<[f32; 3]>) -> Result<Self> {
        author_point3f_array(self.prim.stage(), self.prim.path(), A_POINTS, points)?;
        Ok(self)
    }

    /// Set `faceVertexCounts` — vertices per face.
    pub fn set_face_vertex_counts(self, counts: Vec<i32>) -> Result<Self> {
        author_int_vec(self.prim.stage(), self.prim.path(), A_FACE_VERTEX_COUNTS, counts)?;
        Ok(self)
    }

    /// Set `faceVertexIndices` — index buffer.
    pub fn set_face_vertex_indices(self, indices: Vec<i32>) -> Result<Self> {
        author_int_vec(self.prim.stage(), self.prim.path(), A_FACE_VERTEX_INDICES, indices)?;
        Ok(self)
    }

    /// Set `normals` (`normal3f[]` per `usdGeom/schema.usda`) with the given
    /// `interpolation`. The `primvars:normals` form is reserved for per-face
    /// / face-varying normals authored as a primvar.
    ///
    /// `interpolation` is required: USD treats unauthored interpolation as
    /// `constant`, which would silently consume only `normals[0]` for any
    /// downstream renderer.
    pub fn set_normals(self, normals: Vec<[f32; 3]>, interpolation: Interpolation) -> Result<Self> {
        author_primvar(
            self.prim.stage(),
            self.prim.path(),
            A_NORMALS,
            "normal3f[]",
            Value::Vec3fVec(normals),
            interpolation,
        )?;
        Ok(self)
    }

    /// Set `subdivisionScheme` (uniform token, `catmullClark` / `loop`
    /// / `bilinear` / `none`).
    pub fn set_subdivision_scheme(self, scheme: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_SUBDIVISION_SCHEME, scheme)?;
        Ok(self)
    }

    /// Set `orientation` (uniform token, `rightHanded` / `leftHanded`).
    pub fn set_orientation(self, orientation: Orientation) -> Result<Self> {
        author_uniform_token(
            self.prim.stage(),
            self.prim.path(),
            A_ORIENTATION,
            orientation.as_token(),
        )?;
        Ok(self)
    }

    /// Set `primvars:displayColor` (color3f[]) — the most commonly authored
    /// display primvar. `interpolation` is required (see [`Self::set_normals`]
    /// for the rationale).
    pub fn set_display_color(self, colors: Vec<[f32; 3]>, interpolation: Interpolation) -> Result<Self> {
        author_primvar(
            self.prim.stage(),
            self.prim.path(),
            "primvars:displayColor",
            "color3f[]",
            Value::Vec3fVec(colors),
            interpolation,
        )?;
        Ok(self)
    }

    /// Set `primvars:st` (texCoord2f[]) — texture coordinates.
    /// `interpolation` is required (typically `FaceVarying` for meshes with
    /// UV seams, or `Vertex` for shared UV layouts).
    pub fn set_st(self, uvs: Vec<[f32; 2]>, interpolation: Interpolation) -> Result<Self> {
        author_primvar(
            self.prim.stage(),
            self.prim.path(),
            "primvars:st",
            "texCoord2f[]",
            Value::Vec2fVec(uvs),
            interpolation,
        )?;
        Ok(self)
    }

    /// Set `primvars:widths` (float[]) — per-point widths, mainly used by
    /// curves but also valid on PointBased prims.
    pub fn set_widths(self, widths: Vec<f32>, interpolation: Interpolation) -> Result<Self> {
        author_primvar(
            self.prim.stage(),
            self.prim.path(),
            "primvars:widths",
            "float[]",
            Value::FloatVec(widths),
            interpolation,
        )?;
        Ok(self)
    }
}

/// Author a `def GeomSubset` prim under a Mesh.
pub fn define_subset<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<SubsetAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_GEOM_SUBSET)?;
    Ok(SubsetAuthor { prim })
}

pub struct SubsetAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> SubsetAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `elementType` (uniform token, `face` / `point` / `edge` /
    /// `tetrahedron`). Spec default `face`.
    pub fn set_element_type(self, element_type: ElementType) -> Result<Self> {
        author_uniform_token(
            self.prim.stage(),
            self.prim.path(),
            A_ELEMENT_TYPE,
            element_type.as_token(),
        )?;
        Ok(self)
    }

    /// Set `familyName` (uniform token) — groups related subsets.
    pub fn set_family_name(self, family_name: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_FAMILY_NAME, family_name)?;
        Ok(self)
    }

    /// Set `indices` (int[]) — selected element indices into the
    /// owning Mesh.
    pub fn set_indices(self, indices: Vec<i32>) -> Result<Self> {
        self.prim
            .create_attribute(A_INDICES, "int[]")?
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
            .set_display_color(vec![[1.0, 0.0, 0.0]], Interpolation::Constant)?
            .set_st(
                vec![[0.0, 0.0], [1.0, 0.0], [1.0, 1.0], [0.0, 1.0]],
                Interpolation::FaceVarying,
            )?;

        let mesh = crate::schemas::geom::read_mesh(&stage, &sdf::path("/M")?)?.expect("Mesh");
        assert_eq!(mesh.points.len(), 4);
        assert_eq!(mesh.face_vertex_counts, vec![4]);
        assert_eq!(mesh.face_vertex_indices, vec![0, 1, 2, 3]);
        assert_eq!(mesh.orientation, Orientation::RightHanded);

        let uvs = mesh.uvs.expect("uvs");
        assert_eq!(uvs.values.len(), 4);
        assert_eq!(uvs.interpolation, Interpolation::FaceVarying);
        let colors = mesh.display_color.expect("displayColor");
        assert_eq!(colors.values.len(), 1);
        assert_eq!(colors.interpolation, Interpolation::Constant);
        Ok(())
    }

    #[test]
    fn mesh_normals_roundtrip_vertex_interpolation() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_mesh(&stage, sdf::path("/M")?)?
            .set_points(vec![[0.0, 0.0, 0.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.0]])?
            .set_face_vertex_counts(vec![3])?
            .set_face_vertex_indices(vec![0, 1, 2])?
            .set_normals(
                vec![[0.0, 0.0, 1.0], [0.0, 0.0, 1.0], [0.0, 0.0, 1.0]],
                Interpolation::Vertex,
            )?;

        let mesh = crate::schemas::geom::read_mesh(&stage, &sdf::path("/M")?)?.expect("Mesh");
        let normals = mesh.normals.expect("normals");
        assert_eq!(normals.values.len(), 3);
        assert_eq!(normals.interpolation, Interpolation::Vertex);
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
