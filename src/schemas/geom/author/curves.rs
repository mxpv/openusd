//! Curve / patch / points / tet-mesh / point-instancer authoring.
//!
//! Covers `UsdGeomBasisCurves`, `UsdGeomNurbsCurves`,
//! `UsdGeomNurbsPatch`, `UsdGeomHermiteCurves`, `UsdGeomPoints`,
//! `UsdGeomTetMesh`, and `UsdGeomPointInstancer`. Each helper
//! authors a typed prim and exposes chainable setters for the
//! attribute set documented in `usdGeom/schema.usda`.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::Stage;

use crate::schemas::geom::tokens::{
    A_ACCELERATIONS, A_ANGULAR_VELOCITIES, A_BASIS, A_CURVE_VERTEX_COUNTS, A_IDS, A_INVISIBLE_IDS, A_KNOTS, A_ORDER,
    A_ORIENTATIONS, A_POINTS, A_POSITIONS, A_PROTO_INDICES, A_RANGES, A_SCALES, A_TANGENTS, A_TET_VERTEX_INDICES,
    A_TYPE, A_U_FORM, A_U_KNOTS, A_U_ORDER, A_U_RANGE, A_U_VERTEX_COUNT, A_VELOCITIES, A_V_FORM, A_V_KNOTS, A_V_ORDER,
    A_V_RANGE, A_V_VERTEX_COUNT, A_WIDTHS, A_WRAP, REL_PROTOTYPES, T_BASIS_CURVES, T_HERMITE_CURVES, T_NURBS_CURVES,
    T_NURBS_PATCH, T_POINTS, T_POINT_INSTANCER, T_TET_MESH,
};

use super::common::{
    author_double_array, author_float_array, author_int64_array, author_int_vec, author_point3f_array,
    author_quatf_array, author_rel_targets, author_token, author_vec3f_array,
};
use crate::sdf::{Value, Variability};

// ── BasisCurves ────────────────────────────────────────────────────

pub fn define_basis_curves<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<BasisCurvesAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_BASIS_CURVES)?;
    Ok(BasisCurvesAuthor {
        stage,
        path: prim.path().clone(),
    })
}

pub struct BasisCurvesAuthor<'s> {
    stage: &'s Stage,
    path: Path,
}

impl BasisCurvesAuthor<'_> {
    pub fn set_points(self, points: Vec<[f32; 3]>) -> Result<Self> {
        author_point3f_array(self.stage, &self.path, A_POINTS, points)?;
        Ok(self)
    }
    pub fn set_curve_vertex_counts(self, counts: Vec<i32>) -> Result<Self> {
        author_int_vec(self.stage, &self.path, A_CURVE_VERTEX_COUNTS, counts)?;
        Ok(self)
    }
    /// Set `type` (`linear` / `cubic`).
    pub fn set_curve_type(self, type_name: impl Into<String>) -> Result<Self> {
        author_token(self.stage, &self.path, A_TYPE, type_name)?;
        Ok(self)
    }
    /// Set `basis` (`bezier` / `bspline` / `catmullRom`).
    pub fn set_basis(self, basis: impl Into<String>) -> Result<Self> {
        author_token(self.stage, &self.path, A_BASIS, basis)?;
        Ok(self)
    }
    /// Set `wrap` (`nonperiodic` / `periodic` / `pinned`).
    pub fn set_wrap(self, wrap: impl Into<String>) -> Result<Self> {
        author_token(self.stage, &self.path, A_WRAP, wrap)?;
        Ok(self)
    }
    pub fn set_widths(self, widths: Vec<f32>) -> Result<Self> {
        author_float_array(self.stage, &self.path, A_WIDTHS, widths)?;
        Ok(self)
    }
}

// ── NurbsCurves ────────────────────────────────────────────────────

pub fn define_nurbs_curves<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<NurbsCurvesAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_NURBS_CURVES)?;
    Ok(NurbsCurvesAuthor {
        stage,
        path: prim.path().clone(),
    })
}

pub struct NurbsCurvesAuthor<'s> {
    stage: &'s Stage,
    path: Path,
}

impl NurbsCurvesAuthor<'_> {
    pub fn set_points(self, points: Vec<[f32; 3]>) -> Result<Self> {
        author_point3f_array(self.stage, &self.path, A_POINTS, points)?;
        Ok(self)
    }
    pub fn set_curve_vertex_counts(self, counts: Vec<i32>) -> Result<Self> {
        author_int_vec(self.stage, &self.path, A_CURVE_VERTEX_COUNTS, counts)?;
        Ok(self)
    }
    pub fn set_order(self, order: Vec<i32>) -> Result<Self> {
        author_int_vec(self.stage, &self.path, A_ORDER, order)?;
        Ok(self)
    }
    pub fn set_knots(self, knots: Vec<f64>) -> Result<Self> {
        author_double_array(self.stage, &self.path, A_KNOTS, knots)?;
        Ok(self)
    }
    pub fn set_ranges(self, ranges: Vec<[f64; 2]>) -> Result<Self> {
        let attr = self.path.append_property(A_RANGES)?;
        self.stage
            .create_attribute(attr, "double2[]")?
            .set_custom(false)?
            .set(Value::Vec2dVec(ranges))?;
        Ok(self)
    }
    pub fn set_widths(self, widths: Vec<f32>) -> Result<Self> {
        author_float_array(self.stage, &self.path, A_WIDTHS, widths)?;
        Ok(self)
    }
}

// ── NurbsPatch ─────────────────────────────────────────────────────

pub fn define_nurbs_patch<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<NurbsPatchAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_NURBS_PATCH)?;
    Ok(NurbsPatchAuthor {
        stage,
        path: prim.path().clone(),
    })
}

pub struct NurbsPatchAuthor<'s> {
    stage: &'s Stage,
    path: Path,
}

impl NurbsPatchAuthor<'_> {
    pub fn set_points(self, points: Vec<[f32; 3]>) -> Result<Self> {
        author_point3f_array(self.stage, &self.path, A_POINTS, points)?;
        Ok(self)
    }
    pub fn set_uv_vertex_counts(self, u_count: i32, v_count: i32) -> Result<Self> {
        let attr_u = self.path.append_property(A_U_VERTEX_COUNT)?;
        self.stage
            .create_attribute(attr_u, "int")?
            .set_custom(false)?
            .set(Value::Int(u_count))?;
        let attr_v = self.path.append_property(A_V_VERTEX_COUNT)?;
        self.stage
            .create_attribute(attr_v, "int")?
            .set_custom(false)?
            .set(Value::Int(v_count))?;
        Ok(self)
    }
    pub fn set_uv_order(self, u_order: i32, v_order: i32) -> Result<Self> {
        let attr_u = self.path.append_property(A_U_ORDER)?;
        self.stage
            .create_attribute(attr_u, "int")?
            .set_custom(false)?
            .set(Value::Int(u_order))?;
        let attr_v = self.path.append_property(A_V_ORDER)?;
        self.stage
            .create_attribute(attr_v, "int")?
            .set_custom(false)?
            .set(Value::Int(v_order))?;
        Ok(self)
    }
    pub fn set_uv_knots(self, u_knots: Vec<f64>, v_knots: Vec<f64>) -> Result<Self> {
        author_double_array(self.stage, &self.path, A_U_KNOTS, u_knots)?;
        author_double_array(self.stage, &self.path, A_V_KNOTS, v_knots)?;
        Ok(self)
    }
    pub fn set_uv_range(self, u_range: [f64; 2], v_range: [f64; 2]) -> Result<Self> {
        let attr_u = self.path.append_property(A_U_RANGE)?;
        self.stage
            .create_attribute(attr_u, "double2")?
            .set_custom(false)?
            .set(Value::Vec2d(u_range))?;
        let attr_v = self.path.append_property(A_V_RANGE)?;
        self.stage
            .create_attribute(attr_v, "double2")?
            .set_custom(false)?
            .set(Value::Vec2d(v_range))?;
        Ok(self)
    }
    /// Set `uForm` / `vForm` (uniform token, `open` / `closed` / `periodic`).
    pub fn set_forms(self, u_form: impl Into<String>, v_form: impl Into<String>) -> Result<Self> {
        let attr_u = self.path.append_property(A_U_FORM)?;
        self.stage
            .create_attribute(attr_u, "token")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::Token(u_form.into()))?;
        let attr_v = self.path.append_property(A_V_FORM)?;
        self.stage
            .create_attribute(attr_v, "token")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::Token(v_form.into()))?;
        Ok(self)
    }
}

// ── HermiteCurves ──────────────────────────────────────────────────

pub fn define_hermite_curves<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<HermiteCurvesAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_HERMITE_CURVES)?;
    Ok(HermiteCurvesAuthor {
        stage,
        path: prim.path().clone(),
    })
}

pub struct HermiteCurvesAuthor<'s> {
    stage: &'s Stage,
    path: Path,
}

impl HermiteCurvesAuthor<'_> {
    pub fn set_points(self, points: Vec<[f32; 3]>) -> Result<Self> {
        author_point3f_array(self.stage, &self.path, A_POINTS, points)?;
        Ok(self)
    }
    pub fn set_tangents(self, tangents: Vec<[f32; 3]>) -> Result<Self> {
        author_vec3f_array(self.stage, &self.path, A_TANGENTS, tangents)?;
        Ok(self)
    }
    pub fn set_curve_vertex_counts(self, counts: Vec<i32>) -> Result<Self> {
        author_int_vec(self.stage, &self.path, A_CURVE_VERTEX_COUNTS, counts)?;
        Ok(self)
    }
    pub fn set_widths(self, widths: Vec<f32>) -> Result<Self> {
        author_float_array(self.stage, &self.path, A_WIDTHS, widths)?;
        Ok(self)
    }
}

// ── Points ─────────────────────────────────────────────────────────

pub fn define_points<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<PointsAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_POINTS)?;
    Ok(PointsAuthor {
        stage,
        path: prim.path().clone(),
    })
}

pub struct PointsAuthor<'s> {
    stage: &'s Stage,
    path: Path,
}

impl PointsAuthor<'_> {
    pub fn set_points(self, points: Vec<[f32; 3]>) -> Result<Self> {
        author_point3f_array(self.stage, &self.path, A_POINTS, points)?;
        Ok(self)
    }
    pub fn set_widths(self, widths: Vec<f32>) -> Result<Self> {
        author_float_array(self.stage, &self.path, A_WIDTHS, widths)?;
        Ok(self)
    }
    pub fn set_ids(self, ids: Vec<i64>) -> Result<Self> {
        author_int64_array(self.stage, &self.path, A_IDS, ids)?;
        Ok(self)
    }
}

// ── TetMesh ────────────────────────────────────────────────────────

pub fn define_tet_mesh<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<TetMeshAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_TET_MESH)?;
    Ok(TetMeshAuthor {
        stage,
        path: prim.path().clone(),
    })
}

pub struct TetMeshAuthor<'s> {
    stage: &'s Stage,
    path: Path,
}

impl TetMeshAuthor<'_> {
    pub fn set_points(self, points: Vec<[f32; 3]>) -> Result<Self> {
        author_point3f_array(self.stage, &self.path, A_POINTS, points)?;
        Ok(self)
    }
    /// Set `tetVertexIndices` — flat `int[]` of length
    /// `4 * num_tets`. Each consecutive 4-tuple is one tetrahedron
    /// in the order the reader expects.
    pub fn set_tet_vertex_indices(self, indices: Vec<i32>) -> Result<Self> {
        author_int_vec(self.stage, &self.path, A_TET_VERTEX_INDICES, indices)?;
        Ok(self)
    }
}

// ── PointInstancer ─────────────────────────────────────────────────

pub fn define_point_instancer<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<PointInstancerAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_POINT_INSTANCER)?;
    Ok(PointInstancerAuthor {
        stage,
        path: prim.path().clone(),
    })
}

pub struct PointInstancerAuthor<'s> {
    stage: &'s Stage,
    path: Path,
}

impl PointInstancerAuthor<'_> {
    /// Set the `prototypes` rel targets — paths to the prototype prims.
    pub fn set_prototypes<I, P>(self, prototypes: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        author_rel_targets(self.stage, &self.path, REL_PROTOTYPES, prototypes)?;
        Ok(self)
    }
    pub fn set_proto_indices(self, indices: Vec<i32>) -> Result<Self> {
        author_int_vec(self.stage, &self.path, A_PROTO_INDICES, indices)?;
        Ok(self)
    }
    pub fn set_positions(self, positions: Vec<[f32; 3]>) -> Result<Self> {
        author_point3f_array(self.stage, &self.path, A_POSITIONS, positions)?;
        Ok(self)
    }
    pub fn set_scales(self, scales: Vec<[f32; 3]>) -> Result<Self> {
        let attr = self.path.append_property(A_SCALES)?;
        self.stage
            .create_attribute(attr, "float3[]")?
            .set_custom(false)?
            .set(Value::Vec3fVec(scales))?;
        Ok(self)
    }
    pub fn set_orientations(self, quats: Vec<[f32; 4]>) -> Result<Self> {
        author_quatf_array(self.stage, &self.path, A_ORIENTATIONS, quats)?;
        Ok(self)
    }
    pub fn set_velocities(self, velocities: Vec<[f32; 3]>) -> Result<Self> {
        author_vec3f_array(self.stage, &self.path, A_VELOCITIES, velocities)?;
        Ok(self)
    }
    pub fn set_accelerations(self, accelerations: Vec<[f32; 3]>) -> Result<Self> {
        author_vec3f_array(self.stage, &self.path, A_ACCELERATIONS, accelerations)?;
        Ok(self)
    }
    pub fn set_angular_velocities(self, vels: Vec<[f32; 3]>) -> Result<Self> {
        author_vec3f_array(self.stage, &self.path, A_ANGULAR_VELOCITIES, vels)?;
        Ok(self)
    }
    pub fn set_ids(self, ids: Vec<i64>) -> Result<Self> {
        author_int64_array(self.stage, &self.path, A_IDS, ids)?;
        Ok(self)
    }
    pub fn set_invisible_ids(self, ids: Vec<i64>) -> Result<Self> {
        author_int64_array(self.stage, &self.path, A_INVISIBLE_IDS, ids)?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::geom::{
        define_camera, define_cube, define_mesh, define_xform, set_translate, Projection, Purpose, Visibility,
    };
    use crate::sdf;

    #[test]
    fn basis_curves_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_basis_curves(&stage, sdf::path("/C")?)?
            .set_points(vec![[0.0, 0.0, 0.0], [1.0, 0.0, 0.0]])?
            .set_curve_vertex_counts(vec![2])?
            .set_curve_type("linear")?
            .set_basis("bezier")?
            .set_wrap("nonperiodic")?
            .set_widths(vec![0.1, 0.1])?;

        let c = crate::schemas::geom::read_basis_curves(&stage, &sdf::path("/C")?)?.expect("BasisCurves");
        assert_eq!(c.points.len(), 2);
        assert_eq!(c.curve_vertex_counts, vec![2]);
        Ok(())
    }

    #[test]
    fn point_instancer_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_cube(&stage, sdf::path("/Proto/Marker")?)?.set_size(0.1)?;
        define_point_instancer(&stage, sdf::path("/Instances")?)?
            .set_prototypes([sdf::path("/Proto/Marker")?])?
            .set_proto_indices(vec![0, 0, 0])?
            .set_positions(vec![[0.0, 0.0, 0.0], [1.0, 0.0, 0.0], [2.0, 0.0, 0.0]])?
            .set_ids(vec![100, 200, 300])?
            .set_invisible_ids(vec![200])?;

        let inst =
            crate::schemas::geom::read_point_instancer(&stage, &sdf::path("/Instances")?)?.expect("PointInstancer");
        assert_eq!(inst.positions.len(), 3);
        assert_eq!(inst.proto_indices, vec![0, 0, 0]);
        assert_eq!(inst.prototypes, vec!["/Proto/Marker".to_string()]);
        assert_eq!(inst.invisible_ids, vec![200]);
        Ok(())
    }

    #[test]
    fn tet_mesh_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_tet_mesh(&stage, sdf::path("/T")?)?
            .set_points(vec![[0.0, 0.0, 0.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]])?
            .set_tet_vertex_indices(vec![0, 1, 2, 3])?;

        let t = crate::schemas::geom::read_tet_mesh(&stage, &sdf::path("/T")?)?.expect("TetMesh");
        assert_eq!(t.points.len(), 4);
        Ok(())
    }

    #[test]
    fn full_scene_authoring_to_reader_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;

        define_xform(&stage, sdf::path("/World")?)?;
        set_translate(&stage, &sdf::path("/World")?, [0.0, 1.0, 0.0])?;
        super::super::set_visibility(&stage, &sdf::path("/World")?, Visibility::Inherited)?;
        super::super::set_purpose(&stage, &sdf::path("/World")?, Purpose::Render)?;

        define_cube(&stage, sdf::path("/World/Box")?)?.set_size(0.5)?;
        define_mesh(&stage, sdf::path("/World/Mesh")?)?
            .set_points(vec![[0.0, 0.0, 0.0], [1.0, 0.0, 0.0], [1.0, 1.0, 0.0]])?
            .set_face_vertex_counts(vec![3])?
            .set_face_vertex_indices(vec![0, 1, 2])?;
        define_camera(&stage, sdf::path("/World/Cam")?)?
            .set_projection(Projection::Perspective)?
            .set_focal_length(35.0)?;

        // Read every prim back via the existing readers.
        assert_eq!(stage.type_name(&sdf::path("/World")?)?.as_deref(), Some("Xform"),);
        assert!(crate::schemas::geom::read_cube(&stage, &sdf::path("/World/Box")?)?.is_some());
        assert!(crate::schemas::geom::read_mesh(&stage, &sdf::path("/World/Mesh")?)?.is_some());
        assert!(crate::schemas::geom::read_camera(&stage, &sdf::path("/World/Cam")?)?.is_some());
        let order = crate::schemas::geom::read_xform_op_order(&stage, &sdf::path("/World")?)?.expect("xformOpOrder");
        assert_eq!(order, vec!["xformOp:translate".to_string()]);
        Ok(())
    }
}
