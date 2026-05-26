//! Curve / patch / point / tet-mesh readers.
//!
//! Covers `UsdGeomBasisCurves`, `UsdGeomNurbsCurves`,
//! `UsdGeomNurbsPatch`, `UsdGeomHermiteCurves`, `UsdGeomPoints`,
//! and `UsdGeomTetMesh`. Each reader returns `None` when the prim's
//! `typeName` doesn't match. Required geometry attributes (`points`,
//! `curveVertexCounts` / `tetVertexIndices`) must be authored.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::Stage;

use super::mesh::read_primvar_vec3f;
use super::tokens::*;
use super::types::*;

/// Read a `BasisCurves` prim. Returns `None` when the prim isn't
/// typed `BasisCurves` or has no `points`/`curveVertexCounts`
/// authored.
pub fn read_basis_curves(stage: &Stage, prim: &Path) -> Result<Option<ReadBasisCurves>> {
    if stage.type_name(prim)?.as_deref() != Some(T_BASIS_CURVES) {
        return Ok(None);
    }
    let Some(points) = read_vec3f_vec_opt(stage, prim, A_POINTS)? else {
        return Ok(None);
    };
    let Some(curve_vertex_counts) = read_int_vec(stage, prim, A_CURVE_VERTEX_COUNTS)? else {
        return Ok(None);
    };
    Ok(Some(ReadBasisCurves {
        path: prim.as_str().to_string(),
        points,
        curve_vertex_counts,
        curve_type: read_token(stage, prim, A_TYPE)?
            .as_deref()
            .and_then(CurveType::from_token)
            .unwrap_or_default(),
        basis: read_token(stage, prim, A_BASIS)?
            .as_deref()
            .and_then(CurveBasis::from_token)
            .unwrap_or_default(),
        wrap: read_token(stage, prim, A_WRAP)?
            .as_deref()
            .and_then(CurveWrap::from_token)
            .unwrap_or_default(),
        widths: read_float_vec(stage, prim, A_WIDTHS)?.unwrap_or_default(),
        normals: read_primvar_vec3f(stage, prim, A_NORMALS)?,
        display_color: read_primvar_vec3f(stage, prim, "primvars:displayColor")?,
        extent: read_extent(stage, prim)?,
    }))
}

/// Read a `NurbsCurves` prim. Returns `None` when the prim isn't
/// typed `NurbsCurves` or lacks the required `points` /
/// `curveVertexCounts`.
pub fn read_nurbs_curves(stage: &Stage, prim: &Path) -> Result<Option<ReadNurbsCurves>> {
    if stage.type_name(prim)?.as_deref() != Some(T_NURBS_CURVES) {
        return Ok(None);
    }
    let Some(points) = read_vec3f_vec_opt(stage, prim, A_POINTS)? else {
        return Ok(None);
    };
    let Some(curve_vertex_counts) = read_int_vec(stage, prim, A_CURVE_VERTEX_COUNTS)? else {
        return Ok(None);
    };
    // Unauthored order defaults to 4 (cubic) for every curve.
    let order = read_int_vec(stage, prim, A_ORDER)?.unwrap_or_else(|| curve_vertex_counts.iter().map(|_| 4).collect());
    let knots = read_double_vec(stage, prim, A_KNOTS)?.unwrap_or_default();
    let ranges = read_vec2d_vec(stage, prim, A_RANGES)?.unwrap_or_else(|| {
        // Synthesise per-curve ranges from the clamped inner knot span.
        let mut out = Vec::with_capacity(curve_vertex_counts.len());
        let mut k_cursor = 0usize;
        for (i, count) in curve_vertex_counts.iter().enumerate() {
            let n = (*count as usize).max(0);
            let p = order.get(i).copied().unwrap_or(4) as usize;
            let nk = n + p;
            if k_cursor + nk <= knots.len() && p > 0 && n > 0 {
                out.push([knots[k_cursor + p - 1], knots[k_cursor + n]]);
            } else {
                out.push([0.0, 1.0]);
            }
            k_cursor += nk;
        }
        out
    });
    Ok(Some(ReadNurbsCurves {
        path: prim.as_str().to_string(),
        points,
        curve_vertex_counts,
        order,
        knots,
        ranges,
        widths: read_float_vec(stage, prim, A_WIDTHS)?.unwrap_or_default(),
        display_color: read_primvar_vec3f(stage, prim, "primvars:displayColor")?,
    }))
}

/// Read a `NurbsPatch` prim. Returns `None` when the prim isn't
/// typed `NurbsPatch` or has no `points` authored.
pub fn read_nurbs_patch(stage: &Stage, prim: &Path) -> Result<Option<ReadNurbsPatch>> {
    if stage.type_name(prim)?.as_deref() != Some(T_NURBS_PATCH) {
        return Ok(None);
    }
    let Some(points) = read_vec3f_vec_opt(stage, prim, A_POINTS)? else {
        return Ok(None);
    };
    let u_vertex_count = read_int_scalar(stage, prim, A_U_VERTEX_COUNT)?.unwrap_or(0);
    let v_vertex_count = read_int_scalar(stage, prim, A_V_VERTEX_COUNT)?.unwrap_or(0);
    let u_order = read_int_scalar(stage, prim, A_U_ORDER)?.unwrap_or(4);
    let v_order = read_int_scalar(stage, prim, A_V_ORDER)?.unwrap_or(4);
    let u_knots = read_double_vec(stage, prim, A_U_KNOTS)?.unwrap_or_default();
    let v_knots = read_double_vec(stage, prim, A_V_KNOTS)?.unwrap_or_default();
    let u_range = read_vec2d_scalar(stage, prim, A_U_RANGE)?
        .unwrap_or_else(|| clamped_inner_span(&u_knots, u_vertex_count as usize, u_order as usize));
    let v_range = read_vec2d_scalar(stage, prim, A_V_RANGE)?
        .unwrap_or_else(|| clamped_inner_span(&v_knots, v_vertex_count as usize, v_order as usize));
    let u_form = read_token(stage, prim, A_U_FORM)?
        .as_deref()
        .and_then(PatchForm::from_token)
        .unwrap_or_default();
    let v_form = read_token(stage, prim, A_V_FORM)?
        .as_deref()
        .and_then(PatchForm::from_token)
        .unwrap_or_default();
    Ok(Some(ReadNurbsPatch {
        path: prim.as_str().to_string(),
        points,
        u_vertex_count,
        v_vertex_count,
        u_order,
        v_order,
        u_knots,
        v_knots,
        u_range,
        v_range,
        u_form,
        v_form,
        display_color: read_primvar_vec3f(stage, prim, "primvars:displayColor")?,
    }))
}

/// Read a `HermiteCurves` prim. Returns `None` when the prim isn't
/// typed `HermiteCurves` or lacks `points` / `curveVertexCounts`.
pub fn read_hermite_curves(stage: &Stage, prim: &Path) -> Result<Option<ReadHermiteCurves>> {
    if stage.type_name(prim)?.as_deref() != Some(T_HERMITE_CURVES) {
        return Ok(None);
    }
    let Some(points) = read_vec3f_vec_opt(stage, prim, A_POINTS)? else {
        return Ok(None);
    };
    let Some(curve_vertex_counts) = read_int_vec(stage, prim, A_CURVE_VERTEX_COUNTS)? else {
        return Ok(None);
    };
    // Tangents are spec-required but some authoring tools omit them;
    // fall back to forward differences so the curve still renders.
    let tangents = read_vec3f_vec_opt(stage, prim, A_TANGENTS)?.unwrap_or_else(|| {
        let n = points.len();
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            let a = points[i];
            let b = if i + 1 < n { points[i + 1] } else { points[i] };
            out.push([b[0] - a[0], b[1] - a[1], b[2] - a[2]]);
        }
        out
    });
    Ok(Some(ReadHermiteCurves {
        path: prim.as_str().to_string(),
        points,
        tangents,
        curve_vertex_counts,
        widths: read_float_vec(stage, prim, A_WIDTHS)?.unwrap_or_default(),
        display_color: read_primvar_vec3f(stage, prim, "primvars:displayColor")?,
    }))
}

/// Read a `Points` prim. Returns `None` when the prim isn't typed
/// `Points` or has no `points` authored.
pub fn read_points(stage: &Stage, prim: &Path) -> Result<Option<ReadPoints>> {
    if stage.type_name(prim)?.as_deref() != Some(T_POINTS) {
        return Ok(None);
    }
    let Some(points) = read_vec3f_vec_opt(stage, prim, A_POINTS)? else {
        return Ok(None);
    };
    Ok(Some(ReadPoints {
        path: prim.as_str().to_string(),
        points,
        widths: read_float_vec(stage, prim, A_WIDTHS)?.unwrap_or_default(),
        ids: read_int64_vec(stage, prim, A_IDS)?.unwrap_or_default(),
        normals: read_primvar_vec3f(stage, prim, A_NORMALS)?,
        display_color: read_primvar_vec3f(stage, prim, "primvars:displayColor")?,
    }))
}

/// Read a `TetMesh` prim. Returns `None` when the prim isn't typed
/// `TetMesh` or has no `points`/`tetVertexIndices` authored.
pub fn read_tet_mesh(stage: &Stage, prim: &Path) -> Result<Option<ReadTetMesh>> {
    if stage.type_name(prim)?.as_deref() != Some(T_TET_MESH) {
        return Ok(None);
    }
    let Some(points) = read_vec3f_vec_opt(stage, prim, A_POINTS)? else {
        return Ok(None);
    };
    let Some(tet_vertex_indices) = read_int_vec(stage, prim, A_TET_VERTEX_INDICES)? else {
        return Ok(None);
    };
    Ok(Some(ReadTetMesh {
        path: prim.as_str().to_string(),
        points,
        tet_vertex_indices,
        surface_face_vertex_indices: read_int_vec(stage, prim, A_SURFACE_FACE_VERTEX_INDICES)?.unwrap_or_default(),
        display_color: read_primvar_vec3f(stage, prim, "primvars:displayColor")?,
    }))
}

// ────────────────────────────────────────────────────────────────────────
// internal helpers
// ────────────────────────────────────────────────────────────────────────

fn clamped_inner_span(knots: &[f64], n: usize, p: usize) -> [f64; 2] {
    if !knots.is_empty() && n > 0 && p > 0 && knots.len() >= n + p {
        [knots[p - 1], knots[n]]
    } else {
        [0.0, 1.0]
    }
}

fn attr_default(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    let attr = prim.append_property(name)?;
    stage.field::<Value>(attr, "default")
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Token(s) | Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_int_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<i32>>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::IntVec(v)) => Some(v),
        _ => None,
    })
}

fn read_int64_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<i64>>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Int64Vec(v)) => Some(v),
        Some(Value::IntVec(v)) => Some(v.into_iter().map(|i| i as i64).collect()),
        _ => None,
    })
}

fn read_int_scalar(stage: &Stage, prim: &Path, name: &str) -> Result<Option<i32>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Int(v)) => Some(v),
        _ => None,
    })
}

fn read_float_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<f32>>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::FloatVec(v)) => Some(v),
        Some(Value::DoubleVec(v)) => Some(v.into_iter().map(|d| d as f32).collect()),
        Some(Value::HalfVec(v)) => Some(v.into_iter().map(f32::from).collect()),
        _ => None,
    })
}

fn read_double_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<f64>>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::DoubleVec(v)) => Some(v),
        Some(Value::FloatVec(v)) => Some(v.into_iter().map(|f| f as f64).collect()),
        _ => None,
    })
}

fn read_vec3f_vec_opt(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<[f32; 3]>>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Vec3fVec(v)) => Some(v),
        Some(Value::Vec3dVec(v)) => Some(v.into_iter().map(|a| [a[0] as f32, a[1] as f32, a[2] as f32]).collect()),
        Some(Value::Vec3hVec(v)) => Some(
            v.into_iter()
                .map(|a| [a[0].to_f32(), a[1].to_f32(), a[2].to_f32()])
                .collect(),
        ),
        _ => None,
    })
}

fn read_vec2d_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<[f64; 2]>>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Vec2dVec(v)) => Some(v),
        Some(Value::Vec2fVec(v)) => Some(v.into_iter().map(|a| [a[0] as f64, a[1] as f64]).collect()),
        _ => None,
    })
}

fn read_vec2d_scalar(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[f64; 2]>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Vec2d(v)) => Some(v),
        Some(Value::Vec2f(v)) => Some([v[0] as f64, v[1] as f64]),
        _ => None,
    })
}

fn read_extent(stage: &Stage, prim: &Path) -> Result<Option<[[f32; 3]; 2]>> {
    let arr = read_vec3f_vec_opt(stage, prim, A_EXTENT)?.unwrap_or_default();
    Ok(if arr.len() >= 2 { Some([arr[0], arr[1]]) } else { None })
}
