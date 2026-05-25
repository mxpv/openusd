//! `UsdGeomMesh` + `UsdGeomSubset` + `UsdGeomPrimvarsAPI` readers.
//!
//! The mesh reader pulls every spec-defined attribute (topology,
//! subdivision controls, creases, corners, display primvars) plus
//! any material-bind subsets attached as child prims. Unauthored
//! attributes fall back to Pixar's documented defaults — notably,
//! `subdivisionScheme` defaults to `catmullClark`.
//!
//! Primvars are surfaced through [`super::Primvar`], which bundles
//! the values with their `interpolation` and optional `indices` /
//! `elementSize` metadata.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::Stage;

use super::tokens::*;
use super::types::*;

/// Read a `Mesh` prim. Returns `None` when the prim's `typeName`
/// isn't `Mesh`, or when the required `points` /
/// `faceVertexCounts` / `faceVertexIndices` triplet is unauthored.
pub fn read_mesh(stage: &Stage, prim: &Path) -> Result<Option<ReadMesh>> {
    if stage.type_name(prim)?.as_deref() != Some(T_MESH) {
        return Ok(None);
    }
    let Some(points) = read_vec3f_vec_opt(stage, prim, A_POINTS)? else {
        return Ok(None);
    };
    let Some(face_vertex_counts) = read_int_vec(stage, prim, A_FACE_VERTEX_COUNTS)? else {
        return Ok(None);
    };
    let Some(face_vertex_indices) = read_int_vec(stage, prim, A_FACE_VERTEX_INDICES)? else {
        return Ok(None);
    };

    let normals = read_primvar_vec3f(stage, prim, A_NORMALS)?;
    let uvs = read_primvar_vec2f(stage, prim, "primvars:st")?.or(read_primvar_vec2f(stage, prim, "primvars:st0")?);
    let velocities = read_vec3f_vec(stage, prim, A_VELOCITIES)?;
    let accelerations = read_vec3f_vec(stage, prim, A_ACCELERATIONS)?;

    let orientation = read_token(stage, prim, A_ORIENTATION)?
        .as_deref()
        .and_then(Orientation::from_token)
        .unwrap_or_default();
    let double_sided = read_bool(stage, prim, A_DOUBLE_SIDED)?.unwrap_or(false);
    let extent = read_extent(stage, prim)?;

    let subdivision_scheme = read_token(stage, prim, A_SUBDIVISION_SCHEME)?
        .as_deref()
        .and_then(SubdivisionScheme::from_token)
        .unwrap_or_default();
    let interpolate_boundary = read_token(stage, prim, A_INTERPOLATE_BOUNDARY)?;
    let face_varying_linear_interpolation = read_token(stage, prim, A_FACE_VARYING_LINEAR_INTERPOLATION)?;
    let triangle_subdivision_rule = read_token(stage, prim, A_TRIANGLE_SUBDIVISION_RULE)?;

    let hole_indices = read_int_vec(stage, prim, A_HOLE_INDICES)?.unwrap_or_default();
    let corner_indices = read_int_vec(stage, prim, A_CORNER_INDICES)?.unwrap_or_default();
    let corner_sharpnesses = read_float_vec(stage, prim, A_CORNER_SHARPNESSES)?.unwrap_or_default();
    let crease_indices = read_int_vec(stage, prim, A_CREASE_INDICES)?.unwrap_or_default();
    let crease_lengths = read_int_vec(stage, prim, A_CREASE_LENGTHS)?.unwrap_or_default();
    let crease_sharpnesses = read_float_vec(stage, prim, A_CREASE_SHARPNESSES)?.unwrap_or_default();

    let display_color = read_primvar_vec3f(stage, prim, "primvars:displayColor")?;
    let display_opacity = read_primvar_float(stage, prim, "primvars:displayOpacity")?;

    let subsets = read_material_bind_subsets(stage, prim)?;

    Ok(Some(ReadMesh {
        path: prim.as_str().to_string(),
        points,
        face_vertex_counts,
        face_vertex_indices,
        normals,
        uvs,
        velocities,
        accelerations,
        orientation,
        double_sided,
        extent,
        subdivision_scheme,
        interpolate_boundary,
        face_varying_linear_interpolation,
        triangle_subdivision_rule,
        hole_indices,
        corner_indices,
        corner_sharpnesses,
        crease_indices,
        crease_lengths,
        crease_sharpnesses,
        display_color,
        display_opacity,
        subsets,
    }))
}

/// Read any `GeomSubset` prim. Returns `None` when the prim isn't
/// typed `GeomSubset`.
pub fn read_subset(stage: &Stage, prim: &Path) -> Result<Option<ReadSubset>> {
    if stage.type_name(prim)?.as_deref() != Some(T_GEOM_SUBSET) {
        return Ok(None);
    }
    Ok(Some(ReadSubset {
        path: prim.as_str().to_string(),
        family_name: read_token(stage, prim, A_FAMILY_NAME)?,
        element_type: read_token(stage, prim, A_ELEMENT_TYPE)?
            .as_deref()
            .and_then(ElementType::from_token)
            .unwrap_or_default(),
        indices: read_int_vec(stage, prim, A_INDICES)?.unwrap_or_default(),
    }))
}

/// Read every authored primvar of `Vec3f` shape on `prim`. Honours
/// the `interpolation`, `elementSize`, and `<name>:indices` metadata.
/// Returns `None` when the named primvar isn't authored.
pub fn read_primvar_vec3f(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Primvar<[f32; 3]>>> {
    let Some(values) = read_vec3f_vec_opt(stage, prim, name)? else {
        return Ok(None);
    };
    Ok(Some(Primvar {
        values,
        interpolation: read_primvar_interpolation(stage, prim, name)?.unwrap_or_default(),
        indices: read_int_vec(stage, prim, &format!("{name}:indices"))?.unwrap_or_default(),
        element_size: read_primvar_element_size(stage, prim, name)?.unwrap_or(1),
    }))
}

/// `Vec2f`-shaped primvar variant. Texture coordinates are the
/// canonical case (`primvars:st`).
pub fn read_primvar_vec2f(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Primvar<[f32; 2]>>> {
    let Some(values) = read_vec2f_vec_opt(stage, prim, name)? else {
        return Ok(None);
    };
    Ok(Some(Primvar {
        values,
        interpolation: read_primvar_interpolation(stage, prim, name)?
            // For UV-like primvars Pixar's most common interpolation
            // is `faceVarying` (one value per face-vertex, so seams
            // work). Fall back to that when unauthored.
            .unwrap_or(Interpolation::FaceVarying),
        indices: read_int_vec(stage, prim, &format!("{name}:indices"))?.unwrap_or_default(),
        element_size: read_primvar_element_size(stage, prim, name)?.unwrap_or(1),
    }))
}

/// Scalar `float` primvar variant — e.g. `primvars:displayOpacity`.
pub fn read_primvar_float(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Primvar<f32>>> {
    let Some(values) = read_float_vec(stage, prim, name)? else {
        return Ok(None);
    };
    Ok(Some(Primvar {
        values,
        interpolation: read_primvar_interpolation(stage, prim, name)?.unwrap_or_default(),
        indices: read_int_vec(stage, prim, &format!("{name}:indices"))?.unwrap_or_default(),
        element_size: read_primvar_element_size(stage, prim, name)?.unwrap_or(1),
    }))
}

// ────────────────────────────────────────────────────────────────────────
// internal helpers
// ────────────────────────────────────────────────────────────────────────

fn read_material_bind_subsets(stage: &Stage, mesh_prim: &Path) -> Result<Vec<ReadSubset>> {
    let mut out = Vec::new();
    for child_name in stage.prim_children(mesh_prim.clone())? {
        let child_path = mesh_prim.append_path(child_name.as_str())?;
        let Some(subset) = read_subset(stage, &child_path)? else {
            continue;
        };
        if subset.family_name.as_deref() == Some(FAMILY_NAME_MATERIAL_BIND) {
            out.push(subset);
        }
    }
    Ok(out)
}

fn read_primvar_interpolation(stage: &Stage, prim: &Path, attr_name: &str) -> Result<Option<Interpolation>> {
    let attr = prim.append_property(attr_name)?;
    if let Some(Value::Token(s) | Value::String(s)) = stage.field::<Value>(attr, META_INTERPOLATION)? {
        return Ok(Interpolation::from_token(&s));
    }
    // Legacy fallback: some authoring tools store the interpolation
    // as a sibling `<name>:interpolation` attribute's default value.
    Ok(read_token(stage, prim, &format!("{attr_name}:interpolation"))?
        .as_deref()
        .and_then(Interpolation::from_token))
}

fn read_primvar_element_size(stage: &Stage, prim: &Path, attr_name: &str) -> Result<Option<i32>> {
    let attr = prim.append_property(attr_name)?;
    Ok(match stage.field::<Value>(attr, META_ELEMENT_SIZE)? {
        Some(Value::Int(n)) => Some(n),
        Some(Value::Int64(n)) => Some(n as i32),
        _ => None,
    })
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

fn read_bool(stage: &Stage, prim: &Path, name: &str) -> Result<Option<bool>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Bool(b)) => Some(b),
        _ => None,
    })
}

fn read_int_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<i32>>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::IntVec(v)) => Some(v),
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

/// Returns the raw `Vec3f` array or `None` when unauthored.
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

/// Returns the raw `Vec3f` array, defaulting to empty when
/// unauthored. Used for optional motion attributes (velocities,
/// accelerations) where "not authored" means "no motion data".
fn read_vec3f_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Vec<[f32; 3]>> {
    Ok(read_vec3f_vec_opt(stage, prim, name)?.unwrap_or_default())
}

fn read_vec2f_vec_opt(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<[f32; 2]>>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Vec2fVec(v)) => Some(v),
        Some(Value::Vec2dVec(v)) => Some(v.into_iter().map(|a| [a[0] as f32, a[1] as f32]).collect()),
        Some(Value::Vec2hVec(v)) => Some(v.into_iter().map(|a| [a[0].to_f32(), a[1].to_f32()]).collect()),
        _ => None,
    })
}

fn read_extent(stage: &Stage, prim: &Path) -> Result<Option<[[f32; 3]; 2]>> {
    let arr = read_vec3f_vec(stage, prim, A_EXTENT)?;
    Ok(if arr.len() >= 2 { Some([arr[0], arr[1]]) } else { None })
}
