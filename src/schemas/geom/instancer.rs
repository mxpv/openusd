//! `UsdGeomPointInstancer` reader.
//!
//! Decodes the vectorized-instancing prim: a `prototypes`
//! relationship plus per-instance `proto_indices`, `positions`,
//! optional `orientations` / `scales`, motion data, and prune lists.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::Stage;

use super::tokens::*;
use super::types::*;

/// Read a `PointInstancer` prim. Returns `None` when the prim isn't
/// typed `PointInstancer` or has no `protoIndices` / `positions`
/// authored.
pub fn read_point_instancer(stage: &Stage, prim: &Path) -> Result<Option<ReadPointInstancer>> {
    if stage.type_name(prim)?.as_deref() != Some(T_POINT_INSTANCER) {
        return Ok(None);
    }
    let Some(proto_indices) = read_int_vec(stage, prim, A_PROTO_INDICES)? else {
        return Ok(None);
    };
    let Some(positions) = read_vec3f_vec_opt(stage, prim, A_POSITIONS)? else {
        return Ok(None);
    };
    Ok(Some(ReadPointInstancer {
        path: prim.as_str().to_string(),
        prototypes: read_rel_targets(stage, prim, REL_PROTOTYPES)?,
        proto_indices,
        positions,
        // Pixar's canonical attribute is `orientations` (`quath[]`),
        // but the newer `orientationsf` (`quatf[]`) is also accepted.
        // Try both — first wins.
        orientations: read_quat_vec(stage, prim, A_ORIENTATIONS)?
            .or(read_quat_vec(stage, prim, A_ORIENTATIONS_F)?)
            .unwrap_or_default(),
        scales: read_vec3f_vec(stage, prim, A_SCALES)?,
        velocities: read_vec3f_vec(stage, prim, A_VELOCITIES)?,
        accelerations: read_vec3f_vec(stage, prim, A_ACCELERATIONS)?,
        angular_velocities: read_vec3f_vec(stage, prim, A_ANGULAR_VELOCITIES)?,
        ids: read_int64_vec(stage, prim, A_IDS)?.unwrap_or_default(),
        invisible_ids: read_int64_vec(stage, prim, A_INVISIBLE_IDS)?.unwrap_or_default(),
        inactive_ids: read_inactive_ids_metadata(stage, prim)?,
    }))
}

// ────────────────────────────────────────────────────────────────────────
// internal helpers
// ────────────────────────────────────────────────────────────────────────

fn attr_default(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    let attr = prim.append_property(name)?;
    stage.field::<Value>(attr, "default")
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

fn read_vec3f_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Vec<[f32; 3]>> {
    Ok(read_vec3f_vec_opt(stage, prim, name)?.unwrap_or_default())
}

fn read_quat_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<[f32; 4]>>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::QuatfVec(v)) => Some(v),
        Some(Value::QuatdVec(v)) => Some(
            v.into_iter()
                .map(|q| [q[0] as f32, q[1] as f32, q[2] as f32, q[3] as f32])
                .collect(),
        ),
        Some(Value::QuathVec(v)) => Some(
            v.into_iter()
                .map(|q| [q[0].to_f32(), q[1].to_f32(), q[2].to_f32(), q[3].to_f32()])
                .collect(),
        ),
        _ => None,
    })
}

fn read_rel_targets(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Vec<String>> {
    let rel_path = prim.append_property(rel_name)?;
    let raw = stage.field::<Value>(rel_path, "targetPaths")?;
    let paths = match raw {
        Some(Value::PathListOp(op)) => op.flatten(),
        Some(Value::PathVec(v)) => v,
        _ => Vec::new(),
    };
    Ok(paths.into_iter().map(|p| p.as_str().to_string()).collect())
}

/// `inactiveIds` lives on the prim's metadata, not as an attribute.
/// Try `Int64Vec` first (Pixar's authored shape) then `IntVec`.
fn read_inactive_ids_metadata(stage: &Stage, prim: &Path) -> Result<Vec<i64>> {
    Ok(match stage.field::<Value>(prim.clone(), META_INACTIVE_IDS)? {
        Some(Value::Int64Vec(v)) => v,
        Some(Value::IntVec(v)) => v.into_iter().map(|i| i as i64).collect(),
        _ => Vec::new(),
    })
}
