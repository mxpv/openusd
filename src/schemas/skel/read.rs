//! Reader functions for the [UsdSkel](super) schema family.
//!
//! Each `read_*` helper takes a composed [`Stage`] plus the prim
//! [`Path`] to inspect, returns the decoded struct (or [`None`] when
//! the schema isn't applied / the prim isn't of the expected type),
//! or surfaces a `Result` for IO / decode errors.
//!
//! Numeric conventions follow USD's authored form:
//! - Matrices are row-major flattened (16 doubles for 4×4).
//! - Quaternions are USD's `(w, x, y, z)` order.
//! - Half-precision storage (`half3[] scales`, `quath[] rotations`) is
//!   widened to `f32` so callers don't need the `half` crate.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::Stage;

use super::tokens::*;
use super::types::*;

/// Read a `SkelRoot` prim. Returns `None` when the prim isn't typed
/// `SkelRoot`.
pub fn read_skel_root(stage: &Stage, prim: &Path) -> Result<Option<ReadSkelRoot>> {
    if stage.type_name(prim)?.as_deref() != Some(T_SKEL_ROOT) {
        return Ok(None);
    }
    let extent = read_extent(stage, prim)?;
    Ok(Some(ReadSkelRoot {
        path: prim.as_str().to_string(),
        extent,
    }))
}

/// Read a `Skeleton` prim. Returns `None` when the prim isn't typed
/// `Skeleton`.
pub fn read_skeleton(stage: &Stage, prim: &Path) -> Result<Option<ReadSkeleton>> {
    if stage.type_name(prim)?.as_deref() != Some(T_SKELETON) {
        return Ok(None);
    }
    let joints = read_token_vec(stage, prim, A_JOINTS)?;
    let bind_transforms = read_mat4_vec(stage, prim, A_BIND_TRANSFORMS)?;
    let rest_transforms = read_mat4_vec(stage, prim, A_REST_TRANSFORMS)?;
    Ok(Some(ReadSkeleton {
        path: prim.as_str().to_string(),
        joints,
        bind_transforms,
        rest_transforms,
    }))
}

/// Read a `SkelAnimation` prim. Returns `None` when the prim isn't
/// typed `SkelAnimation`.
///
/// Attributes that author only a `default` (no `timeSamples`) are
/// surfaced as a single entry at time `0.0`, so the caller can treat
/// static and animated SkelAnimations uniformly.
pub fn read_skel_animation(stage: &Stage, prim: &Path) -> Result<Option<ReadSkelAnimation>> {
    if stage.type_name(prim)?.as_deref() != Some(T_SKEL_ANIMATION) {
        return Ok(None);
    }
    let joints = read_token_vec(stage, prim, A_JOINTS)?;
    let blend_shapes = read_token_vec(stage, prim, A_BLEND_SHAPES)?;
    let translations = read_vec3f_timed(stage, prim, A_TRANSLATIONS)?;
    let rotations = read_quatf_timed(stage, prim, A_ROTATIONS)?;
    let scales = read_vec3f_timed(stage, prim, A_SCALES)?;
    let blend_shape_weights = read_float_timed(stage, prim, A_BLEND_SHAPE_WEIGHTS)?;
    Ok(Some(ReadSkelAnimation {
        path: prim.as_str().to_string(),
        joints,
        blend_shapes,
        translations,
        rotations,
        scales,
        blend_shape_weights,
    }))
}

/// Read a `BlendShape` prim. Returns `None` when the prim isn't typed
/// `BlendShape` or has no `offsets` authored.
pub fn read_blend_shape(stage: &Stage, prim: &Path) -> Result<Option<ReadBlendShape>> {
    if stage.type_name(prim)?.as_deref() != Some(T_BLEND_SHAPE) {
        return Ok(None);
    }
    let offsets = read_vec3f_vec(stage, prim, A_OFFSETS)?;
    if offsets.is_empty() {
        return Ok(None);
    }
    let normal_offsets = read_vec3f_vec(stage, prim, A_NORMAL_OFFSETS)?;
    let point_indices = read_int_vec(stage, prim, A_POINT_INDICES)?.unwrap_or_default();
    let inbetweens = read_inbetweens(stage, prim)?;
    Ok(Some(ReadBlendShape {
        path: prim.as_str().to_string(),
        offsets,
        normal_offsets,
        point_indices,
        inbetweens,
    }))
}

/// Read every `inbetweens:<name>` attribute authored on `prim`.
///
/// Walks the prim's property list looking for the `inbetweens:`
/// namespace, then reads each one's `weight` metadata,
/// `offsets`-style default value, and the matching
/// `inbetweens:<name>:normalOffsets` sibling.
fn read_inbetweens(stage: &Stage, prim: &Path) -> Result<Vec<ReadInbetween>> {
    let mut out = Vec::new();
    let props = stage.prim_properties(prim.clone())?;
    for name in &props {
        let Some(rest) = name.strip_prefix(NS_INBETWEENS) else {
            continue;
        };
        // Skip the per-inbetween `normalOffsets` siblings — they're
        // folded into the inbetween that names them.
        if rest.contains(':') {
            continue;
        }
        let attr_path = prim.append_property(name)?;
        let offsets = match stage.field::<Value>(attr_path.clone(), "default")? {
            Some(Value::Vec3fVec(v)) => v,
            Some(Value::Vec3dVec(v)) => v.into_iter().map(|a| [a[0] as f32, a[1] as f32, a[2] as f32]).collect(),
            Some(Value::Vec3hVec(v)) => v
                .into_iter()
                .map(|a| [a[0].to_f32(), a[1].to_f32(), a[2].to_f32()])
                .collect(),
            _ => Vec::new(),
        };
        let weight = match stage.field::<Value>(attr_path, META_WEIGHT)? {
            Some(Value::Float(f)) => Some(f),
            Some(Value::Double(d)) => Some(d as f32),
            _ => None,
        };
        let normal_offsets_name = format!("{NS_INBETWEENS}{rest}:{A_NORMAL_OFFSETS}");
        let normal_offsets = if props.iter().any(|n| n == &normal_offsets_name) {
            read_vec3f_vec(stage, prim, &normal_offsets_name)?
        } else {
            Vec::new()
        };
        out.push(ReadInbetween {
            name: rest.to_string(),
            weight,
            offsets,
            normal_offsets,
        });
    }
    Ok(out)
}

/// Read `SkelBindingAPI` state from a prim. Returns `None` when the
/// API isn't applied.
///
/// Note that `skel:skeleton` and `skel:animationSource` are inheritable
/// down namespace — this function reports only the values authored
/// *directly* on `prim`. Use [`read_inherited_skeleton`] /
/// [`read_inherited_animation_source`] to walk ancestors.
pub fn read_skel_binding(stage: &Stage, prim: &Path) -> Result<Option<ReadSkelBinding>> {
    if !stage.has_api_schema(prim, API_SKEL_BINDING)? {
        return Ok(None);
    }
    let skeleton = read_rel_first_target(stage, prim, REL_SKEL_SKELETON)?;
    let animation_source = read_rel_first_target(stage, prim, REL_SKEL_ANIMATION_SOURCE)?;
    let joint_indices = read_int_vec(stage, prim, A_JOINT_INDICES)?.unwrap_or_default();
    let joint_weights = read_float_vec(stage, prim, A_JOINT_WEIGHTS)?.unwrap_or_default();
    let elements_per_element = read_attr_field(stage, prim, A_JOINT_INDICES, META_ELEMENT_SIZE)?
        .and_then(|v| match v {
            Value::Int(n) => Some(n),
            Value::Int64(n) => Some(n as i32),
            _ => None,
        })
        .unwrap_or(1);
    let interpolation = read_attr_field(stage, prim, A_JOINT_INDICES, META_INTERPOLATION)?
        .and_then(|v| match v {
            Value::Token(s) | Value::String(s) => InfluenceInterpolation::from_token(&s),
            _ => None,
        })
        .unwrap_or(InfluenceInterpolation::Vertex);
    let joint_subset = read_token_vec(stage, prim, A_SKEL_JOINTS)?;
    let blend_shapes = read_token_vec(stage, prim, A_SKEL_BLEND_SHAPES)?;
    let blend_shape_targets = read_rel_all_targets(stage, prim, REL_SKEL_BLEND_SHAPE_TARGETS)?;
    let geom_bind_transform = read_mat4(stage, prim, A_GEOM_BIND_TRANSFORM)?;
    let skinning_method = read_token(stage, prim, A_SKINNING_METHOD)?
        .and_then(|s| SkinningMethod::from_token(&s))
        .unwrap_or_default();
    Ok(Some(ReadSkelBinding {
        path: prim.as_str().to_string(),
        skeleton,
        animation_source,
        joint_indices,
        joint_weights,
        elements_per_element,
        interpolation,
        joint_subset,
        blend_shapes,
        blend_shape_targets,
        geom_bind_transform,
        skinning_method,
    }))
}

/// Resolve the inherited `skel:skeleton` binding for `prim` by walking
/// up its ancestors. Returns the rel target authored on the nearest
/// ancestor (inclusive of `prim` itself) that authors the rel, or
/// `None` if no such ancestor exists.
///
/// The walk does not require `SkelBindingAPI` to be formally applied
/// on the ancestor — `skel:skeleton` is inheritable down namespace by
/// virtue of being a `skel:`-prefixed rel, regardless of where the
/// API is declared.
pub fn read_inherited_skeleton(stage: &Stage, prim: &Path) -> Result<Option<String>> {
    read_inherited_rel(stage, prim, REL_SKEL_SKELETON)
}

/// Resolve the inherited `skel:animationSource` binding for `prim` by
/// walking up its ancestors. Same inheritance rules as
/// [`read_inherited_skeleton`].
pub fn read_inherited_animation_source(stage: &Stage, prim: &Path) -> Result<Option<String>> {
    read_inherited_rel(stage, prim, REL_SKEL_ANIMATION_SOURCE)
}

fn read_inherited_rel(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Option<String>> {
    let mut cur = prim.clone();
    loop {
        if let Some(target) = read_rel_first_target(stage, &cur, rel_name)? {
            return Ok(Some(target));
        }
        if cur.as_str() == "/" {
            return Ok(None);
        }
        match cur.parent() {
            Some(p) => cur = p,
            None => return Ok(None),
        }
    }
}

/// Walk the entire stage once and return categorised path lists.
/// Saves callers from re-walking for each schema family.
pub fn find_skel_prims(stage: &Stage) -> Result<SkelPrims> {
    let mut out = SkelPrims::default();
    let mut first_err: Result<()> = Ok(());
    stage.traverse(|path| {
        if first_err.is_err() {
            return;
        }
        let mut visit = || -> Result<()> {
            if let Some(type_name) = stage.type_name(path)? {
                match type_name.as_str() {
                    T_SKEL_ROOT => out.skel_roots.push(path.as_str().to_string()),
                    T_SKELETON => out.skeletons.push(path.as_str().to_string()),
                    T_SKEL_ANIMATION => out.animations.push(path.as_str().to_string()),
                    T_BLEND_SHAPE => out.blend_shapes.push(path.as_str().to_string()),
                    _ => {}
                }
            }
            let api = stage.api_schemas(path)?;
            if api.iter().any(|s| s == API_SKEL_BINDING) {
                out.bindings.push(path.as_str().to_string());
            }
            Ok(())
        };
        if let Err(e) = visit() {
            first_err = Err(e);
        }
    })?;
    first_err?;
    Ok(out)
}

// ────────────────────────────────────────────────────────────────────────
// internal value helpers
// ────────────────────────────────────────────────────────────────────────

fn read_attr_default(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    let attr_path = prim.append_property(name)?;
    stage.field::<Value>(attr_path, "default")
}

fn read_attr_field(stage: &Stage, prim: &Path, attr_name: &str, field: &str) -> Result<Option<Value>> {
    let attr_path = prim.append_property(attr_name)?;
    stage.field::<Value>(attr_path, field)
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match read_attr_default(stage, prim, name)? {
        Some(Value::Token(s)) | Some(Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_token_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Vec<String>> {
    Ok(match read_attr_default(stage, prim, name)? {
        Some(Value::TokenVec(v)) | Some(Value::StringVec(v)) => v,
        _ => Vec::new(),
    })
}

fn read_int_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<i32>>> {
    Ok(match read_attr_default(stage, prim, name)? {
        Some(Value::IntVec(v)) => Some(v),
        _ => None,
    })
}

fn read_float_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<f32>>> {
    Ok(match read_attr_default(stage, prim, name)? {
        Some(Value::FloatVec(v)) => Some(v),
        Some(Value::DoubleVec(v)) => Some(v.into_iter().map(|d| d as f32).collect()),
        _ => None,
    })
}

fn read_vec3f_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Vec<[f32; 3]>> {
    Ok(match read_attr_default(stage, prim, name)? {
        Some(Value::Vec3fVec(v)) => v,
        Some(Value::Vec3dVec(v)) => v.into_iter().map(|a| [a[0] as f32, a[1] as f32, a[2] as f32]).collect(),
        Some(Value::Vec3hVec(v)) => v
            .into_iter()
            .map(|a| [a[0].to_f32(), a[1].to_f32(), a[2].to_f32()])
            .collect(),
        _ => Vec::new(),
    })
}

fn read_mat4(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[f64; 16]>> {
    Ok(match read_attr_default(stage, prim, name)? {
        Some(Value::Matrix4d(m)) => Some(m),
        _ => None,
    })
}

fn read_mat4_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Vec<[f64; 16]>> {
    Ok(match read_attr_default(stage, prim, name)? {
        Some(Value::Matrix4dVec(v)) => v,
        _ => Vec::new(),
    })
}

fn read_extent(stage: &Stage, prim: &Path) -> Result<Option<[[f32; 3]; 2]>> {
    let arr = read_vec3f_vec(stage, prim, A_EXTENT)?;
    Ok(if arr.len() >= 2 { Some([arr[0], arr[1]]) } else { None })
}

fn read_rel_first_target(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Option<String>> {
    Ok(read_rel_all_targets(stage, prim, rel_name)?.into_iter().next())
}

fn read_rel_all_targets(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Vec<String>> {
    let rel_path = prim.append_property(rel_name)?;
    let raw = stage.field::<Value>(rel_path, "targetPaths")?;
    let paths = match raw {
        Some(Value::PathListOp(op)) => op.flatten(),
        Some(Value::PathVec(v)) => v,
        _ => Vec::new(),
    };
    Ok(paths.into_iter().map(|p| p.as_str().to_string()).collect())
}

// ── time-sample readers ─────────────────────────────────────────────
//
// Each `read_*_timed` helper returns `Vec<(time, payload)>`.
// `default`-only attributes are surfaced as a single sample at `t = 0.0`.
// `timeSamples` are returned in authored order (the parser sorts
// ascending by timecode).

fn read_vec3f_timed(stage: &Stage, prim: &Path, name: &str) -> Result<Vec<(f64, Vec<[f32; 3]>)>> {
    let attr_path = prim.append_property(name)?;
    if let Some(Value::TimeSamples(samples)) = stage.field::<Value>(attr_path.clone(), "timeSamples")? {
        let mut out = Vec::with_capacity(samples.len());
        for (t, v) in samples {
            if let Some(arr) = value_to_vec3f_array(v) {
                out.push((t, arr));
            }
        }
        return Ok(out);
    }
    if let Some(arr) = stage
        .field::<Value>(attr_path, "default")?
        .and_then(value_to_vec3f_array)
    {
        return Ok(vec![(0.0, arr)]);
    }
    Ok(Vec::new())
}

fn read_quatf_timed(stage: &Stage, prim: &Path, name: &str) -> Result<Vec<(f64, Vec<[f32; 4]>)>> {
    let attr_path = prim.append_property(name)?;
    if let Some(Value::TimeSamples(samples)) = stage.field::<Value>(attr_path.clone(), "timeSamples")? {
        let mut out = Vec::with_capacity(samples.len());
        for (t, v) in samples {
            if let Some(arr) = value_to_quatf_array(v) {
                out.push((t, arr));
            }
        }
        return Ok(out);
    }
    if let Some(arr) = stage
        .field::<Value>(attr_path, "default")?
        .and_then(value_to_quatf_array)
    {
        return Ok(vec![(0.0, arr)]);
    }
    Ok(Vec::new())
}

fn read_float_timed(stage: &Stage, prim: &Path, name: &str) -> Result<Vec<(f64, Vec<f32>)>> {
    let attr_path = prim.append_property(name)?;
    if let Some(Value::TimeSamples(samples)) = stage.field::<Value>(attr_path.clone(), "timeSamples")? {
        let mut out = Vec::with_capacity(samples.len());
        for (t, v) in samples {
            if let Some(arr) = value_to_f32_array(v) {
                out.push((t, arr));
            }
        }
        return Ok(out);
    }
    if let Some(arr) = stage.field::<Value>(attr_path, "default")?.and_then(value_to_f32_array) {
        return Ok(vec![(0.0, arr)]);
    }
    Ok(Vec::new())
}

fn value_to_vec3f_array(v: Value) -> Option<Vec<[f32; 3]>> {
    Some(match v {
        Value::Vec3fVec(v) => v,
        Value::Vec3dVec(v) => v.into_iter().map(|a| [a[0] as f32, a[1] as f32, a[2] as f32]).collect(),
        Value::Vec3hVec(v) => v
            .into_iter()
            .map(|a| [a[0].to_f32(), a[1].to_f32(), a[2].to_f32()])
            .collect(),
        _ => return None,
    })
}

fn value_to_quatf_array(v: Value) -> Option<Vec<[f32; 4]>> {
    Some(match v {
        Value::QuatfVec(v) => v,
        Value::QuatdVec(v) => v
            .into_iter()
            .map(|q| [q[0] as f32, q[1] as f32, q[2] as f32, q[3] as f32])
            .collect(),
        Value::QuathVec(v) => v
            .into_iter()
            .map(|q| [q[0].to_f32(), q[1].to_f32(), q[2].to_f32(), q[3].to_f32()])
            .collect(),
        _ => return None,
    })
}

fn value_to_f32_array(v: Value) -> Option<Vec<f32>> {
    Some(match v {
        Value::FloatVec(v) => v,
        Value::DoubleVec(v) => v.into_iter().map(|d| d as f32).collect(),
        Value::HalfVec(v) => v.into_iter().map(f32::from).collect(),
        _ => return None,
    })
}
