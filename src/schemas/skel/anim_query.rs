//! Time-dependent view of a `SkelAnimation` prim.
//!
//! Mirrors Pixar's `UsdSkelAnimQuery`. Thin wrapper: each
//! `compute_*` method pulls the underlying `timeSamples` through
//! [`crate::Stage::value_at`], so the values it returns already
//! honour the stage's interpolation mode (AOUSD §12.5 — linear by
//! default, with per-joint slerp for the `rotations` array).
//!
//! The resolver itself is static — build once, then query at
//! whatever stage times the consumer needs. Defaults for unauthored
//! components match Pixar's reference: identity translation, identity
//! quaternion, unit scale, zero blend-shape weight.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::Stage;

use super::skinning::{mat4_mul, IDENTITY_MAT4};
use super::tokens::{
    A_BLEND_SHAPES, A_BLEND_SHAPE_WEIGHTS, A_JOINTS, A_ROTATIONS, A_SCALES, A_TRANSLATIONS, T_SKEL_ANIMATION,
};

/// Decomposed joint-local transforms at a stage time: one entry per
/// joint, holding translation `[x, y, z]`, rotation `[w, x, y, z]`,
/// and scale `[x, y, z]`. Returned by
/// [`SkelAnimQuery::compute_joint_local_transform_components`].
pub type JointTransformComponents = (Vec<[f32; 3]>, Vec<[f32; 4]>, Vec<[f32; 3]>);

/// Pre-resolved description of one `SkelAnimation` prim. Holds the
/// joint and blend-shape ordering tokens plus flags recording which
/// time-sampled attributes were actually authored, so the
/// `*_might_be_time_varying` predicates can answer without going back
/// to the stage.
#[derive(Debug, Clone)]
pub struct SkelAnimQuery {
    prim: Path,
    joints: Vec<String>,
    blend_shapes: Vec<String>,
    has_translations: bool,
    has_rotations: bool,
    has_scales: bool,
    has_blend_shape_weights: bool,
}

impl SkelAnimQuery {
    /// Build a query for a `SkelAnimation` prim. Returns `None` when
    /// the prim isn't typed `SkelAnimation`, or when neither joints
    /// nor blend shapes are authored on it.
    pub fn new(stage: &Stage, prim: Path) -> Result<Option<Self>> {
        if stage.type_name(&prim)?.as_deref() != Some(T_SKEL_ANIMATION) {
            return Ok(None);
        }
        let joints = read_token_vec(stage, &prim, A_JOINTS)?;
        let blend_shapes = read_token_vec(stage, &prim, A_BLEND_SHAPES)?;
        if joints.is_empty() && blend_shapes.is_empty() {
            return Ok(None);
        }
        Ok(Some(Self {
            has_translations: attr_authored(stage, &prim, A_TRANSLATIONS)?,
            has_rotations: attr_authored(stage, &prim, A_ROTATIONS)?,
            has_scales: attr_authored(stage, &prim, A_SCALES)?,
            has_blend_shape_weights: attr_authored(stage, &prim, A_BLEND_SHAPE_WEIGHTS)?,
            joints,
            blend_shapes,
            prim,
        }))
    }

    /// Path of the underlying `SkelAnimation` prim.
    pub fn prim_path(&self) -> &str {
        self.prim.as_str()
    }

    /// Joint ordering as authored on the SkelAnimation. Does not
    /// have to match the bound Skeleton's joint order — callers
    /// remap by name when needed.
    pub fn joint_order(&self) -> &[String] {
        &self.joints
    }

    /// Blend-shape ordering as authored on the SkelAnimation.
    pub fn blend_shape_order(&self) -> &[String] {
        &self.blend_shapes
    }

    /// `true` when any of `translations` / `rotations` / `scales`
    /// is authored on the prim. Mirrors Pixar's
    /// `JointTransformsMightBeTimeVarying` — a `false` lets callers
    /// skip per-frame work when the animation is static.
    pub fn joint_transforms_might_be_time_varying(&self) -> bool {
        self.has_translations || self.has_rotations || self.has_scales
    }

    /// `true` when `blendShapeWeights` is authored on the prim.
    pub fn blend_shape_weights_might_be_time_varying(&self) -> bool {
        self.has_blend_shape_weights
    }

    /// Returns `(translations, rotations, scales)` at `time`. Each
    /// vector has `joints.len()` entries. Components fall back to
    /// the spec's identity values when not authored: zero translation,
    /// identity quaternion `(w=1, x=y=z=0)`, unit scale.
    pub fn compute_joint_local_transform_components(
        &self,
        stage: &Stage,
        time: f64,
    ) -> Result<JointTransformComponents> {
        let n = self.joints.len();
        let translations = self.read_vec3f_attr_at(stage, A_TRANSLATIONS, time, n, [0.0, 0.0, 0.0])?;
        let rotations = self.read_quatf_attr_at(stage, A_ROTATIONS, time, n, [1.0, 0.0, 0.0, 0.0])?;
        let scales = self.read_vec3f_attr_at(stage, A_SCALES, time, n, [1.0, 1.0, 1.0])?;
        Ok((translations, rotations, scales))
    }

    /// Returns the joint-local 4×4 transform per joint at `time`,
    /// composed `scale · rotation · translation` in USD's row-major
    /// convention. Callers feeding the result into
    /// [`super::SkeletonResolver::compute_skinning_transforms_from_local`]
    /// get full skinning transforms out the other side.
    pub fn compute_joint_local_transforms(&self, stage: &Stage, time: f64) -> Result<Vec<[f64; 16]>> {
        let (translations, rotations, scales) = self.compute_joint_local_transform_components(stage, time)?;
        Ok(translations
            .iter()
            .zip(rotations.iter())
            .zip(scales.iter())
            .map(|((t, r), s)| compose_trs(*t, *r, *s))
            .collect())
    }

    /// Blend-shape weight per entry in [`blend_shape_order`] at
    /// `time`. Unauthored weights default to zero (no contribution).
    pub fn compute_blend_shape_weights(&self, stage: &Stage, time: f64) -> Result<Vec<f32>> {
        let n = self.blend_shapes.len();
        if n == 0 {
            return Ok(Vec::new());
        }
        let attr = self.prim.append_property(A_BLEND_SHAPE_WEIGHTS)?;
        let v = stage.value_at(attr, time)?;
        Ok(match v {
            Some(Value::FloatVec(w)) if w.len() == n => w,
            Some(Value::DoubleVec(w)) if w.len() == n => w.into_iter().map(|d| d as f32).collect(),
            Some(Value::HalfVec(w)) if w.len() == n => w.into_iter().map(f32::from).collect(),
            _ => vec![0.0; n],
        })
    }

    fn read_vec3f_attr_at(
        &self,
        stage: &Stage,
        name: &str,
        time: f64,
        n: usize,
        default: [f32; 3],
    ) -> Result<Vec<[f32; 3]>> {
        let attr = self.prim.append_property(name)?;
        let v = stage.value_at(attr, time)?;
        Ok(match v {
            Some(Value::Vec3fVec(a)) if a.len() == n => a,
            Some(Value::Vec3dVec(a)) if a.len() == n => {
                a.into_iter().map(|x| [x[0] as f32, x[1] as f32, x[2] as f32]).collect()
            }
            Some(Value::Vec3hVec(a)) if a.len() == n => a
                .into_iter()
                .map(|x| [x[0].to_f32(), x[1].to_f32(), x[2].to_f32()])
                .collect(),
            _ => vec![default; n],
        })
    }

    fn read_quatf_attr_at(
        &self,
        stage: &Stage,
        name: &str,
        time: f64,
        n: usize,
        default: [f32; 4],
    ) -> Result<Vec<[f32; 4]>> {
        let attr = self.prim.append_property(name)?;
        let v = stage.value_at(attr, time)?;
        Ok(match v {
            Some(Value::QuatfVec(a)) if a.len() == n => a,
            Some(Value::QuatdVec(a)) if a.len() == n => a
                .into_iter()
                .map(|q| [q[0] as f32, q[1] as f32, q[2] as f32, q[3] as f32])
                .collect(),
            Some(Value::QuathVec(a)) if a.len() == n => a
                .into_iter()
                .map(|q| [q[0].to_f32(), q[1].to_f32(), q[2].to_f32(), q[3].to_f32()])
                .collect(),
            _ => vec![default; n],
        })
    }
}

fn read_token_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Vec<String>> {
    let attr = prim.append_property(name)?;
    Ok(match stage.field::<Value>(attr, "default")? {
        Some(Value::TokenVec(v)) | Some(Value::StringVec(v)) => v,
        _ => Vec::new(),
    })
}

fn attr_authored(stage: &Stage, prim: &Path, name: &str) -> Result<bool> {
    let attr = prim.append_property(name)?;
    let default = stage.field::<Value>(attr.clone(), "default")?;
    if default.is_some() {
        return Ok(true);
    }
    let samples = stage.field::<Value>(attr, "timeSamples")?;
    Ok(matches!(samples, Some(Value::TimeSamples(_))))
}

/// Compose translation + rotation + scale into a 4×4 in USD's
/// row-major form, where `v_out = v_in · M`. Component order is
/// `M = scale · rotation · translation`, matching every other matrix
/// helper in this crate.
fn compose_trs(t: [f32; 3], r: [f32; 4], s: [f32; 3]) -> [f64; 16] {
    let scale = scale_matrix(s);
    let rotation = quat_to_matrix(r);
    let translation = translation_matrix(t);
    mat4_mul(&mat4_mul(&scale, &rotation), &translation)
}

fn translation_matrix(t: [f32; 3]) -> [f64; 16] {
    let mut m = IDENTITY_MAT4;
    m[12] = t[0] as f64;
    m[13] = t[1] as f64;
    m[14] = t[2] as f64;
    m
}

fn scale_matrix(s: [f32; 3]) -> [f64; 16] {
    let mut m = IDENTITY_MAT4;
    m[0] = s[0] as f64;
    m[5] = s[1] as f64;
    m[10] = s[2] as f64;
    m
}

/// Convert a `(w, x, y, z)` quaternion to the row-major rotation
/// matrix used elsewhere in this crate. The translation row is
/// identity.
fn quat_to_matrix(q: [f32; 4]) -> [f64; 16] {
    let w = q[0] as f64;
    let x = q[1] as f64;
    let y = q[2] as f64;
    let z = q[3] as f64;
    let xx = x * x;
    let yy = y * y;
    let zz = z * z;
    let xy = x * y;
    let xz = x * z;
    let yz = y * z;
    let wx = w * x;
    let wy = w * y;
    let wz = w * z;
    [
        1.0 - 2.0 * (yy + zz),
        2.0 * (xy + wz),
        2.0 * (xz - wy),
        0.0,
        2.0 * (xy - wz),
        1.0 - 2.0 * (xx + zz),
        2.0 * (yz + wx),
        0.0,
        2.0 * (xz + wy),
        2.0 * (yz - wx),
        1.0 - 2.0 * (xx + yy),
        0.0,
        0.0,
        0.0,
        0.0,
        1.0,
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_quat_to_matrix_is_identity() {
        let m = quat_to_matrix([1.0, 0.0, 0.0, 0.0]);
        assert_eq!(m, IDENTITY_MAT4);
    }

    #[test]
    fn compose_trs_with_identity_rotation_and_unit_scale() {
        let m = compose_trs([1.0, 2.0, 3.0], [1.0, 0.0, 0.0, 0.0], [1.0, 1.0, 1.0]);
        // Translation lives in the last row (row-major).
        assert_eq!(m[12..16], [1.0, 2.0, 3.0, 1.0]);
        // Upper-left 3x3 is identity.
        assert_eq!(m[0], 1.0);
        assert_eq!(m[5], 1.0);
        assert_eq!(m[10], 1.0);
    }

    #[test]
    fn compose_trs_with_scale_then_translation() {
        let m = compose_trs([10.0, 0.0, 0.0], [1.0, 0.0, 0.0, 0.0], [2.0, 3.0, 4.0]);
        // Scale on diagonal.
        assert_eq!(m[0], 2.0);
        assert_eq!(m[5], 3.0);
        assert_eq!(m[10], 4.0);
        // Translation unchanged by scale (translation row is last
        // and scale applies to the linear part).
        assert_eq!(m[12], 10.0);
    }
}
