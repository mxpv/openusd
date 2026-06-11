//! Time-dependent view of a `SkelAnimation` prim.
//!
//! Mirrors Pixar's `UsdSkelAnimQuery`. Thin wrapper: each
//! `compute_*` method pulls the underlying `timeSamples` through
//! [`crate::usd::Attribute::get`], so the values it returns already
//! honour the stage's interpolation mode (AOUSD §12.5 — linear by
//! default, with per-joint slerp for the `rotations` array).
//!
//! The resolver itself is static — build once, then query at
//! whatever stage times the consumer needs. Defaults for unauthored
//! components match Pixar's reference: identity translation, identity
//! quaternion, unit scale, zero blend-shape weight.

use anyhow::Result;

use crate::gf;
use crate::sdf::{Path, Value};
use crate::tf;
use crate::usd::{SchemaBase, Stage, TimeCode};

use super::schema::SkelAnimation;
use super::tokens::{A_BLEND_SHAPE_WEIGHTS, A_ROTATIONS, A_SCALES, A_TRANSLATIONS};

/// Decomposed joint-local transforms at a stage time: one entry per
/// joint, holding translation, rotation, and scale. Returned by
/// [`SkelAnimQuery::compute_joint_local_transform_components`].
pub type JointTransformComponents = (Vec<gf::Vec3f>, Vec<gf::Quatf>, Vec<gf::Vec3f>);

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
        let Some(anim) = SkelAnimation::get(stage, prim)? else {
            return Ok(None);
        };
        let joints = anim.joints()?;
        let blend_shapes = anim.blend_shapes()?;
        if joints.is_empty() && blend_shapes.is_empty() {
            return Ok(None);
        }
        let prim = anim.path().clone();
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
        time: impl Into<TimeCode>,
    ) -> Result<JointTransformComponents> {
        let time = time.into();
        let n = self.joints.len();
        let translations = self.read_vec3f_attr_at(stage, A_TRANSLATIONS, time, n, gf::Vec3f::default())?;
        let rotations = self.read_quatf_attr_at(stage, A_ROTATIONS, time, n, gf::Quatf::IDENTITY)?;
        let scales = self.read_vec3f_attr_at(stage, A_SCALES, time, n, gf::vec3f(1.0, 1.0, 1.0))?;
        Ok((translations, rotations, scales))
    }

    /// Returns the joint-local 4×4 transform per joint at `time`,
    /// composed `scale · rotation · translation` in USD's row-major
    /// convention. Callers feeding the result into
    /// [`super::SkeletonResolver::compute_skinning_transforms_from_local`]
    /// get full skinning transforms out the other side.
    pub fn compute_joint_local_transforms(
        &self,
        stage: &Stage,
        time: impl Into<TimeCode>,
    ) -> Result<Vec<gf::Matrix4d>> {
        let (translations, rotations, scales) = self.compute_joint_local_transform_components(stage, time.into())?;
        Ok(translations
            .iter()
            .zip(rotations.iter())
            .zip(scales.iter())
            .map(|((t, r), s)| gf::Matrix4d::from_trs(*t, *r, *s))
            .collect())
    }

    /// Blend-shape weight per entry in
    /// [`blend_shape_order`](Self::blend_shape_order) at `time`. Unauthored
    /// weights default to zero (no contribution).
    pub fn compute_blend_shape_weights(&self, stage: &Stage, time: impl Into<TimeCode>) -> Result<Vec<f32>> {
        let n = self.blend_shapes.len();
        if n == 0 {
            return Ok(Vec::new());
        }
        let attr = self.prim.append_property(A_BLEND_SHAPE_WEIGHTS)?;
        let v = stage.attribute(attr).get_at::<Value>(time.into())?;
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
        name: impl Into<tf::Token>,
        time: TimeCode,
        n: usize,
        default: gf::Vec3f,
    ) -> Result<Vec<gf::Vec3f>> {
        let attr = self.prim.append_property(name)?;
        let v = stage.attribute(attr).get_at::<Value>(time)?;
        Ok(match v {
            Some(Value::Vec3fVec(a)) if a.len() == n => a,
            Some(Value::Vec3dVec(a)) if a.len() == n => a
                .into_iter()
                .map(|x| gf::vec3f(x.x as f32, x.y as f32, x.z as f32))
                .collect(),
            Some(Value::Vec3hVec(a)) if a.len() == n => a
                .into_iter()
                .map(|x| gf::vec3f(x.x.to_f32(), x.y.to_f32(), x.z.to_f32()))
                .collect(),
            _ => vec![default; n],
        })
    }

    fn read_quatf_attr_at(
        &self,
        stage: &Stage,
        name: impl Into<tf::Token>,
        time: TimeCode,
        n: usize,
        default: gf::Quatf,
    ) -> Result<Vec<gf::Quatf>> {
        let attr = self.prim.append_property(name)?;
        let v = stage.attribute(attr).get_at::<Value>(time)?;
        Ok(match v {
            Some(Value::QuatfVec(a)) if a.len() == n => a,
            Some(Value::QuatdVec(a)) if a.len() == n => a
                .into_iter()
                .map(|q| gf::quatf(q.w as f32, q.x as f32, q.y as f32, q.z as f32))
                .collect(),
            Some(Value::QuathVec(a)) if a.len() == n => a
                .into_iter()
                .map(|q| gf::quatf(q.w.to_f32(), q.x.to_f32(), q.y.to_f32(), q.z.to_f32()))
                .collect(),
            _ => vec![default; n],
        })
    }
}

fn attr_authored(stage: &Stage, prim: &Path, name: impl Into<tf::Token>) -> Result<bool> {
    let attr = prim.append_property(name)?;
    let default = stage.field::<Value>(attr.clone(), "default")?;
    if default.is_some() {
        return Ok(true);
    }
    let samples = stage.field::<Value>(attr, "timeSamples")?;
    Ok(matches!(samples, Some(Value::TimeSamples(_))))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_trs_identity_rotation_unit_scale() {
        let m = gf::Matrix4d::from_trs(gf::vec3f(1.0, 2.0, 3.0), gf::Quatf::IDENTITY, gf::vec3f(1.0, 1.0, 1.0));
        assert_eq!(m.0[12..16], [1.0, 2.0, 3.0, 1.0]);
        assert_eq!(m[(0, 0)], 1.0);
        assert_eq!(m[(1, 1)], 1.0);
        assert_eq!(m[(2, 2)], 1.0);
    }

    #[test]
    fn from_trs_scale_then_translation() {
        let m = gf::Matrix4d::from_trs(gf::vec3f(10.0, 0.0, 0.0), gf::Quatf::IDENTITY, gf::vec3f(2.0, 3.0, 4.0));
        assert_eq!(m[(0, 0)], 2.0);
        assert_eq!(m[(1, 1)], 3.0);
        assert_eq!(m[(2, 2)], 4.0);
        assert_eq!(m[(3, 0)], 10.0);
    }
}
