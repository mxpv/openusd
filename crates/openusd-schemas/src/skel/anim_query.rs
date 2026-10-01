//! Time-dependent view of a `Animation` prim.
//!
//! Mirrors Pixar's `UsdSkelAnimQuery`. Thin wrapper: each
//! `compute_*` method pulls the underlying `timeSamples` through
//! [`openusd::usd::Attribute::get_at`], so the values it returns already
//! honour the stage's interpolation mode (AOUSD §12.5 — linear by
//! default, with per-joint slerp for the `rotations` array). The
//! `*_time_samples` methods say at which times those attributes are
//! authored, for a consumer stepping through the animation sample by
//! sample.
//!
//! Built once over the prim, then queried at whatever stage times the
//! consumer needs. Defaults for unauthored components match Pixar's
//! reference: identity translation, identity quaternion, unit scale,
//! zero blend-shape weight.
//
// TODO(perf): every read builds its attribute handle afresh and resolves
// the value source again. C++ holds a `UsdAttributeQuery` per attribute,
// which resolves the source once; the query here could hold four
// `openusd::usd::AttributeQuery`s the same way once that type is `Clone`
// and `Debug`, and answers sample times from its cached source.

use openusd::Result;

use openusd::gf;
use openusd::sdf::{self, Value};
use openusd::usd::{Attribute, TimeCode};

use super::{Animation, AnimationSchema};

/// Decomposed joint-local transforms at a stage time: one entry per
/// joint, holding translation, rotation, and scale. Returned by
/// [`SkelAnimQuery::compute_joint_local_transform_components`].
pub type JointTransformComponents = (Vec<gf::Vec3f>, Vec<gf::Quatf>, Vec<gf::Vec3f>);

/// Pre-resolved description of one `Animation` prim: the view itself,
/// and the joint and blend-shape orderings as authored on it.
#[derive(Debug, Clone)]
pub struct SkelAnimQuery {
    anim: Animation,
    joints: Vec<String>,
    blend_shapes: Vec<String>,
}

impl SkelAnimQuery {
    /// Build a query over an `Animation`. Returns `None` when neither
    /// joints nor blend shapes are authored on it, there being nothing to
    /// animate.
    pub fn new(anim: Animation) -> Result<Option<Self>> {
        let joints = anim.joint_paths()?;
        let blend_shapes: Vec<String> = anim.blend_shapes_attr().cast()?.unwrap_or_default();
        if joints.is_empty() && blend_shapes.is_empty() {
            return Ok(None);
        }
        Ok(Some(Self {
            anim,
            joints,
            blend_shapes,
        }))
    }

    /// The `Animation` prim the query reads.
    pub fn animation(&self) -> &Animation {
        &self.anim
    }

    /// Joint ordering as authored on the Animation. Does not
    /// have to match the bound Skeleton's joint order — callers
    /// remap by name when needed.
    pub fn joint_order(&self) -> &[String] {
        &self.joints
    }

    /// Blend-shape ordering as authored on the Animation.
    pub fn blend_shape_order(&self) -> &[String] {
        &self.blend_shapes
    }

    /// Whether any of `translations` / `rotations` / `scales` may change
    /// over time. Mirrors Pixar's `JointTransformsMightBeTimeVarying` — a
    /// `false` lets callers skip per-frame work when the animation is
    /// static.
    pub fn joint_transforms_might_be_time_varying(&self) -> Result<bool> {
        for attribute in self.joint_transform_attributes() {
            if attribute.value_might_be_time_varying()? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Whether `blendShapeWeights` may change over time. Mirrors Pixar's
    /// `BlendShapeWeightsMightBeTimeVarying`.
    pub fn blend_shape_weights_might_be_time_varying(&self) -> Result<bool> {
        self.anim.blend_shape_weights_attr().value_might_be_time_varying()
    }

    /// The three attributes a joint transform is composed from:
    /// `translations`, `rotations` and `scales`, whether or not each is
    /// authored. Mirrors Pixar's `GetJointTransformAttributes`.
    pub fn joint_transform_attributes(&self) -> [Attribute; 3] {
        [
            self.anim.translations_attr(),
            self.anim.rotations_attr(),
            self.anim.scales_attr(),
        ]
    }

    /// Returns `(translations, rotations, scales)` at `time`. Each
    /// vector has `joints.len()` entries. Components fall back to
    /// the spec's identity values when not authored: zero translation,
    /// identity quaternion `(w=1, x=y=z=0)`, unit scale.
    pub fn compute_joint_local_transform_components(
        &self,
        time: impl Into<TimeCode>,
    ) -> Result<JointTransformComponents> {
        let time = time.into();
        let n = self.joints.len();
        let translations = array_at(&self.anim.translations_attr(), time, n, gf::Vec3f::default())?;
        let rotations = array_at(&self.anim.rotations_attr(), time, n, gf::Quatf::IDENTITY)?;
        let scales = array_at(&self.anim.scales_attr(), time, n, gf::vec3f(1.0, 1.0, 1.0))?;
        Ok((translations, rotations, scales))
    }

    /// Returns the joint-local 4×4 transform per joint at `time`,
    /// composed `scale · rotation · translation` in USD's row-major
    /// convention. Callers feeding the result into
    /// [`super::SkeletonResolver::compute_skinning_transforms_from_local`]
    /// get full skinning transforms out the other side.
    pub fn compute_joint_local_transforms(&self, time: impl Into<TimeCode>) -> Result<Vec<gf::Matrix4d>> {
        let (translations, rotations, scales) = self.compute_joint_local_transform_components(time.into())?;
        Ok(translations
            .iter()
            .zip(rotations.iter())
            .zip(scales.iter())
            .map(|((t, r), s)| gf::Matrix4d::from_trs(*t, *r, *s))
            .collect())
    }

    /// Every time at which a joint transform component is authored, across
    /// `translations`, `rotations` and `scales`, ascending and without
    /// repeats. Mirrors Pixar's `GetJointTransformTimeSamples`.
    pub fn joint_transform_time_samples(&self) -> Result<Vec<f64>> {
        Attribute::unioned_time_samples(&self.joint_transform_attributes())
    }

    /// The joint transform sample times within `interval`. Mirrors Pixar's
    /// `GetJointTransformTimeSamplesInInterval`.
    pub fn joint_transform_time_samples_in_interval(&self, interval: impl Into<gf::Interval>) -> Result<Vec<f64>> {
        Attribute::unioned_time_samples_in_interval(&self.joint_transform_attributes(), interval)
    }

    /// Every time at which `blendShapeWeights` is authored, ascending.
    /// Mirrors Pixar's `GetBlendShapeWeightTimeSamples`.
    pub fn blend_shape_weight_time_samples(&self) -> Result<Vec<f64>> {
        self.anim.blend_shape_weights_attr().time_sample_times()
    }

    /// The blend-shape weight sample times within `interval`. Mirrors Pixar's
    /// `GetBlendShapeWeightTimeSamplesInInterval`.
    pub fn blend_shape_weight_time_samples_in_interval(&self, interval: impl Into<gf::Interval>) -> Result<Vec<f64>> {
        self.anim.blend_shape_weights_attr().time_samples_in_interval(interval)
    }

    /// Blend-shape weight per entry in
    /// [`blend_shape_order`](Self::blend_shape_order) at `time`. Unauthored
    /// weights default to zero (no contribution).
    pub fn compute_blend_shape_weights(&self, time: impl Into<TimeCode>) -> Result<Vec<f32>> {
        array_at(
            &self.anim.blend_shape_weights_attr(),
            time.into(),
            self.blend_shapes.len(),
            0.0,
        )
    }
}

/// `attribute`'s value at `time` as `n` entries of `T`, whatever precision it
/// was authored at, or `n` copies of `default` where it holds nothing of that
/// shape.
fn array_at<T: Clone>(attribute: &Attribute, time: TimeCode, n: usize, default: T) -> Result<Vec<T>>
where
    Vec<T>: sdf::FromValueCast,
{
    let array = attribute
        .get_at::<Value>(time)?
        .and_then(|value| value.cast::<Vec<T>>().ok())
        .filter(|array| array.len() == n);
    Ok(array.unwrap_or_else(|| vec![default; n]))
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
