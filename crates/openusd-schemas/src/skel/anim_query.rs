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
//! consumer needs. The schema gives the animation's arrays no fallbacks, so a
//! read answers `None` where an array has no value, as C++ answers `false`.
//
// TODO(perf): every read builds its attribute handle afresh and resolves
// the value source again. C++ holds a `UsdAttributeQuery` per attribute,
// which resolves the source once; the query here could hold four
// `openusd::usd::AttributeQuery`s the same way once that type is `Clone`
// and `Debug`, and answers sample times from its cached source.

use std::sync::Arc;

use openusd::Result;

use openusd::gf;
use openusd::usd::{Attribute, TimeCode};
use openusd::vt::{self, Value};

use super::skinning::{JointTransformComponents, make_transforms};
use super::{Animation, AnimationSchema};

/// Pre-resolved description of one `Animation` prim: the view itself,
/// and the joint and blend-shape orderings as authored on it.
#[derive(Debug, Clone)]
pub struct AnimQuery {
    anim: Animation,
    joints: Vec<String>,
    blend_shapes: Arc<[String]>,
}

impl AnimQuery {
    /// Build a query over an `Animation`, reading its joint and blend-shape
    /// orders (C++ `UsdSkel_AnimQueryImpl::New`). An animation that authors
    /// neither has empty orders.
    pub fn new(anim: Animation) -> Result<Self> {
        let joints = anim.joint_paths()?;
        let blend_shapes = anim
            .blend_shapes_attr()
            .cast::<Vec<String>>()?
            .unwrap_or_default()
            .into();
        Ok(Self {
            anim,
            joints,
            blend_shapes,
        })
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

    /// [`blend_shape_order`](Self::blend_shape_order), shared with every
    /// skinning query built against it.
    pub(super) fn shared_blend_shape_order(&self) -> Arc<[String]> {
        self.blend_shapes.clone()
    }

    /// Whether any of `translations` / `rotations` / `scales` may change
    /// over time. Mirrors Pixar's `JointTransformsMightBeTimeVarying` — a
    /// `false` lets callers skip per-frame work when the animation is
    /// static.
    pub fn joint_transforms_might_be_time_varying(&self) -> Result<bool> {
        for attribute in self.joint_transform_attributes() {
            if attribute.might_be_time_varying()? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Whether `blendShapeWeights` may change over time. Mirrors Pixar's
    /// `BlendShapeWeightsMightBeTimeVarying`.
    pub fn blend_shape_weights_might_be_time_varying(&self) -> Result<bool> {
        self.anim.blend_shape_weights_attr().might_be_time_varying()
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

    /// The attributes the blend-shape weights are read from:
    /// `blendShapeWeights`, whether or not it is authored (C++
    /// `GetBlendShapeWeightAttributes`).
    pub fn blend_shape_weight_attributes(&self) -> [Attribute; 1] {
        [self.anim.blend_shape_weights_attr()]
    }

    /// Returns `(translations, rotations, scales)` at `time`, `None` being
    /// the default time (C++ `ComputeJointLocalTransformComponents`). `None`
    /// when any of the three has no value at `time`: unauthored, blocked, or
    /// not decodable as its declared array type. A component authored at
    /// another precision of its type decodes, scales widened from `half3`.
    /// The arrays are answered as authored, of whatever lengths.
    pub fn joint_transform_components(
        &self,
        time: impl Into<Option<TimeCode>>,
    ) -> Result<Option<JointTransformComponents>> {
        transform_components(&self.anim, time.into())
    }

    /// Returns the joint-local 4×4 transform per joint at `time`,
    /// composed `scale · rotation · translation` in USD's row-major
    /// convention (C++ `ComputeJointLocalTransforms`). `None` when the
    /// components have no value, differ in length, or do not hold one entry
    /// per joint of [`joint_order`](Self::joint_order). The transforms are in
    /// the animation's joint order.
    pub fn joint_local_transforms(&self, time: impl Into<Option<TimeCode>>) -> Result<Option<Vec<gf::Mat4d>>> {
        Ok(self
            .joint_transform_components(time)?
            .filter(|(translations, _, _)| translations.len() == self.joints.len())
            .and_then(|(translations, rotations, scales): JointTransformComponents| {
                make_transforms(&translations, &rotations, &scales)
            }))
    }

    /// Every time at which a joint transform component is authored, across
    /// `translations`, `rotations` and `scales`, ascending and without
    /// repeats. Mirrors Pixar's `GetJointTransformTimeSamples`.
    pub fn joint_transform_time_samples(&self) -> Result<Vec<f64>> {
        Attribute::unioned_time_samples(&self.joint_transform_attributes())
    }

    /// The joint transform sample times within `interval`. Mirrors Pixar's
    /// `GetJointTransformTimeSamplesInInterval`.
    pub fn joint_transform_time_samples_in(&self, interval: impl Into<gf::Interval>) -> Result<Vec<f64>> {
        Attribute::unioned_time_samples_in(&self.joint_transform_attributes(), interval)
    }

    /// Every time at which `blendShapeWeights` is authored, ascending.
    /// Mirrors Pixar's `GetBlendShapeWeightTimeSamples`.
    pub fn blend_shape_weight_time_samples(&self) -> Result<Vec<f64>> {
        self.anim.blend_shape_weights_attr().time_sample_times()
    }

    /// The blend-shape weight sample times within `interval`. Mirrors Pixar's
    /// `GetBlendShapeWeightTimeSamplesInInterval`.
    pub fn blend_shape_weight_time_samples_in(&self, interval: impl Into<gf::Interval>) -> Result<Vec<f64>> {
        self.anim.blend_shape_weights_attr().time_samples_in(interval)
    }

    /// The blend-shape weights at `time`, as authored (C++
    /// `ComputeBlendShapeWeights`). `None` when the weights have no value at
    /// `time`. Their length is checked against
    /// [`blend_shape_order`](Self::blend_shape_order) where they are remapped,
    /// as in C++.
    pub fn blend_shape_weights(&self, time: impl Into<Option<TimeCode>>) -> Result<Option<Vec<f32>>> {
        array_at(&self.anim.blend_shape_weights_attr(), time.into())
    }
}

/// `attribute`'s value at `time` as an array of `T`, whatever precision it
/// was authored at, or `None` where it holds no value of that shape.
/// `anim`'s `(translations, rotations, scales)` at `time`, as
/// [`AnimQuery::joint_transform_components`] answers them.
pub(super) fn transform_components(
    anim: &Animation,
    time: Option<TimeCode>,
) -> Result<Option<JointTransformComponents>> {
    let Some(translations) = array_at(&anim.translations_attr(), time)? else {
        return Ok(None);
    };
    let Some(rotations) = array_at(&anim.rotations_attr(), time)? else {
        return Ok(None);
    };
    let Some(scales) = array_at(&anim.scales_attr(), time)? else {
        return Ok(None);
    };
    Ok(Some((translations, rotations, scales)))
}

fn array_at<T>(attribute: &Attribute, time: Option<TimeCode>) -> Result<Option<Vec<T>>>
where
    Vec<T>: vt::FromValueCast,
{
    Ok(attribute
        .get_at::<Value>(time)?
        .and_then(|value| value.cast::<Vec<T>>().ok()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_trs_identity_rotation_unit_scale() {
        let m = gf::Mat4d::from_trs(gf::vec3f(1.0, 2.0, 3.0), gf::Quatf::IDENTITY, gf::vec3f(1.0, 1.0, 1.0));
        assert_eq!(m.0[12..16], [1.0, 2.0, 3.0, 1.0]);
        assert_eq!(m[(0, 0)], 1.0);
        assert_eq!(m[(1, 1)], 1.0);
        assert_eq!(m[(2, 2)], 1.0);
    }

    #[test]
    fn from_trs_scale_then_translation() {
        let m = gf::Mat4d::from_trs(gf::vec3f(10.0, 0.0, 0.0), gf::Quatf::IDENTITY, gf::vec3f(2.0, 3.0, 4.0));
        assert_eq!(m[(0, 0)], 2.0);
        assert_eq!(m[(1, 1)], 3.0);
        assert_eq!(m[(2, 2)], 4.0);
        assert_eq!(m[(3, 0)], 10.0);
    }
}
