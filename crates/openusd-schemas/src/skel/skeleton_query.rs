//! Static (time-independent) resolver bundle for a `Skeleton`.
//!
//! Mirrors the *static* surface of Pixar's `UsdSkelSkeletonQuery`:
//! topology, joint order, world-space bind transforms (per spec
//! `bindTransforms` is already world-space), pre-computed inverse-bind
//! matrices, and the helpers that compose joint-local transforms into
//! skel-space and combine them with current poses to produce skinning
//! matrices.
//!
//! Time-dependent methods (`ComputeJointLocalTransforms(time)`,
//! `ComputeSkinningTransforms(time)`, etc.) require evaluating a bound
//! `Animation` at a specific stage time — see [`super::AnimQuery`].
//! Map its pre-evaluated local transforms onto the skeleton with
//! [`SkeletonResolver::joint_local_transforms`], then feed them into
//! [`SkeletonResolver::skinning_transforms_from_local`].

use openusd::Result;

use openusd::gf;

use super::anim_mapper::AnimMapper;
use super::skinning::{inverse_bind_transforms, joint_local_to_skel_space, skinning_transforms as math_skin_xforms};
use super::topology::Topology;
use super::{Skeleton, SkeletonSchema};

/// Resolved, time-independent view of one `Skeleton` prim.
///
/// Build with [`SkeletonResolver::from_skeleton`]; the constructor decodes the
/// joints / bind / rest poses and pre-computes the topology and the
/// inverse-bind matrices that every skinning pipeline reuses every frame.
#[derive(Debug, Clone)]
pub struct SkeletonResolver {
    joints: Vec<String>,
    topology: Topology,
    /// The bind pose, where `bindTransforms` holds one entry per joint.
    bind: Option<BindPose>,
    /// `restTransforms`, where it holds one entry per joint.
    rest_transforms: Option<Vec<gf::Mat4d>>,
}

/// A skeleton's bind transforms and their inverses.
#[derive(Debug, Clone)]
struct BindPose {
    transforms: Vec<gf::Mat4d>,
    inverse: Vec<gf::Mat4d>,
}

impl SkeletonResolver {
    /// Decode `skeleton` and pre-compute its topology and inverse-bind matrices
    /// (C++ `UsdSkel_SkelDefinition`). `None` when the joint topology is invalid.
    ///
    /// A `bindTransforms` or `restTransforms` array whose length differs from
    /// the joint count counts as no bind or rest pose. Joints with a singular
    /// bind transform invert as [`gf::Mat4d::inverse_or_max`] does (C++
    /// `GfMatrix4d::GetInverse`).
    pub fn from_skeleton(skeleton: &Skeleton) -> Result<Option<Self>> {
        let joints = skeleton.joint_paths()?;
        let topology = Topology::from_joint_paths(&joints);
        if topology.validate().is_err() {
            return Ok(None);
        }
        let per_joint = |transforms: Option<Vec<gf::Mat4d>>| transforms.filter(|t| t.len() == joints.len());
        let bind = per_joint(skeleton.bind_transforms()?).map(|transforms| BindPose {
            inverse: inverse_bind_transforms(&transforms),
            transforms,
        });
        let rest_transforms = per_joint(skeleton.rest_transforms()?);
        Ok(Some(Self {
            joints,
            topology,
            bind,
            rest_transforms,
        }))
    }

    /// Borrow the skeleton's path-encoded joint order.
    pub fn joint_order(&self) -> &[String] {
        &self.joints
    }

    /// Borrow the topology — handy for callers that want to do their own walks
    /// (e.g. computing a name→index mapping).
    pub fn topology(&self) -> &Topology {
        &self.topology
    }

    /// `true` when `bindTransforms` holds one transform per joint (C++
    /// `HasBindPose`).
    pub fn has_bind_pose(&self) -> bool {
        self.bind.is_some()
    }

    /// `true` when `restTransforms` holds one transform per joint (C++
    /// `HasRestPose`).
    pub fn has_rest_pose(&self) -> bool {
        self.rest_transforms.is_some()
    }

    /// World-space joint bind transforms — verbatim from
    /// `Skeleton.bindTransforms` — where the skeleton has a bind pose.
    pub fn bind_transforms(&self) -> Option<&[gf::Mat4d]> {
        self.bind.as_ref().map(|bind| bind.transforms.as_slice())
    }

    /// Pre-computed `inverse(bindTransform)` per joint, where the skeleton has
    /// a bind pose. Used by [`skinning_transforms`](Self::skinning_transforms)
    /// and [`skinning_transforms_from_local`](Self::skinning_transforms_from_local).
    pub fn inverse_bind_transforms(&self) -> Option<&[gf::Mat4d]> {
        self.bind.as_ref().map(|bind| bind.inverse.as_slice())
    }

    /// Compose joint-local transforms into skel-space transforms (C++
    /// `UsdSkelConcatJointTransforms`). `None` unless `local` holds one
    /// transform per joint.
    pub fn joint_local_to_skel_space(&self, local: &[gf::Mat4d]) -> Option<Vec<gf::Mat4d>> {
        joint_local_to_skel_space(local, &self.topology, None)
    }

    /// The joint-local transforms of this skeleton posed by an animation (C++
    /// `UsdSkelSkeletonQuery::ComputeJointLocalTransforms`). `anim_local`
    /// holds the animation's joint-local transforms in its own joint order,
    /// and `mapper` maps that order onto this skeleton's
    /// (`AnimMapper::new(anim.joint_order(), self.joint_order())`).
    ///
    /// A joint the animation does not cover keeps its rest transform. `None`
    /// when `anim_local` does not match the mapper's source, or when the
    /// animation leaves joints uncovered and the skeleton has no rest pose.
    pub fn joint_local_transforms(&self, mapper: &AnimMapper, anim_local: &[gf::Mat4d]) -> Option<Vec<gf::Mat4d>> {
        let mut local = if mapper.is_sparse() {
            self.rest_transforms.clone()?
        } else {
            vec![gf::Mat4d::IDENTITY; self.joints.len()]
        };
        mapper.remap_into(anim_local, &mut local).then_some(local)
    }

    /// Skinning transforms (`inverse(bind) · joint_skel`) from skel-space joint
    /// transforms (C++ `UsdSkelSkeletonQuery::ComputeSkinningTransforms`). The
    /// skinned points they produce are in skeleton space. `None` when the
    /// skeleton has no bind pose or `joint_skel` holds other than one
    /// transform per joint.
    pub fn skinning_transforms(&self, joint_skel: &[gf::Mat4d]) -> Option<Vec<gf::Mat4d>> {
        math_skin_xforms(joint_skel, self.inverse_bind_transforms()?)
    }

    /// Skinning transforms from joint-local transforms: composed into skel
    /// space, then multiplied by the inverse bind transforms, as
    /// [`skinning_transforms`](Self::skinning_transforms) does.
    pub fn skinning_transforms_from_local(&self, joint_local: &[gf::Mat4d]) -> Option<Vec<gf::Mat4d>> {
        // TODO(perf): the skel-space transforms could be multiplied by the
        // inverse bind transforms in place, or written into a caller's buffer.
        let inverse = self.inverse_bind_transforms()?;
        math_skin_xforms(&self.joint_local_to_skel_space(joint_local)?, inverse)
    }

    /// The rest-pose joint-local transforms a caller can hand to
    /// [`skinning_transforms_from_local`](Self::skinning_transforms_from_local)
    /// when no Animation is bound (or for a preview / fallback pose), where
    /// the skeleton has a rest pose.
    pub fn rest_pose_local(&self) -> Option<&[gf::Mat4d]> {
        self.rest_transforms.as_deref()
    }

    /// Rest pose composed into skel-space — equivalent to feeding
    /// [`rest_pose_local`](Self::rest_pose_local) into
    /// [`joint_local_to_skel_space`](Self::joint_local_to_skel_space).
    pub fn rest_pose_skel_space(&self) -> Option<Vec<gf::Mat4d>> {
        self.joint_local_to_skel_space(self.rest_pose_local()?)
    }
}
