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
//! `SkelAnimation` at a specific stage time — see [`super::SkelAnimQuery`].
//! Feed its pre-evaluated local transforms into
//! [`SkeletonResolver::compute_skinning_transforms_from_local`] below.

use anyhow::Result;

use crate::gf;

use super::schema::Skeleton;
use super::skinning::{
    compute_inverse_bind_transforms, compute_skinning_transforms as math_skin_xforms, joint_local_to_skel_space,
    joint_skel_to_world,
};
use super::topology::Topology;

/// Resolved, time-independent view of one `Skeleton` prim.
///
/// Build with [`SkeletonResolver::from_skeleton`]; the constructor decodes the
/// joints / bind / rest poses and pre-computes the topology and the
/// inverse-bind matrices that every skinning pipeline reuses every frame.
#[derive(Debug, Clone)]
pub struct SkeletonResolver {
    joints: Vec<String>,
    bind_transforms: Vec<gf::Matrix4d>,
    rest_transforms: Vec<gf::Matrix4d>,
    topology: Topology,
    inverse_bind_transforms: Vec<gf::Matrix4d>,
}

impl SkeletonResolver {
    /// Decode `skeleton` and pre-compute its topology + inverse-bind matrices.
    /// Joints with a singular bind transform fall back to the identity inverse
    /// — same as Pixar's reference implementation.
    pub fn from_skeleton(skeleton: &Skeleton) -> Result<Self> {
        let joints = skeleton.joints()?;
        let bind_transforms = skeleton.bind_transforms()?;
        let rest_transforms = skeleton.rest_transforms()?;
        let topology = Topology::from_joint_paths(&joints);
        let inverse_bind_transforms = compute_inverse_bind_transforms(&bind_transforms);
        Ok(Self {
            joints,
            bind_transforms,
            rest_transforms,
            topology,
            inverse_bind_transforms,
        })
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

    /// World-space joint bind transforms — verbatim from `Skeleton.bindTransforms`.
    pub fn joint_world_bind_transforms(&self) -> &[gf::Matrix4d] {
        &self.bind_transforms
    }

    /// Pre-computed `inverse(bindTransform)` per joint. Used by
    /// [`compute_skinning_transforms_from_world`](Self::compute_skinning_transforms_from_world)
    /// / [`compute_skinning_transforms_from_local`](Self::compute_skinning_transforms_from_local).
    pub fn inverse_bind_transforms(&self) -> &[gf::Matrix4d] {
        &self.inverse_bind_transforms
    }

    /// Compose joint-local transforms into skel-space transforms.
    pub fn joint_local_to_skel_space(&self, local: &[gf::Matrix4d]) -> Vec<gf::Matrix4d> {
        joint_local_to_skel_space(local, &self.topology)
    }

    /// Lift skel-space joint transforms into world space using the supplied
    /// SkelRoot local-to-world matrix.
    pub fn joint_skel_to_world(&self, skel: &[gf::Matrix4d], skel_local_to_world: gf::Matrix4d) -> Vec<gf::Matrix4d> {
        joint_skel_to_world(skel, skel_local_to_world)
    }

    /// Compute skinning transforms (`inverse(bind) · joint_world`) from
    /// world-space joint transforms.
    pub fn compute_skinning_transforms_from_world(&self, joint_world: &[gf::Matrix4d]) -> Vec<gf::Matrix4d> {
        math_skin_xforms(joint_world, &self.inverse_bind_transforms)
    }

    /// Compute skinning transforms from joint-local transforms in one step:
    /// compose to skel-space, lift to world, then multiply by the inverse-bind.
    /// Use when you have only local poses (typical after evaluating a
    /// SkelAnimation).
    pub fn compute_skinning_transforms_from_local(
        &self,
        joint_local: &[gf::Matrix4d],
        skel_local_to_world: gf::Matrix4d,
    ) -> Vec<gf::Matrix4d> {
        let skel = self.joint_local_to_skel_space(joint_local);
        let world = self.joint_skel_to_world(&skel, skel_local_to_world);
        math_skin_xforms(&world, &self.inverse_bind_transforms)
    }

    /// The rest-pose joint-local transforms a caller can hand to
    /// [`compute_skinning_transforms_from_local`](Self::compute_skinning_transforms_from_local)
    /// when no SkelAnimation is bound (or for a preview / fallback pose).
    pub fn rest_pose_local(&self) -> &[gf::Matrix4d] {
        &self.rest_transforms
    }

    /// Rest pose composed into skel-space — equivalent to feeding
    /// [`rest_pose_local`](Self::rest_pose_local) into
    /// [`joint_local_to_skel_space`](Self::joint_local_to_skel_space).
    pub fn rest_pose_skel_space(&self) -> Vec<gf::Matrix4d> {
        joint_local_to_skel_space(&self.rest_transforms, &self.topology)
    }
}
