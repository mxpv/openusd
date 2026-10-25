//! A `Skeleton` with the animation it inherits, posed at any time (C++
//! `UsdSkelSkeletonQuery` over `UsdSkel_SkelDefinition`).
//!
//! The query reads the skeleton's joint order, bind and rest poses once, at
//! the default time, and validates the topology. It reads the bound
//! animation at whatever time it is asked for. The definition is a snapshot:
//! after an edit to the skeleton's `joints`, `bindTransforms` or
//! `restTransforms`, to the animation the skeleton binds, or to that
//! animation's `joints`, build a new query.

use std::cell::OnceCell;
use std::rc::Rc;
use std::sync::Arc;

use openusd::Result;
use openusd::gf;
use openusd::usd::{SchemaBase, TimeCode};

use super::anim_mapper::AnimMapper;
use super::anim_query::AnimQuery;
use super::skinning::{inverse_transforms, joint_local_to_skel_space, skinning_transforms};
use super::topology::Topology;
use super::{Cache, Skeleton, SkeletonSchema};
use crate::SchemaError;
use crate::geom::XformCache;

/// A skeleton and its bound animation, posed at any time.
///
/// Build with [`SkeletonQuery::new`]. A pose answers `None` where it cannot be
/// computed: no bind pose for the skinning transforms, no rest pose for a
/// joint the animation leaves out, or no rest pose at all without an
/// animation.
#[derive(Debug, Clone)]
pub struct SkeletonQuery {
    /// The skeleton as asked for, an instance proxy where it is one.
    skeleton: Skeleton,
    definition: Rc<Definition>,
    /// The animation the skeleton binds and its mapping onto the skeleton's
    /// joint order. `None` without an animation; the mapper is null when
    /// either joint order is empty.
    anim: Option<(AnimQuery, AnimMapper)>,
}

/// A skeleton's joints, topology, and bind and rest poses, read once at the
/// default time (C++ `UsdSkel_SkelDefinition`). The poses derived from them
/// are computed on first use and kept here, where every clone of the query,
/// and every query a [`Cache`](super::Cache) builds over an instance of the
/// same skeleton, shares them.
#[derive(Debug)]
pub(super) struct Definition {
    joints: Arc<[String]>,
    topology: Topology,
    /// The bind pose, where `bindTransforms` holds one entry per joint.
    bind: Option<BindPose>,
    /// `restTransforms`, where it holds one entry per joint.
    rest: Option<Vec<gf::Mat4d>>,
    /// The rest pose in skeleton space, computed on first use.
    rest_skel: OnceCell<Option<Vec<gf::Mat4d>>>,
    /// The inverse of each joint-local rest transform, computed on first use.
    inverse_rest: OnceCell<Option<Vec<gf::Mat4d>>>,
}

/// A skeleton's bind transforms and their inverses.
#[derive(Debug)]
struct BindPose {
    transforms: Vec<gf::Mat4d>,
    inverse: Vec<gf::Mat4d>,
}

impl SkeletonQuery {
    /// The query over `skeleton`, bound to the animation it inherits
    /// ([`Skeleton::animation_source`]; C++ `UsdSkelCache::GetSkelQuery`).
    /// `None` when the skeleton is inactive or its joint topology is invalid
    /// (C++ `UsdSkel_SkelDefinition::New`).
    ///
    /// A `bindTransforms` or `restTransforms` array whose length differs from
    /// the joint count counts as no bind or rest pose. Joints with a singular
    /// bind transform invert as [`gf::Mat4d::inverse_or_max`] does (C++
    /// `GfMatrix4d::GetInverse`).
    pub fn new(skeleton: &Skeleton) -> Result<Option<Self>> {
        Cache::new().skel_query(skeleton)
    }

    /// The query over `skeleton`, whose definition is `definition`, bound to
    /// `anim`.
    pub(super) fn from_definition(skeleton: Skeleton, definition: Rc<Definition>, anim: Option<AnimQuery>) -> Self {
        let anim = anim.map(|query| {
            let mapper = AnimMapper::new(query.joint_order(), &definition.joints);
            (query, mapper)
        });
        Self {
            skeleton,
            definition,
            anim,
        }
    }

    /// The skeleton the query poses, as it was asked for: an instance proxy
    /// where it is one. C++ answers the prototype's skeleton, which places
    /// [`joint_world_transforms`](Self::joint_world_transforms) at the
    /// prototype's transform.
    pub fn skeleton(&self) -> &Skeleton {
        &self.skeleton
    }

    /// The animation the skeleton binds, if any (C++ `GetAnimQuery`).
    pub fn anim_query(&self) -> Option<&AnimQuery> {
        self.anim.as_ref().map(|(query, _)| query)
    }

    /// The mapping from the animation's joint order onto the skeleton's, if
    /// an animation is bound (C++ `GetMapper`).
    pub fn mapper(&self) -> Option<&AnimMapper> {
        self.anim.as_ref().map(|(_, mapper)| mapper)
    }

    /// The skeleton's path-encoded joint order.
    pub fn joint_order(&self) -> &[String] {
        &self.definition.joints
    }

    /// [`joint_order`](Self::joint_order), shared with every skinning query
    /// built against it.
    pub(super) fn shared_joint_order(&self) -> Arc<[String]> {
        self.definition.joints.clone()
    }

    /// The joint topology the joint order encodes.
    pub fn topology(&self) -> &Topology {
        &self.definition.topology
    }

    /// `true` when `bindTransforms` holds one transform per joint (C++
    /// `HasBindPose`).
    pub fn has_bind_pose(&self) -> bool {
        self.definition.bind.is_some()
    }

    /// `true` when `restTransforms` holds one transform per joint (C++
    /// `HasRestPose`).
    pub fn has_rest_pose(&self) -> bool {
        self.definition.rest.is_some()
    }

    /// The world-space joint bind transforms, verbatim from
    /// `Skeleton.bindTransforms`, where the skeleton has a bind pose (C++
    /// `GetJointWorldBindTransforms`).
    pub fn bind_transforms(&self) -> Option<&[gf::Mat4d]> {
        self.definition.bind.as_ref().map(|bind| bind.transforms.as_slice())
    }

    /// The inverse of each bind transform, computed once, where the skeleton
    /// has a bind pose. With a pose from elsewhere in skeleton space,
    /// [`skinning::skinning_transforms`](super::skinning::skinning_transforms)
    /// over these gives its skinning transforms.
    pub fn inverse_bind_transforms(&self) -> Option<&[gf::Mat4d]> {
        self.definition.bind.as_ref().map(|bind| bind.inverse.as_slice())
    }

    /// The joint-local rest transforms, where the skeleton has a rest pose
    /// (C++ `ComputeJointLocalTransforms` with `atRest`).
    pub fn rest_local_transforms(&self) -> Option<&[gf::Mat4d]> {
        self.definition.rest.as_deref()
    }

    /// The rest pose in skeleton space, where the skeleton has a rest pose
    /// (C++ `ComputeJointSkelTransforms` with `atRest`).
    pub fn rest_skel_transforms(&self) -> Option<&[gf::Mat4d]> {
        let definition = &*self.definition;
        definition
            .rest_skel
            .get_or_init(|| joint_local_to_skel_space(definition.rest.as_deref()?, &definition.topology, None))
            .as_deref()
    }

    /// The joint-local transforms at `time`, `None` being the default time
    /// (C++ `ComputeJointLocalTransforms`).
    ///
    /// Without an animation, or with one whose joint order or the skeleton's
    /// is empty, this is the rest pose. A joint the animation does not cover
    /// keeps its rest transform. An animation that cannot compute at `time`
    /// leaves the rest pose. `None` when the rest pose is needed and the
    /// skeleton has none.
    pub fn joint_local_transforms(&self, time: impl Into<Option<TimeCode>>) -> Result<Option<Vec<gf::Mat4d>>> {
        let rest = self.rest_local_transforms();
        let Some((query, mapper)) = self.mappable_anim() else {
            return Ok(rest.map(<[_]>::to_vec));
        };
        // A sparse mapping fills the joints it leaves out from the rest pose.
        let fill = if mapper.is_sparse() {
            match rest {
                Some(rest) => Some(rest),
                None => return Ok(None),
            }
        } else {
            None
        };
        let Some(anim_local) = query.joint_local_transforms(time)? else {
            return Ok(rest.map(<[_]>::to_vec));
        };
        if mapper.is_identity() {
            return Ok(Some(anim_local));
        }
        let mut local = match fill {
            Some(rest) => rest.to_vec(),
            None => vec![gf::Mat4d::IDENTITY; self.definition.joints.len()],
        };
        Ok(mapper.remap_into(&anim_local, &mut local).then_some(local))
    }

    /// The skel-space joint transforms at `time` (C++
    /// `ComputeJointSkelTransforms`): the rest pose's without a usable
    /// animation, else the [`joint_local_transforms`](Self::joint_local_transforms)
    /// concatenated down the topology.
    pub fn joint_skel_transforms(&self, time: impl Into<Option<TimeCode>>) -> Result<Option<Vec<gf::Mat4d>>> {
        if self.mappable_anim().is_none() {
            return Ok(self.rest_skel_transforms().map(<[_]>::to_vec));
        }
        // TODO(perf): parents precede children, so the concatenation could run
        // in place over the local transforms.
        Ok(self
            .joint_local_transforms(time)?
            .and_then(|local| joint_local_to_skel_space(&local, &self.definition.topology, None)))
    }

    /// Each joint's local transform at `time` relative to its rest transform,
    /// `local · inverse(rest)` (C++ `ComputeJointRestRelativeTransforms`).
    /// Without a usable animation every joint is at rest, so each transform is
    /// the identity. `None` when the skeleton has no rest pose.
    pub fn joint_rest_relative_transforms(&self, time: impl Into<Option<TimeCode>>) -> Result<Option<Vec<gf::Mat4d>>> {
        if self.mappable_anim().is_none() {
            return Ok(Some(vec![gf::Mat4d::IDENTITY; self.definition.joints.len()]));
        }
        let Some(inverse_rest) = self.inverse_rest_transforms() else {
            return Ok(None);
        };
        Ok(self.joint_local_transforms(time)?.map(|mut local| {
            for (local, &inverse) in local.iter_mut().zip(inverse_rest) {
                *local = *local * inverse;
            }
            local
        }))
    }

    /// The world-space joint transforms at the time of `xforms` (C++
    /// `ComputeJointWorldTransforms`): the joint-local transforms concatenated
    /// down the topology, the roots carried by the skeleton's local-to-world
    /// transform.
    pub fn joint_world_transforms(&self, xforms: &mut XformCache) -> Result<Option<Vec<gf::Mat4d>>, SchemaError> {
        let Some(local) = self.joint_local_transforms(xforms.time())? else {
            return Ok(None);
        };
        self.world_from_local(&local, xforms)
    }

    /// The rest pose in world space, at the time of `xforms` (C++
    /// `ComputeJointWorldTransforms` with `atRest`).
    pub fn rest_world_transforms(&self, xforms: &mut XformCache) -> Result<Option<Vec<gf::Mat4d>>, SchemaError> {
        let Some(rest) = self.rest_local_transforms() else {
            return Ok(None);
        };
        self.world_from_local(rest, xforms)
    }

    /// The skinning transforms at `time`, `inverse(bind) · jointSkel` per
    /// joint (C++ `ComputeSkinningTransforms`). The skinned points they
    /// produce are in skeleton space. `None` when the skeleton has no bind
    /// pose, or no skel-space pose at `time`.
    pub fn skinning_transforms(&self, time: impl Into<Option<TimeCode>>) -> Result<Option<Vec<gf::Mat4d>>> {
        let Some(bind) = &self.definition.bind else {
            return Ok(None);
        };
        // TODO(perf): the inverse bind transforms could multiply the skel-space
        // transforms in place.
        Ok(self
            .joint_skel_transforms(time)?
            .and_then(|skel| skinning_transforms(&skel, &bind.inverse)))
    }

    /// The bound animation and its mapper, where the mapper maps anything
    /// onto the skeleton (C++ `_HasMappableAnim`).
    fn mappable_anim(&self) -> Option<&(AnimQuery, AnimMapper)> {
        self.anim.as_ref().filter(|(_, mapper)| !mapper.is_null())
    }

    /// The inverse of each joint-local rest transform, where the skeleton has
    /// a rest pose.
    fn inverse_rest_transforms(&self) -> Option<&[gf::Mat4d]> {
        let definition = &*self.definition;
        definition
            .inverse_rest
            .get_or_init(|| definition.rest.as_deref().map(inverse_transforms))
            .as_deref()
    }

    /// Joint-local transforms concatenated into world space under the
    /// skeleton's local-to-world transform at the time of `xforms`.
    fn world_from_local(
        &self,
        local: &[gf::Mat4d],
        xforms: &mut XformCache,
    ) -> Result<Option<Vec<gf::Mat4d>>, SchemaError> {
        let root = xforms.local_to_world_transform(self.skeleton().prim())?;
        Ok(joint_local_to_skel_space(local, &self.definition.topology, Some(root)))
    }
}

impl Definition {
    /// The definition of `skeleton`, or `None` when its joint topology is
    /// invalid.
    pub(super) fn new(skeleton: &Skeleton) -> Result<Option<Self>> {
        let joints = skeleton.joint_paths()?;
        let topology = Topology::from_joint_paths(&joints);
        if topology.validate().is_err() {
            return Ok(None);
        }
        let per_joint = |transforms: Option<Vec<gf::Mat4d>>| transforms.filter(|t| t.len() == joints.len());
        let bind = per_joint(skeleton.bind_transforms()?).map(|transforms| BindPose {
            inverse: inverse_transforms(&transforms),
            transforms,
        });
        let rest = per_joint(skeleton.rest_transforms()?);
        Ok(Some(Self {
            joints: joints.into(),
            topology,
            bind,
            rest,
            rest_skel: OnceCell::new(),
            inverse_rest: OnceCell::new(),
        }))
    }
}
