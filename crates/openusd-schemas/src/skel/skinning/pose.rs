//! One pose's skinning transforms, shared by the prims skinned through it.

use std::borrow::Cow;
use std::sync::OnceLock;

use openusd::gf;

use super::dual_quat::{
    Joints, Rigid, skin_face_varying_normals_dqs, skin_normals_dqs, skin_points_dqs, skin_transform_dqs,
};
use super::{
    names_joints, normal_transforms, single_joint, skin_face_varying_normals_lbs_with, skin_normals_lbs_with,
    skin_points_lbs, skin_transform_lbs,
};
use crate::skel::{AnimMapper, SkinningMethod};

/// One pose's skinning transforms, in the skeleton's joint order, as
/// [`SkeletonQuery::skinning_transforms`](crate::skel::SkeletonQuery::skinning_transforms)
/// answers them. What a skinning method derives from the transforms, such as
/// their inverse-transposes for normals or their dual quaternions, is made on
/// first use and shared by every prim skinned through the pose.
#[derive(Debug, Clone, Default)]
pub struct Pose {
    xforms: Vec<gf::Mat4d>,
    /// The inverse-transpose of each transform, for linear skinning of
    /// normals.
    normals: OnceLock<Vec<gf::Mat3d>>,
    /// The transforms factored for dual-quaternion skinning of points and
    /// transforms.
    rigid: OnceLock<Joints<gf::DualQuatd>>,
    /// The transforms factored for dual-quaternion skinning of normals.
    rotations: OnceLock<Joints<gf::Quatd>>,
}

/// A [`Pose`] in one prim's joint order: the pose's own order, or the order
/// of the prim's `skel:joints` where it is authored.
pub(crate) struct PrimPose<'a> {
    pose: &'a Pose,
    /// The mapping from the skeleton's joint order onto `skel:joints`, where
    /// it reorders or subsets the joints.
    mapper: Option<&'a AnimMapper>,
}

impl Pose {
    /// The skinning transforms, in the skeleton's joint order.
    pub fn xforms(&self) -> &[gf::Mat4d] {
        &self.xforms
    }

    fn normals(&self) -> &[gf::Mat3d] {
        self.normals.get_or_init(|| normal_transforms(&self.xforms))
    }

    fn rigid(&self) -> &Joints<gf::DualQuatd> {
        self.rigid.get_or_init(|| Joints::rigid(&self.xforms))
    }

    fn rotations(&self) -> &Joints<gf::Quatd> {
        self.rotations.get_or_init(|| Joints::rotations(&self.xforms))
    }
}

impl From<Vec<gf::Mat4d>> for Pose {
    fn from(xforms: Vec<gf::Mat4d>) -> Self {
        Self {
            xforms,
            ..Self::default()
        }
    }
}

impl<'a> PrimPose<'a> {
    /// `pose` remapped through `mapper`, the mapping from the skeleton's
    /// joint order onto a prim's `skel:joints`. A joint of `skel:joints` the
    /// skeleton lacks takes the identity. `None` unless `mapper` maps from as
    /// many joints as `pose` holds.
    pub(crate) fn new(pose: &'a Pose, mapper: Option<&'a AnimMapper>) -> Option<Self> {
        if mapper.is_some_and(|mapper| mapper.source_len() != pose.xforms.len()) {
            return None;
        }
        Some(Self {
            pose,
            mapper: mapper.filter(|mapper| !mapper.is_identity()),
        })
    }

    /// Skin `points` by `method`, as [`skin_points`](super::skin_points)
    /// describes.
    pub(crate) fn skin_points(
        &self,
        method: SkinningMethod,
        points: &[gf::Vec3f],
        joint_indices: &[i32],
        joint_weights: &[f32],
        num_influences: usize,
        geom_bind_transform: gf::Mat4d,
    ) -> Option<Vec<gf::Vec3f>> {
        match method {
            SkinningMethod::ClassicLinear => skin_points_lbs(
                points,
                joint_indices,
                joint_weights,
                num_influences,
                geom_bind_transform,
                &self.remap(self.pose.xforms(), gf::Mat4d::IDENTITY),
            ),
            SkinningMethod::DualQuaternion => skin_points_dqs(
                points,
                joint_indices,
                joint_weights,
                num_influences,
                geom_bind_transform,
                &self.remap_joints(self.pose.rigid()),
            ),
        }
    }

    /// Skin `normals` by `method`, as [`skin_normals`](super::skin_normals)
    /// describes.
    pub(crate) fn skin_normals(
        &self,
        method: SkinningMethod,
        normals: &[gf::Vec3f],
        joint_indices: &[i32],
        joint_weights: &[f32],
        num_influences: usize,
        geom_bind_transform: gf::Mat4d,
    ) -> Option<Vec<gf::Vec3f>> {
        match method {
            SkinningMethod::ClassicLinear => skin_normals_lbs_with(
                normals,
                joint_indices,
                joint_weights,
                num_influences,
                geom_bind_transform,
                &self.remap(self.pose.normals(), gf::Mat3d::IDENTITY),
            ),
            SkinningMethod::DualQuaternion => skin_normals_dqs(
                normals,
                joint_indices,
                joint_weights,
                num_influences,
                geom_bind_transform,
                &self.remap_joints(self.pose.rotations()),
            ),
        }
    }

    /// Skin face-varying `normals` by `method`, as
    /// [`skin_face_varying_normals`](super::skin_face_varying_normals)
    /// describes.
    #[allow(clippy::too_many_arguments)] // C++ `UsdSkelSkinFaceVaryingNormals`'s inputs, one per argument.
    pub(crate) fn skin_face_varying_normals(
        &self,
        method: SkinningMethod,
        normals: &[gf::Vec3f],
        face_vertex_indices: &[i32],
        joint_indices: &[i32],
        joint_weights: &[f32],
        num_influences: usize,
        geom_bind_transform: gf::Mat4d,
    ) -> Option<Vec<gf::Vec3f>> {
        match method {
            SkinningMethod::ClassicLinear => skin_face_varying_normals_lbs_with(
                normals,
                face_vertex_indices,
                joint_indices,
                joint_weights,
                num_influences,
                geom_bind_transform,
                &self.remap(self.pose.normals(), gf::Mat3d::IDENTITY),
            ),
            SkinningMethod::DualQuaternion => skin_face_varying_normals_dqs(
                normals,
                face_vertex_indices,
                joint_indices,
                joint_weights,
                num_influences,
                geom_bind_transform,
                &self.remap_joints(self.pose.rotations()),
            ),
        }
    }

    /// Skin a rigid transform by `method`, as
    /// [`skin_transform`](super::skin_transform) describes.
    pub(crate) fn skin_transform(
        &self,
        method: SkinningMethod,
        joint_indices: &[i32],
        joint_weights: &[f32],
        geom_bind_transform: gf::Mat4d,
    ) -> Option<gf::Mat4d> {
        let xforms = self.xforms();
        match method {
            SkinningMethod::ClassicLinear => {
                skin_transform_lbs(joint_indices, joint_weights, geom_bind_transform, &xforms)
            }
            SkinningMethod::DualQuaternion => {
                if joint_indices.len() != joint_weights.len() || !names_joints(joint_indices, xforms.len()) {
                    return None;
                }
                if let Some(xform) = single_joint(joint_indices, joint_weights, geom_bind_transform, &xforms) {
                    return Some(xform);
                }
                Some(skin_transform_dqs(
                    joint_indices,
                    joint_weights,
                    geom_bind_transform,
                    &self.remap_joints(self.pose.rigid()),
                ))
            }
        }
    }

    /// The skinning transforms in the prim's joint order, with the identity
    /// for a joint the skeleton lacks.
    pub(crate) fn xforms(&self) -> Cow<'a, [gf::Mat4d]> {
        self.remap(self.pose.xforms(), gf::Mat4d::IDENTITY)
    }

    /// `source`, one element per skeleton joint, in the prim's joint order,
    /// with `identity` for a joint the skeleton lacks.
    fn remap<T: Clone>(&self, source: &'a [T], identity: T) -> Cow<'a, [T]> {
        // TODO(perf): the remapped elements could go into a buffer the caller
        // keeps across frames.
        match self.mapper {
            Some(mapper) => Cow::Owned(mapper.remap(source, identity)),
            None => Cow::Borrowed(source),
        }
    }

    /// The factored `joints` in the prim's joint order.
    fn remap_joints<R: Rigid>(&self, joints: &'a Joints<R>) -> Cow<'a, Joints<R>> {
        match self.mapper {
            Some(mapper) => Cow::Owned(joints.remap(mapper)),
            None => Cow::Borrowed(joints),
        }
    }
}
