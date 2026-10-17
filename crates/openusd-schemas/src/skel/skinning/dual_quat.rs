//! Dual-quaternion skinning (C++ `_SkinPointsDQS`, `_SkinNormalsDQS` and
//! `UsdSkel_SkinTransformDQS`): each skinning transform's rotation and
//! translation blend as dual quaternions, and the scale and shear left over
//! blend linearly.

use std::ops::{AddAssign, Mul};

use openusd::gf;

use super::{
    blend, face_varying_points, has_vertex_influences, names_joints, normal_transform, single_joint, skin_frame,
    skin_normals_with, skin_points_with,
};

/// Dual-quaternion skinning of a point cloud (C++ `_SkinPointsDQS`), as
/// [`skin_points`](super::skin_points) describes it.
pub(super) fn skin_points_dqs(
    points: &[gf::Vec3f],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    if !has_vertex_influences(
        points.len(),
        joint_indices,
        joint_weights,
        num_influences,
        skinning_xforms,
    ) {
        return None;
    }
    let joints = Joints::rigid(skinning_xforms);
    Some(skin_points_with(
        points,
        joint_indices,
        joint_weights,
        num_influences,
        geom_bind_transform,
        |point, indices, weights| joints.skin(point, indices, weights),
    ))
}

/// Dual-quaternion skinning of normals (C++ `_SkinNormalsDQS`), as
/// [`skin_normals`](super::skin_normals) describes it.
pub(super) fn skin_normals_dqs(
    normals: &[gf::Vec3f],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    if !has_vertex_influences(
        normals.len(),
        joint_indices,
        joint_weights,
        num_influences,
        skinning_xforms,
    ) {
        return None;
    }
    let joints = Joints::rotations(skinning_xforms);
    Some(skin_normals_with(
        normals,
        |normal| normal,
        joint_indices,
        joint_weights,
        num_influences,
        geom_bind_transform,
        |normal, indices, weights| joints.skin(normal, indices, weights),
    ))
}

/// [`skin_normals_dqs`] over face-varying `normals` (C++ `_SkinNormalsDQS`
/// with face-varying point indices), as
/// [`skin_face_varying_normals`](super::skin_face_varying_normals) describes
/// it.
pub(super) fn skin_face_varying_normals_dqs(
    normals: &[gf::Vec3f],
    face_vertex_indices: &[i32],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    let point_of = face_varying_points(
        normals.len(),
        face_vertex_indices,
        joint_indices,
        joint_weights,
        num_influences,
        skinning_xforms,
    )?;
    let joints = Joints::rotations(skinning_xforms);
    Some(skin_normals_with(
        normals,
        point_of,
        joint_indices,
        joint_weights,
        num_influences,
        geom_bind_transform,
        |normal, indices, weights| joints.skin(normal, indices, weights),
    ))
}

/// Dual-quaternion skinning of one rigid transform (C++
/// `UsdSkel_SkinTransformDQS`), as [`skin_transform`](super::skin_transform)
/// describes it.
pub(super) fn skin_transform_dqs(
    joint_indices: &[i32],
    joint_weights: &[f32],
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<gf::Mat4d> {
    if joint_indices.len() != joint_weights.len() || !names_joints(joint_indices, skinning_xforms) {
        return None;
    }
    if let Some(xform) = single_joint(joint_indices, joint_weights, geom_bind_transform, skinning_xforms) {
        return Some(xform);
    }
    // TODO(perf): share the factored joints of one pose across prims. Every
    // joint is factored, not only those `joint_indices` names: whether any
    // joint scales decides whether the leftover scales blend, as in C++.
    let joints = Joints::rigid(skinning_xforms);
    let rigid = joints.blend(joint_indices, joint_weights);
    Some(skin_frame(geom_bind_transform, |point| {
        rigid.transform(joints.scale(point, joint_indices, joint_weights))
    }))
}

/// Skinning transforms taken apart for dual-quaternion skinning: the rigid
/// part of each, and the scale and shear left over.
struct Joints<R> {
    /// Each joint's rotation, with its translation for points.
    rigid: Vec<R>,
    /// Each joint's leftover scale and shear. `None` when every one lies
    /// within `1e-6` of the identity in each entry.
    scales: Option<Vec<gf::Mat3d>>,
}

impl Joints<gf::DualQuatd> {
    /// Point skinning transforms, each factored into a rotation, with its
    /// shear removed, and a translation (C++ `_ConvertToDualQuaternions`).
    /// The scale is what remains once the rigid part is divided out. A
    /// transform with no inverse takes the zero dual quaternion and the
    /// identity scale.
    fn rigid(skinning_xforms: &[gf::Mat4d]) -> Self {
        let (rigid, scales) = skinning_xforms
            .iter()
            .map(|&xform| {
                let factors = xform.factor(gf::Mat4d::FACTOR_EPSILON);
                if factors.singular {
                    return (gf::DualQuatd::ZERO, gf::Mat3d::IDENTITY);
                }
                let mut rotation = factors.rotation;
                rotation.orthonormalize();
                let rigid = rotation * gf::Mat4d::translation(factors.translation);
                (
                    gf::DualQuatd::from_rotation_translation(
                        rotation.extract_rotation_matrix().extract_rotation_quat(),
                        factors.translation,
                    ),
                    (xform * rigid.inverse_or_max()).extract_rotation_matrix(),
                )
            })
            .unzip();
        Self::new(rigid, scales)
    }
}

impl Joints<gf::Quatd> {
    /// The [`normal_transform`] of each skinning transform, split into its
    /// orthonormalized rotation and the scale that remains once the rotation
    /// is divided out (C++ `_ConvertToQuaternions`).
    fn rotations(skinning_xforms: &[gf::Mat4d]) -> Self {
        let (rigid, scales) = skinning_xforms
            .iter()
            .map(|&xform| {
                let xform = normal_transform(xform);
                let mut rotation = xform;
                rotation.orthonormalize();
                (rotation.extract_rotation_quat(), xform * rotation.inverse_or_max())
            })
            .unzip();
        Self::new(rigid, scales)
    }
}

impl<R: Rigid> Joints<R> {
    fn new(rigid: Vec<R>, scales: Vec<gf::Mat3d>) -> Self {
        let scaled = scales.iter().any(|scale| !scale.is_close(gf::Mat3d::IDENTITY, 1e-6));
        Self {
            rigid,
            scales: scaled.then_some(scales),
        }
    }

    /// `point` skinned through one run of influences: carried through the
    /// blended scales, then by the blended rigid transform.
    fn skin(&self, point: gf::Vec3d, indices: &[i32], weights: &[f32]) -> gf::Vec3d {
        self.blend(indices, weights)
            .transform(self.scale(point, indices, weights))
    }

    /// The rigid transform of one run of influences: the sum of the joints'
    /// rigid parts scaled by weight, each negated where its rotation
    /// lies on the far hemisphere from the most-weighted joint's, normalized.
    /// A zero weight is skipped.
    fn blend(&self, indices: &[i32], weights: &[f32]) -> R {
        let pivot = pivot(indices, weights).map_or(gf::Quatd::ZERO, |joint| self.rigid[joint].rotation());
        blend(indices, weights, &self.rigid, |&joint| {
            if joint.rotation().dot(pivot) < 0.0 {
                joint * -1.0
            } else {
                joint
            }
        })
        .normalize()
    }

    /// `point` through the joints' leftover scales, blended linearly by
    /// weight, or `point` as it is where no joint scales.
    fn scale(&self, point: gf::Vec3d, indices: &[i32], weights: &[f32]) -> gf::Vec3d {
        match &self.scales {
            Some(scales) => blend(indices, weights, scales, |scale| scale.transform(point)),
            None => point,
        }
    }
}

/// A joint's rigid part as dual-quaternion skinning blends it: a dual
/// quaternion for points and transforms, and a quaternion for normals, which
/// C++ blends without a translation.
trait Rigid: Copy + Default + AddAssign + Mul<f64, Output = Self> {
    /// The rotation, whose hemisphere the blend aligns.
    fn rotation(self) -> gf::Quatd;

    /// The blended sum made unit length.
    fn normalize(self) -> Self;

    /// `point` under the normalized rigid part.
    fn transform(self, point: gf::Vec3d) -> gf::Vec3d;
}

impl Rigid for gf::DualQuatd {
    fn rotation(self) -> gf::Quatd {
        self.real
    }

    fn normalize(self) -> Self {
        gf::DualQuatd::normalize(self)
    }

    fn transform(self, point: gf::Vec3d) -> gf::Vec3d {
        gf::DualQuatd::transform(self, point)
    }
}

impl Rigid for gf::Quatd {
    fn rotation(self) -> gf::Quatd {
        self
    }

    fn normalize(self) -> Self {
        gf::Quatd::normalize(self)
    }

    fn transform(self, point: gf::Vec3d) -> gf::Vec3d {
        gf::Quatd::transform(self, point)
    }
}

/// The joint of the first influence whose weight no other exceeds, zero
/// weights included (C++ `_GetPivotJointIndex`). `None` for no influences.
fn pivot(indices: &[i32], weights: &[f32]) -> Option<usize> {
    let mut pivot: Option<(usize, f32)> = None;
    for (&index, &weight) in indices.iter().zip(weights) {
        if pivot.is_none_or(|(_, max)| max < weight) {
            pivot = Some((index as usize, weight));
        }
    }
    pivot.map(|(joint, _)| joint)
}

#[cfg(test)]
mod tests {
    use std::f64::consts::{FRAC_PI_2, FRAC_PI_4};

    use super::super::{skin_normals_lbs, skin_points_lbs, skin_transform_lbs};
    use super::*;

    fn assert_near(a: gf::Vec3f, b: gf::Vec3d) {
        assert!((gf::Vec3d::from(a) - b).length() < 1e-6, "{a:?} != {b:?}");
    }

    #[test]
    fn rigid_matches_linear() {
        // One joint, rotated, scaled and translated: both methods agree.
        let xform = gf::Mat4d::scale([2.0, 2.0, 2.0])
            * gf::Mat4d::rotation_z(FRAC_PI_2)
            * gf::Mat4d::translation([1.0, 0.0, 0.0]);
        let bind = gf::Mat4d::translation([0.0, 0.0, 1.0]);
        let points = [gf::vec3f(1.0, 0.0, 0.0), gf::vec3f(0.0, 2.0, 0.0)];
        let dqs = skin_points_dqs(&points, &[0, 0], &[1.0, 1.0], 1, bind, &[xform]).expect("valid influences");
        let lbs = skin_points_lbs(&points, &[0, 0], &[1.0, 1.0], 1, bind, &[xform]).expect("valid influences");
        for (dqs, lbs) in dqs.into_iter().zip(lbs) {
            assert_near(dqs, lbs.into());
        }
        // A non-uniform scale bends normals the same way under both.
        let skin = [gf::Mat4d::scale([2.0, 1.0, 1.0])];
        let normals = [gf::vec3f(1.0, 1.0, 0.0).normalize()];
        let dqs = skin_normals_dqs(&normals, &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin).expect("valid influences");
        let lbs = skin_normals_lbs(&normals, &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin).expect("valid influences");
        assert_near(dqs[0], lbs[0].into());
    }

    #[test]
    fn twist_keeps_length() {
        // Halfway between the rest pose and a quarter turn about x, a point
        // turns by an eighth, where linear blending would shrink it.
        let skin = [gf::Mat4d::IDENTITY, gf::Mat4d::rotation_x(FRAC_PI_2)];
        let points = [gf::vec3f(0.0, 1.0, 0.0)];
        let dqs = skin_points_dqs(&points, &[0, 1], &[0.5, 0.5], 2, gf::Mat4d::IDENTITY, &skin).expect("valid");
        let eighth = gf::Mat4d::rotation_x(FRAC_PI_4).transform_dir(gf::Vec3d::Y_AXIS);
        assert_near(dqs[0], eighth);
        let normals = skin_normals_dqs(&points, &[0, 1], &[0.5, 0.5], 2, gf::Mat4d::IDENTITY, &skin).expect("valid");
        assert_near(normals[0], eighth);
        let lbs = skin_points_lbs(&points, &[0, 1], &[0.5, 0.5], 2, gf::Mat4d::IDENTITY, &skin).expect("valid");
        assert!(lbs[0].length() < 0.8);

        // A transform skins rigidly too: the frame turns by the same eighth.
        let xform = skin_transform_dqs(&[0, 1], &[0.5, 0.5], gf::Mat4d::IDENTITY, &skin).expect("valid");
        let expected = gf::Mat4d::rotation_x(FRAC_PI_4);
        assert!(xform.is_close(expected, 1e-9), "{xform:?}");
        // Translations alone blend as linear skinning blends them.
        let moves = [
            gf::Mat4d::translation([1.0, 0.0, 0.0]),
            gf::Mat4d::translation([0.0, 1.0, 0.0]),
        ];
        let dqs = skin_transform_dqs(&[0, 1], &[0.5, 0.5], gf::Mat4d::IDENTITY, &moves).expect("valid");
        let lbs = skin_transform_lbs(&[0, 1], &[0.5, 0.5], gf::Mat4d::IDENTITY, &moves).expect("valid");
        assert!(dqs.is_close(lbs, 1e-9), "{dqs:?}");
    }

    #[test]
    fn far_hemisphere_flips() {
        // A 200° turn about x extracts with a negative real part. Blended
        // with the more heavily weighted rest pose, it flips onto the rest
        // pose's hemisphere and takes the short way round, through -160°.
        let skin = [gf::Mat4d::IDENTITY, gf::Mat4d::rotation_x(200f64.to_radians())];
        assert!(skin[1].extract_rotation_quat().w < 0.0);
        let points = [gf::vec3f(0.0, 1.0, 0.0)];
        let dqs = skin_points_dqs(&points, &[0, 1], &[0.6, 0.4], 2, gf::Mat4d::IDENTITY, &skin).expect("valid");
        let half = 100f64.to_radians();
        let angle = 2.0 * (-0.4 * half.sin()).atan2(0.6 - 0.4 * half.cos());
        assert!(angle < 0.0);
        assert_near(dqs[0], gf::Mat4d::rotation_x(angle).transform_dir(gf::Vec3d::Y_AXIS));
    }

    #[test]
    fn singular_joint_rests() {
        // A joint with no inverse contributes a zero rotation and no scale,
        // which normalizes to the identity: the point stays where it is.
        let skin = [gf::Mat4d::scale([0.0, 0.0, 0.0])];
        let points = [gf::vec3f(1.0, 2.0, 3.0)];
        let dqs = skin_points_dqs(&points, &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin);
        assert_eq!(dqs, Some(points.to_vec()));
    }

    #[test]
    fn rejects_bad_input() {
        let skin = [gf::Mat4d::IDENTITY];
        let pts = [gf::Vec3f::default(); 2];
        assert!(skin_points_dqs(&pts, &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_points_dqs(&pts, &[0, 1], &[1.0, 1.0], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_points_dqs(&pts, &[], &[], 0, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_normals_dqs(&pts, &[], &[], 0, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_face_varying_normals_dqs(&pts, &[0], &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_transform_dqs(&[1], &[1.0], gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_transform_dqs(&[0, 0], &[1.0], gf::Mat4d::IDENTITY, &skin).is_none());
    }

    #[test]
    fn face_varying_reads_points() {
        // The second normal reads the turned point; the third names no point
        // and reads point 0.
        let skin = [gf::Mat4d::IDENTITY, gf::Mat4d::rotation_z(FRAC_PI_2)];
        let normals = [gf::vec3f(1.0, 0.0, 0.0); 3];
        let out = skin_face_varying_normals_dqs(
            &normals,
            &[0, 1, 7],
            &[0, 1],
            &[1.0, 1.0],
            1,
            gf::Mat4d::IDENTITY,
            &skin,
        )
        .expect("one face-vertex index per normal");
        assert_near(out[0], gf::Vec3d::X_AXIS);
        assert_near(out[1], gf::Vec3d::Y_AXIS);
        assert_near(out[2], gf::Vec3d::X_AXIS);
    }
}
