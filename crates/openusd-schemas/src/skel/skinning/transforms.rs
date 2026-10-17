//! Joint transform math: composing joint-local transforms into skeleton space
//! and back, skinning transforms, joint extents, and the decomposition of a
//! transform into translation, rotation and scale (C++ `usdSkel/utils.h`).

use openusd::gf;

use crate::geom::Extent;
use crate::skel::Topology;

/// Decomposed joint-local transforms: translations, rotations and scales.
/// [`decompose_transforms`] answers one entry per transform in each array;
/// [`AnimQuery::joint_transform_components`](crate::skel::AnimQuery::joint_transform_components)
/// answers the arrays as authored, which can differ in length. Scales are
/// widened from the schema's `half3`.
pub type JointTransformComponents = (Vec<gf::Vec3f>, Vec<gf::Quatf>, Vec<gf::Vec3f>);

/// Compose joint-local transforms into skeleton-space transforms by
/// concatenating each joint's local transform with its parent's
/// already-resolved skel-space transform.
///
/// Per the UsdSkel spec: `jointSkelSpaceTransform =
/// jointLocalSpaceTransform * parentJointSkelSpaceTransform`, in one forward
/// pass over the canonical UsdSkel `joints` ordering, where parents precede
/// children (C++ `UsdSkelConcatJointTransforms`).
///
/// Root joints (a negative parent index) keep their local transform as
/// their skel-space transform, times `root` where one is given. `None` when
/// `local` holds other than one transform per joint, or a joint's parent does
/// not precede it.
pub fn joint_local_to_skel_space(
    local: &[gf::Mat4d],
    topology: &Topology,
    root: Option<gf::Mat4d>,
) -> Option<Vec<gf::Mat4d>> {
    if local.len() != topology.joint_count() {
        return None;
    }
    let mut out = Vec::with_capacity(local.len());
    for (i, &transform) in local.iter().enumerate() {
        out.push(match topology.parent(i) {
            Some(parent) => transform * *out.get(parent)?,
            None => root.map_or(transform, |root| transform * root),
        });
    }
    Some(out)
}

/// The joint-local transforms that compose into the skel-space transforms
/// `skel`, the inverse of [`joint_local_to_skel_space`] (C++
/// `UsdSkelComputeJointLocalTransforms`): each joint's skel-space transform
/// times the inverse of its parent's.
///
/// Root joints keep their skel-space transform, times `root_inverse` where
/// one is given. A singular parent transform inverts as
/// [`gf::Mat4d::inverse_or_max`] does. `None` when `skel` holds other than one
/// transform per joint, or a joint's parent does not precede it.
pub fn joint_skel_to_local(
    skel: &[gf::Mat4d],
    topology: &Topology,
    root_inverse: Option<gf::Mat4d>,
) -> Option<Vec<gf::Mat4d>> {
    if skel.len() != topology.joint_count() {
        return None;
    }
    // TODO(perf): only a joint with children needs its inverse; the inverses
    // are independent of each other (TODO(rayon)).
    let inverse = inverse_transforms(skel);
    skel.iter()
        .enumerate()
        .map(|(i, &transform)| match topology.parent(i) {
            Some(parent) if parent < i => Some(transform * inverse[parent]),
            Some(_) => None,
            None => Some(root_inverse.map_or(transform, |root| transform * root)),
        })
        .collect()
}

/// Compute per-joint skinning transforms from current joint poses and
/// the bind-pose inverses.
///
/// Per Pixar's `UsdSkelSkeletonQuery::ComputeSkinningTransforms`:
/// `skinningTransform = inverse(bindTransform) · jointSkelTransform`, with
/// `joint` in skeleton space. `None` unless the two arrays have the same
/// length.
pub fn skinning_transforms(joint: &[gf::Mat4d], inverse_bind: &[gf::Mat4d]) -> Option<Vec<gf::Mat4d>> {
    (joint.len() == inverse_bind.len()).then(|| joint.iter().zip(inverse_bind).map(|(j, b)| *b * *j).collect())
}

/// The inverse of each of `xforms`, as [`gf::Mat4d::inverse_or_max`] answers
/// it (C++ `GfMatrix4d::GetInverse`): the inverse bind transforms
/// [`skinning_transforms`] takes, or the inverse rest transforms.
pub fn inverse_transforms(xforms: &[gf::Mat4d]) -> Vec<gf::Mat4d> {
    xforms.iter().map(|xform| xform.inverse_or_max()).collect()
}

/// The box around the joints' pivots, the translations of `xforms`, each
/// carried through `root` where one is given and grown by `pad` on every side
/// (C++ `UsdSkelComputeJointsExtent`). `None` for no joints, where C++ writes
/// an empty range grown by `pad`.
pub fn joints_extent(xforms: &[gf::Mat4d], pad: f32, root: Option<gf::Mat4d>) -> Option<Extent> {
    let mut pivots = xforms.iter().map(|xform| {
        let pivot = xform.extract_translation().to_f32();
        root.map_or(pivot, |root| root.transform_affine(pivot.into()).to_f32())
    });
    let first = pivots.next()?;
    let (min, max) = pivots.fold((first, first), |(min, max), pivot| (min.min(pivot), max.max(pivot)));
    let pad = gf::vec3f(pad, pad, pad);
    Some([min - pad, max + pad])
}

/// The translation, rotation and scale `xform` composes from, in the
/// `scale · rotation · translation` order [`gf::Mat4d::from_trs`] builds
/// (C++ `UsdSkelDecomposeTransform`). A negative scale is kept, so the
/// rotation stays right-handed. The scale stays at `f32` precision, where C++
/// rounds it to a `GfVec3h`, by the crate's convention of widening `half3`.
/// `None` for a singular matrix, or one whose rotation does not
/// orthonormalize.
pub fn decompose_transform(xform: gf::Mat4d) -> Option<(gf::Vec3f, gf::Quatf, gf::Vec3f)> {
    let factors = xform.factor(gf::Mat4d::FACTOR_EPSILON);
    if factors.singular {
        return None;
    }
    let mut rotation = factors.rotation;
    if !rotation.orthonormalize() {
        return None;
    }
    Some((
        factors.translation.to_f32(),
        rotation.extract_rotation_quat().to_f32(),
        factors.scale.to_f32(),
    ))
}

/// [`decompose_transform`] over each of `xforms` (C++
/// `UsdSkelDecomposeTransforms`). `None` when any matrix does not decompose.
pub fn decompose_transforms(xforms: &[gf::Mat4d]) -> Option<JointTransformComponents> {
    let mut components = (
        Vec::with_capacity(xforms.len()),
        Vec::with_capacity(xforms.len()),
        Vec::with_capacity(xforms.len()),
    );
    for &xform in xforms {
        let (translation, rotation, scale) = decompose_transform(xform)?;
        components.0.push(translation);
        components.1.push(rotation);
        components.2.push(scale);
    }
    Some(components)
}

/// One transform per joint, each [`gf::Mat4d::from_trs`] of the joint's
/// translation, rotation and scale (C++ `UsdSkelMakeTransforms`). `None`
/// unless the three arrays have the same length.
pub fn make_transforms(
    translations: &[gf::Vec3f],
    rotations: &[gf::Quatf],
    scales: &[gf::Vec3f],
) -> Option<Vec<gf::Mat4d>> {
    if translations.len() != rotations.len() || translations.len() != scales.len() {
        return None;
    }
    Some(
        translations
            .iter()
            .zip(rotations)
            .zip(scales)
            .map(|((&t, &r), &s)| gf::Mat4d::from_trs(t, r, s))
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::skel::NO_PARENT;

    fn translation(x: f64, y: f64, z: f64) -> gf::Mat4d {
        gf::Mat4d::translation([x, y, z])
    }

    #[test]
    fn joint_local_to_skel_chains_translations() {
        let topo = Topology::from_parents(vec![NO_PARENT, 0]);
        let local = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let skel = joint_local_to_skel_space(&local, &topo, None).expect("ordered joints");
        assert_eq!(skel[0][(3, 0)], 1.0);
        assert_eq!(skel[1][(3, 0)], 1.0);
        assert_eq!(skel[1][(3, 1)], 1.0);

        // A root transform carries every joint.
        let skel = joint_local_to_skel_space(&local, &topo, Some(translation(0.0, 0.0, 5.0))).expect("ordered");
        assert_eq!(skel[1], translation(1.0, 1.0, 5.0));
    }

    #[test]
    fn misordered_parent_rejected() {
        let topo = Topology::from_parents(vec![1, NO_PARENT]);
        assert!(joint_local_to_skel_space(&[gf::Mat4d::IDENTITY; 2], &topo, None).is_none());
        assert!(joint_local_to_skel_space(&[gf::Mat4d::IDENTITY], &topo, None).is_none());
        assert!(joint_skel_to_local(&[gf::Mat4d::IDENTITY; 2], &topo, None).is_none());
    }

    #[test]
    fn skel_to_local_roundtrip() {
        let topo = Topology::from_parents(vec![NO_PARENT, 0, 1, NO_PARENT]);
        let local = vec![
            gf::Mat4d::rotation_z(0.5) * translation(1.0, 2.0, 3.0),
            gf::Mat4d::scale([2.0, 1.0, 1.0]) * translation(0.0, 1.0, 0.0),
            gf::Mat4d::rotation_x(1.0),
            translation(4.0, 0.0, 0.0),
        ];
        let root = translation(0.0, 0.0, 7.0);
        let skel = joint_local_to_skel_space(&local, &topo, Some(root)).expect("ordered");
        let back = joint_skel_to_local(&skel, &topo, root.inverse()).expect("ordered");
        for (a, b) in back.iter().zip(&local) {
            assert!(a.is_close(*b, 1e-4), "{a:?} != {b:?}");
        }
    }

    #[test]
    fn skinning_transform_is_inverse_bind_times_current() {
        let bind = vec![translation(1.0, 0.0, 0.0)];
        let inv_bind = inverse_transforms(&bind);
        let current = vec![translation(1.0, 2.0, 0.0)];
        let skin = skinning_transforms(&current, &inv_bind).expect("one inverse per joint");
        let p = skin[0].transform_affine(gf::vec3d(1.0, 0.0, 0.0));
        assert_eq!(p, gf::vec3d(1.0, 2.0, 0.0));
    }

    #[test]
    fn joints_extent_bounds_pivots() {
        let xforms = [translation(1.0, -2.0, 0.0), translation(-1.0, 3.0, 0.5)];
        assert_eq!(
            joints_extent(&xforms, 0.5, None),
            Some([gf::vec3f(-1.5, -2.5, -0.5), gf::vec3f(1.5, 3.5, 1.0)])
        );
        assert_eq!(
            joints_extent(&xforms, 0.0, Some(translation(10.0, 0.0, 0.0))),
            Some([gf::vec3f(9.0, -2.0, 0.0), gf::vec3f(11.0, 3.0, 0.5)])
        );
        assert_eq!(joints_extent(&[], 1.0, None), None);
    }

    #[test]
    fn transforms_decompose_and_rebuild() {
        // Rotations about each axis, with scales that flip handedness.
        let translations = [gf::vec3f(10.0, -20.0, 30.0), gf::vec3f(-5.0, 0.5, 2.0)];
        let rotations = [
            gf::Mat4d::rotation_x(0.3) * gf::Mat4d::rotation_y(-1.2),
            gf::Mat4d::rotation_z(2.5) * gf::Mat4d::rotation_x(-0.7),
        ]
        .map(|rotation| rotation.extract_rotation_quat().to_f32());
        let scales = [gf::vec3f(1.0, -1.0, 1.0), gf::vec3f(-1.0, -1.0, -1.0)];
        let xforms = make_transforms(&translations, &rotations, &scales).expect("one of each per joint");

        // The components can differ from the originals, but rebuild the
        // same matrices.
        let (t, r, s) = decompose_transforms(&xforms).expect("non-singular");
        for (a, b) in t.iter().zip(&translations) {
            assert!((*a - *b).length() < 1e-4);
        }
        let rebuilt = make_transforms(&t, &r, &s).expect("one of each per joint");
        for (a, b) in rebuilt.iter().zip(&xforms) {
            assert!(a.is_close(*b, 1e-4), "{a:?} != {b:?}");
        }

        // Decomposing singular matrices fails.
        assert!(decompose_transform(gf::Mat4d([0.0; 16])).is_none());
        assert!(decompose_transforms(&[gf::Mat4d::IDENTITY, gf::Mat4d([0.0; 16])]).is_none());
        assert!(make_transforms(&translations, &rotations[..1], &scales).is_none());
    }
}
