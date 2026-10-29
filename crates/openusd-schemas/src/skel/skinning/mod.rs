//! The skinning math (C++ `usdSkel/utils.h`): linear blend and
//! dual-quaternion skinning of points, normals and rigid transforms,
//! blend-shape application, and the joint-transform and joint-influence
//! utilities they consume, and the [`Pose`] a skinning query skins through.
//! Every function takes pre-resolved arrays and reads nothing from a stage.

mod dual_quat;
mod influences;
mod pose;
mod transforms;

use std::ops::{AddAssign, Mul, Range};

use openusd::gf;

pub(crate) use influences::has_shape;
pub use influences::{
    Influences, interleave_influences, normalize_weights, resize_influences, resize_weights, sort_influences,
};
pub use pose::Pose;
pub(crate) use pose::PrimPose;
pub use transforms::{
    JointTransformComponents, decompose_transform, decompose_transforms, inverse_transforms, joint_local_to_skel_space,
    joint_skel_to_local, joints_extent, make_transforms, skinning_transforms,
};

use super::SkinningMethod;

/// Skin `points` by `method` (C++ `UsdSkelSkinPoints`): [`skin_points_lbs`]
/// for `classicLinear`, and dual-quaternion skinning for `dualQuaternion`.
/// `None` under the conditions of [`skin_points_lbs`].
///
/// Under dual-quaternion skinning, each point's rotation and translation are
/// the weighted sum of its joints' dual quaternions, each flipped onto the
/// hemisphere of the most-weighted joint's, normalized. Where a skinning
/// transform scales or shears, the point first goes through its joints'
/// leftover scales, blended linearly. A skinning transform with no inverse
/// contributes a zero dual quaternion and no scale, as in C++.
pub fn skin_points(
    method: SkinningMethod,
    points: &[gf::Vec3f],
    influences: Influences<'_>,
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    PrimPose::new(&Pose::from(skinning_xforms.to_vec()), None)?.skin_points(
        method,
        points,
        influences,
        num_influences,
        geom_bind_transform,
    )
}

/// Skin `normals` by `method` (C++ `UsdSkelSkinNormals`): [`skin_normals_lbs`]
/// for `classicLinear`, and dual-quaternion skinning for `dualQuaternion`.
/// `None` under the conditions of [`skin_normals_lbs`].
///
/// Under dual-quaternion skinning, each normal goes through the
/// inverse-transpose of the upper-left 3×3 of `geom_bind_transform`, then
/// through the leftover scales of its joints' inverse-transposes, blended
/// linearly, and is rotated by the weighted sum of their rotations, aligned
/// and normalized as [`skin_points`] aligns them. Each result is
/// renormalised.
pub fn skin_normals(
    method: SkinningMethod,
    normals: &[gf::Vec3f],
    influences: Influences<'_>,
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    PrimPose::new(&Pose::from(skinning_xforms.to_vec()), None)?.skin_normals(
        method,
        normals,
        influences,
        num_influences,
        geom_bind_transform,
    )
}

/// Skin face-varying `normals` by `method` (C++
/// `UsdSkelSkinFaceVaryingNormals`): [`skin_face_varying_normals_lbs`] for
/// `classicLinear`, and for `dualQuaternion` the dual-quaternion skinning
/// [`skin_normals`] describes. The point each normal reads, and the
/// conditions for `None`, are those of [`skin_face_varying_normals_lbs`].
pub fn skin_face_varying_normals(
    method: SkinningMethod,
    normals: &[gf::Vec3f],
    face_vertex_indices: &[i32],
    influences: Influences<'_>,
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    PrimPose::new(&Pose::from(skinning_xforms.to_vec()), None)?.skin_face_varying_normals(
        method,
        normals,
        face_vertex_indices,
        influences,
        num_influences,
        geom_bind_transform,
    )
}

/// Skin a rigid transform by `method` (C++ `UsdSkelSkinTransform`):
/// [`skin_transform_lbs`] for `classicLinear`, and dual-quaternion skinning
/// for `dualQuaternion`. `None` under the conditions of
/// [`skin_transform_lbs`].
///
/// Under dual-quaternion skinning, a single influence of weight one gives
/// `geom_bind_transform` times that joint's skinning transform, and otherwise
/// the frame [`skin_transform_lbs`] rebuilds the transform from is skinned as
/// [`skin_points`] skins a point, all by one blended dual quaternion.
pub fn skin_transform(
    method: SkinningMethod,
    influences: Influences<'_>,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<gf::Mat4d> {
    PrimPose::new(&Pose::from(skinning_xforms.to_vec()), None)?.skin_transform(method, influences, geom_bind_transform)
}

/// Linear blend skinning of a point cloud — the canonical UsdSkel
/// algorithm from the spec's "Skinning a Point" section (C++
/// `UsdSkelSkinPointsLBS`):
///
/// ```text
/// skelSpacePoint = geomBindTransform.Transform(localSpacePoint)
/// p = (0, 0, 0)
/// for (jointIndex, jointWeight) in jointInfluencesForPoint:
///     p += skinningTransforms[jointIndex].TransformAffine(skelSpacePoint) * jointWeight
/// ```
///
/// `points` are in the mesh's local space at bind time.
/// `influences` are the flattened per-point influence lists, split as
/// `BindingAPI` holds them or interleaved by [`interleave_influences`];
/// `num_influences` is the
/// per-vertex stride (`elementSize` on the primvar).
/// `skinning_xforms` must be in the *mesh-effective* joint order
/// (apply [`super::AnimMapper`] first if the mesh uses `skel:joints`
/// to subset/reorder the skeleton's joints).
///
/// Returns one deformed point per input point. `None` when `num_influences`
/// is zero, split influences differ in length, the influences hold other
/// than `num_influences` entries per point, or an index names no skinning
/// transform. C++ accepts zero influences and skins every point to the
/// origin.
pub fn skin_points_lbs(
    points: &[gf::Vec3f],
    influences: Influences<'_>,
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    if !has_vertex_influences(points.len(), influences, num_influences, skinning_xforms.len()) {
        return None;
    }
    Some(skin_points_with(
        points,
        influences,
        num_influences,
        geom_bind_transform,
        |point, run| blend(run, skinning_xforms, |xform| xform.transform_affine(point)),
    ))
}

/// Linear blend skinning of normals. Same per-vertex influence layout
/// as [`skin_points_lbs`], but each normal goes through the
/// inverse-transpose of the upper-left 3×3 of `geom_bind_transform` and of
/// each skinning transform, and each result is renormalised (C++
/// `UsdSkelSkinningQuery::ComputeSkinnedNormals`). `None` under the same
/// conditions as [`skin_points_lbs`].
pub fn skin_normals_lbs(
    normals: &[gf::Vec3f],
    influences: Influences<'_>,
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    skin_normals_lbs_with(
        normals,
        influences,
        num_influences,
        geom_bind_transform,
        &normal_transforms(skinning_xforms),
    )
}

/// [`skin_normals_lbs`] over face-varying `normals`, each taking the
/// influences of the point `face_vertex_indices` names for it (C++
/// `UsdSkelSkinFaceVaryingNormalsLBS`). A face-vertex index that names no
/// point reads the influences of point 0, as C++ does. `None` when split
/// influences differ in length, the influences do not split into runs of
/// `num_influences`, `face_vertex_indices` holds other than one index per
/// normal, there are normals but no points, or a joint index of a point some
/// normal reads names no skinning transform. As in C++, the influences of a
/// point no face vertex names are not checked. C++ checks that split
/// influences divide into runs and skins interleaved ones that do not.
pub fn skin_face_varying_normals_lbs(
    normals: &[gf::Vec3f],
    face_vertex_indices: &[i32],
    influences: Influences<'_>,
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    skin_face_varying_normals_lbs_with(
        normals,
        face_vertex_indices,
        influences,
        num_influences,
        geom_bind_transform,
        &normal_transforms(skinning_xforms),
    )
}

/// [`skin_face_varying_normals_lbs`] through `normal_xforms`, the
/// [`normal_transform`] of each skinning transform.
fn skin_face_varying_normals_lbs_with(
    normals: &[gf::Vec3f],
    face_vertex_indices: &[i32],
    influences: Influences<'_>,
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    normal_xforms: &[gf::Mat3d],
) -> Option<Vec<gf::Vec3f>> {
    let point_of = face_varying_points(
        normals.len(),
        face_vertex_indices,
        influences,
        num_influences,
        normal_xforms.len(),
    )?;
    Some(skin_normals_with(
        normals,
        point_of,
        influences,
        num_influences,
        geom_bind_transform,
        |normal, run| blend(run, normal_xforms, |xform| xform.transform(normal)),
    ))
}

/// Linear blend skinning of one rigid transform (C++
/// `UsdSkelSkinTransformLBS`). A single influence of weight one gives
/// `geom_bind_transform` times that joint's skinning transform. Otherwise
/// the pivot of `geom_bind_transform` and the tips of its three basis rows
/// are skinned as points, and the result is rebuilt from them: the skinned
/// pivot is the translation, and each skinned tip less the pivot a row.
/// `None` when split influences differ in length or an index names no
/// skinning transform.
pub fn skin_transform_lbs(
    influences: Influences<'_>,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<gf::Mat4d> {
    if !names_joints(influences, skinning_xforms.len()) {
        return None;
    }
    if let Some(xform) = single_joint(influences, geom_bind_transform, skinning_xforms) {
        return Some(xform);
    }
    Some(skin_frame(geom_bind_transform, |point| {
        blend(influences, skinning_xforms, |xform| xform.transform_affine(point))
    }))
}

/// One blend-shape contribution ready to apply to mesh points.
/// `point_indices` may be empty to indicate a dense shape (entry `i`
/// affects vertex `i`).
#[derive(Debug, Clone)]
pub struct BlendShapeWeighted<'a> {
    /// The weight `offsets` are scaled by, as
    /// [`sub_shape_weights`] answers it for one sub-shape.
    pub weight: f32,
    /// Per-affected-vertex position offsets, parallel to
    /// `point_indices` when sparse.
    pub offsets: &'a [gf::Vec3f],
    /// Optional sparse-vertex remap. Empty = dense.
    pub point_indices: &'a [i32],
}

/// Apply a stack of blend shapes to a mesh's points (C++
/// `UsdSkelApplyBlendShape`, once per shape).
///
/// Per the canonical UsdSkel pipeline blend shapes are evaluated
/// *before* skinning; the deformed mesh is then skinned through
/// [`skin_points_lbs`]. This helper does only the morph step:
///
/// `p_morphed[i] = p[i] + Σ_s (weight_s * offset_s[i])`
///
/// A shape whose weight is within `1e-6` of zero is skipped. `None` when a
/// dense shape holds other than one offset per point, a sparse shape holds
/// other than one offset per point index, or a point index names no point.
pub fn apply_blend_shapes(points: &[gf::Vec3f], shapes: &[BlendShapeWeighted<'_>]) -> Option<Vec<gf::Vec3f>> {
    let mut out = points.to_vec();
    for shape in shapes {
        if is_close(shape.weight, 0.0) {
            continue;
        }
        if shape.point_indices.is_empty() {
            if shape.offsets.len() != out.len() {
                return None;
            }
            for (point, &offset) in out.iter_mut().zip(shape.offsets) {
                *point += offset * shape.weight;
            }
        } else {
            if shape.offsets.len() != shape.point_indices.len() {
                return None;
            }
            for (&index, &offset) in shape.point_indices.iter().zip(shape.offsets) {
                *out.get_mut(usize::try_from(index).ok()?)? += offset * shape.weight;
            }
        }
    }
    Some(out)
}

/// One of the shapes a blend shape interpolates between: its primary shape
/// at weight 1, or one of its inbetweens.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubShape {
    /// The blend shape's own `offsets`.
    Primary,
    /// The inbetween at this index of the weights given to
    /// [`sub_shape_weights`].
    Inbetween(usize),
}

/// The sub-shapes a blend shape driven at `weight` applies, each with the
/// weight to scale its offsets by (C++
/// `UsdSkelBlendShapeQuery::ComputeSubShapeWeights`, for one blend shape).
/// `inbetween_weights` holds the `weight` of each of the blend shape's
/// inbetweens.
///
/// The primary shape sits at weight 1 and an implicit rest shape at weight 0.
/// Without inbetweens the primary shape takes `weight` as it is. Otherwise
/// `weight` interpolates linearly between the two nearest sub-shapes by
/// weight, and extrapolates from the two nearest ones beyond either end.
/// An inbetween whose weight lies within `1e-6` of 0 or 1 is skipped, and so
/// is a sub-shape whose share is within `1e-6` of zero.
pub fn sub_shape_weights(weight: f32, inbetween_weights: &[f32]) -> Vec<(SubShape, f32)> {
    let inbetweens = inbetween_weights
        .iter()
        .enumerate()
        .map(|(index, &weight)| (SubShape::Inbetween(index), weight));
    interpolate_run(weight, &sub_shape_run(SubShape::Primary, inbetweens))
}

/// One blend shape's sub-shapes sorted by weight, as C++
/// `UsdSkelBlendShapeQuery` lays them out: `primary` at weight 1, the rest
/// shape (`None`) at weight 0, and each of `inbetweens` whose weight does not
/// lie within `1e-6` of 0 or 1.
pub(crate) fn sub_shape_run<T>(primary: T, inbetweens: impl IntoIterator<Item = (T, f32)>) -> Vec<(Option<T>, f32)> {
    let mut run = vec![(Some(primary), 1.0), (None, 0.0)];
    run.extend(
        inbetweens
            .into_iter()
            .filter(|&(_, weight)| !is_close(weight, 0.0) && !is_close(weight, 1.0))
            .map(|(shape, weight)| (Some(shape), weight)),
    );
    run.sort_by(|a, b| a.1.total_cmp(&b.1));
    run
}

/// The sub-shapes of one blend shape that `weight` applies, each with its
/// share (the per-shape step of C++
/// `UsdSkelBlendShapeQuery::ComputeSubShapeWeights`). `run` holds the blend
/// shape's sub-shapes sorted by weight, `None` standing for the rest shape.
/// A run of fewer than three sub-shapes applies `weight` as it is to its
/// sub-shape other than the rest shape, and an empty run applies nothing.
pub(crate) fn interpolate_run<T: Copy>(weight: f32, run: &[(Option<T>, f32)]) -> Vec<(T, f32)> {
    if run.len() < 3 {
        return run
            .iter()
            .filter_map(|&(shape, _)| shape)
            .map(|shape| (shape, weight))
            .collect();
    }
    let (lower, upper) = match run.partition_point(|&(_, w)| w <= weight) {
        0 => (0, 1),
        end if end == run.len() => (end - 2, end - 1),
        upper => (upper - 1, upper),
    };
    let ((lower_shape, lower_weight), (upper_shape, upper_weight)) = (run[lower], run[upper]);
    let span = upper_weight - lower_weight;
    if span <= EPS {
        return Vec::new();
    }
    let alpha = (weight - lower_weight) / span;
    let mut out = Vec::with_capacity(2);
    if let Some(shape) = lower_shape
        && !is_close(alpha, 1.0)
    {
        out.push((shape, 1.0 - alpha));
    }
    if let Some(shape) = upper_shape
        && !is_close(alpha, 0.0)
    {
        out.push((shape, alpha));
    }
    out
}

/// One inbetween shape — its authored weight and its offsets.
/// Inputs to [`resolve_blend_shape_offsets`].
pub type InbetweenRef<'a> = (f32, &'a [gf::Vec3f]);

/// The offsets a single blend shape (primary + optional inbetweens) applies
/// at `weight`: the offsets of each sub-shape [`sub_shape_weights`] picks,
/// scaled by its share and summed. A sub-shape with no offsets contributes
/// nothing; `None` when another holds a different number of offsets than
/// `primary`.
pub fn resolve_blend_shape_offsets(
    weight: f32,
    inbetweens: &[InbetweenRef<'_>],
    primary: &[gf::Vec3f],
) -> Option<Vec<gf::Vec3f>> {
    let inbetween_weights: Vec<f32> = inbetweens.iter().map(|&(weight, _)| weight).collect();
    let mut out = vec![gf::Vec3f::default(); primary.len()];
    for (shape, share) in sub_shape_weights(weight, &inbetween_weights) {
        let offsets = match shape {
            SubShape::Primary => primary,
            SubShape::Inbetween(index) => inbetweens[index].1,
        };
        if offsets.is_empty() {
            continue;
        }
        if offsets.len() != out.len() {
            return None;
        }
        for (total, &offset) in out.iter_mut().zip(offsets) {
            *total += offset * share;
        }
    }
    Some(out)
}

/// Linear blend skinning of normals through `normal_xforms`, the
/// [`normal_transform`] of each skinning transform, as [`skin_normals_lbs`]
/// describes it.
fn skin_normals_lbs_with(
    normals: &[gf::Vec3f],
    influences: Influences<'_>,
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    normal_xforms: &[gf::Mat3d],
) -> Option<Vec<gf::Vec3f>> {
    if !has_vertex_influences(normals.len(), influences, num_influences, normal_xforms.len()) {
        return None;
    }
    Some(skin_normals_with(
        normals,
        |normal| normal,
        influences,
        num_influences,
        geom_bind_transform,
        |normal, run| blend(run, normal_xforms, |xform| xform.transform(normal)),
    ))
}

/// `true` when `influences` are whole, hold `num_influences`, a positive
/// count, for each of `count` vertices, and name only `joints` joints, as
/// [`names_joints`] checks them.
fn has_vertex_influences(count: usize, influences: Influences<'_>, num_influences: usize, joints: usize) -> bool {
    num_influences != 0 && influences.len() == Some(count * num_influences) && names_joints(influences, joints)
}

/// The point each of `normals` face-varying normals reads its influences
/// from, by the normal's index: the one `face_vertex_indices` names, or point
/// 0 for an index that names no point, as C++ reads it. `None` when split
/// `influences` differ in length, the influences do not split into runs of
/// `num_influences`, `face_vertex_indices` holds other than one index per
/// normal, there are normals but no points, or a joint index of a point some
/// normal reads names none of `joints` joints.
fn face_varying_points(
    normals: usize,
    face_vertex_indices: &[i32],
    influences: Influences<'_>,
    num_influences: usize,
    joints: usize,
) -> Option<impl Fn(usize) -> usize> {
    let len = influences.len()?;
    if !has_shape(len, num_influences) || face_vertex_indices.len() != normals {
        return None;
    }
    let num_points = len / num_influences;
    if num_points == 0 && normals != 0 {
        return None;
    }
    let point_of = move |normal: usize| {
        usize::try_from(face_vertex_indices[normal])
            .ok()
            .filter(|&point| point < num_points)
            .unwrap_or(0)
    };
    (0..normals)
        .all(|normal| names_joints(influences.run(influence_run(point_of(normal), num_influences)), joints))
        .then_some(point_of)
}

/// Skin each point by `skin`, which takes the point carried into skeleton
/// space by `geom_bind_transform` and the point's run of influences, after
/// the checks each caller makes on the array shapes and the joint indices.
fn skin_points_with(
    points: &[gf::Vec3f],
    influences: Influences<'_>,
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skin: impl Fn(gf::Vec3d, Influences<'_>) -> gf::Vec3d,
) -> Vec<gf::Vec3f> {
    // TODO(rayon): each point is skinned from its own influence run and the
    // shared read-only transforms.
    points
        .iter()
        .enumerate()
        .map(|(point, &p)| {
            let run = influences.run(influence_run(point, num_influences));
            skin(geom_bind_transform.transform(p.into()), run).to_f32()
        })
        .collect()
}

/// Skin each normal by `skin`, which takes the normal carried into skeleton
/// space by the inverse-transpose of `geom_bind_transform` and the run of
/// influences of the point `point_of` names for it, and normalize the result.
/// The checks each caller makes on the array shapes and the joint indices
/// come first.
fn skin_normals_with(
    normals: &[gf::Vec3f],
    point_of: impl Fn(usize) -> usize,
    influences: Influences<'_>,
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skin: impl Fn(gf::Vec3d, Influences<'_>) -> gf::Vec3d,
) -> Vec<gf::Vec3f> {
    let geom_bind_transform = normal_transform(geom_bind_transform);
    // TODO(rayon): each normal is skinned from its own influence run and the
    // shared read-only transforms.
    normals
        .iter()
        .enumerate()
        .map(|(normal, &n)| {
            let run = influences.run(influence_run(point_of(normal), num_influences));
            skin(geom_bind_transform.transform(n.into()), run).normalize().to_f32()
        })
        .collect()
}

/// `geom_bind_transform` times the skinning transform of a lone influence of
/// weight one, which C++ skins without a frame. `None` for any other
/// influences.
fn single_joint(
    influences: Influences<'_>,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<gf::Mat4d> {
    let mut iter = influences.iter();
    match (iter.next(), iter.next()) {
        (Some((index, weight)), None) if is_close(weight, 1.0) => {
            Some(geom_bind_transform * skinning_xforms[index as usize])
        }
        _ => None,
    }
}

/// The transform rebuilt from the pivot of `geom_bind_transform` and the tips
/// of its three basis rows, each skinned as a point by `skin`: the skinned
/// pivot is the translation, and each skinned tip less the pivot a row.
fn skin_frame(geom_bind_transform: gf::Mat4d, skin: impl Fn(gf::Vec3d) -> gf::Vec3d) -> gf::Mat4d {
    // The basis tips and the pivot, each the image of a unit point.
    let [i, j, k, pivot] = [
        gf::Vec3d::X_AXIS,
        gf::Vec3d::Y_AXIS,
        gf::Vec3d::Z_AXIS,
        gf::Vec3d::default(),
    ]
    .map(|point| skin(geom_bind_transform.transform_affine(point)));
    let mut out = gf::Mat4d::translation(pivot);
    for (row, tip) in [i, j, k].into_iter().enumerate() {
        let basis = tip - pivot;
        out[(row, 0)] = basis.x;
        out[(row, 1)] = basis.y;
        out[(row, 2)] = basis.z;
    }
    out
}

/// The range of the influences of `point` in an array of `num_influences`
/// influences per point.
fn influence_run(point: usize, num_influences: usize) -> Range<usize> {
    point * num_influences..(point + 1) * num_influences
}

/// The sum of `apply` over the joints `influences` name, each scaled by its
/// weight. A zero weight is skipped. Every index must name one of `joints`
/// ([`names_joints`]).
fn blend<J, T>(influences: Influences<'_>, joints: &[J], apply: impl Fn(&J) -> T) -> T
where
    T: Default + AddAssign + Mul<f64, Output = T>,
{
    influences.iter().fold(T::default(), |mut sum, (index, weight)| {
        if weight != 0.0 {
            sum += apply(&joints[index as usize]) * f64::from(weight);
        }
        sum
    })
}

/// `true` when split `influences` agree in length and every index,
/// whatever its weight, names one of `joints` joints, as C++ requires of
/// each influence.
fn names_joints(influences: Influences<'_>, joints: usize) -> bool {
    influences.len().is_some()
        && influences
            .iter()
            .all(|(index, _)| usize::try_from(index).is_ok_and(|index| index < joints))
}

/// The transform a normal takes through `transform`: the inverse-transpose of
/// its upper-left 3×3 (C++ `ExtractRotationMatrix().GetInverse()
/// .GetTranspose()`). A singular 3×3 inverts as
/// [`gf::Mat3d::inverse_or_max`] does.
pub(crate) fn normal_transform(transform: gf::Mat4d) -> gf::Mat3d {
    transform.extract_rotation_matrix().inverse_or_max().transpose()
}

/// The [`normal_transform`] of each of `skinning_xforms`.
fn normal_transforms(skinning_xforms: &[gf::Mat4d]) -> Vec<gf::Mat3d> {
    skinning_xforms.iter().copied().map(normal_transform).collect()
}

/// The tolerance C++ `UsdSkelBlendShapeQuery` and `UsdSkelApplyBlendShape`
/// compare blend-shape weights with.
const EPS: f32 = 1e-6;

/// `true` when `a` lies within [`EPS`] of `b` (C++ `GfIsClose`).
pub(crate) fn is_close(a: f32, b: f32) -> bool {
    (a - b).abs() < EPS
}

#[cfg(test)]
mod tests {
    use std::f32::consts::FRAC_1_SQRT_2;
    use std::f64::consts::FRAC_PI_2;

    use super::*;

    fn translation(x: f64, y: f64, z: f64) -> gf::Mat4d {
        gf::Mat4d::translation([x, y, z])
    }

    /// Interleaved influences skin as the split arrays they interleave.
    #[test]
    fn interleaved_matches_split() {
        let skin = [translation(1.0, 0.0, 0.0), gf::Mat4d::rotation_z(FRAC_PI_2)];
        let points = [gf::vec3f(1.0, 0.0, 0.0), gf::vec3f(0.0, 2.0, 1.0)];
        let (indices, weights) = ([0, 1, 1, 0], [0.25, 0.75, 1.0, 0.0]);
        let split = Influences::Split(&indices, &weights);
        let pairs = interleave_influences(&indices, &weights).expect("same lengths");
        let interleaved = Influences::Interleaved(&pairs);
        let bind = translation(0.0, 0.0, 1.0);
        let normals = [points[0]; 3];
        let face_vertex_indices = [1, 0, 1];
        for method in [SkinningMethod::ClassicLinear, SkinningMethod::DualQuaternion] {
            let both = |skin: &dyn Fn(Influences<'_>) -> Option<Vec<gf::Vec3f>>| {
                let expected = skin(split).expect("valid split influences");
                assert_eq!(skin(interleaved), Some(expected));
            };
            both(&|influences| skin_points(method, &points, influences, 2, bind, &skin));
            both(&|influences| skin_normals(method, &points, influences, 2, bind, &skin));
            both(&|influences| {
                skin_face_varying_normals(method, &normals, &face_vertex_indices, influences, 2, bind, &skin)
            });
            let transform = skin_transform(method, Influences::Split(&indices[..2], &weights[..2]), bind, &skin)
                .expect("valid split influences");
            assert_eq!(
                skin_transform(method, Influences::Interleaved(&pairs[..2]), bind, &skin),
                Some(transform)
            );
        }
        // A NaN index names no joint.
        let nan = [gf::vec2f(f32::NAN, 1.0)];
        assert!(skin_transform_lbs(Influences::Interleaved(&nan), bind, &skin).is_none());
    }

    #[test]
    fn skin_points_with_single_full_weight_translates_mesh() {
        let skin = vec![translation(0.0, 1.0, 0.0)];
        let pts = vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(1.0, 0.0, 0.0)];
        let out = skin_points_lbs(
            &pts,
            Influences::Split(&[0, 0], &[1.0, 1.0]),
            1,
            gf::Mat4d::IDENTITY,
            &skin,
        );
        assert_eq!(out, Some(vec![gf::vec3f(0.0, 1.0, 0.0), gf::vec3f(1.0, 1.0, 0.0)]));
    }

    #[test]
    fn skin_points_blends_two_joints_50_50() {
        let skin = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let pts = vec![gf::vec3f(0.0, 0.0, 0.0)];
        let out = skin_points_lbs(
            &pts,
            Influences::Split(&[0, 1], &[0.5, 0.5]),
            2,
            gf::Mat4d::IDENTITY,
            &skin,
        );
        assert_eq!(out, Some(vec![gf::vec3f(0.5, 0.5, 0.0)]));
    }

    #[test]
    fn skin_points_rejects_bad_input() {
        let skin = [gf::Mat4d::IDENTITY];
        let pts = [gf::Vec3f::default(); 2];
        // Too few influences, mismatched weights, an index past the joints.
        assert!(skin_points_lbs(&pts, Influences::Split(&[0], &[1.0]), 1, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_points_lbs(&pts, Influences::Split(&[0, 0], &[1.0]), 1, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(
            skin_points_lbs(
                &pts,
                Influences::Split(&[0, 1], &[1.0, 1.0]),
                1,
                gf::Mat4d::IDENTITY,
                &skin
            )
            .is_none()
        );
        // A zero weight still has to name a joint.
        assert!(
            skin_points_lbs(
                &pts,
                Influences::Split(&[0, -1], &[1.0, 0.0]),
                1,
                gf::Mat4d::IDENTITY,
                &skin
            )
            .is_none()
        );
        // Zero influences per point skin nothing.
        assert!(skin_points_lbs(&pts, Influences::Split(&[], &[]), 0, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_normals_lbs(&pts, Influences::Split(&[], &[]), 0, gf::Mat4d::IDENTITY, &skin).is_none());
    }

    #[test]
    fn apply_blend_shape_dense_adds_offsets() {
        let pts = vec![gf::vec3f(1.0, 0.0, 0.0), gf::vec3f(0.0, 0.0, 0.0)];
        let shape = BlendShapeWeighted {
            weight: 0.5,
            offsets: &[gf::vec3f(0.0, 1.0, 0.0), gf::vec3f(0.0, 2.0, 0.0)],
            point_indices: &[],
        };
        let out = apply_blend_shapes(&pts, &[shape]);
        assert_eq!(out, Some(vec![gf::vec3f(1.0, 0.5, 0.0), gf::vec3f(0.0, 1.0, 0.0)]));
    }

    #[test]
    fn apply_blend_shape_sparse_remaps_via_indices() {
        let pts = vec![gf::Vec3f::default(); 4];
        let shape = BlendShapeWeighted {
            weight: 1.0,
            offsets: &[gf::vec3f(1.0, 0.0, 0.0), gf::vec3f(0.0, 0.0, 5.0)],
            point_indices: &[1, 3],
        };
        let out = apply_blend_shapes(&pts, &[shape]);
        assert_eq!(
            out,
            Some(vec![
                gf::Vec3f::default(),
                gf::vec3f(1.0, 0.0, 0.0),
                gf::Vec3f::default(),
                gf::vec3f(0.0, 0.0, 5.0),
            ])
        );
    }

    #[test]
    fn apply_blend_shape_rejects_mismatch() {
        let pts = vec![gf::Vec3f::default(); 2];
        let offsets = [gf::vec3f(0.0, 1.0, 0.0)];
        let dense = BlendShapeWeighted {
            weight: 1.0,
            offsets: &offsets,
            point_indices: &[],
        };
        assert!(apply_blend_shapes(&pts, &[dense]).is_none());
        let out_of_range = BlendShapeWeighted {
            weight: 1.0,
            offsets: &offsets,
            point_indices: &[2],
        };
        assert!(apply_blend_shapes(&pts, &[out_of_range]).is_none());
        // A zero weight applies nothing, and so checks nothing.
        let silent = BlendShapeWeighted {
            weight: 0.0,
            offsets: &offsets,
            point_indices: &[2],
        };
        assert_eq!(apply_blend_shapes(&pts, &[silent]), Some(pts));
    }

    #[test]
    fn sub_shapes_without_inbetweens() {
        assert_eq!(sub_shape_weights(1.5, &[]), vec![(SubShape::Primary, 1.5)]);
        assert_eq!(sub_shape_weights(-0.5, &[]), vec![(SubShape::Primary, -0.5)]);
    }

    #[test]
    fn sub_shapes_interpolate() {
        let inbetween = SubShape::Inbetween(0);
        assert_eq!(sub_shape_weights(0.25, &[0.5]), vec![(inbetween, 0.5)]);
        assert_eq!(sub_shape_weights(0.5, &[0.5]), vec![(inbetween, 1.0)]);
        assert_eq!(
            sub_shape_weights(0.75, &[0.5]),
            vec![(inbetween, 0.5), (SubShape::Primary, 0.5)]
        );
    }

    #[test]
    fn sub_shapes_extrapolate() {
        let inbetween = SubShape::Inbetween(0);
        // Past the primary shape, from the inbetween and primary pair.
        assert_eq!(
            sub_shape_weights(1.5, &[0.5]),
            vec![(inbetween, -1.0), (SubShape::Primary, 2.0)]
        );
        // Below the rest shape, from the rest and inbetween pair.
        assert_eq!(sub_shape_weights(-0.5, &[0.5]), vec![(inbetween, -1.0)]);
        // A negative inbetween sits below the rest shape.
        assert_eq!(sub_shape_weights(-0.5, &[-1.0]), vec![(inbetween, 0.5)]);
    }

    #[test]
    fn sub_shapes_skip_endpoint_inbetweens() {
        assert_eq!(sub_shape_weights(0.5, &[0.0, 1.0]), vec![(SubShape::Primary, 0.5)]);
    }

    #[test]
    fn resolve_blend_shape_offsets_interpolates_through_inbetween() {
        let inb_off = vec![gf::vec3f(0.0, 1.0, 0.0)];
        let prim = vec![gf::vec3f(0.0, 2.0, 0.0)];
        let inbetweens = [(0.5_f32, inb_off.as_slice())];

        let out = resolve_blend_shape_offsets(0.5, &inbetweens, &prim);
        assert_eq!(out, Some(vec![gf::vec3f(0.0, 1.0, 0.0)]));

        let out = resolve_blend_shape_offsets(0.75, &inbetweens, &prim);
        assert_eq!(out, Some(vec![gf::vec3f(0.0, 1.5, 0.0)]));

        // Past the primary shape the offsets keep growing.
        let out = resolve_blend_shape_offsets(1.5, &inbetweens, &prim);
        assert_eq!(out, Some(vec![gf::vec3f(0.0, 3.0, 0.0)]));
    }

    #[test]
    fn normals_take_inverse_transpose() {
        // A 45° normal on the plane x + y = 0, scaled 2× along x: the plane
        // becomes x/2 + y = 0, whose normal is (1, 2) normalised.
        let skin = [gf::Mat4d::scale([2.0, 1.0, 1.0])];
        let n = FRAC_1_SQRT_2;
        let out = skin_normals_lbs(
            &[gf::vec3f(n, n, 0.0)],
            Influences::Split(&[0], &[1.0]),
            1,
            gf::Mat4d::IDENTITY,
            &skin,
        )
        .expect("one influence per normal");
        let expected = gf::vec3d(1.0, 2.0, 0.0).normalize().to_f32();
        assert!((out[0] - expected).length() < 1e-6, "{:?}", out[0]);
        // Translation does not move a normal.
        let out = skin_normals_lbs(
            &[gf::vec3f(0.0, 1.0, 0.0)],
            Influences::Split(&[0], &[1.0]),
            1,
            gf::Mat4d::translation([5.0, 0.0, 0.0]),
            &[gf::Mat4d::translation([0.0, 3.0, 0.0])],
        );
        assert_eq!(out, Some(vec![gf::vec3f(0.0, 1.0, 0.0)]));
    }

    #[test]
    fn face_varying_normals() {
        // Two points, the second rotated a quarter turn about z; three
        // face-varying normals, the last naming no point and so reading
        // point 0.
        let skin = [gf::Mat4d::IDENTITY, gf::Mat4d::rotation_z(FRAC_PI_2)];
        let normals = [gf::vec3f(1.0, 0.0, 0.0); 3];
        let out = skin_face_varying_normals_lbs(
            &normals,
            &[0, 1, 7],
            Influences::Split(&[0, 1], &[1.0, 1.0]),
            1,
            gf::Mat4d::IDENTITY,
            &skin,
        )
        .expect("one face-vertex index per normal");
        assert!((out[0] - gf::vec3f(1.0, 0.0, 0.0)).length() < 1e-6);
        assert!((out[1] - gf::vec3f(0.0, 1.0, 0.0)).length() < 1e-6, "{:?}", out[1]);
        assert!((out[2] - gf::vec3f(1.0, 0.0, 0.0)).length() < 1e-6);
        assert!(
            skin_face_varying_normals_lbs(
                &normals,
                &[0, 1],
                Influences::Split(&[0, 1], &[1.0, 1.0]),
                1,
                gf::Mat4d::IDENTITY,
                &skin
            )
            .is_none()
        );
        // Normals with no points to read are rejected.
        assert!(
            skin_face_varying_normals_lbs(
                &normals[..1],
                &[0],
                Influences::Split(&[], &[]),
                1,
                gf::Mat4d::IDENTITY,
                &skin
            )
            .is_none()
        );
        // A stale joint index on a point no face vertex names is not read.
        let out = skin_face_varying_normals_lbs(
            &normals[..1],
            &[0],
            Influences::Split(&[0, 9], &[1.0, 1.0]),
            1,
            gf::Mat4d::IDENTITY,
            &skin,
        );
        assert!(out.is_some());
    }

    #[test]
    fn skin_transform_rebuilds_frame() {
        let skin = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let m = skin_transform_lbs(Influences::Split(&[0, 1], &[0.5, 0.5]), gf::Mat4d::IDENTITY, &skin)
            .expect("valid influences");
        assert_eq!(m, translation(0.5, 0.5, 0.0));

        // Weights summing to two scale the rebuilt rows, and the matrix stays
        // affine (C++ rebuilds from the skinned frame points).
        let m = skin_transform_lbs(Influences::Split(&[0, 1], &[1.0, 1.0]), gf::Mat4d::IDENTITY, &skin)
            .expect("valid influences");
        assert_eq!(m[(0, 0)], 2.0);
        assert_eq!(m[(3, 3)], 1.0);
        assert_eq!(m.extract_translation(), gf::vec3d(1.0, 1.0, 0.0));

        // One full-weight influence multiplies straight through.
        let bind = translation(0.0, 0.0, 3.0);
        assert_eq!(
            skin_transform_lbs(Influences::Split(&[1], &[1.0]), bind, &skin),
            Some(bind * translation(0.0, 1.0, 0.0))
        );
        assert!(skin_transform_lbs(Influences::Split(&[2], &[1.0]), bind, &skin).is_none());
        assert!(skin_transform_lbs(Influences::Split(&[0, 1], &[1.0]), bind, &skin).is_none());
    }
}
