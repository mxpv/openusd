//! The skinning math (C++ `usdSkel/utils.h`): linear blend skinning of
//! points, normals and rigid transforms, blend-shape application, and the
//! joint-transform and joint-influence utilities they consume. Every function
//! takes pre-resolved arrays and reads nothing from a stage.

mod influences;
mod transforms;

use openusd::gf;

pub(crate) use influences::has_shape;
pub use influences::{interleave_influences, normalize_weights, resize_influences, resize_weights, sort_influences};
pub use transforms::{
    JointTransformComponents, decompose_transform, decompose_transforms, inverse_bind_transforms,
    joint_local_to_skel_space, joint_skel_to_local, joints_extent, make_transforms, skinning_transforms,
};

use super::SkinningMethod;

/// Skin `points` by `method` (C++ `UsdSkelSkinPoints`): [`skin_points_lbs`]
/// for `classicLinear`, and `None` for `dualQuaternion`.
pub fn skin_points(
    method: SkinningMethod,
    points: &[gf::Vec3f],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    match method {
        SkinningMethod::ClassicLinear => skin_points_lbs(
            points,
            joint_indices,
            joint_weights,
            num_influences,
            geom_bind_transform,
            skinning_xforms,
        ),
        // TODO(dqs): port C++ `_SkinPointsDQS`.
        SkinningMethod::DualQuaternion => None,
    }
}

/// Skin `normals` by `method` (C++ `UsdSkelSkinNormals`): [`skin_normals_lbs`]
/// for `classicLinear`, and `None` for `dualQuaternion`.
pub fn skin_normals(
    method: SkinningMethod,
    normals: &[gf::Vec3f],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    match method {
        SkinningMethod::ClassicLinear => skin_normals_lbs(
            normals,
            joint_indices,
            joint_weights,
            num_influences,
            geom_bind_transform,
            skinning_xforms,
        ),
        // TODO(dqs): port C++ `_SkinNormalsDQS`.
        SkinningMethod::DualQuaternion => None,
    }
}

/// Skin face-varying `normals` by `method` (C++
/// `UsdSkelSkinFaceVaryingNormals`): [`skin_face_varying_normals_lbs`] for
/// `classicLinear`, and `None` for `dualQuaternion`.
#[allow(clippy::too_many_arguments)] // C++ `UsdSkelSkinFaceVaryingNormals`'s inputs, one per argument.
pub fn skin_face_varying_normals(
    method: SkinningMethod,
    normals: &[gf::Vec3f],
    face_vertex_indices: &[i32],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    match method {
        SkinningMethod::ClassicLinear => skin_face_varying_normals_lbs(
            normals,
            face_vertex_indices,
            joint_indices,
            joint_weights,
            num_influences,
            geom_bind_transform,
            skinning_xforms,
        ),
        // TODO(dqs): port C++ `_SkinNormalsDQS` over face-varying normals.
        SkinningMethod::DualQuaternion => None,
    }
}

/// Skin a rigid transform by `method` (C++ `UsdSkelSkinTransform`):
/// [`skin_transform_lbs`] for `classicLinear`, and `None` for
/// `dualQuaternion`.
pub fn skin_transform(
    method: SkinningMethod,
    joint_indices: &[i32],
    joint_weights: &[f32],
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<gf::Mat4d> {
    match method {
        SkinningMethod::ClassicLinear => {
            skin_transform_lbs(joint_indices, joint_weights, geom_bind_transform, skinning_xforms)
        }
        // TODO(dqs): port C++ `UsdSkel_SkinTransformDQS`.
        SkinningMethod::DualQuaternion => None,
    }
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
/// `joint_indices` / `joint_weights` are the flattened per-point
/// influence lists from `BindingAPI`; `num_influences` is the
/// per-vertex stride (`elementSize` on the primvar).
/// `skinning_xforms` must be in the *mesh-effective* joint order
/// (apply [`super::AnimMapper`] first if the mesh uses `skel:joints`
/// to subset/reorder the skeleton's joints).
///
/// Returns one deformed point per input point. `None` when `num_influences`
/// is zero, the index and weight arrays differ in length or hold other than
/// `num_influences` entries per point, or an index names no skinning
/// transform. C++ accepts zero influences and skins every point to the
/// origin.
pub fn skin_points_lbs(
    points: &[gf::Vec3f],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    if num_influences == 0
        || joint_indices.len() != joint_weights.len()
        || joint_indices.len() != points.len() * num_influences
        || !names_joints(joint_indices, skinning_xforms)
    {
        return None;
    }
    // TODO(rayon): each point is skinned from its own influence run and the
    // shared read-only transforms.
    let skinned = points.iter().enumerate().map(|(point, &p)| {
        let skel_p = geom_bind_transform.transform(p.into());
        let run = point * num_influences..(point + 1) * num_influences;
        blend(
            &joint_indices[run.clone()],
            &joint_weights[run],
            skinning_xforms,
            |xform| xform.transform_affine(skel_p),
        )
        .to_f32()
    });
    Some(skinned.collect())
}

/// Linear blend skinning of normals. Same per-vertex influence layout
/// as [`skin_points_lbs`], but each normal goes through the
/// inverse-transpose of the upper-left 3×3 of `geom_bind_transform` and of
/// each skinning transform, and each result is renormalised (C++
/// `UsdSkelSkinningQuery::ComputeSkinnedNormals`). `None` under the same
/// conditions as [`skin_points_lbs`].
pub fn skin_normals_lbs(
    normals: &[gf::Vec3f],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    if num_influences == 0
        || joint_indices.len() != joint_weights.len()
        || joint_indices.len() != normals.len() * num_influences
        || !names_joints(joint_indices, skinning_xforms)
    {
        return None;
    }
    Some(skin_normals_with(
        normals,
        |normal| normal,
        joint_indices,
        joint_weights,
        num_influences,
        geom_bind_transform,
        skinning_xforms,
    ))
}

/// [`skin_normals_lbs`] over face-varying `normals`, each taking the
/// influences of the point `face_vertex_indices` names for it (C++
/// `UsdSkelSkinFaceVaryingNormalsLBS`). A face-vertex index that names no
/// point reads the influences of point 0, as C++ does. `None` when the index
/// and weight arrays differ in length or do not split into runs of
/// `num_influences`, `face_vertex_indices` holds other than one index per
/// normal, there are normals but no points, or a joint index of a point some
/// normal reads names no skinning transform. As in C++, the influences of a
/// point no face vertex names are not checked.
pub fn skin_face_varying_normals_lbs(
    normals: &[gf::Vec3f],
    face_vertex_indices: &[i32],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<Vec<gf::Vec3f>> {
    if joint_indices.len() != joint_weights.len()
        || !has_shape(joint_indices.len(), num_influences)
        || face_vertex_indices.len() != normals.len()
    {
        return None;
    }
    let num_points = joint_indices.len() / num_influences;
    if num_points == 0 && !normals.is_empty() {
        return None;
    }
    let point_of = |normal: usize| {
        usize::try_from(face_vertex_indices[normal])
            .ok()
            .filter(|&point| point < num_points)
            .unwrap_or(0)
    };
    let read = |normal: usize| {
        let point = point_of(normal);
        &joint_indices[point * num_influences..(point + 1) * num_influences]
    };
    if !(0..normals.len()).all(|normal| names_joints(read(normal), skinning_xforms)) {
        return None;
    }
    Some(skin_normals_with(
        normals,
        point_of,
        joint_indices,
        joint_weights,
        num_influences,
        geom_bind_transform,
        skinning_xforms,
    ))
}

/// Linear blend skinning of one rigid transform (C++
/// `UsdSkelSkinTransformLBS`). A single influence of weight one gives
/// `geom_bind_transform` times that joint's skinning transform. Otherwise
/// the pivot of `geom_bind_transform` and the tips of its three basis rows
/// are skinned as points, and the result is rebuilt from them: the skinned
/// pivot is the translation, and each skinned tip less the pivot a row.
/// `None` when the arrays differ in length or an index names no skinning
/// transform.
pub fn skin_transform_lbs(
    joint_indices: &[i32],
    joint_weights: &[f32],
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Option<gf::Mat4d> {
    if joint_indices.len() != joint_weights.len() || !names_joints(joint_indices, skinning_xforms) {
        return None;
    }
    if let ([index], [weight]) = (joint_indices, joint_weights)
        && is_close(*weight, 1.0)
    {
        return Some(geom_bind_transform * skinning_xforms[*index as usize]);
    }
    // The basis tips and the pivot, each the image of a unit point.
    let frame = [
        gf::Vec3d::X_AXIS,
        gf::Vec3d::Y_AXIS,
        gf::Vec3d::Z_AXIS,
        gf::Vec3d::default(),
    ]
    .map(|point| geom_bind_transform.transform_affine(point));
    let [i, j, k, pivot] = frame.map(|point| {
        blend(joint_indices, joint_weights, skinning_xforms, |xform| {
            xform.transform_affine(point)
        })
    });
    let mut out = gf::Mat4d::translation(pivot);
    for (row, tip) in [i, j, k].into_iter().enumerate() {
        let basis = tip - pivot;
        out[(row, 0)] = basis.x;
        out[(row, 1)] = basis.y;
        out[(row, 2)] = basis.z;
    }
    Some(out)
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
    // `None` stands for the rest shape, which contributes no offsets.
    let mut shapes = vec![(Some(SubShape::Primary), 1.0), (None, 0.0)];
    shapes.extend(
        inbetween_weights
            .iter()
            .enumerate()
            .filter(|&(_, &w)| !is_close(w, 0.0) && !is_close(w, 1.0))
            .map(|(index, &w)| (Some(SubShape::Inbetween(index)), w)),
    );
    if shapes.len() < 3 {
        return vec![(SubShape::Primary, weight)];
    }
    shapes.sort_by(|a, b| a.1.total_cmp(&b.1));
    let (lower, upper) = match shapes.partition_point(|&(_, w)| w <= weight) {
        0 => (0, 1),
        end if end == shapes.len() => (end - 2, end - 1),
        upper => (upper - 1, upper),
    };
    let ((lower_shape, lower_weight), (upper_shape, upper_weight)) = (shapes[lower], shapes[upper]);
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

/// Skin each normal through the influences of the point `point_of` names for
/// it, after the checks each caller makes on the array shapes and the joint
/// indices.
fn skin_normals_with(
    normals: &[gf::Vec3f],
    point_of: impl Fn(usize) -> usize,
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Vec<gf::Vec3f> {
    // TODO(perf): the normal transforms depend only on the pose, so one pose
    // could share them across prims, and with points.
    let geom_bind_transform = normal_transform(geom_bind_transform);
    let skinning_xforms: Vec<gf::Mat4d> = skinning_xforms.iter().copied().map(normal_transform).collect();
    // TODO(rayon): each normal is skinned from its own influence run and the
    // shared read-only transforms.
    normals
        .iter()
        .enumerate()
        .map(|(normal, &n)| {
            let skel_n = geom_bind_transform.transform_dir(n.into());
            let point = point_of(normal);
            let run = point * num_influences..(point + 1) * num_influences;
            blend(
                &joint_indices[run.clone()],
                &joint_weights[run],
                &skinning_xforms,
                |xform| xform.transform_dir(skel_n),
            )
            .normalize()
            .to_f32()
        })
        .collect()
}

/// The sum of `apply` over the skinning transforms `indices` name, each
/// scaled by its weight. A zero weight is skipped. Every index must name one
/// of `skinning_xforms` ([`names_joints`]).
fn blend(
    indices: &[i32],
    weights: &[f32],
    skinning_xforms: &[gf::Mat4d],
    apply: impl Fn(&gf::Mat4d) -> gf::Vec3d,
) -> gf::Vec3d {
    let mut sum = gf::Vec3d::default();
    for (&index, &weight) in indices.iter().zip(weights) {
        if weight != 0.0 {
            sum += apply(&skinning_xforms[index as usize]) * f64::from(weight);
        }
    }
    sum
}

/// `true` when every index, whatever its weight, names one of
/// `skinning_xforms`, as C++ requires of each influence.
fn names_joints(indices: &[i32], skinning_xforms: &[gf::Mat4d]) -> bool {
    indices
        .iter()
        .all(|&index| usize::try_from(index).is_ok_and(|index| index < skinning_xforms.len()))
}

/// The transform a normal takes through `transform`: the inverse-transpose of
/// its upper-left 3×3 (C++ `ExtractRotationMatrix().GetInverse()
/// .GetTranspose()`), held in a 4×4 for [`gf::Mat4d::transform_dir`]. A
/// singular 3×3 inverts as [`gf::Mat4d::inverse_or_max`] does, as C++
/// `GfMatrix3d::GetInverse` does.
fn normal_transform(transform: gf::Mat4d) -> gf::Mat4d {
    let mut upper = gf::Mat4d::IDENTITY;
    for row in 0..3 {
        for column in 0..3 {
            upper[(row, column)] = transform[(row, column)];
        }
    }
    upper.inverse_or_max().transpose()
}

/// The tolerance C++ `UsdSkelBlendShapeQuery` and `UsdSkelApplyBlendShape`
/// compare blend-shape weights with.
const EPS: f32 = 1e-6;

/// `true` when `a` lies within [`EPS`] of `b` (C++ `GfIsClose`).
fn is_close(a: f32, b: f32) -> bool {
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

    #[test]
    fn skin_points_with_single_full_weight_translates_mesh() {
        let skin = vec![translation(0.0, 1.0, 0.0)];
        let pts = vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(1.0, 0.0, 0.0)];
        let out = skin_points_lbs(&pts, &[0, 0], &[1.0, 1.0], 1, gf::Mat4d::IDENTITY, &skin);
        assert_eq!(out, Some(vec![gf::vec3f(0.0, 1.0, 0.0), gf::vec3f(1.0, 1.0, 0.0)]));
    }

    #[test]
    fn skin_points_blends_two_joints_50_50() {
        let skin = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let pts = vec![gf::vec3f(0.0, 0.0, 0.0)];
        let out = skin_points_lbs(&pts, &[0, 1], &[0.5, 0.5], 2, gf::Mat4d::IDENTITY, &skin);
        assert_eq!(out, Some(vec![gf::vec3f(0.5, 0.5, 0.0)]));
    }

    #[test]
    fn skin_points_rejects_bad_input() {
        let skin = [gf::Mat4d::IDENTITY];
        let pts = [gf::Vec3f::default(); 2];
        // Too few influences, mismatched weights, an index past the joints.
        assert!(skin_points_lbs(&pts, &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_points_lbs(&pts, &[0, 0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_points_lbs(&pts, &[0, 1], &[1.0, 1.0], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        // A zero weight still has to name a joint.
        assert!(skin_points_lbs(&pts, &[0, -1], &[1.0, 0.0], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        // Zero influences per point skin nothing.
        assert!(skin_points_lbs(&pts, &[], &[], 0, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_normals_lbs(&pts, &[], &[], 0, gf::Mat4d::IDENTITY, &skin).is_none());
    }

    #[test]
    fn dual_quaternion_unsupported() {
        let skin = [gf::Mat4d::IDENTITY];
        let method = SkinningMethod::DualQuaternion;
        let pts = [gf::Vec3f::default()];
        assert!(skin_points(method, &pts, &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_normals(method, &pts, &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_face_varying_normals(method, &pts, &[0], &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        assert!(skin_transform(method, &[0], &[1.0], gf::Mat4d::IDENTITY, &skin).is_none());
        let linear = SkinningMethod::ClassicLinear;
        assert_eq!(
            skin_points(linear, &pts, &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin),
            Some(pts.to_vec())
        );
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
        let out = skin_normals_lbs(&[gf::vec3f(n, n, 0.0)], &[0], &[1.0], 1, gf::Mat4d::IDENTITY, &skin)
            .expect("one influence per normal");
        let expected = gf::vec3d(1.0, 2.0, 0.0).normalize().to_f32();
        assert!((out[0] - expected).length() < 1e-6, "{:?}", out[0]);
        // Translation does not move a normal.
        let out = skin_normals_lbs(
            &[gf::vec3f(0.0, 1.0, 0.0)],
            &[0],
            &[1.0],
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
            &[0, 1],
            &[1.0, 1.0],
            1,
            gf::Mat4d::IDENTITY,
            &skin,
        )
        .expect("one face-vertex index per normal");
        assert!((out[0] - gf::vec3f(1.0, 0.0, 0.0)).length() < 1e-6);
        assert!((out[1] - gf::vec3f(0.0, 1.0, 0.0)).length() < 1e-6, "{:?}", out[1]);
        assert!((out[2] - gf::vec3f(1.0, 0.0, 0.0)).length() < 1e-6);
        assert!(
            skin_face_varying_normals_lbs(&normals, &[0, 1], &[0, 1], &[1.0, 1.0], 1, gf::Mat4d::IDENTITY, &skin)
                .is_none()
        );
        // Normals with no points to read are rejected.
        assert!(skin_face_varying_normals_lbs(&normals[..1], &[0], &[], &[], 1, gf::Mat4d::IDENTITY, &skin).is_none());
        // A stale joint index on a point no face vertex names is not read.
        let out =
            skin_face_varying_normals_lbs(&normals[..1], &[0], &[0, 9], &[1.0, 1.0], 1, gf::Mat4d::IDENTITY, &skin);
        assert!(out.is_some());
    }

    #[test]
    fn skin_transform_rebuilds_frame() {
        let skin = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let m = skin_transform_lbs(&[0, 1], &[0.5, 0.5], gf::Mat4d::IDENTITY, &skin).expect("valid influences");
        assert_eq!(m, translation(0.5, 0.5, 0.0));

        // Weights summing to two scale the rebuilt rows, and the matrix stays
        // affine (C++ rebuilds from the skinned frame points).
        let m = skin_transform_lbs(&[0, 1], &[1.0, 1.0], gf::Mat4d::IDENTITY, &skin).expect("valid influences");
        assert_eq!(m[(0, 0)], 2.0);
        assert_eq!(m[(3, 3)], 1.0);
        assert_eq!(m.extract_translation(), gf::vec3d(1.0, 1.0, 0.0));

        // One full-weight influence multiplies straight through.
        let bind = translation(0.0, 0.0, 3.0);
        assert_eq!(
            skin_transform_lbs(&[1], &[1.0], bind, &skin),
            Some(bind * translation(0.0, 1.0, 0.0))
        );
        assert!(skin_transform_lbs(&[2], &[1.0], bind, &skin).is_none());
        assert!(skin_transform_lbs(&[0, 1], &[1.0], bind, &skin).is_none());
    }
}
