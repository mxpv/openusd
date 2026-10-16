//! Linear blend skinning + blend-shape application — the skinning
//! pipeline math that consumes pre-resolved joint transforms.

use openusd::gf;

use super::topology::Topology;

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
/// their skel-space transform. `None` when `local` holds other than one
/// transform per joint, or a joint's parent does not precede it.
pub fn joint_local_to_skel_space(local: &[gf::Mat4d], topology: &Topology) -> Option<Vec<gf::Mat4d>> {
    if local.len() != topology.joint_count() {
        return None;
    }
    let mut out = Vec::with_capacity(local.len());
    for (i, &transform) in local.iter().enumerate() {
        out.push(match topology.parent(i) {
            Some(parent) => transform * *out.get(parent)?,
            None => transform,
        });
    }
    Some(out)
}

/// Compose skel-space joint transforms with the skel-root's
/// local-to-world transform to obtain world-space joint transforms.
/// Per the UsdSkel spec: `jointWorldSpaceTransform =
/// jointSkelSpaceTransform * skelLocalToWorldTransform`.
///
/// Callers supply the skel-root's world transform; this module does
/// not reach into the Stage for it (UsdSkel intentionally separates
/// the two so consumers can plug in their own xform cache).
pub fn joint_skel_to_world(skel: &[gf::Mat4d], skel_local_to_world: gf::Mat4d) -> Vec<gf::Mat4d> {
    skel.iter().map(|m| *m * skel_local_to_world).collect()
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

/// Pre-compute the per-joint inverse-bind transforms used by
/// [`skinning_transforms`]. Joints whose bind transform is
/// singular get [`gf::Mat4d::IDENTITY`], where C++ `GfMatrix4d::GetInverse`
/// answers `FLT_MAX` times the identity.
pub fn inverse_bind_transforms(bind: &[gf::Mat4d]) -> Vec<gf::Mat4d> {
    bind.iter()
        .map(|m| m.inverse().unwrap_or(gf::Mat4d::IDENTITY))
        .collect()
}

/// Linear blend skinning of a point cloud — the canonical UsdSkel
/// algorithm from the spec's "Skinning a Point" section:
///
/// ```text
/// skelSpacePoint = geomBindTransform.Transform(localSpacePoint)
/// p = (0, 0, 0)
/// for (jointIndex, jointWeight) in jointInfluencesForPoint:
///     p += skinningTransforms[jointIndex].Transform(skelSpacePoint) * jointWeight
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
/// Returns one deformed point per input point.
pub fn skin_points_lbs(
    points: &[gf::Vec3f],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Vec<gf::Vec3f> {
    assert!(num_influences >= 1, "num_influences must be >= 1");
    assert_eq!(
        joint_indices.len(),
        joint_weights.len(),
        "indices and weights must be the same length"
    );
    assert_eq!(
        joint_indices.len(),
        points.len() * num_influences,
        "indices length must equal points * num_influences"
    );

    let mut out = Vec::with_capacity(points.len());
    for (vi, &p) in points.iter().enumerate() {
        let skel_p = geom_bind_transform.transform_affine(p.into());
        let mut acc = gf::Vec3d::default();
        for inf in 0..num_influences {
            let slot = vi * num_influences + inf;
            let w = joint_weights[slot];
            if w == 0.0 {
                continue;
            }
            let j = joint_indices[slot] as usize;
            acc += skinning_xforms[j].transform_affine(skel_p) * f64::from(w);
        }
        out.push(acc.to_f32());
    }
    out
}

/// Linear blend skinning of normals. Same per-vertex influence layout
/// as [`skin_points_lbs`], but treats vectors as directions (no
/// translation) and renormalises each result.
///
/// Note this uses the same per-joint matrix as [`skin_points_lbs`] —
/// a strictly correct implementation would use the inverse-transpose
/// when scale is non-uniform. For typical character rigs (rigid bone
/// transforms) the two are equivalent and consumers don't notice.
pub fn skin_normals_lbs(
    normals: &[gf::Vec3f],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> Vec<gf::Vec3f> {
    assert!(num_influences >= 1, "num_influences must be >= 1");
    let mut out = Vec::with_capacity(normals.len());
    for (vi, &n) in normals.iter().enumerate() {
        let skel_n = geom_bind_transform.transform_dir(n.into());
        let mut acc = gf::Vec3d::default();
        for inf in 0..num_influences {
            let slot = vi * num_influences + inf;
            let w = joint_weights[slot];
            if w == 0.0 {
                continue;
            }
            let j = joint_indices[slot] as usize;
            acc += skinning_xforms[j].transform_dir(skel_n) * f64::from(w);
        }
        out.push(acc.normalize().to_f32());
    }
    out
}

/// Rigid-deformation transform for a constant-interpolation
/// `BindingAPI` — when every vertex shares one set of joint
/// influences, skinning collapses to a single 4×4 to apply to the
/// whole mesh's local-to-world.
///
/// `joint_indices` / `joint_weights` are the (single-element-per-vertex
/// or constant) influences. `num_influences` is the influence count;
/// it doesn't have to be 1 — a constant-interpolation primvar can
/// still carry multiple influences applied to the mesh as a whole.
///
/// Returns `geomBindTransform · Σ(weight_i · skinning_xform_i)`.
pub fn rigid_skinning_transform(
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: gf::Mat4d,
    skinning_xforms: &[gf::Mat4d],
) -> gf::Mat4d {
    assert!(num_influences >= 1, "num_influences must be >= 1");
    assert_eq!(joint_indices.len(), num_influences);
    assert_eq!(joint_weights.len(), num_influences);
    let mut weighted = gf::Mat4d([0.0f64; 16]);
    for inf in 0..num_influences {
        let w = joint_weights[inf] as f64;
        if w == 0.0 {
            continue;
        }
        let j = joint_indices[inf] as usize;
        weighted += skinning_xforms[j] * w;
    }
    geom_bind_transform * weighted
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

/// The tolerance C++ `UsdSkelBlendShapeQuery` and `UsdSkelApplyBlendShape`
/// compare blend-shape weights with.
const EPS: f32 = 1e-6;

/// `true` when `a` lies within [`EPS`] of `b` (C++ `GfIsClose`).
fn is_close(a: f32, b: f32) -> bool {
    (a - b).abs() < EPS
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
        let skel = joint_local_to_skel_space(&local, &topo).expect("ordered joints");
        assert_eq!(skel[0][(3, 0)], 1.0);
        assert_eq!(skel[1][(3, 0)], 1.0);
        assert_eq!(skel[1][(3, 1)], 1.0);
    }

    #[test]
    fn misordered_parent_rejected() {
        let topo = Topology::from_parents(vec![1, NO_PARENT]);
        assert!(joint_local_to_skel_space(&[gf::Mat4d::IDENTITY; 2], &topo).is_none());
        assert!(joint_local_to_skel_space(&[gf::Mat4d::IDENTITY], &topo).is_none());
    }

    #[test]
    fn skinning_transform_is_inverse_bind_times_current() {
        let bind = vec![translation(1.0, 0.0, 0.0)];
        let inv_bind = inverse_bind_transforms(&bind);
        let current = vec![translation(1.0, 2.0, 0.0)];
        let skin = skinning_transforms(&current, &inv_bind).expect("one inverse per joint");
        let p = skin[0].transform_affine(gf::vec3d(1.0, 0.0, 0.0));
        assert_eq!(p, gf::vec3d(1.0, 2.0, 0.0));
    }

    #[test]
    fn skin_points_with_single_full_weight_translates_mesh() {
        let skin = vec![translation(0.0, 1.0, 0.0)];
        let pts = vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(1.0, 0.0, 0.0)];
        let out = skin_points_lbs(&pts, &[0, 0], &[1.0, 1.0], 1, gf::Mat4d::IDENTITY, &skin);
        assert_eq!(out, vec![gf::vec3f(0.0, 1.0, 0.0), gf::vec3f(1.0, 1.0, 0.0)]);
    }

    #[test]
    fn skin_points_blends_two_joints_50_50() {
        let skin = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let pts = vec![gf::vec3f(0.0, 0.0, 0.0)];
        let out = skin_points_lbs(&pts, &[0, 1], &[0.5, 0.5], 2, gf::Mat4d::IDENTITY, &skin);
        assert_eq!(out, vec![gf::vec3f(0.5, 0.5, 0.0)]);
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
    fn rigid_skinning_combines_weighted_joints_then_geom_bind() {
        let skin = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let m = rigid_skinning_transform(&[0, 1], &[0.5, 0.5], 2, gf::Mat4d::IDENTITY, &skin);
        let p = m.transform_affine(gf::vec3d(0.0, 0.0, 0.0));
        assert_eq!(p, gf::vec3d(0.5, 0.5, 0.0));
    }
}
