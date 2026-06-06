//! Linear blend skinning + blend-shape application — the skinning
//! pipeline math that consumes pre-resolved joint transforms.

use crate::gf;

use super::topology::{Topology, NO_PARENT};

/// Compose joint-local transforms into skeleton-space transforms by
/// concatenating each joint's local transform with its parent's
/// already-resolved skel-space transform.
///
/// Per the UsdSkel spec: `jointSkelSpaceTransform =
/// jointLocalSpaceTransform * parentJointSkelSpaceTransform`. The
/// canonical UsdSkel `joints` ordering guarantees parents precede
/// children, so a single forward pass is enough.
///
/// Root joints (parent == [`NO_PARENT`]) keep their local transform
/// as their skel-space transform.
pub fn joint_local_to_skel_space(local: &[gf::Matrix4d], topology: &Topology) -> Vec<gf::Matrix4d> {
    assert_eq!(
        local.len(),
        topology.num_joints(),
        "joint_local_to_skel_space: local.len() must equal topology.num_joints()"
    );
    let mut out = vec![gf::Matrix4d::IDENTITY; local.len()];
    for i in 0..local.len() {
        let p = topology.parent(i);
        out[i] = if p == NO_PARENT {
            local[i]
        } else {
            local[i] * out[p as usize]
        };
    }
    out
}

/// Compose skel-space joint transforms with the skel-root's
/// local-to-world transform to obtain world-space joint transforms.
/// Per the UsdSkel spec: `jointWorldSpaceTransform =
/// jointSkelSpaceTransform * skelLocalToWorldTransform`.
///
/// Callers supply the skel-root's world transform; this module does
/// not reach into the Stage for it (UsdSkel intentionally separates
/// the two so consumers can plug in their own xform cache).
pub fn joint_skel_to_world(skel: &[gf::Matrix4d], skel_local_to_world: gf::Matrix4d) -> Vec<gf::Matrix4d> {
    skel.iter().map(|m| *m * skel_local_to_world).collect()
}

/// Compute per-joint skinning transforms from current joint poses and
/// the bind-pose inverses.
///
/// Per Pixar's `UsdSkelSkeletonQuery::ComputeSkinningTransforms`:
/// `skinningTransform = inverse(bindTransform) · jointTransform`. The
/// caller decides which space `jointTransform` is in (skel-space when
/// `geomBindTransform` is the identity, world-space otherwise — they
/// must match the space of the bind transforms).
pub fn compute_skinning_transforms(joint: &[gf::Matrix4d], inverse_bind: &[gf::Matrix4d]) -> Vec<gf::Matrix4d> {
    assert_eq!(
        joint.len(),
        inverse_bind.len(),
        "compute_skinning_transforms: array lengths must match"
    );
    joint.iter().zip(inverse_bind).map(|(j, b)| *b * *j).collect()
}

/// Pre-compute the per-joint inverse-bind transforms used by
/// [`compute_skinning_transforms`]. Joints whose bind transform is
/// singular get [`gf::Matrix4d::IDENTITY`] — same fallback as Pixar's
/// reference implementation.
pub fn compute_inverse_bind_transforms(bind: &[gf::Matrix4d]) -> Vec<gf::Matrix4d> {
    bind.iter()
        .map(|m| m.inverse().unwrap_or(gf::Matrix4d::IDENTITY))
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
/// influence lists from `SkelBindingAPI`; `num_influences` is the
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
    geom_bind_transform: gf::Matrix4d,
    skinning_xforms: &[gf::Matrix4d],
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
        let skel_p = geom_bind_transform.transform_point(p);
        let mut acc = gf::Vec3f::default();
        for inf in 0..num_influences {
            let slot = vi * num_influences + inf;
            let w = joint_weights[slot];
            if w == 0.0 {
                continue;
            }
            let j = joint_indices[slot] as usize;
            acc += skinning_xforms[j].transform_point(skel_p) * w;
        }
        out.push(acc);
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
    geom_bind_transform: gf::Matrix4d,
    skinning_xforms: &[gf::Matrix4d],
) -> Vec<gf::Vec3f> {
    assert!(num_influences >= 1, "num_influences must be >= 1");
    let mut out = Vec::with_capacity(normals.len());
    for (vi, &n) in normals.iter().enumerate() {
        let skel_n = geom_bind_transform.transform_vec(n);
        let mut acc = gf::Vec3f::default();
        for inf in 0..num_influences {
            let slot = vi * num_influences + inf;
            let w = joint_weights[slot];
            if w == 0.0 {
                continue;
            }
            let j = joint_indices[slot] as usize;
            acc += skinning_xforms[j].transform_vec(skel_n) * w;
        }
        out.push(acc.normalize());
    }
    out
}

/// Rigid-deformation transform for a constant-interpolation
/// SkelBindingAPI — when every vertex shares one set of joint
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
    geom_bind_transform: gf::Matrix4d,
    skinning_xforms: &[gf::Matrix4d],
) -> gf::Matrix4d {
    assert!(num_influences >= 1, "num_influences must be >= 1");
    assert_eq!(joint_indices.len(), num_influences);
    assert_eq!(joint_weights.len(), num_influences);
    let mut weighted = gf::Matrix4d([0.0f64; 16]);
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
    /// Blended weight after inbetween resolution (typically `[0, 1]`).
    pub weight: f32,
    /// Per-affected-vertex position offsets, parallel to
    /// `point_indices` when sparse.
    pub offsets: &'a [gf::Vec3f],
    /// Optional sparse-vertex remap. Empty = dense.
    pub point_indices: &'a [i32],
}

/// Apply a stack of blend shapes to a mesh's points.
///
/// Per the canonical UsdSkel pipeline blend shapes are evaluated
/// *before* skinning; the deformed mesh is then skinned through
/// [`skin_points_lbs`]. This helper does only the morph step:
///
/// `p_morphed[i] = p[i] + Σ_s (weight_s * offset_s[i])`
///
/// Caller supplies the per-shape weight already resolved through
/// any inbetween interpolation — see [`resolve_inbetween_weight`].
pub fn apply_blend_shapes(points: &[gf::Vec3f], shapes: &[BlendShapeWeighted<'_>]) -> Vec<gf::Vec3f> {
    let mut out = points.to_vec();
    for s in shapes {
        if s.weight == 0.0 {
            continue;
        }
        if s.point_indices.is_empty() {
            for (i, &off) in s.offsets.iter().enumerate() {
                if i >= out.len() {
                    break;
                }
                out[i] += off * s.weight;
            }
        } else {
            for (slot, &vi) in s.point_indices.iter().enumerate() {
                let i = vi as usize;
                if i >= out.len() || slot >= s.offsets.len() {
                    continue;
                }
                out[i] += s.offsets[slot] * s.weight;
            }
        }
    }
    out
}

/// Resolve the effective offset contribution at a given weight for a
/// blend shape that has inbetween shapes.
///
/// Implements UsdSkel's piecewise-linear interpolation along the
/// `[0, 1]` weight axis: breakpoints are at `0` (rest, zero offset),
/// each inbetween at its authored weight, and `1` (the primary
/// `BlendShape.offsets`). Caller passes `(inbetween_weight,
/// inbetween_offsets)` pairs **sorted ascending by weight** (this
/// helper sorts internally so authoring order doesn't matter).
///
/// Returns `(effective_weight_on_segment, segment_offsets)` for the
/// segment containing `w`, where `effective_weight_on_segment` is the
/// `[0, 1]` interpolation parameter to apply to `segment_offsets` via
/// `out[i] = lower + t * (segment_offsets[i] - lower[i])`. Since we
/// don't have negative-weight semantics in the spec the result is
/// clamped to `[0, 1]`.
///
/// For consumers that just want a single blended offset array
/// directly, [`resolve_blend_shape_offsets`] does that in one shot.
pub fn resolve_inbetween_weight<'a>(
    w: f32,
    inbetweens: &'a [(f32, &'a [gf::Vec3f])],
    primary: &'a [gf::Vec3f],
) -> (f32, &'a [gf::Vec3f]) {
    let w = w.clamp(0.0, 1.0);
    let mut breakpoints: Vec<(f32, &[gf::Vec3f])> = inbetweens.iter().map(|(w, o)| (*w, *o)).collect();
    breakpoints.push((1.0, primary));
    breakpoints.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
    let mut prev_w = 0.0f32;
    for (bw, off) in breakpoints {
        if w <= bw {
            let span = bw - prev_w;
            let t = if span > 0.0 { (w - prev_w) / span } else { 0.0 };
            return (t, off);
        }
        prev_w = bw;
    }
    (1.0, primary)
}

/// One inbetween shape — its authored weight and its offsets.
/// Inputs to [`resolve_blend_shape_offsets`].
pub type InbetweenRef<'a> = (f32, &'a [gf::Vec3f]);

/// Resolve a single blend shape (primary + optional inbetweens) at
/// weight `w` into the effective per-vertex offset array. Returns a
/// fresh `Vec` whose length matches whichever array is in play for
/// the resolved segment (segments don't span shapes with different
/// vertex counts in well-formed UsdSkel data).
pub fn resolve_blend_shape_offsets(w: f32, inbetweens: &[InbetweenRef<'_>], primary: &[gf::Vec3f]) -> Vec<gf::Vec3f> {
    let w = w.clamp(0.0, 1.0);
    let mut bps: Vec<(f32, &[gf::Vec3f])> = inbetweens.iter().map(|(w, o)| (*w, *o)).collect();
    bps.push((1.0, primary));
    bps.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));

    let mut lower_w = 0.0f32;
    let lower_offsets: Vec<gf::Vec3f> = Vec::new();
    let mut lower_offsets_slice: &[gf::Vec3f] = &lower_offsets;
    for (bw, off) in &bps {
        if w <= *bw {
            let span = bw - lower_w;
            let t = if span > 0.0 { (w - lower_w) / span } else { 0.0 };
            return lerp_offsets(lower_offsets_slice, off, t, off.len());
        }
        lower_w = *bw;
        lower_offsets_slice = off;
    }
    primary.to_vec()
}

fn lerp_offsets(a: &[gf::Vec3f], b: &[gf::Vec3f], t: f32, len: usize) -> Vec<gf::Vec3f> {
    (0..len)
        .map(|i| {
            let av = if a.is_empty() {
                gf::Vec3f::default()
            } else {
                a[i.min(a.len() - 1)]
            };
            let bv = if b.is_empty() {
                gf::Vec3f::default()
            } else {
                b[i.min(b.len() - 1)]
            };
            av.lerp(bv, t)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn translation(x: f64, y: f64, z: f64) -> gf::Matrix4d {
        gf::Matrix4d::translation([x, y, z])
    }

    #[test]
    fn joint_local_to_skel_chains_translations() {
        let topo = Topology::from_parents(vec![NO_PARENT, 0]);
        let local = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let skel = joint_local_to_skel_space(&local, &topo);
        assert_eq!(skel[0][(3, 0)], 1.0);
        assert_eq!(skel[1][(3, 0)], 1.0);
        assert_eq!(skel[1][(3, 1)], 1.0);
    }

    #[test]
    fn skinning_transform_is_inverse_bind_times_current() {
        let bind = vec![translation(1.0, 0.0, 0.0)];
        let inv_bind = compute_inverse_bind_transforms(&bind);
        let current = vec![translation(1.0, 2.0, 0.0)];
        let skin = compute_skinning_transforms(&current, &inv_bind);
        let p = skin[0].transform_point(gf::vec3f(1.0, 0.0, 0.0));
        assert_eq!(p, gf::vec3f(1.0, 2.0, 0.0));
    }

    #[test]
    fn skin_points_with_single_full_weight_translates_mesh() {
        let skin = vec![translation(0.0, 1.0, 0.0)];
        let pts = vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(1.0, 0.0, 0.0)];
        let out = skin_points_lbs(&pts, &[0, 0], &[1.0, 1.0], 1, gf::Matrix4d::IDENTITY, &skin);
        assert_eq!(out, vec![gf::vec3f(0.0, 1.0, 0.0), gf::vec3f(1.0, 1.0, 0.0)]);
    }

    #[test]
    fn skin_points_blends_two_joints_50_50() {
        let skin = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let pts = vec![gf::vec3f(0.0, 0.0, 0.0)];
        let out = skin_points_lbs(&pts, &[0, 1], &[0.5, 0.5], 2, gf::Matrix4d::IDENTITY, &skin);
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
        assert_eq!(out, vec![gf::vec3f(1.0, 0.5, 0.0), gf::vec3f(0.0, 1.0, 0.0)]);
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
            vec![
                gf::Vec3f::default(),
                gf::vec3f(1.0, 0.0, 0.0),
                gf::Vec3f::default(),
                gf::vec3f(0.0, 0.0, 5.0),
            ]
        );
    }

    #[test]
    fn resolve_inbetween_weight_lands_on_segment() {
        let inb_off = vec![gf::vec3f(0.0, 0.5, 0.0)];
        let prim = vec![gf::vec3f(0.0, 1.0, 0.0)];
        let inbetweens = [(0.5_f32, inb_off.as_slice())];

        let (t, segment) = resolve_inbetween_weight(0.25, &inbetweens, &prim);
        assert!((t - 0.5).abs() < 1e-6);
        assert_eq!(segment, inb_off.as_slice());

        let (t, segment) = resolve_inbetween_weight(0.75, &inbetweens, &prim);
        assert!((t - 0.5).abs() < 1e-6);
        assert_eq!(segment, prim.as_slice());
    }

    #[test]
    fn resolve_blend_shape_offsets_interpolates_through_inbetween() {
        let inb_off = vec![gf::vec3f(0.0, 1.0, 0.0)];
        let prim = vec![gf::vec3f(0.0, 2.0, 0.0)];
        let inbetweens = [(0.5_f32, inb_off.as_slice())];

        let out = resolve_blend_shape_offsets(0.5, &inbetweens, &prim);
        assert_eq!(out, vec![gf::vec3f(0.0, 1.0, 0.0)]);

        let out = resolve_blend_shape_offsets(0.75, &inbetweens, &prim);
        assert_eq!(out, vec![gf::vec3f(0.0, 1.5, 0.0)]);
    }

    #[test]
    fn rigid_skinning_combines_weighted_joints_then_geom_bind() {
        let skin = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let m = rigid_skinning_transform(&[0, 1], &[0.5, 0.5], 2, gf::Matrix4d::IDENTITY, &skin);
        let p = m.transform_point(gf::vec3f(0.0, 0.0, 0.0));
        assert_eq!(p, gf::vec3f(0.5, 0.5, 0.0));
    }
}
