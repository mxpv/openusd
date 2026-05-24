//! Pure-math skinning helpers — linear blend skinning, transform
//! composition, blend-shape application.
//!
//! All matrix data uses USD's textual `matrix4d` layout: a flat
//! `[f64; 16]` storing the matrix in row-major order (the same order
//! the USDA writer emits). All operations live in this module so the
//! `skel` crate doesn't grow a top-level math dependency — callers
//! can keep using their own math library and only convert at the
//! interface.

use super::topology::{Topology, NO_PARENT};

/// 4×4 identity in USD's `matrix4d` row-major layout.
pub const IDENTITY_MAT4: [f64; 16] = [
    1.0, 0.0, 0.0, 0.0, //
    0.0, 1.0, 0.0, 0.0, //
    0.0, 0.0, 1.0, 0.0, //
    0.0, 0.0, 0.0, 1.0, //
];

/// `out = a · b` for two 4×4 row-major matrices.
///
/// USD authors transforms in row-major form and applies them by
/// pre-multiplying row vectors: `v_out = v_in · M`. Sequences of
/// transforms therefore chain left-to-right: to place a child's local
/// transform under its parent's, compose `(M_local · M_parent)` — the
/// same form the UsdSkel spec writes as
/// `jointLocalSpaceTransform * parentJointSkelSpaceTransform`.
pub fn mat4_mul(a: &[f64; 16], b: &[f64; 16]) -> [f64; 16] {
    let mut out = [0.0f64; 16];
    for r in 0..4 {
        for c in 0..4 {
            let mut v = 0.0;
            for k in 0..4 {
                v += a[r * 4 + k] * b[k * 4 + c];
            }
            out[r * 4 + c] = v;
        }
    }
    out
}

/// Apply a 4×4 row-major matrix to a position. Equivalent to
/// `(p.x, p.y, p.z, 1) · M` and then dropping `w`.
pub fn mat4_transform_point(m: &[f64; 16], p: [f32; 3]) -> [f32; 3] {
    let x = p[0] as f64;
    let y = p[1] as f64;
    let z = p[2] as f64;
    let nx = x * m[0] + y * m[4] + z * m[8] + m[12];
    let ny = x * m[1] + y * m[5] + z * m[9] + m[13];
    let nz = x * m[2] + y * m[6] + z * m[10] + m[14];
    [nx as f32, ny as f32, nz as f32]
}

/// Apply the rotational + scale part of a matrix to a direction
/// vector (e.g. a normal). Ignores the translation row.
pub fn mat4_transform_vec(m: &[f64; 16], v: [f32; 3]) -> [f32; 3] {
    let x = v[0] as f64;
    let y = v[1] as f64;
    let z = v[2] as f64;
    let nx = x * m[0] + y * m[4] + z * m[8];
    let ny = x * m[1] + y * m[5] + z * m[9];
    let nz = x * m[2] + y * m[6] + z * m[10];
    [nx as f32, ny as f32, nz as f32]
}

/// Singularity threshold for [`mat4_inverse`]. `f64::EPSILON` (≈ 2.2e-16)
/// is tight enough that ill-conditioned real-world bind matrices slip
/// through and produce numerically-unstable inverses; `1e-12` matches
/// the tolerance Pixar's reference inverter uses for skel data.
const MAT4_SINGULAR_DETERMINANT: f64 = 1e-12;

/// Invert a 4×4 row-major matrix using cofactor expansion.
/// Returns [`None`] when the matrix is singular or near-singular
/// (`|det| < `[`MAT4_SINGULAR_DETERMINANT`]).
pub fn mat4_inverse(m: &[f64; 16]) -> Option<[f64; 16]> {
    let mut inv = [0.0f64; 16];

    inv[0] =
        m[5] * m[10] * m[15] - m[5] * m[11] * m[14] - m[9] * m[6] * m[15] + m[9] * m[7] * m[14] + m[13] * m[6] * m[11]
            - m[13] * m[7] * m[10];
    inv[4] =
        -m[4] * m[10] * m[15] + m[4] * m[11] * m[14] + m[8] * m[6] * m[15] - m[8] * m[7] * m[14] - m[12] * m[6] * m[11]
            + m[12] * m[7] * m[10];
    inv[8] =
        m[4] * m[9] * m[15] - m[4] * m[11] * m[13] - m[8] * m[5] * m[15] + m[8] * m[7] * m[13] + m[12] * m[5] * m[11]
            - m[12] * m[7] * m[9];
    inv[12] =
        -m[4] * m[9] * m[14] + m[4] * m[10] * m[13] + m[8] * m[5] * m[14] - m[8] * m[6] * m[13] - m[12] * m[5] * m[10]
            + m[12] * m[6] * m[9];
    inv[1] =
        -m[1] * m[10] * m[15] + m[1] * m[11] * m[14] + m[9] * m[2] * m[15] - m[9] * m[3] * m[14] - m[13] * m[2] * m[11]
            + m[13] * m[3] * m[10];
    inv[5] =
        m[0] * m[10] * m[15] - m[0] * m[11] * m[14] - m[8] * m[2] * m[15] + m[8] * m[3] * m[14] + m[12] * m[2] * m[11]
            - m[12] * m[3] * m[10];
    inv[9] =
        -m[0] * m[9] * m[15] + m[0] * m[11] * m[13] + m[8] * m[1] * m[15] - m[8] * m[3] * m[13] - m[12] * m[1] * m[11]
            + m[12] * m[3] * m[9];
    inv[13] =
        m[0] * m[9] * m[14] - m[0] * m[10] * m[13] - m[8] * m[1] * m[14] + m[8] * m[2] * m[13] + m[12] * m[1] * m[10]
            - m[12] * m[2] * m[9];
    inv[2] =
        m[1] * m[6] * m[15] - m[1] * m[7] * m[14] - m[5] * m[2] * m[15] + m[5] * m[3] * m[14] + m[13] * m[2] * m[7]
            - m[13] * m[3] * m[6];
    inv[6] =
        -m[0] * m[6] * m[15] + m[0] * m[7] * m[14] + m[4] * m[2] * m[15] - m[4] * m[3] * m[14] - m[12] * m[2] * m[7]
            + m[12] * m[3] * m[6];
    inv[10] =
        m[0] * m[5] * m[15] - m[0] * m[7] * m[13] - m[4] * m[1] * m[15] + m[4] * m[3] * m[13] + m[12] * m[1] * m[7]
            - m[12] * m[3] * m[5];
    inv[14] =
        -m[0] * m[5] * m[14] + m[0] * m[6] * m[13] + m[4] * m[1] * m[14] - m[4] * m[2] * m[13] - m[12] * m[1] * m[6]
            + m[12] * m[2] * m[5];
    inv[3] =
        -m[1] * m[6] * m[11] + m[1] * m[7] * m[10] + m[5] * m[2] * m[11] - m[5] * m[3] * m[10] - m[9] * m[2] * m[7]
            + m[9] * m[3] * m[6];
    inv[7] = m[0] * m[6] * m[11] - m[0] * m[7] * m[10] - m[4] * m[2] * m[11] + m[4] * m[3] * m[10] + m[8] * m[2] * m[7]
        - m[8] * m[3] * m[6];
    inv[11] = -m[0] * m[5] * m[11] + m[0] * m[7] * m[9] + m[4] * m[1] * m[11] - m[4] * m[3] * m[9] - m[8] * m[1] * m[7]
        + m[8] * m[3] * m[5];
    inv[15] = m[0] * m[5] * m[10] - m[0] * m[6] * m[9] - m[4] * m[1] * m[10] + m[4] * m[2] * m[9] + m[8] * m[1] * m[6]
        - m[8] * m[2] * m[5];

    let det = m[0] * inv[0] + m[1] * inv[4] + m[2] * inv[8] + m[3] * inv[12];
    if det.abs() < MAT4_SINGULAR_DETERMINANT {
        return None;
    }
    let inv_det = 1.0 / det;
    for v in &mut inv {
        *v *= inv_det;
    }
    Some(inv)
}

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
pub fn joint_local_to_skel_space(local: &[[f64; 16]], topology: &Topology) -> Vec<[f64; 16]> {
    assert_eq!(
        local.len(),
        topology.num_joints(),
        "joint_local_to_skel_space: local.len() must equal topology.num_joints()"
    );
    let mut out = vec![IDENTITY_MAT4; local.len()];
    for i in 0..local.len() {
        let p = topology.parent(i);
        out[i] = if p == NO_PARENT {
            local[i]
        } else {
            mat4_mul(&local[i], &out[p as usize])
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
pub fn joint_skel_to_world(skel: &[[f64; 16]], skel_local_to_world: &[f64; 16]) -> Vec<[f64; 16]> {
    skel.iter().map(|m| mat4_mul(m, skel_local_to_world)).collect()
}

/// Compute per-joint skinning transforms from current joint poses and
/// the bind-pose inverses.
///
/// Per Pixar's `UsdSkelSkeletonQuery::ComputeSkinningTransforms`:
/// `skinningTransform = inverse(bindTransform) · jointTransform`. The
/// caller decides which space `jointTransform` is in (skel-space when
/// `geomBindTransform` is the identity, world-space otherwise — they
/// must match the space of the bind transforms).
pub fn compute_skinning_transforms(joint: &[[f64; 16]], inverse_bind: &[[f64; 16]]) -> Vec<[f64; 16]> {
    assert_eq!(
        joint.len(),
        inverse_bind.len(),
        "compute_skinning_transforms: array lengths must match"
    );
    joint.iter().zip(inverse_bind).map(|(j, b)| mat4_mul(b, j)).collect()
}

/// Pre-compute the per-joint inverse-bind transforms used by
/// [`compute_skinning_transforms`]. Joints whose bind transform is
/// singular get [`IDENTITY_MAT4`] — same fallback as Pixar's
/// reference implementation.
pub fn compute_inverse_bind_transforms(bind: &[[f64; 16]]) -> Vec<[f64; 16]> {
    bind.iter().map(|m| mat4_inverse(m).unwrap_or(IDENTITY_MAT4)).collect()
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
    points: &[[f32; 3]],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: &[f64; 16],
    skinning_xforms: &[[f64; 16]],
) -> Vec<[f32; 3]> {
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
    for (vi, p) in points.iter().enumerate() {
        let skel_p = mat4_transform_point(geom_bind_transform, *p);
        let mut acc = [0.0f32; 3];
        for inf in 0..num_influences {
            let slot = vi * num_influences + inf;
            let w = joint_weights[slot];
            if w == 0.0 {
                continue;
            }
            let j = joint_indices[slot] as usize;
            let warped = mat4_transform_point(&skinning_xforms[j], skel_p);
            acc[0] += warped[0] * w;
            acc[1] += warped[1] * w;
            acc[2] += warped[2] * w;
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
    normals: &[[f32; 3]],
    joint_indices: &[i32],
    joint_weights: &[f32],
    num_influences: usize,
    geom_bind_transform: &[f64; 16],
    skinning_xforms: &[[f64; 16]],
) -> Vec<[f32; 3]> {
    assert!(num_influences >= 1, "num_influences must be >= 1");
    let mut out = Vec::with_capacity(normals.len());
    for (vi, n) in normals.iter().enumerate() {
        let skel_n = mat4_transform_vec(geom_bind_transform, *n);
        let mut acc = [0.0f32; 3];
        for inf in 0..num_influences {
            let slot = vi * num_influences + inf;
            let w = joint_weights[slot];
            if w == 0.0 {
                continue;
            }
            let j = joint_indices[slot] as usize;
            let warped = mat4_transform_vec(&skinning_xforms[j], skel_n);
            acc[0] += warped[0] * w;
            acc[1] += warped[1] * w;
            acc[2] += warped[2] * w;
        }
        let len = (acc[0] * acc[0] + acc[1] * acc[1] + acc[2] * acc[2]).sqrt();
        if len > 0.0 {
            acc[0] /= len;
            acc[1] /= len;
            acc[2] /= len;
        }
        out.push(acc);
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
    geom_bind_transform: &[f64; 16],
    skinning_xforms: &[[f64; 16]],
) -> [f64; 16] {
    assert!(num_influences >= 1, "num_influences must be >= 1");
    assert_eq!(joint_indices.len(), num_influences);
    assert_eq!(joint_weights.len(), num_influences);
    let mut weighted = [0.0f64; 16];
    for inf in 0..num_influences {
        let w = joint_weights[inf] as f64;
        if w == 0.0 {
            continue;
        }
        let j = joint_indices[inf] as usize;
        let m = &skinning_xforms[j];
        for k in 0..16 {
            weighted[k] += m[k] * w;
        }
    }
    mat4_mul(geom_bind_transform, &weighted)
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
    pub offsets: &'a [[f32; 3]],
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
pub fn apply_blend_shapes(points: &[[f32; 3]], shapes: &[BlendShapeWeighted<'_>]) -> Vec<[f32; 3]> {
    let mut out = points.to_vec();
    for s in shapes {
        if s.weight == 0.0 {
            continue;
        }
        if s.point_indices.is_empty() {
            // Dense: offsets[i] applies to vertex i.
            for (i, off) in s.offsets.iter().enumerate() {
                if i >= out.len() {
                    break;
                }
                out[i][0] += off[0] * s.weight;
                out[i][1] += off[1] * s.weight;
                out[i][2] += off[2] * s.weight;
            }
        } else {
            for (slot, &vi) in s.point_indices.iter().enumerate() {
                let i = vi as usize;
                if i >= out.len() || slot >= s.offsets.len() {
                    continue;
                }
                let off = s.offsets[slot];
                out[i][0] += off[0] * s.weight;
                out[i][1] += off[1] * s.weight;
                out[i][2] += off[2] * s.weight;
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
    inbetweens: &'a [(f32, &'a [[f32; 3]])],
    primary: &'a [[f32; 3]],
) -> (f32, &'a [[f32; 3]]) {
    let w = w.clamp(0.0, 1.0);
    // Sort by weight ascending. Small-N (typical: 1-3 inbetweens)
    // so a copy + sort is fine.
    let mut breakpoints: Vec<(f32, &[[f32; 3]])> = inbetweens.iter().map(|(w, o)| (*w, *o)).collect();
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
    // Past the last breakpoint (which is the primary at 1.0):
    // saturate to full primary.
    (1.0, primary)
}

/// One inbetween shape — its authored weight and its offsets.
/// Inputs to [`resolve_blend_shape_offsets`].
pub type InbetweenRef<'a> = (f32, &'a [[f32; 3]]);

/// Resolve a single blend shape (primary + optional inbetweens) at
/// weight `w` into the effective per-vertex offset array. Returns a
/// fresh `Vec` whose length matches whichever array is in play for
/// the resolved segment (segments don't span shapes with different
/// vertex counts in well-formed UsdSkel data).
pub fn resolve_blend_shape_offsets(w: f32, inbetweens: &[InbetweenRef<'_>], primary: &[[f32; 3]]) -> Vec<[f32; 3]> {
    let w = w.clamp(0.0, 1.0);
    // Find the segment as above, but this time return the actual
    // interpolated offsets between (lower_offsets, upper_offsets).
    let mut bps: Vec<(f32, &[[f32; 3]])> = inbetweens.iter().map(|(w, o)| (*w, *o)).collect();
    bps.push((1.0, primary));
    bps.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));

    let mut lower_w = 0.0f32;
    let lower_offsets: Vec<[f32; 3]> = Vec::new();
    let mut lower_offsets_slice: &[[f32; 3]] = &lower_offsets;
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

fn lerp_offsets(a: &[[f32; 3]], b: &[[f32; 3]], t: f32, len: usize) -> Vec<[f32; 3]> {
    (0..len)
        .map(|i| {
            let av = if a.is_empty() { [0.0; 3] } else { a[i.min(a.len() - 1)] };
            let bv = if b.is_empty() { [0.0; 3] } else { b[i.min(b.len() - 1)] };
            [
                av[0] + (bv[0] - av[0]) * t,
                av[1] + (bv[1] - av[1]) * t,
                av[2] + (bv[2] - av[2]) * t,
            ]
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn translation(x: f64, y: f64, z: f64) -> [f64; 16] {
        let mut m = IDENTITY_MAT4;
        m[12] = x;
        m[13] = y;
        m[14] = z;
        m
    }

    #[test]
    fn mat4_mul_identity_is_noop() {
        let m = translation(1.0, 2.0, 3.0);
        assert_eq!(mat4_mul(&IDENTITY_MAT4, &m), m);
        assert_eq!(mat4_mul(&m, &IDENTITY_MAT4), m);
    }

    #[test]
    fn point_transform_applies_translation() {
        let m = translation(10.0, 20.0, 30.0);
        let p = mat4_transform_point(&m, [1.0, 2.0, 3.0]);
        assert_eq!(p, [11.0, 22.0, 33.0]);
    }

    #[test]
    fn vec_transform_ignores_translation() {
        let m = translation(10.0, 20.0, 30.0);
        let v = mat4_transform_vec(&m, [1.0, 2.0, 3.0]);
        assert_eq!(v, [1.0, 2.0, 3.0]);
    }

    #[test]
    fn inverse_round_trips() {
        let m = translation(5.0, -2.0, 7.0);
        let inv = mat4_inverse(&m).unwrap();
        let id = mat4_mul(&m, &inv);
        for i in 0..16 {
            assert!((id[i] - IDENTITY_MAT4[i]).abs() < 1e-10, "row-col {i}: {id:?}");
        }
    }

    #[test]
    fn inverse_round_trips_with_rotation() {
        // Build a non-trivial transform that exercises every off-diagonal
        // term of the 3x3 sub-block plus the translation row. A translation-
        // only round-trip is too easy — its inverse is just the negated row
        // — and would not catch an `m[r*4 + c]` ↔ `m[c*4 + r]` typo in any
        // of the 16 cofactor formulas in mat4_inverse.
        let scale = {
            let mut m = IDENTITY_MAT4;
            m[0] = 2.0;
            m[5] = 3.0;
            m[10] = 0.5;
            m
        };
        // 30° rotation around Z (row-vector form: v_new = v · R_z).
        let rot_z = {
            let c = 0.8660254037844387_f64;
            let s = 0.5_f64;
            let mut m = IDENTITY_MAT4;
            m[0] = c;
            m[1] = s;
            m[4] = -s;
            m[5] = c;
            m
        };
        let trans = translation(7.0, -3.0, 11.0);

        // M = scale · rot_z · trans. Order doesn't matter for the test;
        // any invertible non-axis-aligned composition lights up the cofactors.
        let m = mat4_mul(&mat4_mul(&scale, &rot_z), &trans);
        let inv = mat4_inverse(&m).expect("non-singular");

        // Both M · inv and inv · M must equal identity. Checking both
        // catches any cofactor-expansion asymmetry that a one-sided check
        // would miss.
        let id1 = mat4_mul(&m, &inv);
        let id2 = mat4_mul(&inv, &m);
        for i in 0..16 {
            assert!((id1[i] - IDENTITY_MAT4[i]).abs() < 1e-10, "M·inv off at {i}: {id1:?}");
            assert!((id2[i] - IDENTITY_MAT4[i]).abs() < 1e-10, "inv·M off at {i}: {id2:?}");
        }

        // Round-trip a non-trivial point through M then inv — independent
        // sanity check on top of the matrix identity.
        let p = [4.0_f32, -2.5, 7.5];
        let warped = mat4_transform_point(&m, p);
        let back = mat4_transform_point(&inv, warped);
        for k in 0..3 {
            assert!((back[k] - p[k]).abs() < 1e-4, "point round-trip off: {back:?} vs {p:?}");
        }
    }

    #[test]
    fn inverse_rejects_near_singular() {
        // A 4x4 with two identical rows is singular (det = 0); a
        // matrix scaled by ~1e-7 across the board is well above
        // f64::EPSILON but well below the 1e-12 skel threshold.
        let mut near_singular = [0.0f64; 16];
        // Diagonal scale of 1e-4 means det = 1e-16 — under 1e-12.
        for i in 0..4 {
            near_singular[i * 4 + i] = 1e-4;
        }
        assert!(mat4_inverse(&near_singular).is_none(), "should reject near-singular");

        // Plain singular (row of zeros).
        let singular = [0.0f64; 16];
        assert!(mat4_inverse(&singular).is_none(), "should reject zero matrix");
    }

    #[test]
    fn joint_local_to_skel_chains_translations() {
        // Two joints in a chain. Root is at (1, 0, 0); child is
        // (0, 1, 0) relative to root. Expected: root at (1, 0, 0),
        // child at (1, 1, 0).
        let topo = Topology::from_parents(vec![NO_PARENT, 0]);
        let local = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let skel = joint_local_to_skel_space(&local, &topo);
        assert_eq!(skel[0][12..16], [1.0, 0.0, 0.0, 1.0]);
        assert_eq!(skel[1][12..16], [1.0, 1.0, 0.0, 1.0]);
    }

    #[test]
    fn skinning_transform_is_inverse_bind_times_current() {
        // Joint bound at (1, 0, 0), now at (1, 2, 0). Skinning xform
        // for a point at (1, 0, 0) should produce (1, 2, 0).
        let bind = vec![translation(1.0, 0.0, 0.0)];
        let inv_bind = compute_inverse_bind_transforms(&bind);
        let current = vec![translation(1.0, 2.0, 0.0)];
        let skin = compute_skinning_transforms(&current, &inv_bind);
        let p = mat4_transform_point(&skin[0], [1.0, 0.0, 0.0]);
        assert_eq!(p, [1.0, 2.0, 0.0]);
    }

    #[test]
    fn skin_points_with_single_full_weight_translates_mesh() {
        // One joint that translates by (0, 1, 0). Identity geom-bind.
        // Two points, each fully influenced by joint 0.
        let skin = vec![translation(0.0, 1.0, 0.0)];
        let pts = [[0.0_f32, 0.0, 0.0], [1.0, 0.0, 0.0]];
        let out = skin_points_lbs(&pts, &[0, 0], &[1.0, 1.0], 1, &IDENTITY_MAT4, &skin);
        assert_eq!(out, vec![[0.0, 1.0, 0.0], [1.0, 1.0, 0.0]]);
    }

    #[test]
    fn skin_points_blends_two_joints_50_50() {
        // Two joints: one translates +x, one translates +y. Weight
        // 0.5/0.5 → point at (0,0,0) goes to (0.5, 0.5, 0).
        let skin = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let pts = [[0.0_f32, 0.0, 0.0]];
        let out = skin_points_lbs(&pts, &[0, 1], &[0.5, 0.5], 2, &IDENTITY_MAT4, &skin);
        assert_eq!(out, vec![[0.5, 0.5, 0.0]]);
    }

    #[test]
    fn apply_blend_shape_dense_adds_offsets() {
        let pts = vec![[1.0_f32, 0.0, 0.0], [0.0, 0.0, 0.0]];
        let shape = BlendShapeWeighted {
            weight: 0.5,
            offsets: &[[0.0, 1.0, 0.0], [0.0, 2.0, 0.0]],
            point_indices: &[],
        };
        let out = apply_blend_shapes(&pts, &[shape]);
        assert_eq!(out, vec![[1.0, 0.5, 0.0], [0.0, 1.0, 0.0]]);
    }

    #[test]
    fn apply_blend_shape_sparse_remaps_via_indices() {
        let pts = vec![[0.0_f32; 3]; 4];
        let shape = BlendShapeWeighted {
            weight: 1.0,
            offsets: &[[1.0, 0.0, 0.0], [0.0, 0.0, 5.0]],
            point_indices: &[1, 3],
        };
        let out = apply_blend_shapes(&pts, &[shape]);
        assert_eq!(out, vec![[0.0; 3], [1.0, 0.0, 0.0], [0.0; 3], [0.0, 0.0, 5.0]]);
    }

    #[test]
    fn resolve_inbetween_weight_lands_on_segment() {
        let inb_off = [[0.0_f32, 0.5, 0.0]];
        let prim = [[0.0_f32, 1.0, 0.0]];
        let inbetweens = [(0.5_f32, &inb_off[..])];

        // At w=0.25 we're 50% across the (0 → 0.5) segment.
        let (t, segment) = resolve_inbetween_weight(0.25, &inbetweens, &prim);
        assert!((t - 0.5).abs() < 1e-6);
        assert_eq!(segment, &inb_off[..]);

        // At w=0.75 we're 50% across the (0.5 → 1.0) segment.
        let (t, segment) = resolve_inbetween_weight(0.75, &inbetweens, &prim);
        assert!((t - 0.5).abs() < 1e-6);
        assert_eq!(segment, &prim[..]);
    }

    #[test]
    fn resolve_blend_shape_offsets_interpolates_through_inbetween() {
        // Inbetween at 0.5 with offset (0, 1, 0); primary at 1.0 with (0, 2, 0).
        let inb_off = [[0.0_f32, 1.0, 0.0]];
        let prim = [[0.0_f32, 2.0, 0.0]];
        let inbetweens = [(0.5_f32, &inb_off[..])];

        // At w=0.5: exactly the inbetween shape.
        let out = resolve_blend_shape_offsets(0.5, &inbetweens, &prim);
        assert_eq!(out, vec![[0.0, 1.0, 0.0]]);

        // At w=0.75: halfway between inbetween (0, 1, 0) and primary (0, 2, 0).
        let out = resolve_blend_shape_offsets(0.75, &inbetweens, &prim);
        assert_eq!(out, vec![[0.0, 1.5, 0.0]]);
    }

    #[test]
    fn rigid_skinning_combines_weighted_joints_then_geom_bind() {
        let skin = vec![translation(1.0, 0.0, 0.0), translation(0.0, 1.0, 0.0)];
        let m = rigid_skinning_transform(&[0, 1], &[0.5, 0.5], 2, &IDENTITY_MAT4, &skin);
        // Apply to (0, 0, 0): should land at (0.5, 0.5, 0).
        let p = mat4_transform_point(&m, [0.0, 0.0, 0.0]);
        assert_eq!(p, [0.5, 0.5, 0.0]);
    }
}
