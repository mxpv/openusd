//! Small 4×4 matrix helpers shared by the schema layer.
//!
//! USD authors transforms as `matrix4d` — a row-major 4×4 stored as
//! a flat `[f64; 16]`. UsdGeomXformable composes them left-to-right
//! against row vectors (`v_out = v_in · M`); UsdSkel's bind / skinning
//! transforms use the same convention. These helpers express that
//! shared algebra so the schema modules can share one implementation
//! instead of each shipping its own.
//!
//! The functions intentionally take `&[f64; 16]` rather than a wrapper
//! struct so callers can keep using their own math library at the
//! edges and only convert at the call site. There is no top-level
//! `Mat4` type here — Pixar's `Gf` analogues can be added later if a
//! richer surface becomes useful.

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
/// vector. Ignores the translation row.
///
/// This is the correct transform for tangents and velocity-like
/// directions. Normals under non-uniform scale technically require
/// the inverse-transpose; for rigid (rotation-only) transforms and
/// uniform scale the two are equivalent.
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
pub const MAT4_SINGULAR_DETERMINANT: f64 = 1e-12;

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

/// Pure-translation row-major 4×4. Loads `t` into the translation
/// row (`m[12..=14]`); rotation/scale block is identity.
pub fn mat4_translation<T: Into<f64> + Copy>(t: [T; 3]) -> [f64; 16] {
    let mut m = IDENTITY_MAT4;
    m[12] = t[0].into();
    m[13] = t[1].into();
    m[14] = t[2].into();
    m
}

/// Pure-scale row-major 4×4 with per-axis factors on the diagonal.
pub fn mat4_scale<T: Into<f64> + Copy>(s: [T; 3]) -> [f64; 16] {
    let mut m = IDENTITY_MAT4;
    m[0] = s[0].into();
    m[5] = s[1].into();
    m[10] = s[2].into();
    m
}

/// Row-major rotation about the X axis by `rad` radians.
pub fn mat4_rotation_x(rad: f64) -> [f64; 16] {
    let (s, c) = rad.sin_cos();
    let mut m = IDENTITY_MAT4;
    m[5] = c;
    m[6] = s;
    m[9] = -s;
    m[10] = c;
    m
}

/// Row-major rotation about the Y axis by `rad` radians.
pub fn mat4_rotation_y(rad: f64) -> [f64; 16] {
    let (s, c) = rad.sin_cos();
    let mut m = IDENTITY_MAT4;
    m[0] = c;
    m[2] = -s;
    m[8] = s;
    m[10] = c;
    m
}

/// Row-major rotation about the Z axis by `rad` radians.
pub fn mat4_rotation_z(rad: f64) -> [f64; 16] {
    let (s, c) = rad.sin_cos();
    let mut m = IDENTITY_MAT4;
    m[0] = c;
    m[1] = s;
    m[4] = -s;
    m[5] = c;
    m
}

/// Convert a `(w, x, y, z)` quaternion to a row-major 4×4 rotation
/// matrix. The translation row is identity.
pub fn mat4_from_quat<T: Into<f64> + Copy>(q: [T; 4]) -> [f64; 16] {
    let w = q[0].into();
    let x = q[1].into();
    let y = q[2].into();
    let z = q[3].into();
    let xx = x * x;
    let yy = y * y;
    let zz = z * z;
    let xy = x * y;
    let xz = x * z;
    let yz = y * z;
    let wx = w * x;
    let wy = w * y;
    let wz = w * z;
    [
        1.0 - 2.0 * (yy + zz),
        2.0 * (xy + wz),
        2.0 * (xz - wy),
        0.0,
        2.0 * (xy - wz),
        1.0 - 2.0 * (xx + zz),
        2.0 * (yz + wx),
        0.0,
        2.0 * (xz + wy),
        2.0 * (yz - wx),
        1.0 - 2.0 * (xx + yy),
        0.0,
        0.0,
        0.0,
        0.0,
        1.0,
    ]
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
    fn translation_layout_matches_row_major() {
        let m = mat4_translation([5.0, -2.0, 7.0]);
        assert_eq!(&m[12..15], &[5.0, -2.0, 7.0]);
        let p = mat4_transform_point(&m, [1.0, 1.0, 1.0]);
        assert_eq!(p, [6.0, -1.0, 8.0]);
    }

    #[test]
    fn scale_layout_matches_row_major() {
        let m = mat4_scale([2.0, 3.0, 4.0]);
        let p = mat4_transform_point(&m, [1.0, 1.0, 1.0]);
        assert_eq!(p, [2.0, 3.0, 4.0]);
    }

    #[test]
    fn rotation_x_takes_y_to_z() {
        let m = mat4_rotation_x(std::f64::consts::FRAC_PI_2);
        let p = mat4_transform_point(&m, [0.0, 1.0, 0.0]);
        assert!(p[0].abs() < 1e-6);
        assert!(p[1].abs() < 1e-6);
        assert!((p[2] - 1.0).abs() < 1e-6, "z: {}", p[2]);
    }

    #[test]
    fn rotation_y_takes_x_to_neg_z() {
        let m = mat4_rotation_y(std::f64::consts::FRAC_PI_2);
        let p = mat4_transform_point(&m, [1.0, 0.0, 0.0]);
        assert!(p[0].abs() < 1e-6);
        assert!(p[1].abs() < 1e-6);
        assert!((p[2] + 1.0).abs() < 1e-6, "z: {}", p[2]);
    }

    #[test]
    fn rotation_z_takes_x_to_y() {
        let m = mat4_rotation_z(std::f64::consts::FRAC_PI_2);
        let p = mat4_transform_point(&m, [1.0, 0.0, 0.0]);
        assert!(p[0].abs() < 1e-6, "x: {}", p[0]);
        assert!((p[1] - 1.0).abs() < 1e-6, "y: {}", p[1]);
        assert!(p[2].abs() < 1e-6);
    }

    #[test]
    fn identity_quat_to_matrix_is_identity() {
        assert_eq!(mat4_from_quat([1.0, 0.0, 0.0, 0.0]), IDENTITY_MAT4);
    }

    #[test]
    fn quat_90_about_z_takes_x_to_y() {
        // q = (cos(45°), 0, 0, sin(45°)) = 90° about +Z.
        let h = std::f32::consts::FRAC_PI_4;
        let m = mat4_from_quat([h.cos(), 0.0, 0.0, h.sin()]);
        let p = mat4_transform_point(&m, [1.0, 0.0, 0.0]);
        assert!(p[0].abs() < 1e-5);
        assert!((p[1] - 1.0).abs() < 1e-5);
        assert!(p[2].abs() < 1e-5);
    }
}
