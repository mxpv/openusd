//! Row-major double-precision matrix types (`GfMatrix2d`, `GfMatrix3d`,
//! `GfMatrix4d`).

use std::ops::{Index, IndexMut, Mul};

use bytemuck::{Pod, Zeroable};

use super::quat::Quatf;
use super::vec::Vec3f;

/// Row-major 2×2 double-precision matrix (`GfMatrix2d`).
///
/// Element `m[(r, c)]` is row `r`, column `c`; `m[r * 2 + c]` is the
/// flat index. See the module-level [conventions](super) doc.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Zeroable, Pod)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[[f64; 2]; 2]", into = "[[f64; 2]; 2]"))]
pub struct Mat2d(pub [f64; 4]);

impl Mat2d {
    pub const IDENTITY: Mat2d = Mat2d([1.0, 0.0, 0.0, 1.0]);

    /// Component-wise linear interpolation.
    pub fn lerp(self, other: Self, t: f64) -> Self {
        Self(std::array::from_fn(|i| self.0[i] + (other.0[i] - self.0[i]) * t))
    }
}

impl Default for Mat2d {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl From<[f64; 4]> for Mat2d {
    fn from(v: [f64; 4]) -> Self {
        Mat2d(v)
    }
}

impl From<Mat2d> for [f64; 4] {
    fn from(m: Mat2d) -> Self {
        m.0
    }
}

impl From<[[f64; 2]; 2]> for Mat2d {
    fn from(v: [[f64; 2]; 2]) -> Self {
        Self([v[0][0], v[0][1], v[1][0], v[1][1]])
    }
}

impl From<Mat2d> for [[f64; 2]; 2] {
    fn from(m: Mat2d) -> Self {
        [[m.0[0], m.0[1]], [m.0[2], m.0[3]]]
    }
}

impl Index<usize> for Mat2d {
    type Output = f64;
    fn index(&self, i: usize) -> &f64 {
        &self.0[i]
    }
}

impl IndexMut<usize> for Mat2d {
    fn index_mut(&mut self, i: usize) -> &mut f64 {
        &mut self.0[i]
    }
}

impl Index<(usize, usize)> for Mat2d {
    type Output = f64;
    fn index(&self, (r, c): (usize, usize)) -> &f64 {
        &self.0[r * 2 + c]
    }
}

impl IndexMut<(usize, usize)> for Mat2d {
    fn index_mut(&mut self, (r, c): (usize, usize)) -> &mut f64 {
        &mut self.0[r * 2 + c]
    }
}

/// Row-major 3×3 double-precision matrix (`GfMatrix3d`).
///
/// Element `m[(r, c)]` is row `r`, column `c`; `m[r * 3 + c]` is the
/// flat index. See the module-level [conventions](super) doc.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Zeroable, Pod)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[[f64; 3]; 3]", into = "[[f64; 3]; 3]"))]
pub struct Mat3d(pub [f64; 9]);

impl Mat3d {
    pub const IDENTITY: Mat3d = Mat3d([1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0]);

    /// Component-wise linear interpolation.
    pub fn lerp(self, other: Self, t: f64) -> Self {
        Self(std::array::from_fn(|i| self.0[i] + (other.0[i] - self.0[i]) * t))
    }
}

impl Default for Mat3d {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl From<[f64; 9]> for Mat3d {
    fn from(v: [f64; 9]) -> Self {
        Mat3d(v)
    }
}

impl From<Mat3d> for [f64; 9] {
    fn from(m: Mat3d) -> Self {
        m.0
    }
}

impl From<[[f64; 3]; 3]> for Mat3d {
    fn from(v: [[f64; 3]; 3]) -> Self {
        Self([
            v[0][0], v[0][1], v[0][2], v[1][0], v[1][1], v[1][2], v[2][0], v[2][1], v[2][2],
        ])
    }
}

impl From<Mat3d> for [[f64; 3]; 3] {
    fn from(m: Mat3d) -> Self {
        [
            [m.0[0], m.0[1], m.0[2]],
            [m.0[3], m.0[4], m.0[5]],
            [m.0[6], m.0[7], m.0[8]],
        ]
    }
}

impl Index<usize> for Mat3d {
    type Output = f64;
    fn index(&self, i: usize) -> &f64 {
        &self.0[i]
    }
}

impl IndexMut<usize> for Mat3d {
    fn index_mut(&mut self, i: usize) -> &mut f64 {
        &mut self.0[i]
    }
}

impl Index<(usize, usize)> for Mat3d {
    type Output = f64;
    fn index(&self, (r, c): (usize, usize)) -> &f64 {
        &self.0[r * 3 + c]
    }
}

impl IndexMut<(usize, usize)> for Mat3d {
    fn index_mut(&mut self, (r, c): (usize, usize)) -> &mut f64 {
        &mut self.0[r * 3 + c]
    }
}

/// Row-major 4×4 double-precision matrix.
///
/// Element `m[(r, c)]` is row `r`, column `c`; `m[r * 4 + c]` is the
/// equivalent flat index. The translation of a transform lives in the last
/// row (`m[(3, 0)]..=m[(3, 2)]`). See the module-level [conventions](super)
/// doc for the full row-vector contract.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Zeroable, Pod)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[[f64; 4]; 4]", into = "[[f64; 4]; 4]"))]
pub struct Matrix4d(pub [f64; 16]);

impl Matrix4d {
    pub const IDENTITY: Matrix4d = Matrix4d([
        1.0, 0.0, 0.0, 0.0, //
        0.0, 1.0, 0.0, 0.0, //
        0.0, 0.0, 1.0, 0.0, //
        0.0, 0.0, 0.0, 1.0, //
    ]);

    /// Determinant magnitude below which a matrix is treated as singular
    /// in [`inverse`](Self::inverse). Matches Pixar's reference inverter
    /// threshold for skel bind matrices.
    pub const SINGULAR_DETERMINANT: f64 = 1e-12;

    /// Pure-translation matrix. `t` is accepted as any type that
    /// converts to `[f64; 3]`; callers may pass `Vec3f` or `[f64; 3]`
    /// directly.
    pub fn translation(t: impl Into<[f64; 3]>) -> Self {
        let t = t.into();
        let mut m = Self::IDENTITY;
        m.0[12] = t[0];
        m.0[13] = t[1];
        m.0[14] = t[2];
        m
    }

    /// Pure-scale matrix with per-axis factors.
    pub fn scale(s: impl Into<[f64; 3]>) -> Self {
        let s = s.into();
        let mut m = Self::IDENTITY;
        m.0[0] = s[0];
        m.0[5] = s[1];
        m.0[10] = s[2];
        m
    }

    /// Row-major rotation about the X axis by `rad` radians.
    pub fn rotation_x(rad: f64) -> Self {
        let (s, c) = rad.sin_cos();
        let mut m = Self::IDENTITY;
        m.0[5] = c;
        m.0[6] = s;
        m.0[9] = -s;
        m.0[10] = c;
        m
    }

    /// Row-major rotation about the Y axis by `rad` radians.
    pub fn rotation_y(rad: f64) -> Self {
        let (s, c) = rad.sin_cos();
        let mut m = Self::IDENTITY;
        m.0[0] = c;
        m.0[2] = -s;
        m.0[8] = s;
        m.0[10] = c;
        m
    }

    /// Row-major rotation about the Z axis by `rad` radians.
    pub fn rotation_z(rad: f64) -> Self {
        let (s, c) = rad.sin_cos();
        let mut m = Self::IDENTITY;
        m.0[0] = c;
        m.0[1] = s;
        m.0[4] = -s;
        m.0[5] = c;
        m
    }

    /// Component-wise linear interpolation.
    pub fn lerp(self, other: Self, t: f64) -> Self {
        Self(std::array::from_fn(|i| self.0[i] + (other.0[i] - self.0[i]) * t))
    }

    /// Compose a transform from translation, rotation, and scale components.
    /// Follows USD's left-to-right convention: `M = S · R · T`, so
    /// `v_out = v_in · M` applies scale first, then rotation, then translation.
    pub fn from_trs(t: Vec3f, r: Quatf, s: Vec3f) -> Self {
        Self::scale([s.x as f64, s.y as f64, s.z as f64])
            * Self::from_quat([r.w as f64, r.x as f64, r.y as f64, r.z as f64])
            * Self::translation([t.x as f64, t.y as f64, t.z as f64])
    }

    /// Build a rotation matrix from a `(w, x, y, z)` quaternion.
    /// `q` is accepted as any type that converts to `[f64; 4]`; callers
    /// may pass `Quatf` or `[f64; 4]` directly.
    pub fn from_quat(q: impl Into<[f64; 4]>) -> Self {
        let [w, x, y, z] = q.into();
        let xx = x * x;
        let yy = y * y;
        let zz = z * z;
        let xy = x * y;
        let xz = x * z;
        let yz = y * z;
        let wx = w * x;
        let wy = w * y;
        let wz = w * z;
        Matrix4d([
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
        ])
    }

    /// Invert using cofactor expansion. Returns `None` when
    /// `|det| < `[`SINGULAR_DETERMINANT`](Self::SINGULAR_DETERMINANT).
    pub fn inverse(self) -> Option<Matrix4d> {
        let m = &self.0;
        let mut inv = [0.0f64; 16];

        inv[0] = m[5] * m[10] * m[15] - m[5] * m[11] * m[14] - m[9] * m[6] * m[15]
            + m[9] * m[7] * m[14]
            + m[13] * m[6] * m[11]
            - m[13] * m[7] * m[10];
        inv[4] = -m[4] * m[10] * m[15] + m[4] * m[11] * m[14] + m[8] * m[6] * m[15]
            - m[8] * m[7] * m[14]
            - m[12] * m[6] * m[11]
            + m[12] * m[7] * m[10];
        inv[8] = m[4] * m[9] * m[15] - m[4] * m[11] * m[13] - m[8] * m[5] * m[15]
            + m[8] * m[7] * m[13]
            + m[12] * m[5] * m[11]
            - m[12] * m[7] * m[9];
        inv[12] = -m[4] * m[9] * m[14] + m[4] * m[10] * m[13] + m[8] * m[5] * m[14]
            - m[8] * m[6] * m[13]
            - m[12] * m[5] * m[10]
            + m[12] * m[6] * m[9];
        inv[1] = -m[1] * m[10] * m[15] + m[1] * m[11] * m[14] + m[9] * m[2] * m[15]
            - m[9] * m[3] * m[14]
            - m[13] * m[2] * m[11]
            + m[13] * m[3] * m[10];
        inv[5] = m[0] * m[10] * m[15] - m[0] * m[11] * m[14] - m[8] * m[2] * m[15]
            + m[8] * m[3] * m[14]
            + m[12] * m[2] * m[11]
            - m[12] * m[3] * m[10];
        inv[9] = -m[0] * m[9] * m[15] + m[0] * m[11] * m[13] + m[8] * m[1] * m[15]
            - m[8] * m[3] * m[13]
            - m[12] * m[1] * m[11]
            + m[12] * m[3] * m[9];
        inv[13] = m[0] * m[9] * m[14] - m[0] * m[10] * m[13] - m[8] * m[1] * m[14]
            + m[8] * m[2] * m[13]
            + m[12] * m[1] * m[10]
            - m[12] * m[2] * m[9];
        inv[2] =
            m[1] * m[6] * m[15] - m[1] * m[7] * m[14] - m[5] * m[2] * m[15] + m[5] * m[3] * m[14] + m[13] * m[2] * m[7]
                - m[13] * m[3] * m[6];
        inv[6] = -m[0] * m[6] * m[15] + m[0] * m[7] * m[14] + m[4] * m[2] * m[15]
            - m[4] * m[3] * m[14]
            - m[12] * m[2] * m[7]
            + m[12] * m[3] * m[6];
        inv[10] =
            m[0] * m[5] * m[15] - m[0] * m[7] * m[13] - m[4] * m[1] * m[15] + m[4] * m[3] * m[13] + m[12] * m[1] * m[7]
                - m[12] * m[3] * m[5];
        inv[14] = -m[0] * m[5] * m[14] + m[0] * m[6] * m[13] + m[4] * m[1] * m[14]
            - m[4] * m[2] * m[13]
            - m[12] * m[1] * m[6]
            + m[12] * m[2] * m[5];
        inv[3] =
            -m[1] * m[6] * m[11] + m[1] * m[7] * m[10] + m[5] * m[2] * m[11] - m[5] * m[3] * m[10] - m[9] * m[2] * m[7]
                + m[9] * m[3] * m[6];
        inv[7] =
            m[0] * m[6] * m[11] - m[0] * m[7] * m[10] - m[4] * m[2] * m[11] + m[4] * m[3] * m[10] + m[8] * m[2] * m[7]
                - m[8] * m[3] * m[6];
        inv[11] =
            -m[0] * m[5] * m[11] + m[0] * m[7] * m[9] + m[4] * m[1] * m[11] - m[4] * m[3] * m[9] - m[8] * m[1] * m[7]
                + m[8] * m[3] * m[5];
        inv[15] =
            m[0] * m[5] * m[10] - m[0] * m[6] * m[9] - m[4] * m[1] * m[10] + m[4] * m[2] * m[9] + m[8] * m[1] * m[6]
                - m[8] * m[2] * m[5];

        let det = m[0] * inv[0] + m[1] * inv[4] + m[2] * inv[8] + m[3] * inv[12];
        if det.abs() < Self::SINGULAR_DETERMINANT {
            return None;
        }
        let inv_det = 1.0 / det;
        for v in &mut inv {
            *v *= inv_det;
        }
        Some(Matrix4d(inv))
    }

    /// Apply this transform to a position (includes translation).
    /// Equivalent to `(p.x, p.y, p.z, 1) · M`.
    pub fn transform_point(self, p: Vec3f) -> Vec3f {
        let (x, y, z) = (p.x as f64, p.y as f64, p.z as f64);
        let m = &self.0;
        Vec3f {
            x: (x * m[0] + y * m[4] + z * m[8] + m[12]) as f32,
            y: (x * m[1] + y * m[5] + z * m[9] + m[13]) as f32,
            z: (x * m[2] + y * m[6] + z * m[10] + m[14]) as f32,
        }
    }

    /// Apply the rotation/scale part of this transform to a direction
    /// vector (ignores the translation row). Correct for tangents and
    /// velocity-like directions. Normals under non-uniform scale require
    /// the inverse-transpose; for rigid transforms the two are equivalent.
    pub fn transform_vec(self, v: Vec3f) -> Vec3f {
        let (x, y, z) = (v.x as f64, v.y as f64, v.z as f64);
        let m = &self.0;
        Vec3f {
            x: (x * m[0] + y * m[4] + z * m[8]) as f32,
            y: (x * m[1] + y * m[5] + z * m[9]) as f32,
            z: (x * m[2] + y * m[6] + z * m[10]) as f32,
        }
    }
}

impl Default for Matrix4d {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl From<[f64; 16]> for Matrix4d {
    fn from(v: [f64; 16]) -> Self {
        Matrix4d(v)
    }
}

impl From<Matrix4d> for [f64; 16] {
    fn from(m: Matrix4d) -> Self {
        m.0
    }
}

impl From<[[f64; 4]; 4]> for Matrix4d {
    fn from(v: [[f64; 4]; 4]) -> Self {
        Self([
            v[0][0], v[0][1], v[0][2], v[0][3], v[1][0], v[1][1], v[1][2], v[1][3], v[2][0], v[2][1], v[2][2], v[2][3],
            v[3][0], v[3][1], v[3][2], v[3][3],
        ])
    }
}

impl From<Matrix4d> for [[f64; 4]; 4] {
    fn from(m: Matrix4d) -> Self {
        [
            [m.0[0], m.0[1], m.0[2], m.0[3]],
            [m.0[4], m.0[5], m.0[6], m.0[7]],
            [m.0[8], m.0[9], m.0[10], m.0[11]],
            [m.0[12], m.0[13], m.0[14], m.0[15]],
        ]
    }
}

// Gf-type coercions used by translation(), scale(), and from_quat().

impl From<Vec3f> for [f64; 3] {
    fn from(v: Vec3f) -> Self {
        [v.x as f64, v.y as f64, v.z as f64]
    }
}

impl From<Quatf> for [f64; 4] {
    fn from(q: Quatf) -> Self {
        [q.w as f64, q.x as f64, q.y as f64, q.z as f64]
    }
}

/// Matrix product `self · rhs` (row-vector convention).
impl Mul<Matrix4d> for Matrix4d {
    type Output = Matrix4d;
    fn mul(self, rhs: Matrix4d) -> Matrix4d {
        let (a, b) = (&self.0, &rhs.0);
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
        Matrix4d(out)
    }
}

/// Element-wise addition (used for weighted matrix accumulation in rigid
/// skinning).
impl std::ops::Add<Matrix4d> for Matrix4d {
    type Output = Matrix4d;
    fn add(self, rhs: Matrix4d) -> Matrix4d {
        let mut out = self;
        out += rhs;
        out
    }
}

impl std::ops::AddAssign for Matrix4d {
    fn add_assign(&mut self, rhs: Matrix4d) {
        for i in 0..16 {
            self.0[i] += rhs.0[i];
        }
    }
}

/// Scalar scale (used for weighted matrix accumulation in rigid skinning).
impl Mul<f64> for Matrix4d {
    type Output = Matrix4d;
    fn mul(self, s: f64) -> Matrix4d {
        let mut out = self.0;
        for v in &mut out {
            *v *= s;
        }
        Matrix4d(out)
    }
}

impl Index<usize> for Matrix4d {
    type Output = f64;
    fn index(&self, i: usize) -> &f64 {
        &self.0[i]
    }
}

impl IndexMut<usize> for Matrix4d {
    fn index_mut(&mut self, i: usize) -> &mut f64 {
        &mut self.0[i]
    }
}

/// `m[(row, col)]` — row-major two-dimensional element access.
impl Index<(usize, usize)> for Matrix4d {
    type Output = f64;
    fn index(&self, (r, c): (usize, usize)) -> &f64 {
        &self.0[r * 4 + c]
    }
}

impl IndexMut<(usize, usize)> for Matrix4d {
    fn index_mut(&mut self, (r, c): (usize, usize)) -> &mut f64 {
        &mut self.0[r * 4 + c]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn translation(x: f64, y: f64, z: f64) -> Matrix4d {
        Matrix4d::translation([x, y, z])
    }

    #[test]
    fn mul_identity_is_noop() {
        let m = translation(1.0, 2.0, 3.0);
        assert_eq!(Matrix4d::IDENTITY * m, m);
        assert_eq!(m * Matrix4d::IDENTITY, m);
    }

    #[test]
    fn point_transform_applies_translation() {
        let m = translation(10.0, 20.0, 30.0);
        let p = m.transform_point(Vec3f { x: 1.0, y: 2.0, z: 3.0 });
        assert_eq!(
            p,
            Vec3f {
                x: 11.0,
                y: 22.0,
                z: 33.0
            }
        );
    }

    #[test]
    fn vec_transform_ignores_translation() {
        let m = translation(10.0, 20.0, 30.0);
        let v = m.transform_vec(Vec3f { x: 1.0, y: 2.0, z: 3.0 });
        assert_eq!(v, Vec3f { x: 1.0, y: 2.0, z: 3.0 });
    }

    #[test]
    fn inverse_round_trips() {
        let m = translation(5.0, -2.0, 7.0);
        let inv = m.inverse().unwrap();
        let id = m * inv;
        for i in 0..16 {
            assert!((id[i] - Matrix4d::IDENTITY[i]).abs() < 1e-10, "row-col {i}: {id:?}");
        }
    }

    #[test]
    fn inverse_round_trips_with_rotation() {
        let scale = Matrix4d::scale([2.0f64, 3.0, 0.5]);
        let rot_z = {
            let c = 0.8660254037844387_f64;
            let s = 0.5_f64;
            let mut m = Matrix4d::IDENTITY;
            m[(0, 0)] = c;
            m[(0, 1)] = s;
            m[(1, 0)] = -s;
            m[(1, 1)] = c;
            m
        };
        let trans = translation(7.0, -3.0, 11.0);
        let m = scale * rot_z * trans;
        let inv = m.inverse().expect("non-singular");

        let id1 = m * inv;
        let id2 = inv * m;
        for i in 0..16 {
            assert!(
                (id1[i] - Matrix4d::IDENTITY[i]).abs() < 1e-10,
                "M·inv off at {i}: {id1:?}"
            );
            assert!(
                (id2[i] - Matrix4d::IDENTITY[i]).abs() < 1e-10,
                "inv·M off at {i}: {id2:?}"
            );
        }

        let p = Vec3f {
            x: 4.0,
            y: -2.5,
            z: 7.5,
        };
        let warped = m.transform_point(p);
        let back = inv.transform_point(warped);
        for k in 0..3 {
            assert!((back[k] - p[k]).abs() < 1e-4, "point round-trip off: {back:?} vs {p:?}");
        }
    }

    #[test]
    fn inverse_rejects_near_singular() {
        let mut near_singular = Matrix4d([0.0f64; 16]);
        for i in 0..4 {
            near_singular[(i, i)] = 1e-4;
        }
        assert!(near_singular.inverse().is_none(), "should reject near-singular");
        assert!(Matrix4d([0.0f64; 16]).inverse().is_none(), "should reject zero matrix");
    }

    #[test]
    fn translation_layout() {
        let m = Matrix4d::translation([5.0f64, -2.0, 7.0]);
        assert_eq!(&m.0[12..15], &[5.0, -2.0, 7.0]);
        let p = m.transform_point(Vec3f { x: 1.0, y: 1.0, z: 1.0 });
        assert_eq!(
            p,
            Vec3f {
                x: 6.0,
                y: -1.0,
                z: 8.0
            }
        );
    }

    #[test]
    fn scale_layout() {
        let m = Matrix4d::scale([2.0f64, 3.0, 4.0]);
        let p = m.transform_point(Vec3f { x: 1.0, y: 1.0, z: 1.0 });
        assert_eq!(p, Vec3f { x: 2.0, y: 3.0, z: 4.0 });
    }

    #[test]
    fn rotation_x_takes_y_to_z() {
        let m = Matrix4d::rotation_x(std::f64::consts::FRAC_PI_2);
        let p = m.transform_point(Vec3f { x: 0.0, y: 1.0, z: 0.0 });
        assert!(p.x.abs() < 1e-6);
        assert!(p.y.abs() < 1e-6);
        assert!((p.z - 1.0).abs() < 1e-6, "z: {}", p.z);
    }

    #[test]
    fn rotation_y_takes_x_to_neg_z() {
        let m = Matrix4d::rotation_y(std::f64::consts::FRAC_PI_2);
        let p = m.transform_point(Vec3f { x: 1.0, y: 0.0, z: 0.0 });
        assert!(p.x.abs() < 1e-6);
        assert!(p.y.abs() < 1e-6);
        assert!((p.z + 1.0).abs() < 1e-6, "z: {}", p.z);
    }

    #[test]
    fn rotation_z_takes_x_to_y() {
        let m = Matrix4d::rotation_z(std::f64::consts::FRAC_PI_2);
        let p = m.transform_point(Vec3f { x: 1.0, y: 0.0, z: 0.0 });
        assert!(p.x.abs() < 1e-6, "x: {}", p.x);
        assert!((p.y - 1.0).abs() < 1e-6, "y: {}", p.y);
        assert!(p.z.abs() < 1e-6);
    }

    #[test]
    fn identity_quat_gives_identity_matrix() {
        assert_eq!(Matrix4d::from_quat([1.0f64, 0.0, 0.0, 0.0]), Matrix4d::IDENTITY);
    }

    #[test]
    fn quat_90_z_takes_x_to_y() {
        let h = std::f32::consts::FRAC_PI_4;
        let m = Matrix4d::from_quat([h.cos() as f64, 0.0, 0.0, h.sin() as f64]);
        let p = m.transform_point(Vec3f { x: 1.0, y: 0.0, z: 0.0 });
        assert!(p.x.abs() < 1e-5);
        assert!((p.y - 1.0).abs() < 1e-5);
        assert!(p.z.abs() < 1e-5);
    }
}
