//! Row-major double-precision matrix types (`GfMatrix2d`, `GfMatrix3d`,
//! `GfMatrix4d`).

use std::array;
use std::ops::{Index, IndexMut, Mul};

use bytemuck::{Pod, Zeroable};

use super::quat::{Quatd, Quatf, Quath};
use super::vec::{Vec3d, Vec3f};
use super::{MIN_ORTHO_TOLERANCE, MIN_VECTOR_LENGTH, Rotation};

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
        Self(array::from_fn(|i| self.0[i] + (other.0[i] - self.0[i]) * t))
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
        Self(array::from_fn(|i| self.0[i] + (other.0[i] - self.0[i]) * t))
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
pub struct Mat4d(pub [f64; 16]);

impl Mat4d {
    pub const IDENTITY: Mat4d = Mat4d([
        1.0, 0.0, 0.0, 0.0, //
        0.0, 1.0, 0.0, 0.0, //
        0.0, 0.0, 1.0, 0.0, //
        0.0, 0.0, 0.0, 1.0, //
    ]);

    /// The eigenvalue floor C++ `GfMatrix4d::Factor` defaults to, for
    /// [`factor`](Self::factor).
    pub const FACTOR_EPSILON: f64 = 1e-10;

    /// Determinant magnitude at or below which a matrix is treated as
    /// singular in [`inverse`](Self::inverse). Matches Pixar's reference inverter
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

    /// The perspective projection that sees through the window from
    /// `(left, bottom)` to `(right, top)`, between the distances `near` and
    /// `far` along −Z.
    ///
    /// The window stands at a distance of one from the camera, where
    /// `glFrustum`'s is on the near plane. Its size is the tangent of the
    /// field of view whatever `near` is. The matrix carries the volume into
    /// OpenGL clip space, with the near plane at −1 and the far plane at 1
    /// after the divide (C++ `GfFrustum::ComputeProjectionMatrix`).
    pub fn perspective(left: f64, right: f64, bottom: f64, top: f64, near: f64, far: f64) -> Self {
        let (width, height, depth) = (right - left, top - bottom, far - near);
        let mut m = Self::IDENTITY;
        m[(0, 0)] = 2.0 / width;
        m[(1, 1)] = 2.0 / height;
        m[(2, 0)] = (right + left) / width;
        m[(2, 1)] = (top + bottom) / height;
        m[(2, 2)] = -(far + near) / depth;
        m[(2, 3)] = -1.0;
        m[(3, 2)] = -2.0 * near * far / depth;
        m[(3, 3)] = 0.0;
        m
    }

    /// The orthographic projection that sees the box from `(left, bottom)`
    /// to `(right, top)`, between the distances `near` and `far` along −Z.
    ///
    /// The matrix carries the box into OpenGL clip space, with the near
    /// plane at −1 and the far plane at 1 (C++
    /// `GfFrustum::ComputeProjectionMatrix`).
    pub fn orthographic(left: f64, right: f64, bottom: f64, top: f64, near: f64, far: f64) -> Self {
        let (width, height, depth) = (right - left, top - bottom, far - near);
        let mut m = Self::IDENTITY;
        m[(0, 0)] = 2.0 / width;
        m[(1, 1)] = 2.0 / height;
        m[(2, 2)] = -2.0 / depth;
        m[(3, 0)] = -(right + left) / width;
        m[(3, 1)] = -(top + bottom) / height;
        m[(3, 2)] = -(far + near) / depth;
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
        Self(array::from_fn(|i| self.0[i] + (other.0[i] - self.0[i]) * t))
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
        Mat4d([
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

    /// The inverse, or `None` for a matrix whose determinant is no greater
    /// in magnitude than
    /// [`SINGULAR_DETERMINANT`](Self::SINGULAR_DETERMINANT).
    pub fn inverse(self) -> Option<Mat4d> {
        self.inverse_above(Self::SINGULAR_DETERMINANT)
    }

    /// The inverse of a matrix whose determinant is greater than `epsilon`
    /// in magnitude, by cofactor expansion, and `None` for any other (C++
    /// `GetInverse` with its `eps` argument).
    pub fn inverse_above(self, epsilon: f64) -> Option<Mat4d> {
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
        (det.abs() > epsilon).then(|| Mat4d(inv) * (1.0 / det))
    }

    /// The transpose of the matrix (C++ `GetTranspose`).
    pub fn transpose(self) -> Mat4d {
        Mat4d(array::from_fn(|i| self.0[(i % 4) * 4 + i / 4]))
    }

    /// The determinant of the upper-left 3×3 (C++ `GetDeterminant3`).
    pub fn determinant3(self) -> f64 {
        let m = |r: usize, c: usize| self[(r, c)];
        m(0, 0) * m(1, 1) * m(2, 2) + m(0, 1) * m(1, 2) * m(2, 0) + m(0, 2) * m(1, 0) * m(2, 1)
            - m(0, 0) * m(1, 2) * m(2, 1)
            - m(0, 1) * m(1, 0) * m(2, 2)
            - m(0, 2) * m(1, 1) * m(2, 0)
    }

    /// Replace the translation of the transform, its last row, and set the
    /// homogeneous coordinate of that row to one (C++ `SetTranslateOnly`).
    /// The rotation and scale stay as they are.
    pub fn set_translation(&mut self, translation: Vec3d) {
        self.0[12] = translation.x;
        self.0[13] = translation.y;
        self.0[14] = translation.z;
        self.0[15] = 1.0;
    }

    /// The translation of the transform, its last row (C++
    /// `ExtractTranslation`).
    pub fn extract_translation(self) -> Vec3d {
        Vec3d {
            x: self.0[12],
            y: self.0[13],
            z: self.0[14],
        }
    }

    /// The rotation of the upper-left 3×3 as a quaternion (C++
    /// `ExtractRotationQuat`). The 3×3 is taken to be a pure rotation: scale
    /// or shear in it skews the answer.
    pub fn extract_rotation_quat(self) -> Quatd {
        let m = |r: usize, c: usize| self[(r, c)];
        // The largest diagonal entry keeps the divisor away from zero.
        let i = if m(0, 0) > m(1, 1) {
            if m(0, 0) > m(2, 2) { 0 } else { 2 }
        } else if m(1, 1) > m(2, 2) {
            1
        } else {
            2
        };

        let mut im = [0.0; 3];
        let real;
        if m(0, 0) + m(1, 1) + m(2, 2) > m(i, i) {
            real = 0.5 * (m(0, 0) + m(1, 1) + m(2, 2) + m(3, 3)).sqrt();
            im = [
                (m(1, 2) - m(2, 1)) / (4.0 * real),
                (m(2, 0) - m(0, 2)) / (4.0 * real),
                (m(0, 1) - m(1, 0)) / (4.0 * real),
            ];
        } else {
            let (j, k) = ((i + 1) % 3, (i + 2) % 3);
            let q = 0.5 * (m(i, i) - m(j, j) - m(k, k) + m(3, 3)).sqrt();
            im[i] = q;
            im[j] = (m(i, j) + m(j, i)) / (4.0 * q);
            im[k] = (m(k, i) + m(i, k)) / (4.0 * q);
            real = (m(j, k) - m(k, j)) / (4.0 * q);
        }
        Quatd {
            w: real.clamp(-1.0, 1.0),
            x: im[0],
            y: im[1],
            z: im[2],
        }
    }

    /// The rotation of the upper-left 3×3 (C++ `ExtractRotation`), on the
    /// terms of [`extract_rotation_quat`](Self::extract_rotation_quat).
    pub fn extract_rotation(self) -> Rotation {
        Rotation::from_quat(self.extract_rotation_quat())
    }

    /// Make the rows of the upper-left 3×3 orthogonal and of unit length, and
    /// divide a homogeneous coordinate other than one or zero out of the
    /// translation (C++ `Orthonormalize`).
    ///
    /// Returns `false` when the rows did not settle on an orthonormal basis,
    /// in which case the matrix holds the closest estimate reached.
    pub fn orthonormalize(&mut self) -> bool {
        let row = |m: &Mat4d, r: usize| Vec3d {
            x: m[(r, 0)],
            y: m[(r, 1)],
            z: m[(r, 2)],
        };
        let (mut r0, mut r1, mut r2) = (row(self, 0), row(self, 1), row(self, 2));
        let converged = Vec3d::orthogonalize_basis(&mut r0, &mut r1, &mut r2, true, MIN_ORTHO_TOLERANCE);
        for (r, v) in [r0, r1, r2].into_iter().enumerate() {
            self[(r, 0)] = v.x;
            self[(r, 1)] = v.y;
            self[(r, 2)] = v.z;
        }

        let w = self.0[15];
        if w != 1.0 && w.abs() >= MIN_VECTOR_LENGTH {
            for i in 12..15 {
                self.0[i] /= w;
            }
            self.0[15] = 1.0;
        }
        converged
    }

    /// Factor the matrix into scale, rotation and translation (C++
    /// `Factor`), reading `self` as `r · s · rᵀ · u · t`.
    ///
    /// An eigenvalue of the upper-left 3×3 below `eps` scales by `eps`, so a
    /// singular matrix still factors; [`Factors::singular`] reports it.
    pub fn factor(self, eps: f64) -> Factors {
        // The upper-left 3×3 on its own, and the translation beside it.
        let mut a = self;
        for i in 0..3 {
            a[(3, i)] = 0.0;
            a[(i, 3)] = 0.0;
        }
        a[(3, 3)] = 1.0;

        let det = a.determinant3();
        let det_sign = if det < 0.0 { -1.0 } else { 1.0 };

        // The eigenvectors of `a · aᵀ` are the scale orientation, and the
        // roots of its eigenvalues the scales.
        let (eigenvalues, eigenvectors) = (a * a.transpose()).jacobi3();
        let mut scale_orientation = Mat4d::IDENTITY;
        for (r, vector) in eigenvectors.into_iter().enumerate() {
            for c in 0..3 {
                scale_orientation[(r, c)] = vector[c];
            }
        }

        let scale = eigenvalues.map(|value| det_sign * if value < eps { eps } else { value.sqrt() });
        let rotation = scale_orientation * Mat4d::scale(scale.map(|s| 1.0 / s)) * scale_orientation.transpose() * a;
        Factors {
            scale_orientation,
            scale: Vec3d {
                x: scale[0],
                y: scale[1],
                z: scale[2],
            },
            rotation,
            translation: self.extract_translation(),
            singular: det * det_sign < eps,
        }
    }

    /// The eigenvalues and eigenvectors of the symmetric upper-left 3×3, by
    /// Jacobi iteration (C++ `_Jacobi3`). Eigenvector `i` is
    /// `[vectors[0][i], vectors[1][i], vectors[2][i]]`.
    fn jacobi3(self) -> ([f64; 3], [[f64; 3]; 3]) {
        let mut values = [self[(0, 0)], self[(1, 1)], self[(2, 2)]];
        let mut vectors = [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]];
        let mut a = self;
        let mut b = values;
        let mut z = [0.0; 3];

        for sweep in 0..50 {
            let off_diagonal = a[(0, 1)].abs() + a[(0, 2)].abs() + a[(1, 2)].abs();
            if off_diagonal == 0.0 {
                break;
            }
            let threshold = if sweep < 3 { 0.2 * off_diagonal / 9.0 } else { 0.0 };

            for p in 0..3 {
                for q in p + 1..3 {
                    let g = 100.0 * a[(p, q)].abs();
                    if sweep > 3 && values[p].abs() + g == values[p].abs() && values[q].abs() + g == values[q].abs() {
                        a[(p, q)] = 0.0;
                    } else if a[(p, q)].abs() > threshold {
                        let mut h = values[q] - values[p];
                        // The tangent of the rotation angle.
                        let t = if h.abs() + g == h.abs() {
                            a[(p, q)] / h
                        } else {
                            let theta = 0.5 * h / a[(p, q)];
                            let t = 1.0 / (theta.abs() + (1.0 + theta * theta).sqrt());
                            if theta < 0.0 { -t } else { t }
                        };
                        let c = 1.0 / (1.0 + t * t).sqrt();
                        let s = t * c;
                        let tau = s / (1.0 + c);
                        h = t * a[(p, q)];
                        z[p] -= h;
                        z[q] += h;
                        values[p] -= h;
                        values[q] += h;
                        a[(p, q)] = 0.0;

                        let rotate = |a: &mut Mat4d, first: (usize, usize), second: (usize, usize)| {
                            let (g, h) = (a[first], a[second]);
                            a[first] = g - s * (h + g * tau);
                            a[second] = h + s * (g - h * tau);
                        };
                        for j in 0..p {
                            rotate(&mut a, (j, p), (j, q));
                        }
                        for j in p + 1..q {
                            rotate(&mut a, (p, j), (j, q));
                        }
                        for j in q + 1..3 {
                            rotate(&mut a, (p, j), (q, j));
                        }
                        for vector in &mut vectors {
                            let (g, h) = (vector[p], vector[q]);
                            vector[p] = g - s * (h + g * tau);
                            vector[q] = h + s * (g - h * tau);
                        }
                    }
                }
            }
            for p in 0..3 {
                b[p] += z[p];
                values[p] = b[p];
                z[p] = 0.0;
            }
        }
        (values, vectors)
    }

    /// The point `p` under this transform (C++ `Transform`): `(p.x, p.y,
    /// p.z, 1) · M`, divided through by the homogeneous coordinate that
    /// gives. A coordinate of zero divides by one.
    pub fn transform(self, p: Vec3d) -> Vec3d {
        let m = &self.0;
        let w = match p.x * m[3] + p.y * m[7] + p.z * m[11] + m[15] {
            0.0 => 1.0,
            w => w,
        };
        self.transform_affine(p) * (1.0 / w)
    }

    /// The point `p` under this transform, taken to be affine (C++
    /// `TransformAffine`): the first three components of `(p.x, p.y, p.z, 1)
    /// · M`, with no division by the fourth.
    pub fn transform_affine(self, p: Vec3d) -> Vec3d {
        let m = &self.0;
        Vec3d {
            x: p.x * m[0] + p.y * m[4] + p.z * m[8] + m[12],
            y: p.x * m[1] + p.y * m[5] + p.z * m[9] + m[13],
            z: p.x * m[2] + p.y * m[6] + p.z * m[10] + m[14],
        }
    }

    /// The direction `v` under the rotation and scale of this transform,
    /// its translation left out (C++ `TransformDir`). Correct for tangents
    /// and velocity-like directions. Normals under non-uniform scale require
    /// the inverse-transpose; for rigid transforms the two are equivalent.
    pub fn transform_dir(self, v: Vec3d) -> Vec3d {
        let m = &self.0;
        Vec3d {
            x: v.x * m[0] + v.y * m[4] + v.z * m[8],
            y: v.x * m[1] + v.y * m[5] + v.z * m[9],
            z: v.x * m[2] + v.y * m[6] + v.z * m[10],
        }
    }
}

/// What [`Mat4d::factor`] takes a matrix apart into (C++
/// `GfMatrix4d::Factor`): the matrix is `r · s · rᵀ · u · t`, for the scale
/// orientation `r`, the scale `s`, the rotation `u` and the translation `t`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Factors {
    /// The rotation into the axes the scale applies along.
    pub scale_orientation: Mat4d,
    /// The scale along each of those axes, negative for a matrix that flips
    /// handedness.
    pub scale: Vec3d,
    /// The rotation, which keeps any shear the matrix has.
    pub rotation: Mat4d,
    /// The translation.
    pub translation: Vec3d,
    /// `true` when the upper-left 3×3 has no inverse.
    pub singular: bool,
}

impl Default for Mat4d {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl From<[f64; 16]> for Mat4d {
    fn from(v: [f64; 16]) -> Self {
        Mat4d(v)
    }
}

impl From<Mat4d> for [f64; 16] {
    fn from(m: Mat4d) -> Self {
        m.0
    }
}

impl From<[[f64; 4]; 4]> for Mat4d {
    fn from(v: [[f64; 4]; 4]) -> Self {
        Self([
            v[0][0], v[0][1], v[0][2], v[0][3], v[1][0], v[1][1], v[1][2], v[1][3], v[2][0], v[2][1], v[2][2], v[2][3],
            v[3][0], v[3][1], v[3][2], v[3][3],
        ])
    }
}

impl From<Mat4d> for [[f64; 4]; 4] {
    fn from(m: Mat4d) -> Self {
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

impl From<Quath> for [f64; 4] {
    fn from(q: Quath) -> Self {
        [q.w.to_f64(), q.x.to_f64(), q.y.to_f64(), q.z.to_f64()]
    }
}

impl From<Quatf> for [f64; 4] {
    fn from(q: Quatf) -> Self {
        [q.w as f64, q.x as f64, q.y as f64, q.z as f64]
    }
}

/// Matrix product `self · rhs` (row-vector convention).
impl Mul<Mat4d> for Mat4d {
    type Output = Mat4d;
    fn mul(self, rhs: Mat4d) -> Mat4d {
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
        Mat4d(out)
    }
}

/// Element-wise addition (used for weighted matrix accumulation in rigid
/// skinning).
impl std::ops::Add<Mat4d> for Mat4d {
    type Output = Mat4d;
    fn add(self, rhs: Mat4d) -> Mat4d {
        let mut out = self;
        out += rhs;
        out
    }
}

impl std::ops::AddAssign for Mat4d {
    fn add_assign(&mut self, rhs: Mat4d) {
        for i in 0..16 {
            self.0[i] += rhs.0[i];
        }
    }
}

/// Scalar scale (used for weighted matrix accumulation in rigid skinning).
impl Mul<f64> for Mat4d {
    type Output = Mat4d;
    fn mul(self, s: f64) -> Mat4d {
        let mut out = self.0;
        for v in &mut out {
            *v *= s;
        }
        Mat4d(out)
    }
}

impl Index<usize> for Mat4d {
    type Output = f64;
    fn index(&self, i: usize) -> &f64 {
        &self.0[i]
    }
}

impl IndexMut<usize> for Mat4d {
    fn index_mut(&mut self, i: usize) -> &mut f64 {
        &mut self.0[i]
    }
}

/// `m[(row, col)]` — row-major two-dimensional element access.
impl Index<(usize, usize)> for Mat4d {
    type Output = f64;
    fn index(&self, (r, c): (usize, usize)) -> &f64 {
        &self.0[r * 4 + c]
    }
}

impl IndexMut<(usize, usize)> for Mat4d {
    fn index_mut(&mut self, (r, c): (usize, usize)) -> &mut f64 {
        &mut self.0[r * 4 + c]
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    fn translation(x: f64, y: f64, z: f64) -> Mat4d {
        Mat4d::translation([x, y, z])
    }

    #[test]
    fn mul_identity_is_noop() {
        let m = translation(1.0, 2.0, 3.0);
        assert_eq!(Mat4d::IDENTITY * m, m);
        assert_eq!(m * Mat4d::IDENTITY, m);
    }

    #[test]
    fn point_transform_applies_translation() {
        let m = translation(10.0, 20.0, 30.0);
        let p = m.transform_affine(Vec3d { x: 1.0, y: 2.0, z: 3.0 });
        assert_eq!(
            p,
            Vec3d {
                x: 11.0,
                y: 22.0,
                z: 33.0
            }
        );
    }

    #[test]
    fn vec_transform_ignores_translation() {
        let m = translation(10.0, 20.0, 30.0);
        let v = m.transform_dir(Vec3d { x: 1.0, y: 2.0, z: 3.0 });
        assert_eq!(v, Vec3d { x: 1.0, y: 2.0, z: 3.0 });
    }

    #[test]
    fn inverse_round_trips() {
        let m = translation(5.0, -2.0, 7.0);
        let inv = m.inverse().unwrap();
        let id = m * inv;
        for i in 0..16 {
            assert!((id[i] - Mat4d::IDENTITY[i]).abs() < 1e-10, "row-col {i}: {id:?}");
        }
    }

    #[test]
    fn inverse_round_trips_with_rotation() {
        let scale = Mat4d::scale([2.0f64, 3.0, 0.5]);
        let rot_z = {
            let c = 0.8660254037844387_f64;
            let s = 0.5_f64;
            let mut m = Mat4d::IDENTITY;
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
            assert!((id1[i] - Mat4d::IDENTITY[i]).abs() < 1e-10, "M·inv off at {i}: {id1:?}");
            assert!((id2[i] - Mat4d::IDENTITY[i]).abs() < 1e-10, "inv·M off at {i}: {id2:?}");
        }

        let p = Vec3d {
            x: 4.0,
            y: -2.5,
            z: 7.5,
        };
        let warped = m.transform_affine(p);
        let back = inv.transform_affine(warped);
        for k in 0..3 {
            assert!((back[k] - p[k]).abs() < 1e-4, "point round-trip off: {back:?} vs {p:?}");
        }
    }

    #[test]
    fn inverse_rejects_near_singular() {
        let mut near_singular = Mat4d([0.0f64; 16]);
        for i in 0..4 {
            near_singular[(i, i)] = 1e-4;
        }
        assert!(near_singular.inverse().is_none(), "should reject near-singular");
        assert!(Mat4d([0.0f64; 16]).inverse().is_none(), "should reject zero matrix");
    }

    #[test]
    fn translation_layout() {
        let m = Mat4d::translation([5.0f64, -2.0, 7.0]);
        assert_eq!(&m.0[12..15], &[5.0, -2.0, 7.0]);
        let p = m.transform_affine(Vec3d { x: 1.0, y: 1.0, z: 1.0 });
        assert_eq!(
            p,
            Vec3d {
                x: 6.0,
                y: -1.0,
                z: 8.0
            }
        );
    }

    #[test]
    fn scale_layout() {
        let m = Mat4d::scale([2.0f64, 3.0, 4.0]);
        let p = m.transform_affine(Vec3d { x: 1.0, y: 1.0, z: 1.0 });
        assert_eq!(p, Vec3d { x: 2.0, y: 3.0, z: 4.0 });
    }

    #[test]
    fn rotation_x_takes_y_to_z() {
        let m = Mat4d::rotation_x(std::f64::consts::FRAC_PI_2);
        let p = m.transform_affine(Vec3d { x: 0.0, y: 1.0, z: 0.0 });
        assert!(p.x.abs() < 1e-6);
        assert!(p.y.abs() < 1e-6);
        assert!((p.z - 1.0).abs() < 1e-6, "z: {}", p.z);
    }

    #[test]
    fn rotation_y_takes_x_to_neg_z() {
        let m = Mat4d::rotation_y(std::f64::consts::FRAC_PI_2);
        let p = m.transform_affine(Vec3d { x: 1.0, y: 0.0, z: 0.0 });
        assert!(p.x.abs() < 1e-6);
        assert!(p.y.abs() < 1e-6);
        assert!((p.z + 1.0).abs() < 1e-6, "z: {}", p.z);
    }

    #[test]
    fn rotation_z_takes_x_to_y() {
        let m = Mat4d::rotation_z(std::f64::consts::FRAC_PI_2);
        let p = m.transform_affine(Vec3d { x: 1.0, y: 0.0, z: 0.0 });
        assert!(p.x.abs() < 1e-6, "x: {}", p.x);
        assert!((p.y - 1.0).abs() < 1e-6, "y: {}", p.y);
        assert!(p.z.abs() < 1e-6);
    }

    #[test]
    fn identity_quat_gives_identity_matrix() {
        assert_eq!(Mat4d::from_quat([1.0f64, 0.0, 0.0, 0.0]), Mat4d::IDENTITY);
    }

    #[test]
    fn quat_90_z_takes_x_to_y() {
        let h = std::f32::consts::FRAC_PI_4;
        let m = Mat4d::from_quat([h.cos() as f64, 0.0, 0.0, h.sin() as f64]);
        let p = m.transform_affine(Vec3d { x: 1.0, y: 0.0, z: 0.0 });
        assert!(p.x.abs() < 1e-5);
        assert!((p.y - 1.0).abs() < 1e-5);
        assert!(p.z.abs() < 1e-5);
    }

    pub(crate) fn assert_close(got: Mat4d, want: Mat4d) {
        for i in 0..16 {
            assert!((got[i] - want[i]).abs() < 1e-9, "{got:?} != {want:?}");
        }
    }

    /// The inverse exists for a determinant above the threshold asked for.
    #[test]
    fn inverse_threshold() {
        let small = Mat4d::scale([1e-5, 1e-5, 1e-5]);
        assert_eq!(small.inverse(), None);
        let inverse = small.inverse_above(1e-16).expect("above the threshold");
        assert_close(inverse * small, Mat4d::IDENTITY);
        assert_eq!(Mat4d::scale([1.0, 0.0, 1.0]).inverse_above(0.0), None);
    }

    /// A point takes the translation, and a projective row divides through.
    #[test]
    fn transform_double_point() {
        let m = Mat4d::scale([2.0, 2.0, 2.0]) * translation(1.0, 0.0, 0.0);
        let p = Vec3d { x: 1.0, y: 2.0, z: 3.0 };
        assert_eq!(m.transform(p), Vec3d { x: 3.0, y: 4.0, z: 6.0 });

        let mut projective = Mat4d::IDENTITY;
        projective[(3, 3)] = 2.0;
        assert_eq!(projective.transform(p), Vec3d { x: 0.5, y: 1.0, z: 1.5 });
        projective[(3, 3)] = 0.0;
        assert_eq!(projective.transform(p), p);
    }

    #[test]
    fn transpose_swaps_rows() {
        let m = translation(1.0, 2.0, 3.0);
        let t = m.transpose();
        assert_eq!([t[(0, 3)], t[(1, 3)], t[(2, 3)]], [1.0, 2.0, 3.0]);
        assert_eq!(t.transpose(), m);
    }

    #[test]
    fn determinant3_of_scale() {
        let m = Mat4d::scale([2.0, 3.0, 4.0]) * translation(9.0, 9.0, 9.0);
        assert_eq!(m.determinant3(), 24.0);
        assert_eq!(Mat4d::rotation_y(0.7).determinant3().round(), 1.0);
    }

    /// A rotation matrix reads back as the rotation that made it, whichever
    /// diagonal entry is largest.
    #[test]
    fn extract_rotation_round_trips() {
        for (axis, degrees) in [
            (Vec3d { x: 1.0, y: 2.0, z: 3.0 }, 40.0),
            (Vec3d { x: 1.0, y: 0.0, z: 0.0 }, 170.0),
            (Vec3d { x: 0.0, y: 1.0, z: 0.0 }, 170.0),
            (Vec3d { x: 0.0, y: 0.0, z: 1.0 }, 170.0),
        ] {
            let m = Mat4d::from_quat(Rotation::new(axis, degrees).quat()) * translation(1.0, 2.0, 3.0);
            assert_eq!(m.extract_translation(), Vec3d { x: 1.0, y: 2.0, z: 3.0 });
            let back = Mat4d::from_quat(m.extract_rotation().quat()) * translation(1.0, 2.0, 3.0);
            assert_close(back, m);
        }
    }

    /// Rows a little off orthonormal settle onto the basis they are near.
    #[test]
    fn orthonormalize_settles() {
        let rotation = Mat4d::rotation_z(0.3) * Mat4d::rotation_x(1.1);
        let mut m = rotation;
        m[(0, 1)] += 1e-4;
        m[(2, 0)] -= 1e-4;
        assert!(m.orthonormalize());
        for i in 0..16 {
            assert!((m[i] - rotation[i]).abs() < 1e-3);
        }
        let product = m * m.transpose();
        for i in 0..16 {
            assert!((product[i] - Mat4d::IDENTITY[i]).abs() < 1e-6, "{product:?}");
        }

        // Two colinear rows have no basis to settle onto.
        let mut colinear = Mat4d::IDENTITY;
        colinear[(1, 0)] = 1.0;
        colinear[(1, 1)] = 0.0;
        assert!(!colinear.orthonormalize());
    }

    #[test]
    fn orthonormalize_divides_w() {
        let mut m = translation(2.0, 4.0, 6.0);
        m[(3, 3)] = 2.0;
        assert!(m.orthonormalize());
        assert_eq!(m, translation(1.0, 2.0, 3.0));
    }

    /// The factors of a scaled, rotated and translated matrix multiply back
    /// to it.
    #[test]
    fn factor_recomposes() {
        let rotation = Mat4d::rotation_x(0.4) * Mat4d::rotation_y(-1.2) * Mat4d::rotation_z(2.0);
        let m = Mat4d::scale([1.0, 2.0, 3.0]) * rotation * translation(10.0, 20.0, 30.0);
        let f = m.factor(1e-10);
        assert!(!f.singular);
        assert_eq!(
            f.translation,
            Vec3d {
                x: 10.0,
                y: 20.0,
                z: 30.0
            }
        );

        let mut scales: [f64; 3] = f.scale.into();
        scales.sort_by(f64::total_cmp);
        for (got, want) in scales.into_iter().zip([1.0, 2.0, 3.0]) {
            assert!((got - want).abs() < 1e-9, "{scales:?}");
        }
        let recomposed = f.scale_orientation
            * Mat4d::scale(f.scale)
            * f.scale_orientation.transpose()
            * f.rotation
            * Mat4d::translation(f.translation);
        assert_close(recomposed, m);
        assert_close(f.rotation * f.rotation.transpose(), Mat4d::IDENTITY);
    }

    /// A mirrored matrix factors with negative scales, and a flattened one
    /// reports that it is singular.
    #[test]
    fn factor_sign_and_singular() {
        let mirrored = Mat4d::scale([-1.0, 2.0, 3.0]).factor(1e-10);
        assert!(!mirrored.singular);
        let scales: [f64; 3] = mirrored.scale.into();
        assert!(scales.iter().all(|s| *s < 0.0), "{scales:?}");

        let flat = Mat4d::scale([1.0, 0.0, 1.0]).factor(1e-10);
        assert!(flat.singular);
    }
}
