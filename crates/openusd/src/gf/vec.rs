//! `GfVec` — fixed-arity vector types.
//!
//! All arithmetic derives (Add, Sub, Neg, Mul, Sum) work because the
//! underlying scalar fields (f32, f64, f16, i32) all implement the
//! corresponding traits. `#[derive(Mul)]` generates scalar multiplication
//! (`vec * scalar_type`), which is the form most commonly needed in USD schema
//! code (e.g. `point * weight` in LBS accumulation).
//!
//! `From<[T; N]>` and `From<VecNt> for [T; N]` bridge to raw arrays —
//! and therefore to any other math library — at zero cost.

use std::ops::{Index, IndexMut};

use super::MIN_VECTOR_LENGTH;

use bytemuck::{Pod, Zeroable};
use derive_more::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign, Sum};

use super::f16;

/// 2-component single-precision float vector (`GfVec2f`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f32; 2]", into = "[f32; 2]"))]
pub struct Vec2f {
    pub x: f32,
    pub y: f32,
}

impl From<[f32; 2]> for Vec2f {
    #[inline]
    fn from([x, y]: [f32; 2]) -> Self {
        Self { x, y }
    }
}

impl From<Vec2f> for [f32; 2] {
    #[inline]
    fn from(v: Vec2f) -> Self {
        [v.x, v.y]
    }
}

impl Index<usize> for Vec2f {
    type Output = f32;
    #[inline]
    fn index(&self, i: usize) -> &f32 {
        match i {
            0 => &self.x,
            1 => &self.y,
            _ => panic!("index {i} out of bounds for Vec2f"),
        }
    }
}

impl IndexMut<usize> for Vec2f {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut f32 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            _ => panic!("index {i} out of bounds for Vec2f"),
        }
    }
}

impl Vec2f {
    pub fn lerp(self, other: Self, t: f32) -> Self {
        self + (other - self) * t
    }
}

/// 2-component double-precision float vector (`GfVec2d`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f64; 2]", into = "[f64; 2]"))]
pub struct Vec2d {
    pub x: f64,
    pub y: f64,
}

impl From<[f64; 2]> for Vec2d {
    #[inline]
    fn from([x, y]: [f64; 2]) -> Self {
        Self { x, y }
    }
}

impl From<Vec2d> for [f64; 2] {
    #[inline]
    fn from(v: Vec2d) -> Self {
        [v.x, v.y]
    }
}

impl Index<usize> for Vec2d {
    type Output = f64;
    #[inline]
    fn index(&self, i: usize) -> &f64 {
        match i {
            0 => &self.x,
            1 => &self.y,
            _ => panic!("index {i} out of bounds for Vec2d"),
        }
    }
}

impl IndexMut<usize> for Vec2d {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut f64 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            _ => panic!("index {i} out of bounds for Vec2d"),
        }
    }
}

impl Vec2d {
    /// The lesser of this vector and `other` along each axis. A component
    /// that is NaN in one is taken from the other.
    pub fn min(self, other: Vec2d) -> Vec2d {
        Vec2d {
            x: self.x.min(other.x),
            y: self.y.min(other.y),
        }
    }

    /// The greater of this vector and `other` along each axis. A component
    /// that is NaN in one is taken from the other.
    pub fn max(self, other: Vec2d) -> Vec2d {
        Vec2d {
            x: self.x.max(other.x),
            y: self.y.max(other.y),
        }
    }

    pub fn lerp(self, other: Self, t: f64) -> Self {
        self + (other - self) * t
    }
}

/// 2-component half-precision float vector (`GfVec2h`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f16; 2]", into = "[f16; 2]"))]
pub struct Vec2h {
    pub x: f16,
    pub y: f16,
}

impl From<[f16; 2]> for Vec2h {
    #[inline]
    fn from([x, y]: [f16; 2]) -> Self {
        Self { x, y }
    }
}

impl From<Vec2h> for [f16; 2] {
    #[inline]
    fn from(v: Vec2h) -> Self {
        [v.x, v.y]
    }
}

impl Index<usize> for Vec2h {
    type Output = f16;
    #[inline]
    fn index(&self, i: usize) -> &f16 {
        match i {
            0 => &self.x,
            1 => &self.y,
            _ => panic!("index {i} out of bounds for Vec2h"),
        }
    }
}

impl IndexMut<usize> for Vec2h {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut f16 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            _ => panic!("index {i} out of bounds for Vec2h"),
        }
    }
}

impl Vec2h {
    pub fn lerp(self, other: Self, t: f32) -> Self {
        Self {
            x: super::lerp_half(self.x, other.x, t),
            y: super::lerp_half(self.y, other.y, t),
        }
    }
}

/// 2-component integer vector (`GfVec2i`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[i32; 2]", into = "[i32; 2]"))]
pub struct Vec2i {
    pub x: i32,
    pub y: i32,
}

impl From<[i32; 2]> for Vec2i {
    #[inline]
    fn from([x, y]: [i32; 2]) -> Self {
        Self { x, y }
    }
}

impl From<Vec2i> for [i32; 2] {
    #[inline]
    fn from(v: Vec2i) -> Self {
        [v.x, v.y]
    }
}

impl Index<usize> for Vec2i {
    type Output = i32;
    #[inline]
    fn index(&self, i: usize) -> &i32 {
        match i {
            0 => &self.x,
            1 => &self.y,
            _ => panic!("index {i} out of bounds for Vec2i"),
        }
    }
}

impl IndexMut<usize> for Vec2i {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut i32 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            _ => panic!("index {i} out of bounds for Vec2i"),
        }
    }
}

/// 3-component single-precision float vector (`GfVec3f`).
///
/// The most commonly used vector type in the USD skel/geom schema layer.
/// Methods `dot`, `length`, `normalize`, and `lerp` cover the operations
/// needed by LBS skinning and blend-shape interpolation.
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f32; 3]", into = "[f32; 3]"))]
pub struct Vec3f {
    pub x: f32,
    pub y: f32,
    pub z: f32,
}

impl From<[f32; 3]> for Vec3f {
    #[inline]
    fn from([x, y, z]: [f32; 3]) -> Self {
        Self { x, y, z }
    }
}

impl From<Vec3f> for [f32; 3] {
    #[inline]
    fn from(v: Vec3f) -> Self {
        [v.x, v.y, v.z]
    }
}

impl Index<usize> for Vec3f {
    type Output = f32;
    #[inline]
    fn index(&self, i: usize) -> &f32 {
        match i {
            0 => &self.x,
            1 => &self.y,
            2 => &self.z,
            _ => panic!("index {i} out of bounds for Vec3f"),
        }
    }
}

impl IndexMut<usize> for Vec3f {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut f32 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            2 => &mut self.z,
            _ => panic!("index {i} out of bounds for Vec3f"),
        }
    }
}

impl Vec3f {
    pub fn dot(self, other: Vec3f) -> f32 {
        self.x * other.x + self.y * other.y + self.z * other.z
    }

    /// The lesser of this vector and `other` along each axis. A component
    /// that is NaN in one is taken from the other.
    pub fn min(self, other: Vec3f) -> Vec3f {
        Vec3f {
            x: self.x.min(other.x),
            y: self.y.min(other.y),
            z: self.z.min(other.z),
        }
    }

    /// The greater of this vector and `other` along each axis. A component
    /// that is NaN in one is taken from the other.
    pub fn max(self, other: Vec3f) -> Vec3f {
        Vec3f {
            x: self.x.max(other.x),
            y: self.y.max(other.y),
            z: self.z.max(other.z),
        }
    }

    /// The cross product `self × other` (C++ `GfCross`).
    ///
    /// ```
    /// use openusd::gf;
    ///
    /// let (x, y) = (gf::vec3f(1.0, 0.0, 0.0), gf::vec3f(0.0, 1.0, 0.0));
    /// assert_eq!(x.cross(y), gf::vec3f(0.0, 0.0, 1.0));
    /// assert_eq!(y.cross(x), gf::vec3f(0.0, 0.0, -1.0));
    /// ```
    pub fn cross(self, other: Vec3f) -> Vec3f {
        Vec3f {
            x: self.y * other.z - self.z * other.y,
            y: self.z * other.x - self.x * other.z,
            z: self.x * other.y - self.y * other.x,
        }
    }

    pub fn length(self) -> f32 {
        self.dot(self).sqrt()
    }

    /// The vector scaled to unit length (C++ `GfVec3f::GetNormalized`). A
    /// vector shorter than [`MIN_VECTOR_LENGTH`] is divided by that length
    /// and stays short of unit length.
    pub fn normalize(self) -> Self {
        self * (1.0 / self.length().max(MIN_VECTOR_LENGTH as f32))
    }

    pub fn lerp(self, other: Self, t: f32) -> Self {
        self + (other - self) * t
    }
}

/// 3-component double-precision float vector (`GfVec3d`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f64; 3]", into = "[f64; 3]"))]
pub struct Vec3d {
    pub x: f64,
    pub y: f64,
    pub z: f64,
}

impl From<[f64; 3]> for Vec3d {
    #[inline]
    fn from([x, y, z]: [f64; 3]) -> Self {
        Self { x, y, z }
    }
}

impl From<Vec3d> for [f64; 3] {
    #[inline]
    fn from(v: Vec3d) -> Self {
        [v.x, v.y, v.z]
    }
}

impl From<Vec3f> for Vec3d {
    #[inline]
    fn from(v: Vec3f) -> Self {
        Vec3d {
            x: v.x.into(),
            y: v.y.into(),
            z: v.z.into(),
        }
    }
}

impl Index<usize> for Vec3d {
    type Output = f64;
    #[inline]
    fn index(&self, i: usize) -> &f64 {
        match i {
            0 => &self.x,
            1 => &self.y,
            2 => &self.z,
            _ => panic!("index {i} out of bounds for Vec3d"),
        }
    }
}

impl IndexMut<usize> for Vec3d {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut f64 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            2 => &mut self.z,
            _ => panic!("index {i} out of bounds for Vec3d"),
        }
    }
}

impl Vec3d {
    /// The lesser of this vector and `other` along each axis. A component
    /// that is NaN in one is taken from the other.
    pub fn min(self, other: Vec3d) -> Vec3d {
        Vec3d {
            x: self.x.min(other.x),
            y: self.y.min(other.y),
            z: self.z.min(other.z),
        }
    }

    /// The greater of this vector and `other` along each axis. A component
    /// that is NaN in one is taken from the other.
    pub fn max(self, other: Vec3d) -> Vec3d {
        Vec3d {
            x: self.x.max(other.x),
            y: self.y.max(other.y),
            z: self.z.max(other.z),
        }
    }

    /// The vector in single precision, each component rounded to the
    /// nearest `f32`.
    pub fn to_f32(self) -> Vec3f {
        Vec3f {
            x: self.x as f32,
            y: self.y as f32,
            z: self.z as f32,
        }
    }

    /// The unit vector along X (C++ `GfVec3d::XAxis`).
    pub const X_AXIS: Vec3d = Vec3d { x: 1.0, y: 0.0, z: 0.0 };
    /// The unit vector along Y (C++ `GfVec3d::YAxis`).
    pub const Y_AXIS: Vec3d = Vec3d { x: 0.0, y: 1.0, z: 0.0 };
    /// The unit vector along Z (C++ `GfVec3d::ZAxis`).
    pub const Z_AXIS: Vec3d = Vec3d { x: 0.0, y: 0.0, z: 1.0 };

    pub fn dot(self, other: Vec3d) -> f64 {
        self.x * other.x + self.y * other.y + self.z * other.z
    }

    /// The cross product `self × other`.
    pub fn cross(self, other: Vec3d) -> Vec3d {
        Vec3d {
            x: self.y * other.z - self.z * other.y,
            y: self.z * other.x - self.x * other.z,
            z: self.x * other.y - self.y * other.x,
        }
    }

    /// The component-wise product (C++ `GfCompMult`).
    pub fn comp_mult(self, other: Vec3d) -> Vec3d {
        Vec3d {
            x: self.x * other.x,
            y: self.y * other.y,
            z: self.z * other.z,
        }
    }

    /// Whether `self` is within `tolerance` of `other`: their difference
    /// is at most `tolerance` long (C++ `GfIsClose`).
    pub fn is_close(self, other: Vec3d, tolerance: f64) -> bool {
        let delta = self - other;
        delta.dot(delta) <= tolerance * tolerance
    }

    /// Make three vectors mutually orthogonal by iterating toward the basis
    /// nearest all three, and of unit length when `normalize` is set (C++
    /// `GfVec3d::OrthogonalizeBasis`).
    ///
    /// Returns `false` when two of the vectors are within `eps` of colinear
    /// or the iteration does not settle within `eps`, in which case the
    /// vectors hold its last estimate.
    pub fn orthogonalize_basis(tx: &mut Vec3d, ty: &mut Vec3d, tz: &mut Vec3d, normalize: bool, eps: f64) -> bool {
        const MAX_ITERS: usize = 20;
        let unit = Vec3d::normalize;
        let close = |a: Vec3d, b: Vec3d| (a - b).dot(a - b) < eps * eps;

        if normalize {
            (*tx, *ty, *tz) = (unit(*tx), unit(*ty), unit(*tz));
        }
        let (mut ax, mut ay, mut az) = (unit(*tx), unit(*ty), unit(*tz));
        // Colinear vectors leave an iteration unchanged, which the error
        // below would read as convergence.
        if close(ax, ay) || close(ax, az) || close(ay, az) {
            return false;
        }

        for _ in 0..MAX_ITERS {
            let (mut bx, mut by, mut bz) = (*tx, *ty, *tz);
            bx -= ay * ay.dot(bx);
            bx -= az * az.dot(bx);
            by -= ax * ax.dot(by);
            by -= az * az.dot(by);
            bz -= ax * ax.dot(bz);
            bz -= ay * ay.dot(bz);

            let (mut cx, mut cy, mut cz) = ((*tx + bx) * 0.5, (*ty + by) * 0.5, (*tz + bz) * 0.5);
            if normalize {
                (cx, cy, cz) = (unit(cx), unit(cy), unit(cz));
            }

            let (dx, dy, dz) = (*tx - cx, *ty - cy, *tz - cz);
            if dx.dot(dx) + dy.dot(dy) + dz.dot(dz) < eps * eps {
                return true;
            }
            (*tx, *ty, *tz) = (cx, cy, cz);
            (ax, ay, az) = (unit(cx), unit(cy), unit(cz));
        }
        false
    }

    pub fn length(self) -> f64 {
        self.dot(self).sqrt()
    }

    /// The vector scaled to unit length (C++ `GfVec3d::GetNormalized`). A
    /// vector shorter than [`MIN_VECTOR_LENGTH`] is divided by that length
    /// and stays short of unit length.
    pub fn normalize(self) -> Self {
        self * (1.0 / self.length().max(MIN_VECTOR_LENGTH))
    }

    pub fn lerp(self, other: Self, t: f64) -> Self {
        self + (other - self) * t
    }
}

/// 3-component half-precision float vector (`GfVec3h`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f16; 3]", into = "[f16; 3]"))]
pub struct Vec3h {
    pub x: f16,
    pub y: f16,
    pub z: f16,
}

impl From<[f16; 3]> for Vec3h {
    #[inline]
    fn from([x, y, z]: [f16; 3]) -> Self {
        Self { x, y, z }
    }
}

impl From<Vec3h> for [f16; 3] {
    #[inline]
    fn from(v: Vec3h) -> Self {
        [v.x, v.y, v.z]
    }
}

impl Index<usize> for Vec3h {
    type Output = f16;
    #[inline]
    fn index(&self, i: usize) -> &f16 {
        match i {
            0 => &self.x,
            1 => &self.y,
            2 => &self.z,
            _ => panic!("index {i} out of bounds for Vec3h"),
        }
    }
}

impl IndexMut<usize> for Vec3h {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut f16 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            2 => &mut self.z,
            _ => panic!("index {i} out of bounds for Vec3h"),
        }
    }
}

impl Vec3h {
    pub fn lerp(self, other: Self, t: f32) -> Self {
        Self {
            x: super::lerp_half(self.x, other.x, t),
            y: super::lerp_half(self.y, other.y, t),
            z: super::lerp_half(self.z, other.z, t),
        }
    }
}

/// 3-component integer vector (`GfVec3i`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[i32; 3]", into = "[i32; 3]"))]
pub struct Vec3i {
    pub x: i32,
    pub y: i32,
    pub z: i32,
}

impl From<[i32; 3]> for Vec3i {
    #[inline]
    fn from([x, y, z]: [i32; 3]) -> Self {
        Self { x, y, z }
    }
}

impl From<Vec3i> for [i32; 3] {
    #[inline]
    fn from(v: Vec3i) -> Self {
        [v.x, v.y, v.z]
    }
}

impl Index<usize> for Vec3i {
    type Output = i32;
    #[inline]
    fn index(&self, i: usize) -> &i32 {
        match i {
            0 => &self.x,
            1 => &self.y,
            2 => &self.z,
            _ => panic!("index {i} out of bounds for Vec3i"),
        }
    }
}

impl IndexMut<usize> for Vec3i {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut i32 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            2 => &mut self.z,
            _ => panic!("index {i} out of bounds for Vec3i"),
        }
    }
}

/// 4-component single-precision float vector (`GfVec4f`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f32; 4]", into = "[f32; 4]"))]
pub struct Vec4f {
    pub x: f32,
    pub y: f32,
    pub z: f32,
    pub w: f32,
}

impl From<[f32; 4]> for Vec4f {
    #[inline]
    fn from([x, y, z, w]: [f32; 4]) -> Self {
        Self { x, y, z, w }
    }
}

impl From<Vec4f> for [f32; 4] {
    #[inline]
    fn from(v: Vec4f) -> Self {
        [v.x, v.y, v.z, v.w]
    }
}

impl Index<usize> for Vec4f {
    type Output = f32;
    #[inline]
    fn index(&self, i: usize) -> &f32 {
        match i {
            0 => &self.x,
            1 => &self.y,
            2 => &self.z,
            3 => &self.w,
            _ => panic!("index {i} out of bounds for Vec4f"),
        }
    }
}

impl IndexMut<usize> for Vec4f {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut f32 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            2 => &mut self.z,
            3 => &mut self.w,
            _ => panic!("index {i} out of bounds for Vec4f"),
        }
    }
}

impl Vec4f {
    pub fn lerp(self, other: Self, t: f32) -> Self {
        self + (other - self) * t
    }
}

/// 4-component double-precision float vector (`GfVec4d`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f64; 4]", into = "[f64; 4]"))]
pub struct Vec4d {
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub w: f64,
}

impl From<[f64; 4]> for Vec4d {
    #[inline]
    fn from([x, y, z, w]: [f64; 4]) -> Self {
        Self { x, y, z, w }
    }
}

impl From<Vec4d> for [f64; 4] {
    #[inline]
    fn from(v: Vec4d) -> Self {
        [v.x, v.y, v.z, v.w]
    }
}

impl Index<usize> for Vec4d {
    type Output = f64;
    #[inline]
    fn index(&self, i: usize) -> &f64 {
        match i {
            0 => &self.x,
            1 => &self.y,
            2 => &self.z,
            3 => &self.w,
            _ => panic!("index {i} out of bounds for Vec4d"),
        }
    }
}

impl IndexMut<usize> for Vec4d {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut f64 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            2 => &mut self.z,
            3 => &mut self.w,
            _ => panic!("index {i} out of bounds for Vec4d"),
        }
    }
}

impl Vec4d {
    pub fn lerp(self, other: Self, t: f64) -> Self {
        self + (other - self) * t
    }
}

/// 4-component half-precision float vector (`GfVec4h`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f16; 4]", into = "[f16; 4]"))]
pub struct Vec4h {
    pub x: f16,
    pub y: f16,
    pub z: f16,
    pub w: f16,
}

impl From<[f16; 4]> for Vec4h {
    #[inline]
    fn from([x, y, z, w]: [f16; 4]) -> Self {
        Self { x, y, z, w }
    }
}

impl From<Vec4h> for [f16; 4] {
    #[inline]
    fn from(v: Vec4h) -> Self {
        [v.x, v.y, v.z, v.w]
    }
}

impl Index<usize> for Vec4h {
    type Output = f16;
    #[inline]
    fn index(&self, i: usize) -> &f16 {
        match i {
            0 => &self.x,
            1 => &self.y,
            2 => &self.z,
            3 => &self.w,
            _ => panic!("index {i} out of bounds for Vec4h"),
        }
    }
}

impl IndexMut<usize> for Vec4h {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut f16 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            2 => &mut self.z,
            3 => &mut self.w,
            _ => panic!("index {i} out of bounds for Vec4h"),
        }
    }
}

impl Vec4h {
    pub fn lerp(self, other: Self, t: f32) -> Self {
        Self {
            x: super::lerp_half(self.x, other.x, t),
            y: super::lerp_half(self.y, other.y, t),
            z: super::lerp_half(self.z, other.z, t),
            w: super::lerp_half(self.w, other.w, t),
        }
    }
}

/// 4-component integer vector (`GfVec4i`).
#[repr(C)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Zeroable,
    Pod,
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Neg,
    Mul,
    MulAssign,
    Div,
    DivAssign,
    Sum,
)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[i32; 4]", into = "[i32; 4]"))]
pub struct Vec4i {
    pub x: i32,
    pub y: i32,
    pub z: i32,
    pub w: i32,
}

impl From<[i32; 4]> for Vec4i {
    #[inline]
    fn from([x, y, z, w]: [i32; 4]) -> Self {
        Self { x, y, z, w }
    }
}

impl From<Vec4i> for [i32; 4] {
    #[inline]
    fn from(v: Vec4i) -> Self {
        [v.x, v.y, v.z, v.w]
    }
}

impl Index<usize> for Vec4i {
    type Output = i32;
    #[inline]
    fn index(&self, i: usize) -> &i32 {
        match i {
            0 => &self.x,
            1 => &self.y,
            2 => &self.z,
            3 => &self.w,
            _ => panic!("index {i} out of bounds for Vec4i"),
        }
    }
}

impl IndexMut<usize> for Vec4i {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut i32 {
        match i {
            0 => &mut self.x,
            1 => &mut self.y,
            2 => &mut self.z,
            3 => &mut self.w,
            _ => panic!("index {i} out of bounds for Vec4i"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::gf::vec3d;

    /// The component-wise product multiplies each component by its
    /// partner.
    #[test]
    fn comp_mult() {
        assert_eq!(
            vec3d(1.0, -2.0, 3.0).comp_mult(vec3d(2.0, 0.5, -1.0)),
            vec3d(2.0, -1.0, -3.0)
        );
    }

    /// Closeness is the difference's length against the tolerance.
    #[test]
    fn is_close() {
        let v = vec3d(1.0, 2.0, 3.0);
        assert!(v.is_close(vec3d(1.0, 2.0, 3.001), 0.001));
        assert!(!v.is_close(vec3d(1.0, 2.0, 3.002), 0.001));
    }
}
