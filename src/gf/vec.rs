//! GfVec — fixed-arity vector types.
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

use bytemuck::{Pod, Zeroable};
use derive_more::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign, Sum};

use super::f16;

/// 2-component single-precision float vector (`GfVec2f`).
#[repr(C)]
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
    pub fn lerp(self, other: Self, t: f64) -> Self {
        self + (other - self) * t
    }
}

/// 2-component half-precision float vector (`GfVec2h`).
#[repr(C)]
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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

    pub fn length(self) -> f32 {
        self.dot(self).sqrt()
    }

    /// Returns the unit vector, or `self` unchanged when the length is zero
    /// (matches `GfVec3f::GetNormalized`'s zero-length behaviour).
    pub fn normalize(self) -> Self {
        let len = self.length();
        if len > 0.0 {
            self * (1.0 / len)
        } else {
            self
        }
    }

    pub fn lerp(self, other: Self, t: f32) -> Self {
        self + (other - self) * t
    }
}

/// 3-component double-precision float vector (`GfVec3d`).
#[repr(C)]
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
    pub fn dot(self, other: Vec3d) -> f64 {
        self.x * other.x + self.y * other.y + self.z * other.z
    }

    pub fn length(self) -> f64 {
        self.dot(self).sqrt()
    }

    pub fn normalize(self) -> Self {
        let len = self.length();
        if len > 0.0 {
            self * (1.0 / len)
        } else {
            self
        }
    }

    pub fn lerp(self, other: Self, t: f64) -> Self {
        self + (other - self) * t
    }
}

/// 3-component half-precision float vector (`GfVec3h`).
#[repr(C)]
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
    Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Sum, Zeroable, Pod,
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
