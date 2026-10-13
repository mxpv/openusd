//! Graphics foundations — the value types beneath the schema layer: linear
//! algebra, the [`Interval`] a time-sample query is asked over, the
//! [`Range3d`] and [`BBox3d`] that bound geometry, and the [`Camera`] that
//! looks at it through its [`Frustum`].
//!
//! Mirrors Pixar's `Gf` namespace.
//!
//! # Conventions
//!
//! These follow the
//! [UsdGeom linear algebra spec](https://openusd.org/dev/api/usd_geom_page_front.html#UsdGeom_LinAlgBasics).
//!
//! Row-major storage — for a `Mat4d` datum `m`, element `m[r * 4 + c]`
//! is row `r`, column `c`. This matches the C++ `GfMatrix4d` layout:
//! `mat[3][1]` is the second column of the fourth row.
//!
//! Row vectors — `GfVec` types are row vectors that pre-multiply matrices:
//! `v_out = v_in · M`. The translation of a transform therefore lives in
//! the last row (`m[12..=14]`), not the last column.
//!
//! Left-to-right composition — to apply scale then rotation then
//! translation, compose `M = S · R · T` and evaluate with
//! `v_out = v_in · M`.
//!
//! Right-hand rule — cross products and rotations follow the right-hand
//! rule.
//!
//! Rotation angles — the USD high-level API (`UsdGeomXformOp`) expresses
//! angles in degrees; these low-level types take radians to match Rust's
//! `f32::sin_cos` and friends. [`Rotation`], [`Camera`] and [`Frustum`] are
//! the exceptions: like C++ `GfRotation`, `GfCamera` and `GfFrustum`, they
//! hold and take their angles in degrees.
//!
//! Camera space — a [`Camera`] looks along its own −Z, with +Y up and +X to
//! the right. Its film back and focal length are in tenths of a world unit,
//! and its distances in world units.
//!
//! Quaternion layout — `(w, x, y, z)` with `w` the real (scalar) part,
//! matching `GfQuatf`'s constructor order.

mod bbox;
mod camera;
mod frustum;
mod interval;
mod matrix;
mod plane;
mod projection;
mod quat;
mod range;
mod ray;
mod rotation;
mod vec;

pub use bbox::BBox3d;
pub use camera::{Camera, FovDirection};
pub use frustum::{Frustum, FrustumPlanes};
pub use half::f16;
pub use interval::Interval;
pub use matrix::{Factors, Mat2d, Mat3d, Mat4d};
pub use plane::Plane;
pub use projection::{Projection, ProjectionParams};
pub use quat::{Quatd, Quatf, Quath};
pub use range::{Range1d, Range1f, Range2d, Range3d};
pub use ray::{Ray, TriangleHit};
pub use rotation::Rotation;
pub use vec::{Vec2d, Vec2f, Vec2h, Vec2i, Vec3d, Vec3f, Vec3h, Vec3i, Vec4d, Vec4f, Vec4h, Vec4i};

/// The length below which a vector or quaternion counts as zero when it is
/// normalized (C++ `GF_MIN_VECTOR_LENGTH`).
pub const MIN_VECTOR_LENGTH: f64 = 1e-10;

/// How far from orthogonal the vectors of a basis may be and still count as
/// orthogonal (C++ `GF_MIN_ORTHO_TOLERANCE`).
pub const MIN_ORTHO_TOLERANCE: f64 = 1e-6;

// Free-function constructors — shorthand for struct literals.
pub fn vec2f(x: f32, y: f32) -> Vec2f {
    Vec2f { x, y }
}
pub fn vec3f(x: f32, y: f32, z: f32) -> Vec3f {
    Vec3f { x, y, z }
}
pub fn vec4f(x: f32, y: f32, z: f32, w: f32) -> Vec4f {
    Vec4f { x, y, z, w }
}
pub fn vec2d(x: f64, y: f64) -> Vec2d {
    Vec2d { x, y }
}
pub fn vec3d(x: f64, y: f64, z: f64) -> Vec3d {
    Vec3d { x, y, z }
}
pub fn vec4d(x: f64, y: f64, z: f64, w: f64) -> Vec4d {
    Vec4d { x, y, z, w }
}
pub fn vec2i(x: i32, y: i32) -> Vec2i {
    Vec2i { x, y }
}
pub fn vec3i(x: i32, y: i32, z: i32) -> Vec3i {
    Vec3i { x, y, z }
}
pub fn vec4i(x: i32, y: i32, z: i32, w: i32) -> Vec4i {
    Vec4i { x, y, z, w }
}
pub fn vec2h(x: f16, y: f16) -> Vec2h {
    Vec2h { x, y }
}
pub fn vec3h(x: f16, y: f16, z: f16) -> Vec3h {
    Vec3h { x, y, z }
}
pub fn vec4h(x: f16, y: f16, z: f16, w: f16) -> Vec4h {
    Vec4h { x, y, z, w }
}
/// Linear interpolation: `a + (b - a) * t`.
///
/// Works for `f32`, `f64`, and any scalar type that implements the
/// corresponding arithmetic traits.
pub fn lerp<T>(a: T, b: T, t: T) -> T
where
    T: Copy + std::ops::Add<Output = T> + std::ops::Sub<Output = T> + std::ops::Mul<Output = T>,
{
    a + (b - a) * t
}

/// Linear interpolation between two `f16` values, computed in `f32`
/// to avoid f16 precision loss.
pub fn lerp_half(a: f16, b: f16, t: f32) -> f16 {
    f16::from_f32(lerp(a.to_f32(), b.to_f32(), t))
}

pub fn quatf(w: f32, x: f32, y: f32, z: f32) -> Quatf {
    Quatf { w, x, y, z }
}
pub fn quatd(w: f64, x: f64, y: f64, z: f64) -> Quatd {
    Quatd { w, x, y, z }
}
pub fn quath(w: f16, x: f16, y: f16, z: f16) -> Quath {
    Quath { w, x, y, z }
}
