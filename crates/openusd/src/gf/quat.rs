//! `GfQuat` — unit-quaternion rotation types.
//!
//! Quaternions are stored as `(w, x, y, z)` with `w` the real (scalar)
//! part — matching `GfQuatf`'s constructor order and the layout USD uses
//! in `Quatf`, `Quatd`, and `Quath` attribute values.
//!
//! `From<[T; 4]>` and `From<Quat*> for [T; 4]` bridge to the raw array
//! representation used by `sdf::Value`.

use super::MIN_VECTOR_LENGTH;
use super::f16;

/// Single-precision quaternion (`GfQuatf`). Layout: `(w, x, y, z)`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, bytemuck::Pod, bytemuck::Zeroable)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f32; 4]", into = "[f32; 4]"))]
pub struct Quatf {
    pub w: f32,
    pub x: f32,
    pub y: f32,
    pub z: f32,
}

impl Quatf {
    pub const IDENTITY: Quatf = Quatf {
        w: 1.0,
        x: 0.0,
        y: 0.0,
        z: 0.0,
    };

    /// Returns a normalized copy, or the identity quaternion if the
    /// magnitude is below [`MIN_VECTOR_LENGTH`] (C++ `GetNormalized`).
    ///
    /// The arithmetic is C++'s. The length is taken in single precision,
    /// summing the imaginary components before the real one, so a component
    /// whose square leaves the `f32` range takes the length to zero or
    /// infinity. The real part is divided by the length and the imaginary
    /// part scaled by its double-precision reciprocal.
    pub fn normalize(self) -> Self {
        let length = (self.x * self.x + self.y * self.y + self.z * self.z + self.w * self.w).sqrt();
        if length < MIN_VECTOR_LENGTH as f32 {
            return Self::IDENTITY;
        }
        let reciprocal = 1.0 / f64::from(length);
        let scale = |c: f32| (f64::from(c) * reciprocal) as f32;
        Self {
            w: self.w / length,
            x: scale(self.x),
            y: scale(self.y),
            z: scale(self.z),
        }
    }

    /// Spherical linear interpolation toward `other` at parameter `t`.
    ///
    /// Chooses the shorter great-circle arc and falls back to normalised
    /// lerp when the quaternions are nearly collinear. `t = 0` returns
    /// `self`; `t = 1` returns `other` (or its negation when the dot
    /// product is negative).
    pub fn slerp(self, other: Self, t: f64) -> Self {
        let out = slerp(
            [self.w as f64, self.x as f64, self.y as f64, self.z as f64],
            [other.w as f64, other.x as f64, other.y as f64, other.z as f64],
            t,
        );
        Self {
            w: out[0] as f32,
            x: out[1] as f32,
            y: out[2] as f32,
            z: out[3] as f32,
        }
    }
}

impl From<[f32; 4]> for Quatf {
    #[inline]
    fn from([w, x, y, z]: [f32; 4]) -> Self {
        Self { w, x, y, z }
    }
}

impl From<Quatf> for [f32; 4] {
    #[inline]
    fn from(q: Quatf) -> Self {
        [q.w, q.x, q.y, q.z]
    }
}

/// Double-precision quaternion (`GfQuatd`). Layout: `(w, x, y, z)`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, bytemuck::Pod, bytemuck::Zeroable)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f64; 4]", into = "[f64; 4]"))]
pub struct Quatd {
    pub w: f64,
    pub x: f64,
    pub y: f64,
    pub z: f64,
}

impl Quatd {
    pub const IDENTITY: Quatd = Quatd {
        w: 1.0,
        x: 0.0,
        y: 0.0,
        z: 0.0,
    };

    /// Returns a normalized copy, or the identity quaternion if the
    /// magnitude is below [`MIN_VECTOR_LENGTH`] (C++ `GetNormalized`).
    ///
    /// The arithmetic is C++'s: the squared length sums the imaginary
    /// components before the real one, the real part is divided by the length
    /// and the imaginary part scaled by its reciprocal.
    pub fn normalize(self) -> Self {
        let length = (self.x * self.x + self.y * self.y + self.z * self.z + self.w * self.w).sqrt();
        if length < MIN_VECTOR_LENGTH {
            return Self::IDENTITY;
        }
        let reciprocal = 1.0 / length;
        Self {
            w: self.w / length,
            x: self.x * reciprocal,
            y: self.y * reciprocal,
            z: self.z * reciprocal,
        }
    }

    /// Spherical linear interpolation toward `other` at parameter `t`.
    pub fn slerp(self, other: Self, t: f64) -> Self {
        let out = slerp(
            [self.w, self.x, self.y, self.z],
            [other.w, other.x, other.y, other.z],
            t,
        );
        Self {
            w: out[0],
            x: out[1],
            y: out[2],
            z: out[3],
        }
    }
}

impl From<[f64; 4]> for Quatd {
    #[inline]
    fn from([w, x, y, z]: [f64; 4]) -> Self {
        Self { w, x, y, z }
    }
}

impl From<Quatd> for [f64; 4] {
    #[inline]
    fn from(q: Quatd) -> Self {
        [q.w, q.x, q.y, q.z]
    }
}

/// Half-precision quaternion (`GfQuath`). Layout: `(w, x, y, z)`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, bytemuck::Pod, bytemuck::Zeroable)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "[f16; 4]", into = "[f16; 4]"))]
pub struct Quath {
    pub w: f16,
    pub x: f16,
    pub y: f16,
    pub z: f16,
}

impl Quath {
    /// The identity rotation, `(1, 0, 0, 0)`.
    pub const IDENTITY: Quath = Quath {
        w: f16::ONE,
        x: f16::ZERO,
        y: f16::ZERO,
        z: f16::ZERO,
    };

    /// Returns a normalized copy, or the identity quaternion if the
    /// magnitude is zero.
    pub fn normalize(self) -> Self {
        let n = normalize([
            self.w.to_f32() as f64,
            self.x.to_f32() as f64,
            self.y.to_f32() as f64,
            self.z.to_f32() as f64,
        ]);
        Self {
            w: f16::from_f32(n[0] as f32),
            x: f16::from_f32(n[1] as f32),
            y: f16::from_f32(n[2] as f32),
            z: f16::from_f32(n[3] as f32),
        }
    }

    /// Spherical linear interpolation toward `other` at parameter `t`.
    pub fn slerp(self, other: Self, t: f64) -> Self {
        let out = slerp(
            [
                self.w.to_f32() as f64,
                self.x.to_f32() as f64,
                self.y.to_f32() as f64,
                self.z.to_f32() as f64,
            ],
            [
                other.w.to_f32() as f64,
                other.x.to_f32() as f64,
                other.y.to_f32() as f64,
                other.z.to_f32() as f64,
            ],
            t,
        );
        Self {
            w: f16::from_f32(out[0] as f32),
            x: f16::from_f32(out[1] as f32),
            y: f16::from_f32(out[2] as f32),
            z: f16::from_f32(out[3] as f32),
        }
    }
}

impl From<[f16; 4]> for Quath {
    #[inline]
    fn from([w, x, y, z]: [f16; 4]) -> Self {
        Self { w, x, y, z }
    }
}

impl From<Quath> for [f16; 4] {
    #[inline]
    fn from(q: Quath) -> Self {
        [q.w, q.x, q.y, q.z]
    }
}

/// Normalise a `(w, x, y, z)` quaternion stored as `[f64; 4]`. Returns
/// the identity `[1, 0, 0, 0]` when the magnitude is zero.
fn normalize(q: [f64; 4]) -> [f64; 4] {
    let mag = (q[0] * q[0] + q[1] * q[1] + q[2] * q[2] + q[3] * q[3]).sqrt();
    if mag == 0.0 {
        return [1.0, 0.0, 0.0, 0.0];
    }
    [q[0] / mag, q[1] / mag, q[2] / mag, q[3] / mag]
}

/// Quaternion slerp in `(w, x, y, z)` order. Chooses the shorter
/// great-circle arc, and falls back to nlerp when the two quaternions
/// are within numerical noise of each other to avoid the sin(0)/0
/// singularity.
fn slerp(a: [f64; 4], b: [f64; 4], t: f64) -> [f64; 4] {
    let mut dot = a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3];
    let sign = if dot < 0.0 { -1.0 } else { 1.0 };
    dot = dot.abs();
    if dot > 0.9995 {
        return normalize([
            a[0] + (sign * b[0] - a[0]) * t,
            a[1] + (sign * b[1] - a[1]) * t,
            a[2] + (sign * b[2] - a[2]) * t,
            a[3] + (sign * b[3] - a[3]) * t,
        ]);
    }
    let theta = dot.acos();
    let sin_theta = theta.sin();
    let s_a = ((1.0 - t) * theta).sin() / sin_theta;
    let s_b = (t * theta).sin() / sin_theta * sign;
    [
        a[0] * s_a + b[0] * s_b,
        a[1] * s_a + b[1] * s_b,
        a[2] * s_a + b[2] * s_b,
        a[3] * s_a + b[3] * s_b,
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slerp_90deg() {
        // Identity → 180° about +X. At t=0.5 the result should be 90°
        // about +X: (w=cos(45°), x=sin(45°), 0, 0).
        let id = Quatf::IDENTITY;
        let half_turn = Quatf {
            w: 0.0,
            x: 1.0,
            y: 0.0,
            z: 0.0,
        };
        let out = id.slerp(half_turn, 0.5);
        let expected_w = std::f32::consts::FRAC_PI_4.cos();
        let expected_x = std::f32::consts::FRAC_PI_4.sin();
        assert!((out.w - expected_w).abs() < 1e-5, "w: {out:?}");
        assert!((out.x - expected_x).abs() < 1e-5, "x: {out:?}");
        assert!(out.y.abs() < 1e-5);
        assert!(out.z.abs() < 1e-5);
    }

    #[test]
    fn slerp_shorter_arc() {
        // q and -q represent the same rotation; slerp must detect the
        // sign flip and take the short arc, producing a result near identity.
        let id = Quatd::IDENTITY;
        let neg_id = Quatd {
            w: -1.0,
            x: 0.0,
            y: 0.0,
            z: 0.0,
        };
        let out = id.slerp(neg_id, 0.5);
        assert!((out.w.abs() - 1.0).abs() < 1e-9);
    }

    fn quatf(w: f32, x: f32, y: f32, z: f32) -> Quatf {
        Quatf { w, x, y, z }
    }

    fn quatd(w: f64, x: f64, y: f64, z: f64) -> Quatd {
        Quatd { w, x, y, z }
    }

    /// `Quatf::normalize` gives the bits of C++ `GfQuatf::GetNormalized`
    /// (OpenUSD 26.08); only IEEE-exact operations are involved.
    #[test]
    fn quatf_normalize_cpp_bits() {
        let cases = [
            (
                quatf(0.9511514, 0.04662174, -0.28952447, 0.096504346),
                [0x3f737ea8, 0x3d3ef670, 0xbe943c8d, 0x3dc5a412],
            ),
            (
                quatf(0.5, 1.0, 0.25, -0.75),
                [0x3ebaf4ba, 0x3f3af4ba, 0x3e3af4ba, 0xbf0c378b],
            ),
            (
                quatf(3.0, -7.0, 11.0, 2.0),
                [0x3e6316ba, 0xbf0477ed, 0x3f502a2b, 0x3e17647c],
            ),
            (
                quatf(300.0, 1.0, 2.0, 3.0),
                [0x3f7ffae7, 0x3b5a6fb4, 0x3bda6fb4, 0x3c23d3c7],
            ),
            (
                quatf(0.001, 0.002, -0.003, 0.004),
                [0x3e3af4ba, 0x3ebaf4ba, 0xbf0c378b, 0x3f3af4ba],
            ),
            (
                quatf(100.0, 200.0, -50.0, 25.0),
                [0x3ede2304, 0x3f5e2304, 0xbe5e2304, 0x3dde2304],
            ),
        ];
        for (q, want) in cases {
            let n = q.normalize();
            assert_eq!([n.w, n.x, n.y, n.z].map(f32::to_bits), want, "{q:?}");
        }
    }

    /// The `f32` length decides the outcome at the edges, as in C++: below
    /// the threshold, or with squares that underflow, the identity; at the
    /// threshold, a unit quaternion; with squares that overflow, zero.
    #[test]
    fn quatf_normalize_edges() {
        assert_eq!(quatf(0.0, 0.0, 0.0, 0.0).normalize(), Quatf::IDENTITY);
        assert_eq!(quatf(4e-11, 4e-11, 4e-11, 4e-11).normalize(), Quatf::IDENTITY);
        assert_eq!(quatf(1e-25, 1e-25, 0.0, 0.0).normalize(), Quatf::IDENTITY);
        assert_eq!(quatf(5e-11, 5e-11, 5e-11, 5e-11).normalize(), quatf(0.5, 0.5, 0.5, 0.5));
        assert_eq!(quatf(2e-10, 0.0, 0.0, 0.0).normalize(), Quatf::IDENTITY);
        assert_eq!(quatf(1e20, 1e20, 1e20, 1e20).normalize(), quatf(0.0, 0.0, 0.0, 0.0));
    }

    /// `Quatd::normalize` gives the bits of C++ `GfQuatd::GetNormalized`
    /// (OpenUSD 26.08); only IEEE-exact operations are involved.
    #[test]
    fn quatd_normalize_cpp_bits() {
        let cases: [(Quatd, [u64; 4]); 3] = [
            (
                quatd(0.5, 1.0, 0.25, -0.75),
                [
                    0x3fd75e9746a0b098,
                    0x3fe75e9746a0b098,
                    0x3fc75e9746a0b098,
                    0xbfe186f174f88472,
                ],
            ),
            (
                quatd(3.0, -7.0, 11.0, 2.0),
                [
                    0x3fcc62d73d7d15fd,
                    0xbfe08efd8e88f77e,
                    0x3fea05454db2a97d,
                    0x3fc2ec8f7e5363fe,
                ],
            ),
            (
                quatd(0.001, 0.002, -0.003, 0.004),
                [
                    0x3fc75e9746a0b098,
                    0x3fd75e9746a0b099,
                    0xbfe186f174f88473,
                    0x3fe75e9746a0b099,
                ],
            ),
        ];
        for (q, want) in cases {
            let n = q.normalize();
            assert_eq!([n.w, n.x, n.y, n.z].map(f64::to_bits), want, "{q:?}");
        }
        assert_eq!(quatd(4e-11, 4e-11, 4e-11, 4e-11).normalize(), Quatd::IDENTITY);
        assert_eq!(quatd(5e-11, 5e-11, 5e-11, 5e-11).normalize(), quatd(0.5, 0.5, 0.5, 0.5));
    }
}
