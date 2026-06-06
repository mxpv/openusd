//! GfQuat — unit-quaternion rotation types.
//!
//! Quaternions are stored as `(w, x, y, z)` with `w` the real (scalar)
//! part — matching `GfQuatf`'s constructor order and the layout USD uses
//! in `Quatf`, `Quatd`, and `Quath` attribute values.
//!
//! `From<[T; 4]>` and `From<Quat*> for [T; 4]` bridge to the raw array
//! representation used by `sdf::Value`.

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
    /// magnitude is zero.
    pub fn normalize(self) -> Self {
        let n = normalize([self.w as f64, self.x as f64, self.y as f64, self.z as f64]);
        Self {
            w: n[0] as f32,
            x: n[1] as f32,
            y: n[2] as f32,
            z: n[3] as f32,
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
    /// magnitude is zero.
    pub fn normalize(self) -> Self {
        let n = normalize([self.w, self.x, self.y, self.z]);
        Self {
            w: n[0],
            x: n[1],
            y: n[2],
            z: n[3],
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
}
