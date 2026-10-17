//! `GfDualQuatd` — a rigid transform, a rotation followed by a translation,
//! as a dual quaternion.

use std::ops::Mul;

use derive_more::{Add, AddAssign, Sub};

use super::{MIN_VECTOR_LENGTH, Quatd, Vec3d};

/// Double-precision dual quaternion (C++ `GfDualQuatd`): `real + ε·dual`,
/// where a unit `real` holds a rotation and `dual` the translation applied
/// after it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Add, AddAssign, Sub)]
pub struct DualQuatd {
    /// The real part, the rotation.
    pub real: Quatd,
    /// The dual part, which carries the translation.
    pub dual: Quatd,
}

impl DualQuatd {
    /// The dual quaternion with both parts zero (C++ `GetZero`).
    pub const ZERO: DualQuatd = DualQuatd {
        real: Quatd::ZERO,
        dual: Quatd::ZERO,
    };

    /// The identity transform (C++ `GetIdentity`).
    pub const IDENTITY: DualQuatd = DualQuatd {
        real: Quatd::IDENTITY,
        dual: Quatd::ZERO,
    };

    /// The transform that rotates by `rotation` and then translates by
    /// `translation` (C++ `GfDualQuatd(rotation, translation)`).
    pub fn from_rotation_translation(rotation: Quatd, translation: Vec3d) -> Self {
        Self {
            real: rotation,
            dual: Quatd::new(0.0, translation * 0.5) * rotation,
        }
    }

    /// The length of the real part, and the dual part's component along the
    /// real part divided by that length (C++ `GetLength`). Both are zero for
    /// a zero real part.
    pub fn length(self) -> (f64, f64) {
        let real = self.real.length();
        if real == 0.0 {
            return (0.0, 0.0);
        }
        (real, self.real.dot(self.dual) / real)
    }

    /// The dual quaternion scaled to a unit real part, with the dual part's
    /// component along the real part removed, or the identity for a real
    /// part shorter than [`MIN_VECTOR_LENGTH`] (C++ `GetNormalized`).
    pub fn normalize(self) -> Self {
        let length = self.real.length();
        if length < MIN_VECTOR_LENGTH {
            return Self::IDENTITY;
        }
        let scaled = self * (1.0 / length);
        Self {
            real: scaled.real,
            dual: scaled.dual - scaled.real * scaled.real.dot(scaled.dual),
        }
    }

    /// Both parts conjugated (C++ `GetConjugate`).
    pub fn conjugate(self) -> Self {
        Self {
            real: self.real.conjugate(),
            dual: self.dual.conjugate(),
        }
    }

    /// The dual quaternion whose product with this one is the identity, or
    /// the identity for a zero real part (C++ `GetInverse`).
    pub fn inverse(self) -> Self {
        let square = self.real.dot(self.real);
        if square <= 0.0 {
            return Self::IDENTITY;
        }
        let reciprocal = 1.0 / square;
        let conjugate = self.conjugate() * reciprocal;
        Self {
            real: conjugate.real,
            dual: conjugate.dual - conjugate.real * (2.0 * reciprocal * self.real.dot(self.dual)),
        }
    }

    /// The translation of a normalized dual quaternion (C++
    /// `GetTranslation`).
    pub fn translation(self) -> Vec3d {
        let (r1, r2) = (self.dual.w, self.real.w);
        let (i1, i2) = (self.dual.imaginary(), self.real.imaginary());
        (i2 * r1 - i1 * r2 + i1.cross(i2)) * -2.0
    }

    /// `point` rotated and then translated by a normalized dual quaternion
    /// (C++ `Transform`).
    pub fn transform(self, point: Vec3d) -> Vec3d {
        self.real.transform(point) + self.translation()
    }

    /// The sum of the dot products of the two real parts and the two dual
    /// parts (C++ `GfDot`).
    pub fn dot(self, other: Self) -> f64 {
        self.real.dot(other.real) + self.dual.dot(other.dual)
    }
}

/// The pure rotation `rotation` (C++ `GfDualQuatd(const GfQuatd&)`).
impl From<Quatd> for DualQuatd {
    fn from(rotation: Quatd) -> Self {
        Self {
            real: rotation,
            dual: Quatd::ZERO,
        }
    }
}

/// The product (C++ `GfDualQuatd::operator*`): transforming by the product
/// transforms by `other` and then by `self`.
impl Mul for DualQuatd {
    type Output = DualQuatd;

    fn mul(self, other: DualQuatd) -> DualQuatd {
        DualQuatd {
            real: self.real * other.real,
            dual: self.real * other.dual + self.dual * other.real,
        }
    }
}

impl Mul<f64> for DualQuatd {
    type Output = DualQuatd;

    fn mul(self, s: f64) -> DualQuatd {
        DualQuatd {
            real: self.real * s,
            dual: self.dual * s,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::f64::consts::FRAC_PI_2;

    use super::*;
    use crate::gf::{Mat4d, vec3d};

    fn assert_near(a: Vec3d, b: Vec3d) {
        assert!((a - b).length() < 1e-12, "{a:?} != {b:?}");
    }

    #[test]
    fn rotate_then_translate() {
        let rotation = Mat4d::rotation_z(FRAC_PI_2).extract_rotation_quat();
        let dq = DualQuatd::from_rotation_translation(rotation, vec3d(1.0, 2.0, 3.0));
        assert_near(dq.translation(), vec3d(1.0, 2.0, 3.0));
        assert_near(dq.transform(Vec3d::X_AXIS), vec3d(1.0, 3.0, 3.0));
        assert_eq!(DualQuatd::IDENTITY.transform(Vec3d::X_AXIS), Vec3d::X_AXIS);
        assert_eq!(DualQuatd::from(rotation).translation(), Vec3d::default());
    }

    #[test]
    fn product_and_inverse() {
        let a = DualQuatd::from_rotation_translation(
            Mat4d::rotation_z(FRAC_PI_2).extract_rotation_quat(),
            vec3d(1.0, 0.0, 0.0),
        );
        let b =
            DualQuatd::from_rotation_translation(Mat4d::rotation_x(0.4).extract_rotation_quat(), vec3d(0.0, 0.0, 2.0));
        let point = vec3d(0.5, -1.0, 2.0);
        assert_near((a * b).transform(point), a.transform(b.transform(point)));
        assert_near((a * a.inverse()).transform(point), point);
        // The inverse of a scaled dual quaternion undoes it too.
        assert_near(((a * 2.0) * (a * 2.0).inverse()).transform(point), point);
    }

    #[test]
    fn normalize_scaled_and_zero() {
        let dq =
            DualQuatd::from_rotation_translation(Mat4d::rotation_y(1.0).extract_rotation_quat(), vec3d(3.0, 0.0, 1.0));
        let normalized = (dq * 4.0).normalize();
        assert_near(normalized.transform(Vec3d::Y_AXIS), dq.transform(Vec3d::Y_AXIS));
        assert!((normalized.length().0 - 1.0).abs() < 1e-12);
        assert!(normalized.length().1.abs() < 1e-12);
        assert_eq!(DualQuatd::ZERO.normalize(), DualQuatd::IDENTITY);
        assert_eq!(DualQuatd::ZERO.length(), (0.0, 0.0));
        assert_eq!(DualQuatd::ZERO.inverse(), DualQuatd::IDENTITY);
        assert_eq!((dq - dq).dot(dq), 0.0);
        assert_eq!(dq.conjugate().conjugate(), dq);
    }
}
