//! `GfRotation` — a rotation as an axis and an angle in degrees.

use super::{MIN_VECTOR_LENGTH, Mat4d, Quatd, Vec3d};

/// A rotation of `angle` degrees about a unit `axis` (C++ `GfRotation`).
///
/// A matrix made with [`Mat4d::from_quat`](super::Mat4d::from_quat) of
/// [`quat`](Self::quat) is the one C++ `GfMatrix4d(rotation, translate)`
/// makes. The arithmetic follows C++ operation for operation, for a
/// quaternion of any length. `acos`, `sin` and `cos` come from the platform's
/// math library, so a result can differ from C++'s in its last bits.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Rotation {
    axis: Vec3d,
    angle: f64,
}

impl Rotation {
    /// The rotation of zero degrees about X.
    pub const IDENTITY: Rotation = Rotation {
        axis: Vec3d { x: 1.0, y: 0.0, z: 0.0 },
        angle: 0.0,
    };

    /// The rotation of `degrees` about `axis` (C++ `SetAxisAngle`). The axis
    /// is normalized unless its squared length is within `1e-10` of one; an
    /// axis shorter than [`MIN_VECTOR_LENGTH`] is divided by that length
    /// instead of its own, as C++ `GfVec3d::Normalize` does.
    pub fn new(axis: Vec3d, degrees: f64) -> Self {
        let length_sq = axis.dot(axis);
        let axis = match (length_sq - 1.0).abs() < 1e-10 {
            true => axis,
            false => axis.normalize(),
        };
        Self { axis, angle: degrees }
    }

    /// The rotation a quaternion describes (C++ `SetQuat`).
    ///
    /// The angle is `2·acos(w)`, with `w` clamped to `[-1, 1]`, and the axis
    /// the imaginary part made unit length. The quaternion as a whole is not
    /// normalized, so for one off unit length the real part decides the
    /// angle. A quaternion is the identity when its imaginary part is at
    /// most [`MIN_VECTOR_LENGTH`] long or that length is NaN.
    pub fn from_quat(q: Quatd) -> Self {
        let imaginary = Vec3d { x: q.x, y: q.y, z: q.z };
        let length = imaginary.length();
        if length > MIN_VECTOR_LENGTH {
            let half_angle = q.w.clamp(-1.0, 1.0).acos();
            Self::new(imaginary * (1.0 / length), 2.0 * half_angle.to_degrees())
        } else {
            Self::IDENTITY
        }
    }

    /// The unit axis the rotation turns about.
    pub fn axis(self) -> Vec3d {
        self.axis
    }

    /// The angle of the rotation, in degrees.
    pub fn angle(self) -> f64 {
        self.angle
    }

    /// The rotation undoing this one: the same axis, the negated angle (C++
    /// `GetInverse`).
    pub fn inverse(self) -> Self {
        Self::new(self.axis, -self.angle)
    }

    /// Decompose the rotation into angles, in degrees, about three axes (C++
    /// `Decompose`): turning a point about `axis2` by the third angle, then
    /// `axis1` by the second, then `axis0` by the first, is this rotation.
    ///
    /// The axes are normalized and taken to be mutually orthogonal.
    pub fn decompose(self, axis0: Vec3d, axis1: Vec3d, axis2: Vec3d) -> Vec3d {
        // Below this the middle angle is at a pole and the other two turn
        // about one axis.
        const EPSILON: f64 = 1e-6;
        let (n0, n1, n2) = (axis0.normalize(), axis1.normalize(), axis2.normalize());

        let mut axes = Mat4d::IDENTITY;
        for (c, axis) in [n0, n1, n2].into_iter().enumerate() {
            axes[(0, c)] = axis.x;
            axes[(1, c)] = axis.y;
            axes[(2, c)] = axis.z;
        }
        // The rotation in the frame whose X, Y and Z are the three axes.
        let m = axes.transpose() * Mat4d::from_quat(self.quat()) * axes;

        // Ken Shoemake's Euler angle conversion (Graphics Gems IV, p. 222).
        let (i, j, k) = (0, 1, 2);
        let cy = m[(i, i)].hypot(m[(j, i)]);
        let mut angles = match cy > EPSILON {
            true => [
                m[(k, j)].atan2(m[(k, k)]),
                (-m[(k, i)]).atan2(cy),
                m[(j, i)].atan2(m[(i, i)]),
            ],
            false => [(-m[(j, k)]).atan2(m[(j, j)]), (-m[(k, i)]).atan2(cy), 0.0],
        };
        if n0.cross(n1).dot(n2) >= 0.0 {
            angles = angles.map(|angle| -angle);
        }
        Vec3d {
            x: angles[0].to_degrees(),
            y: angles[1].to_degrees(),
            z: angles[2].to_degrees(),
        }
    }

    /// The rotation as a unit quaternion (C++ `GetQuat`).
    pub fn quat(self) -> Quatd {
        let (sin, cos) = (self.angle.to_radians() / 2.0).sin_cos();
        let axis = self.axis * sin;
        Quatd {
            w: cos,
            x: axis.x,
            y: axis.y,
            z: axis.z,
        }
        .normalize()
    }
}

impl Default for Rotation {
    fn default() -> Self {
        Self::IDENTITY
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf;

    #[test]
    fn quat_round_trip() {
        let q = gf::quatd(0.5, 0.5, 0.5, 0.5);
        let r = Rotation::from_quat(q);
        assert!((r.angle() - 120.0).abs() < 1e-12);
        let back = r.quat();
        for (a, b) in [(back.w, q.w), (back.x, q.x), (back.y, q.y), (back.z, q.z)] {
            assert!((a - b).abs() < 1e-15);
        }
    }

    #[test]
    fn short_imaginary_is_identity() {
        assert_eq!(Rotation::from_quat(gf::quatd(1.0, 0.0, 0.0, 0.0)), Rotation::IDENTITY);
        assert_eq!(Rotation::from_quat(gf::quatd(0.5, 1e-11, 0.0, 0.0)), Rotation::IDENTITY);
    }

    /// An imaginary part exactly [`MIN_VECTOR_LENGTH`] long is the identity;
    /// the next one up is a rotation.
    #[test]
    fn imaginary_length_threshold() {
        let at = Rotation::from_quat(gf::quatd(0.5, MIN_VECTOR_LENGTH, 0.0, 0.0));
        assert_eq!(at, Rotation::IDENTITY);
        let above = Rotation::from_quat(gf::quatd(0.5, 1.0000001e-10, 0.0, 0.0));
        assert_eq!(above.axis(), gf::vec3d(1.0, 0.0, 0.0));
        assert!((above.angle() - 120.0).abs() < 1e-12);
    }

    /// A quaternion with a NaN in its imaginary part is the identity, as in
    /// C++. A NaN real part keeps the axis and makes the angle NaN.
    #[test]
    fn nan_components() {
        for q in [
            gf::quatd(0.5, f64::NAN, 0.0, 0.0),
            gf::quatd(0.5, 0.0, f64::NAN, 1.0),
            gf::quatd(0.5, 1.0, 0.0, f64::NAN),
        ] {
            assert_eq!(Rotation::from_quat(q), Rotation::IDENTITY);
        }
        let r = Rotation::from_quat(gf::quatd(f64::NAN, 1.0, 0.0, 0.0));
        assert_eq!(r.axis(), gf::vec3d(1.0, 0.0, 0.0));
        assert!(r.angle().is_nan());
    }

    #[test]
    fn axis_normalized() {
        let r = Rotation::new(gf::vec3d(0.0, 0.0, 2.0), 90.0);
        assert_eq!(r.axis(), gf::vec3d(0.0, 0.0, 1.0));
        assert_eq!(r.inverse().angle(), -90.0);
    }

    /// The real part, not the quaternion's length, decides the angle: a
    /// `quatf` of a 90° turn about X sits 3.4e-8 past 90°, as in C++.
    #[test]
    fn angle_from_real_part() {
        let r = Rotation::from_quat(gf::quatd(0.70710677_f32 as f64, 0.70710677_f32 as f64, 0.0, 0.0));
        assert!(r.angle() > 90.0 && r.angle() - 90.0 < 3e-6);
        assert_eq!(r.axis(), gf::vec3d(1.0, 0.0, 0.0));
    }

    /// The angles come back against the axes in the order asked, the last
    /// axis being the first a point turns about.
    #[test]
    fn decompose_euler() {
        let (x, y, z) = (
            gf::vec3d(1.0, 0.0, 0.0),
            gf::vec3d(0.0, 1.0, 0.0),
            gf::vec3d(0.0, 0.0, 1.0),
        );
        let turn = |x_deg: f64, y_deg: f64, z_deg: f64| {
            Mat4d::rotation_x(x_deg.to_radians())
                * Mat4d::rotation_y(y_deg.to_radians())
                * Mat4d::rotation_z(z_deg.to_radians())
        };
        let rotation = turn(10.0, 20.0, 30.0).extract_rotation();

        let zyx = rotation.decompose(z, y, x);
        for (got, want) in [(zyx.x, 30.0), (zyx.y, 20.0), (zyx.z, 10.0)] {
            assert!((got - want).abs() < 1e-9, "{zyx:?}");
        }
        // About X, Y, Z the same rotation is a turn about Z first.
        let xyz = rotation.decompose(x, y, z);
        let back = Mat4d::rotation_z(xyz.z.to_radians())
            * Mat4d::rotation_y(xyz.y.to_radians())
            * Mat4d::rotation_x(xyz.x.to_radians());
        crate::gf::matrix::tests::assert_close(back, turn(10.0, 20.0, 30.0));
    }

    /// At the pole of the middle angle the third angle is zero and the first
    /// carries the turn.
    #[test]
    fn decompose_gimbal_lock() {
        let (x, y, z) = (
            gf::vec3d(1.0, 0.0, 0.0),
            gf::vec3d(0.0, 1.0, 0.0),
            gf::vec3d(0.0, 0.0, 1.0),
        );
        let angles = Rotation::new(y, 90.0).decompose(x, y, z);
        assert!((angles.y - 90.0).abs() < 1e-6, "{angles:?}");
        assert_eq!(angles.z, 0.0);
    }
}
