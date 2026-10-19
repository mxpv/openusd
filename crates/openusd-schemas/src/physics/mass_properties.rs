//! The mass, inertia tensor and center of mass of a body, and the arithmetic
//! that moves, turns and combines them (C++ `usdPhysics/massProperties.h`).

use std::ops::Mul;

use openusd::gf;

/// A body's mass, inertia tensor and center of mass (C++
/// `UsdPhysicsMassProperties`), in the units of the stage they come from.
///
/// The inertia tensor is about the center of mass, in the frame the
/// properties are expressed in. The default is a unit mass with the identity
/// tensor at the origin. The arithmetic runs in `f64`, where C++ runs it in
/// `f32`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MassProperties {
    /// The mass.
    pub mass: f64,
    /// The inertia tensor about `center_of_mass`.
    pub inertia: gf::Mat3d,
    /// The center of mass.
    pub center_of_mass: gf::Vec3d,
}

impl Default for MassProperties {
    fn default() -> Self {
        Self {
            mass: 1.0,
            inertia: gf::Mat3d::IDENTITY,
            center_of_mass: gf::Vec3d::default(),
        }
    }
}

impl MassProperties {
    /// Move the center of mass by `t` and carry the inertia tensor along, by
    /// [`translate_inertia`](Self::translate_inertia) (C++ `Translate`).
    pub fn translate(&mut self, t: gf::Vec3d) {
        self.inertia = Self::translate_inertia(self.inertia, self.mass, t);
        self.center_of_mass += t;
    }

    /// The tensor `inertia` of a body of `mass`, about its center of mass,
    /// moved to the point `t` away by the parallel axis theorem (C++
    /// `TranslateInertia`).
    pub fn translate_inertia(inertia: gf::Mat3d, mass: f64, t: gf::Vec3d) -> gf::Mat3d {
        // The cross-product matrix of `t`, whose product with its transpose
        // is `|t|² E − t tᵀ`.
        let s = gf::Mat3d([0.0, -t.z, t.y, t.z, 0.0, -t.x, -t.y, t.x, 0.0]);
        s * s.transpose() * mass + inertia
    }

    /// The tensor `inertia` turned by the unit quaternion `q` about the
    /// center of mass (C++ `RotateInertia`).
    pub fn rotate_inertia(inertia: gf::Mat3d, q: gf::Quatd) -> gf::Mat3d {
        let m = gf::Mat3d::from_quat(q);
        m.transpose() * inertia * m
    }

    /// The bodies in `parts` as one body, each under its transform (C++
    /// `Sum`). The masses add, the center of mass is their mass-weighted
    /// mean, and each inertia tensor is turned by its transform's rotation
    /// and moved to the combined center of mass. The rotation is read by
    /// [`gf::Mat4d::extract_rotation`], which takes the transform's 3×3 for a
    /// pure rotation. Bodies with no mass between them balance at the origin.
    pub fn sum(parts: &[(MassProperties, gf::Mat4d)]) -> MassProperties {
        let mass: f64 = parts.iter().map(|(body, _)| body.mass).sum();
        let mut center_of_mass: gf::Vec3d = parts
            .iter()
            .map(|(body, transform)| transform.transform(body.center_of_mass) * body.mass)
            .sum();
        if mass > 0.0 {
            center_of_mass /= mass;
        }
        let inertia = parts.iter().fold(gf::Mat3d::ZERO, |total, (body, transform)| {
            let turned = Self::rotate_inertia(body.inertia, transform.extract_rotation().quat());
            let offset = center_of_mass - transform.transform(body.center_of_mass);
            total + Self::translate_inertia(turned, body.mass, offset)
        });
        MassProperties {
            mass,
            inertia,
            center_of_mass,
        }
    }

    /// The moments of `inertia` about its principal axes, and the orientation
    /// of those axes (C++ `GetMassSpaceInertia` over `UsdPhysicsDiagonalize`),
    /// which is what `physics:principalAxes` stores:
    /// [`rotate_inertia`](Self::rotate_inertia) of the diagonal of the moments
    /// by that orientation is `inertia` again, to within the last of up to 24
    /// Jacobi rounds.
    pub fn mass_space_inertia(inertia: gf::Mat3d) -> (gf::Vec3d, gf::Quatd) {
        const MAX_ROUNDS: usize = 24;
        let mut q = gf::Quatd::IDENTITY;
        let mut d = gf::Mat3d::IDENTITY;
        for _ in 0..MAX_ROUNDS {
            let axes = gf::Mat3d::from_quat(q);
            d = axes * inertia * axes.transpose();

            // Turn about the axis of the largest off-diagonal entry, which
            // couples the other two.
            let (yz, xz, xy) = (d[(1, 2)].abs(), d[(0, 2)].abs(), d[(0, 1)].abs());
            let a = if yz > xz && yz > xy {
                0
            } else if xz > xy {
                1
            } else {
                2
            };
            let (a1, a2) = ((a + 1) % 3, (a + 2) % 3);
            let coupling = d[(a1, a2)];
            if coupling == 0.0 || (d[(a1, a1)] - d[(a2, a2)]).abs() > 2e6 * (2.0 * coupling).abs() {
                break;
            }

            // cot(2φ) for the rotation angle φ that zeroes the coupling.
            let w = (d[(a1, a1)] - d[(a2, a2)]) / (2.0 * coupling);
            let r = if w.abs() > 1000.0 {
                // cos φ is as good as one: the small-angle form.
                indexed_rotation(a, 1.0 / (4.0 * w), 1.0)
            } else {
                let tan = 1.0 / (w.abs() + (w * w + 1.0).sqrt());
                let cos = 1.0 / (tan * tan + 1.0).sqrt();
                let sign = if w >= 0.0 { 1.0 } else { -1.0 };
                indexed_rotation(a, ((1.0 - cos) / 2.0).sqrt() * sign, ((1.0 + cos) / 2.0).sqrt())
            };
            q = (q * r).normalize();
        }
        let moments = gf::Vec3d {
            x: d[(0, 0)],
            y: d[(1, 1)],
            z: d[(2, 2)],
        };
        (moments, q)
    }
}

/// The body `scale` times as heavy (C++ `operator*`): the mass and the
/// inertia tensor scale, the center of mass stays.
impl Mul<f64> for MassProperties {
    type Output = MassProperties;

    fn mul(self, scale: f64) -> MassProperties {
        MassProperties {
            mass: self.mass * scale,
            inertia: self.inertia * scale,
            center_of_mass: self.center_of_mass,
        }
    }
}

/// The quaternion with real part `c` and imaginary part `s` along `axis`
/// (C++ `UsdPhysicsIndexedRotation`).
fn indexed_rotation(axis: usize, s: f64, c: f64) -> gf::Quatd {
    let mut imaginary = [0.0; 3];
    imaginary[axis] = s;
    gf::Quatd::new(c, imaginary.into())
}

#[cfg(test)]
mod tests {
    use std::f64::consts::FRAC_PI_2;

    use openusd::gf;

    use super::MassProperties;

    fn assert_close(got: gf::Mat3d, want: gf::Mat3d) {
        assert!(got.is_close(want, 1e-9), "{got:?} != {want:?}");
    }

    /// The default is a unit mass with the identity tensor at the origin.
    /// Scaling multiplies the mass and the tensor and keeps the center.
    #[test]
    fn default_and_scale() {
        assert_eq!(
            MassProperties::default(),
            MassProperties {
                mass: 1.0,
                inertia: gf::Mat3d::IDENTITY,
                center_of_mass: gf::Vec3d::default(),
            }
        );
        let doubled = MassProperties {
            center_of_mass: gf::Vec3d::X_AXIS,
            ..Default::default()
        } * 2.0;
        assert_eq!(
            doubled,
            MassProperties {
                mass: 2.0,
                inertia: gf::Mat3d::diagonal([2.0; 3]),
                center_of_mass: gf::Vec3d::X_AXIS,
            }
        );
    }

    /// Moving a point mass by `t` gives it the parallel-axis tensor
    /// `m (|t|² E − t tᵀ)` and moves its center; a tensor already there adds
    /// to it.
    #[test]
    fn translate_point_mass() {
        let t = gf::vec3d(1.0, 2.0, 3.0);
        let mut point = MassProperties {
            mass: 2.0,
            inertia: gf::Mat3d::ZERO,
            ..Default::default()
        };
        point.translate(t);
        assert_eq!(point.center_of_mass, t);
        let expected = gf::Mat3d::from([
            [t.y * t.y + t.z * t.z, -t.x * t.y, -t.x * t.z],
            [-t.x * t.y, t.x * t.x + t.z * t.z, -t.y * t.z],
            [-t.x * t.z, -t.y * t.z, t.x * t.x + t.y * t.y],
        ]) * 2.0;
        assert_close(point.inertia, expected);
        assert_close(
            MassProperties::translate_inertia(gf::Mat3d::IDENTITY, 2.0, t),
            expected + gf::Mat3d::IDENTITY,
        );
    }

    /// A quarter turn about Z swaps the X and Y moments; the identity leaves
    /// the tensor.
    #[test]
    fn rotate_quarter_turn() {
        let d = gf::Mat3d::diagonal([1.0, 2.0, 3.0]);
        assert_eq!(MassProperties::rotate_inertia(d, gf::Quatd::IDENTITY), d);
        let quarter = gf::Mat4d::rotation_z(FRAC_PI_2).extract_rotation_quat();
        assert_close(
            MassProperties::rotate_inertia(d, quarter),
            gf::Mat3d::diagonal([2.0, 1.0, 3.0]),
        );
    }

    /// Two unit point masses a unit either side of the origin weigh two,
    /// balance at the origin and resist turning about Y and Z by two. One
    /// body under a translation keeps its tensor and moves its center; under
    /// a rotation its tensor turns with it. No bodies weigh nothing at the
    /// origin.
    #[test]
    fn sum_bodies() {
        let point = MassProperties {
            mass: 1.0,
            inertia: gf::Mat3d::ZERO,
            ..Default::default()
        };
        let pair = MassProperties::sum(&[
            (point, gf::Mat4d::translation([1.0, 0.0, 0.0])),
            (point, gf::Mat4d::translation([-1.0, 0.0, 0.0])),
        ]);
        assert_eq!(pair.mass, 2.0);
        assert_eq!(pair.center_of_mass, gf::Vec3d::default());
        assert_close(pair.inertia, gf::Mat3d::diagonal([0.0, 2.0, 2.0]));

        let body = MassProperties {
            mass: 3.0,
            inertia: gf::Mat3d::diagonal([1.0, 2.0, 3.0]),
            center_of_mass: gf::Vec3d::X_AXIS,
        };
        let moved = MassProperties::sum(&[(body, gf::Mat4d::translation([0.0, 5.0, 0.0]))]);
        assert_eq!(moved.mass, 3.0);
        assert_eq!(moved.center_of_mass, gf::vec3d(1.0, 5.0, 0.0));
        assert_close(moved.inertia, body.inertia);

        let quarter = gf::Mat4d::rotation_z(FRAC_PI_2);
        let turned = MassProperties::sum(&[(body, quarter)]);
        assert!((turned.center_of_mass - quarter.transform(gf::Vec3d::X_AXIS)).length() < 1e-12);
        assert_close(turned.inertia, gf::Mat3d::diagonal([2.0, 1.0, 3.0]));

        assert_eq!(
            MassProperties::sum(&[]),
            MassProperties {
                mass: 0.0,
                inertia: gf::Mat3d::ZERO,
                center_of_mass: gf::Vec3d::default(),
            }
        );
    }

    /// A diagonal tensor is its own moments in the identity frame. A turned
    /// one comes back to the same moments, and the orientation returned turns
    /// their diagonal back into it.
    #[test]
    fn mass_space_inertia() {
        let d = gf::Mat3d::diagonal([1.0, 2.0, 3.0]);
        assert_eq!(
            MassProperties::mass_space_inertia(d),
            (gf::vec3d(1.0, 2.0, 3.0), gf::Quatd::IDENTITY)
        );

        let q = gf::quatd(0.9, 0.1, 0.2, 0.3).normalize();
        let turned = MassProperties::rotate_inertia(d, q);
        let (moments, axes) = MassProperties::mass_space_inertia(turned);
        let mut sorted: [f64; 3] = moments.into();
        sorted.sort_by(f64::total_cmp);
        assert!(sorted.iter().zip([1.0, 2.0, 3.0]).all(|(a, b)| (a - b).abs() < 1e-9));
        // The rounds stop once the coupling is negligible. The orientation
        // recovers the tensor to within that tolerance.
        let recovered = MassProperties::rotate_inertia(gf::Mat3d::diagonal(moments), axes);
        assert!(recovered.is_close(turned, 1e-6), "{recovered:?} != {turned:?}");
    }
}
