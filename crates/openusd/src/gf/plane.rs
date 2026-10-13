//! `GfPlane` — a plane dividing space in two.

use super::{Mat4d, Range3d, Vec3d, Vec4d};

/// A plane, given by the unit normal it faces along and how far along that
/// normal it stands from the origin (C++ `GfPlane`).
///
/// The plane divides space into the positive half-space its normal points
/// into, and the half-space behind it.
///
/// ```
/// use openusd::gf;
///
/// let floor = gf::Plane::new(gf::Vec3d::Y_AXIS, 2.0);
/// assert_eq!(floor.distance(gf::vec3d(5.0, 3.0, 5.0)), 1.0);
/// assert!(floor.on_positive_side(gf::vec3d(0.0, 2.0, 0.0)));
/// assert!(!floor.on_positive_side(gf::vec3d(0.0, 1.0, 0.0)));
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Plane {
    normal: Vec3d,
    distance: f64,
}

impl Plane {
    /// The plane facing along `normal`, which is made unit length, at
    /// `distance` along it from the origin.
    pub fn new(normal: Vec3d, distance: f64) -> Self {
        Plane {
            normal: normal.normalize(),
            distance,
        }
    }

    /// The plane through three points, facing the side they are seen to run
    /// counter-clockwise from.
    pub fn from_points(p0: Vec3d, p1: Vec3d, p2: Vec3d) -> Self {
        let normal = (p1 - p0).cross(p2 - p0).normalize();
        Plane {
            normal,
            distance: normal.dot(p0),
        }
    }

    /// The plane of the points where `a·x + b·y + c·z + d` is zero, for the
    /// equation `(a, b, c, d)`. The equation is scaled to make the normal
    /// unit length.
    pub fn from_equation(equation: Vec4d) -> Self {
        let normal = Vec3d {
            x: equation.x,
            y: equation.y,
            z: equation.z,
        };
        let length = normal.length();
        Plane {
            normal: normal.normalize(),
            distance: match length {
                0.0 => -equation.w,
                length => -equation.w / length,
            },
        }
    }

    /// The unit normal (C++ `GetNormal`).
    pub fn normal(&self) -> Vec3d {
        self.normal
    }

    /// How far along the normal the plane stands from the origin (C++
    /// `GetDistanceFromOrigin`).
    pub fn distance_from_origin(&self) -> f64 {
        self.distance
    }

    /// The equation `(a, b, c, d)` the points of the plane satisfy as
    /// `a·x + b·y + c·z + d = 0` (C++ `GetEquation`).
    pub fn equation(&self) -> Vec4d {
        Vec4d {
            x: self.normal.x,
            y: self.normal.y,
            z: self.normal.z,
            w: -self.distance,
        }
    }

    /// How far `point` is from the plane (C++ `GetDistance`), positive on
    /// the side the normal points into.
    pub fn distance(&self, point: Vec3d) -> f64 {
        point.dot(self.normal) - self.distance
    }

    /// Whether `point` is on the plane or in its positive half-space (C++
    /// `IntersectsPositiveHalfSpace` of a point).
    pub fn on_positive_side(&self, point: Vec3d) -> bool {
        self.distance(point) >= 0.0
    }

    /// Whether any of `range` is on the plane or in its positive half-space
    /// (C++ `IntersectsPositiveHalfSpace` of a range). An empty range has
    /// nothing there.
    pub fn reaches_positive_side(&self, range: Range3d) -> bool {
        if range.is_empty() {
            return false;
        }
        // The corner furthest along the normal takes, on each axis, the end
        // the normal points toward.
        let (min, max) = (range.min(), range.max());
        let furthest = (0..3)
            .map(|i| self.normal[i] * if self.normal[i] >= 0.0 { max[i] } else { min[i] })
            .sum::<f64>();
        furthest >= self.distance
    }

    /// The plane under `matrix` (C++ `Transform`), or `None` where the
    /// matrix has no inverse.
    pub fn transformed(self, matrix: Mat4d) -> Option<Plane> {
        Some(self.under_inverse(matrix.inverse()?))
    }

    /// The plane under the transform whose inverse is `inverse`. A plane's
    /// equation is carried by the transpose of that inverse.
    pub(super) fn under_inverse(self, inverse: Mat4d) -> Plane {
        Plane::from_equation(inverse.transpose().transform_homogeneous(self.equation()))
    }
}

#[cfg(test)]
mod tests {
    use super::Plane;
    use crate::gf;

    /// Three points give the plane through them, facing the side they turn
    /// counter-clockwise on.
    #[test]
    fn through_three_points() {
        let plane = Plane::from_points(
            gf::vec3d(0.0, 0.0, 2.0),
            gf::vec3d(1.0, 0.0, 2.0),
            gf::vec3d(0.0, 1.0, 2.0),
        );
        assert_eq!(plane.normal(), gf::Vec3d::Z_AXIS);
        assert_eq!(plane.distance_from_origin(), 2.0);
        assert_eq!(plane.distance(gf::vec3d(7.0, 7.0, 5.0)), 3.0);
        assert_eq!(plane.distance(gf::vec3d(7.0, 7.0, 0.0)), -2.0);
    }

    /// The normal is made unit length, and an equation comes back scaled to
    /// match.
    #[test]
    fn equation_round_trip() {
        let plane = Plane::new(gf::vec3d(0.0, 3.0, 0.0), 2.0);
        assert_eq!(plane.normal(), gf::Vec3d::Y_AXIS);
        assert_eq!(plane.equation(), gf::vec4d(0.0, 1.0, 0.0, -2.0));
        assert_eq!(Plane::from_equation(gf::vec4d(0.0, 4.0, 0.0, -8.0)), plane);
    }

    /// A range reaches the positive side when its furthest corner does.
    #[test]
    fn range_against_plane() {
        let plane = Plane::new(gf::vec3d(1.0, 1.0, 0.0), 2.0);
        let near = gf::Range3d::new(gf::vec3d(0.0, 0.0, 0.0), gf::vec3d(1.0, 1.0, 1.0));
        let far = gf::Range3d::new(gf::vec3d(0.0, 0.0, 0.0), gf::vec3d(2.0, 2.0, 1.0));
        assert!(!plane.reaches_positive_side(near));
        assert!(plane.reaches_positive_side(far));
        assert!(!plane.reaches_positive_side(gf::Range3d::EMPTY));

        let back = Plane::new(gf::vec3d(-1.0, 0.0, 0.0), -0.5);
        assert!(back.reaches_positive_side(near));
        assert!(!Plane::new(gf::vec3d(-1.0, 0.0, 0.0), 0.5).reaches_positive_side(near));
    }

    /// A plane moves with the points on it, and keeps a unit normal under a
    /// scale.
    #[test]
    fn transformed_with_points() {
        let plane = Plane::new(gf::Vec3d::Z_AXIS, 1.0);
        let matrix = gf::Mat4d::scale([2.0, 2.0, 3.0]) * gf::Mat4d::translation([0.0, 0.0, 4.0]);
        let moved = plane.transformed(matrix).expect("an invertible matrix");
        assert!((moved.normal() - gf::Vec3d::Z_AXIS).length() < 1e-12);
        assert!((moved.distance_from_origin() - 7.0).abs() < 1e-12);
        assert!(moved.distance(matrix.transform(gf::vec3d(5.0, 6.0, 1.0))).abs() < 1e-12);

        assert_eq!(plane.transformed(gf::Mat4d::scale([1.0, 0.0, 1.0])), None);
    }
}
