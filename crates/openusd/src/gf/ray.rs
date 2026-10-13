//! `GfRay` — a point and the direction it looks along.

use super::{MIN_VECTOR_LENGTH, Mat4d, Plane, Vec3d};

/// A ray: the point it starts at and the direction it runs in (C++ `GfRay`).
///
/// The direction is kept as given, at whatever length. A distance along the
/// ray is in units of that length, so [`point`](Self::point) of one is the
/// start moved by the whole direction.
///
/// ```
/// use openusd::gf;
///
/// let ray = gf::Ray::new(gf::vec3d(0.0, 0.0, 5.0), gf::vec3d(0.0, 0.0, -1.0));
/// let ground = gf::Plane::new(gf::Vec3d::Z_AXIS, 0.0);
/// let (distance, front_facing) = ray.intersect_plane(&ground).expect("the ray points at it");
/// assert_eq!((distance, front_facing), (5.0, true));
/// assert_eq!(ray.point(distance), gf::vec3d(0.0, 0.0, 0.0));
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Ray {
    /// Where the ray starts.
    pub start: Vec3d,
    /// The direction the ray runs in.
    pub direction: Vec3d,
}

/// Where a [`Ray`] meets a triangle.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TriangleHit {
    /// How far along the ray the triangle is, in lengths of its direction.
    pub distance: f64,
    /// The weights of the triangle's three points at the place it is met,
    /// which sum to one.
    pub barycentric: Vec3d,
    /// Whether the ray meets the side the points run counter-clockwise on.
    pub front_facing: bool,
}

impl Ray {
    /// The ray from `start` along `direction`.
    pub const fn new(start: Vec3d, direction: Vec3d) -> Self {
        Ray { start, direction }
    }

    /// The point `distance` lengths of the direction along the ray (C++
    /// `GetPoint`).
    pub fn point(&self, distance: f64) -> Vec3d {
        self.start + self.direction * distance
    }

    /// The ray under `matrix` (C++ `Transform`): its start as a point and
    /// its direction as a direction.
    pub fn transformed(self, matrix: Mat4d) -> Ray {
        Ray {
            start: matrix.transform(self.start),
            direction: matrix.transform_dir(self.direction),
        }
    }

    /// Where the ray meets `plane` (C++ `Intersect` with a plane): the
    /// distance along the ray, and whether it meets the side the normal
    /// points into. `None` for a ray that runs along the plane or away from
    /// it.
    pub fn intersect_plane(&self, plane: &Plane) -> Option<(f64, bool)> {
        let facing = self.direction.dot(plane.normal());
        if facing.abs() < MIN_VECTOR_LENGTH {
            return None;
        }
        let on_plane = plane.normal() * plane.distance_from_origin();
        let distance = (on_plane - self.start).dot(plane.normal()) / facing;
        (distance >= 0.0).then_some((distance, facing < 0.0))
    }

    /// Where the ray meets the triangle of three points (C++ `Intersect`
    /// with a triangle), or `None` where it misses.
    ///
    /// The triangle is projected along the axis its plane faces most, and
    /// the point is placed in it there. A weight that falls short of zero by
    /// less than [`MIN_VECTOR_LENGTH`] counts as zero, so a ray along an
    /// edge is a hit.
    ///
    /// C++ takes a distance past which a hit is not reported; here the
    /// caller compares [`TriangleHit::distance`]. A triangle of no area has
    /// no weights to place a point by and is missed, where C++ reports it
    /// hit with weights that are not numbers.
    pub fn intersect_triangle(&self, p0: Vec3d, p1: Vec3d, p2: Vec3d) -> Option<TriangleHit> {
        let plane = Plane::from_points(p0, p1, p2);
        let (distance, front_facing) = self.intersect_plane(&plane)?;

        let normal = plane.normal();
        let (x, y, z) = (normal.x.abs(), normal.y.abs(), normal.z.abs());
        let (a0, a1) = if x > y && x > z {
            (1, 2)
        } else if y > z {
            (2, 0)
        } else {
            (0, 1)
        };

        let hit = self.point(distance);
        let d0 = [hit[a0] - p0[a0], hit[a1] - p0[a1]];
        let d1 = [p1[a0] - p0[a0], p1[a1] - p0[a1]];
        let d2 = [p2[a0] - p0[a0], p2[a1] - p0[a1]];

        let nearly_zero = |weight: f64| weight < 0.0 && weight > -MIN_VECTOR_LENGTH;
        let mut beta = (d0[1] * d1[0] - d0[0] * d1[1]) / (d2[1] * d1[0] - d2[0] * d1[1]);
        if nearly_zero(beta) {
            beta = 0.0;
        }
        // A weight that is not a number is outside the range too.
        if !(0.0..=1.0).contains(&beta) {
            return None;
        }
        let mut alpha = match d1[1].abs() > MIN_VECTOR_LENGTH {
            true => (d0[1] - beta * d2[1]) / d1[1],
            false => (d0[0] - beta * d2[0]) / d1[0],
        };
        if nearly_zero(alpha) {
            alpha = 0.0;
        }
        // C++ holds the third weight in single precision.
        let mut gamma = f64::from((1.0 - (alpha + beta)) as f32);
        if nearly_zero(gamma) {
            gamma = 0.0;
        }
        if alpha < 0.0 || gamma < 0.0 {
            return None;
        }
        Some(TriangleHit {
            distance,
            barycentric: Vec3d {
                x: gamma,
                y: alpha,
                z: beta,
            },
            front_facing,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Ray;
    use crate::gf;

    /// A ray meets a plane ahead of it, on the side it comes from, and
    /// misses one behind it or alongside it.
    #[test]
    fn plane_ahead_or_behind() {
        let plane = gf::Plane::new(gf::Vec3d::Z_AXIS, 0.0);
        let down = Ray::new(gf::vec3d(1.0, 2.0, 4.0), gf::vec3d(0.0, 0.0, -2.0));
        assert_eq!(down.intersect_plane(&plane), Some((2.0, true)));
        assert_eq!(down.point(2.0), gf::vec3d(1.0, 2.0, 0.0));

        let up = Ray::new(gf::vec3d(1.0, 2.0, -4.0), gf::Vec3d::Z_AXIS);
        assert_eq!(up.intersect_plane(&plane), Some((4.0, false)));

        let away = Ray::new(gf::vec3d(0.0, 0.0, 4.0), gf::Vec3d::Z_AXIS);
        assert_eq!(away.intersect_plane(&plane), None);
        let along = Ray::new(gf::vec3d(0.0, 0.0, 4.0), gf::Vec3d::X_AXIS);
        assert_eq!(along.intersect_plane(&plane), None);
    }

    /// A ray through a triangle reports where, as weights of its points.
    #[test]
    fn triangle_hit_and_miss() {
        let (p0, p1, p2) = (
            gf::vec3d(0.0, 0.0, 0.0),
            gf::vec3d(4.0, 0.0, 0.0),
            gf::vec3d(0.0, 4.0, 0.0),
        );
        let ray = Ray::new(gf::vec3d(1.0, 2.0, 3.0), gf::vec3d(0.0, 0.0, -1.0));
        let hit = ray.intersect_triangle(p0, p1, p2).expect("the ray is over it");
        assert_eq!(hit.distance, 3.0);
        assert!(hit.front_facing);
        assert_eq!(hit.barycentric, gf::vec3d(0.25, 0.25, 0.5));
        let placed = p0 * hit.barycentric.x + p1 * hit.barycentric.y + p2 * hit.barycentric.z;
        assert_eq!(placed, ray.point(hit.distance));

        let beside = Ray::new(gf::vec3d(3.0, 3.0, 3.0), gf::vec3d(0.0, 0.0, -1.0));
        assert_eq!(beside.intersect_triangle(p0, p1, p2), None);
        let behind = Ray::new(gf::vec3d(1.0, 1.0, 3.0), gf::Vec3d::Z_AXIS);
        assert_eq!(behind.intersect_triangle(p0, p1, p2), None);

        // From the other side the same place is met from behind.
        let below = Ray::new(gf::vec3d(1.0, 2.0, -3.0), gf::Vec3d::Z_AXIS);
        let hit = below.intersect_triangle(p0, p1, p2).expect("the ray is under it");
        assert!(!hit.front_facing);

        // A corner and an edge are part of the triangle.
        let corner = Ray::new(gf::vec3d(0.0, 0.0, 1.0), gf::vec3d(0.0, 0.0, -1.0));
        assert!(corner.intersect_triangle(p0, p1, p2).is_some());
        let edge = Ray::new(gf::vec3d(2.0, 2.0, 1.0), gf::vec3d(0.0, 0.0, -1.0));
        assert!(edge.intersect_triangle(p0, p1, p2).is_some());
    }

    /// The start moves as a point and the direction as a direction.
    #[test]
    fn transformed_parts() {
        let ray = Ray::new(gf::vec3d(1.0, 0.0, 0.0), gf::Vec3d::X_AXIS);
        let moved = ray.transformed(gf::Mat4d::scale([2.0, 1.0, 1.0]) * gf::Mat4d::translation([0.0, 5.0, 0.0]));
        assert_eq!(moved.start, gf::vec3d(2.0, 5.0, 0.0));
        assert_eq!(moved.direction, gf::vec3d(2.0, 0.0, 0.0));
    }
}
