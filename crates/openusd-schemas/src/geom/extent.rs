//! The extent of each boundable shape from the values that size it: a
//! sphere's radius, a mesh's points, a curve's points and widths (the C++
//! static `ComputeExtent` of each `UsdGeom` class).
//!
//! An [`Extent`] is the two corners an `extent` attribute holds. Each
//! function takes a transform to compute the extent under, or `None` for the
//! extent in the shape's own space.

use openusd::gf;

use super::{Axis, Capsule, Capsule_1, Cone, Cube, Curves, Cylinder, Cylinder_1, Plane, PointBased, Points, Sphere};
use crate::SchemaError;

/// The minimum and maximum corners of an axis-aligned box, as an `extent`
/// attribute holds them. Geometry with no points has the corners of
/// [`gf::Range3d::EMPTY`], the minimum above the maximum.
pub type Extent = [gf::Vec3f; 2];

impl Sphere {
    /// The extent of a sphere of `radius` (C++ `UsdGeomSphere::ComputeExtent`).
    pub fn extent_from(radius: f64, transform: impl Into<Option<gf::Mat4d>>) -> Extent {
        centered(gf::vec3d(radius, radius, radius), transform.into())
    }
}

impl Cube {
    /// The extent of a cube with edges `size` long (C++
    /// `UsdGeomCube::ComputeExtent`).
    pub fn extent_from(size: f64, transform: impl Into<Option<gf::Mat4d>>) -> Extent {
        let half = size * 0.5;
        centered(gf::vec3d(half, half, half), transform.into())
    }
}

impl Cone {
    /// The extent of a cone `height` long on `axis` with a base of `radius`
    /// (C++ `UsdGeomCone::ComputeExtent`).
    pub fn extent_from(height: f64, radius: f64, axis: Axis, transform: impl Into<Option<gf::Mat4d>>) -> Extent {
        centered(along(axis, height * 0.5, radius), transform.into())
    }
}

impl Cylinder {
    /// The extent of a cylinder `height` long on `axis` with ends of
    /// `radius` (C++ `UsdGeomCylinder::ComputeExtent`).
    pub fn extent_from(height: f64, radius: f64, axis: Axis, transform: impl Into<Option<gf::Mat4d>>) -> Extent {
        centered(along(axis, height * 0.5, radius), transform.into())
    }
}

impl Cylinder_1 {
    /// The extent of a cylinder `height` long on `axis` whose ends have the
    /// radii given (C++ `UsdGeomCylinder_1::ComputeExtent`): the larger
    /// radius bounds both ends.
    pub fn extent_from(
        height: f64,
        radius_top: f64,
        radius_bottom: f64,
        axis: Axis,
        transform: impl Into<Option<gf::Mat4d>>,
    ) -> Extent {
        let radius = larger(radius_top, radius_bottom);
        centered(along(axis, height * 0.5, radius), transform.into())
    }
}

impl Capsule {
    /// The extent of a capsule whose cylinder is `height` long on `axis`,
    /// capped by hemispheres of `radius` (C++ `UsdGeomCapsule::ComputeExtent`).
    /// The caps add `radius` to each end.
    pub fn extent_from(height: f64, radius: f64, axis: Axis, transform: impl Into<Option<gf::Mat4d>>) -> Extent {
        centered(along(axis, height * 0.5 + radius, radius), transform.into())
    }
}

impl Capsule_1 {
    /// The extent of a capsule whose cylinder is `height` long on `axis`,
    /// capped by hemispheres of the radii given (C++
    /// `UsdGeomCapsule_1::ComputeExtent`): the larger radius bounds both
    /// ends.
    pub fn extent_from(
        height: f64,
        radius_top: f64,
        radius_bottom: f64,
        axis: Axis,
        transform: impl Into<Option<gf::Mat4d>>,
    ) -> Extent {
        let radius = larger(radius_top, radius_bottom);
        centered(along(axis, height * 0.5 + radius, radius), transform.into())
    }
}

impl Plane {
    /// The extent of a plane facing `axis`, `width` and `length` across (C++
    /// `UsdGeomPlane::ComputeExtent`). The width lies along X, or along Z
    /// for a plane facing X, and the length along the axis left.
    pub fn extent_from(width: f64, length: f64, axis: Axis, transform: impl Into<Option<gf::Mat4d>>) -> Extent {
        let (half_width, half_length) = ((width * 0.5) as f32, (length * 0.5) as f32);
        let max = match axis {
            Axis::X => gf::vec3f(0.0, half_length, half_width),
            Axis::Y => gf::vec3f(half_width, 0.0, half_length),
            Axis::Z => gf::vec3f(half_width, half_length, 0.0),
        };
        centered(max.into(), transform.into())
    }
}

impl PointBased {
    /// The extent of `points` (C++ `UsdGeomPointBased::ComputeExtent`), each
    /// moved by `transform` first where one is given.
    pub fn extent_from(points: &[gf::Vec3f], transform: impl Into<Option<gf::Mat4d>>) -> Extent {
        let transform = transform.into();
        let [mut min, mut max] = EMPTY;
        // TODO(rayon): each point extends the extent on its own, so chunks
        // of points reduce independently, as C++ `WorkParallelReduceN` does.
        for &point in points {
            let point = moved(point, transform);
            min = min.min(point);
            max = max.max(point);
        }
        [min, max]
    }
}

impl Points {
    /// The extent of `points` drawn `widths` across (C++
    /// `UsdGeomPoints::ComputeExtent`): each point bounds a sphere of half
    /// its width, which `transform` stretches with the point.
    ///
    /// Widths that are not one for each point are
    /// [`SchemaError::WidthCountMismatch`], where C++ returns `false`.
    ///
    /// Under a transform a sphere reaches its half width times the sum,
    /// along each axis, of the absolute values the transform's rotation and
    /// scale put there. C++ projects each sphere on its own, which sums the
    /// same terms in another order and can differ in the last bit.
    pub fn extent_from(
        points: &[gf::Vec3f],
        widths: &[f32],
        transform: impl Into<Option<gf::Mat4d>>,
    ) -> Result<Extent, SchemaError> {
        if points.len() != widths.len() {
            return Err(SchemaError::WidthCountMismatch {
                found: widths.len(),
                expected: points.len(),
            });
        }
        let transform = transform.into();
        // How far a sphere of unit radius reaches along each axis.
        let reach = match transform {
            Some(transform) => gf::Range3d::new(-UNIT, UNIT)
                .transformed(without_translation(transform))
                .max(),
            None => UNIT,
        };
        let [mut min, mut max] = EMPTY;
        // TODO(rayon): each point extends the extent on its own, so chunks
        // of points reduce independently.
        for (&point, &width) in points.iter().zip(widths) {
            let point = moved(point, transform);
            let half_width = f64::from(width * 0.5);
            // A sphere of negative radius holds nothing to stretch, and
            // reaches that radius along every axis, as it does in C++.
            let reach = match half_width < 0.0 {
                true => (UNIT * -half_width).to_f32(),
                false => (reach * half_width).to_f32(),
            };
            min = min.min(point - reach);
            max = max.max(point + reach);
        }
        Ok([min, max])
    }
}

impl Curves {
    /// The extent of curves through `points` drawn `widths` across (C++
    /// `UsdGeomCurves::ComputeExtent`): the extent of the points, grown by
    /// half the largest width, which `transform` stretches as it does the
    /// points. No widths grow it by nothing.
    ///
    /// The points bound a curve of any basis but Catmull-Rom and Hermite,
    /// whose curves may pass outside this extent. The largest width is the
    /// one C++ `std::max_element` finds. A NaN first width is kept.
    pub fn extent_from(points: &[gf::Vec3f], widths: &[f32], transform: impl Into<Option<gf::Mat4d>>) -> Extent {
        let transform = transform.into();
        let widest = widths
            .iter()
            .copied()
            .reduce(|widest, width| if widest < width { width } else { widest });
        let half_width = widest.unwrap_or(0.0) * 0.5;
        let [min, max] = PointBased::extent_from(points, transform);
        let [low, high] = Sphere::extent_from(half_width.into(), transform.map(without_translation));
        [min + low, max + high]
    }
}

/// The extent that holds nothing: the corners of [`gf::Range3d::EMPTY`].
pub(super) const EMPTY: Extent = [
    gf::Vec3f {
        x: f32::MAX,
        y: f32::MAX,
        z: f32::MAX,
    },
    gf::Vec3f {
        x: -f32::MAX,
        y: -f32::MAX,
        z: -f32::MAX,
    },
];

/// The far corner of the cube that bounds a sphere of unit radius.
const UNIT: gf::Vec3d = gf::Vec3d { x: 1.0, y: 1.0, z: 1.0 };

/// The extent of the box from `-max` to `max`, under `transform` where one
/// is given.
fn centered(max: gf::Vec3d, transform: Option<gf::Mat4d>) -> Extent {
    let range = gf::Range3d::new(-max, max);
    transform.map_or(range, |transform| range.transformed(transform)).into()
}

/// The far corner of a shape that reaches `half_length` along `axis` and
/// `radius` along the other two, in single precision as C++ holds it.
fn along(axis: Axis, half_length: f64, radius: f64) -> gf::Vec3d {
    let (half_length, radius) = (half_length as f32, radius as f32);
    gf::Vec3d::from(match axis {
        Axis::X => gf::vec3f(half_length, radius, radius),
        Axis::Y => gf::vec3f(radius, half_length, radius),
        Axis::Z => gf::vec3f(radius, radius, half_length),
    })
}

/// The larger of two radii as C++ `std::max` picks it: the first where the
/// two do not compare. A NaN first radius is kept.
fn larger(a: f64, b: f64) -> f64 {
    if a < b { b } else { a }
}

/// `point` under `transform` where one is given, in single precision as C++
/// transforms a `GfVec3f`.
fn moved(point: gf::Vec3f, transform: Option<gf::Mat4d>) -> gf::Vec3f {
    match transform {
        Some(transform) => transform.transform(point.into()).to_f32(),
        None => point,
    }
}

/// `transform` with its translation removed, which is what a size takes
/// from a transform its position has already been moved by.
fn without_translation(mut transform: gf::Mat4d) -> gf::Mat4d {
    transform.set_translation(gf::Vec3d::default());
    transform
}

#[cfg(test)]
pub(crate) mod tests {
    use openusd::gf;

    use super::Extent;
    use crate::SchemaError;
    use crate::geom::{
        Axis, Capsule, Capsule_1, Cone, Cube, Curves, Cylinder, Cylinder_1, Plane, PointBased, Points, Sphere,
    };

    /// The extent from `min` to `max`.
    pub(crate) fn extent(min: [f32; 3], max: [f32; 3]) -> Extent {
        [min.into(), max.into()]
    }

    fn assert_close(found: Extent, expected: Extent) {
        for (found, expected) in found.into_iter().zip(expected) {
            assert!((found - expected).length() < 1e-5, "{found:?} is not {expected:?}");
        }
    }

    /// A quarter turn about Z, which sends X to Y.
    fn quarter_turn() -> gf::Mat4d {
        gf::Mat4d::rotation_z(90f64.to_radians())
    }

    #[test]
    fn sphere_and_cube() {
        assert_eq!(Sphere::extent_from(2.0, None), extent([-2.0; 3], [2.0; 3]));
        assert_eq!(Cube::extent_from(2.0, None), extent([-1.0; 3], [1.0; 3]));

        let moved = gf::Mat4d::scale([1.0, 2.0, 3.0]) * gf::Mat4d::translation([10.0, 0.0, 0.0]);
        assert_eq!(
            Sphere::extent_from(1.0, moved),
            extent([9.0, -2.0, -3.0], [11.0, 2.0, 3.0])
        );
        assert_eq!(
            Cube::extent_from(2.0, moved),
            extent([9.0, -2.0, -3.0], [11.0, 2.0, 3.0])
        );

        // A turned cube is bounded by its corners.
        let turned = Cube::extent_from(2.0, gf::Mat4d::rotation_z(45f64.to_radians()));
        let reach = 2f32.sqrt();
        assert_close(turned, extent([-reach, -reach, -1.0], [reach, reach, 1.0]));
    }

    /// The height runs along the axis, and a capsule's caps add its radius
    /// to each end.
    #[test]
    fn shapes_along_axis() {
        for (axis, max) in [
            (Axis::X, [2.0, 1.0, 1.0]),
            (Axis::Y, [1.0, 2.0, 1.0]),
            (Axis::Z, [1.0, 1.0, 2.0]),
        ] {
            let expected = extent(max.map(|v: f32| -v), max);
            assert_eq!(Cone::extent_from(4.0, 1.0, axis, None), expected);
            assert_eq!(Cylinder::extent_from(4.0, 1.0, axis, None), expected);
            assert_eq!(Capsule::extent_from(2.0, 1.0, axis, None), expected);
        }

        // The sizes are held in single precision before any transform.
        let third = 1.0 / 3.0;
        let [_, max] = Cylinder::extent_from(2.0, third, Axis::X, gf::Mat4d::scale([1.0, 3.0, 1.0]));
        assert_eq!(max.y, (f64::from(third as f32) * 3.0) as f32);

        // The quarter turn sends a shape along X to one along Y.
        assert_close(
            Cylinder::extent_from(4.0, 1.0, Axis::X, quarter_turn()),
            Cylinder::extent_from(4.0, 1.0, Axis::Y, None),
        );
    }

    /// The larger of two end radii bounds both ends.
    #[test]
    fn two_radii() {
        assert_eq!(
            Cylinder_1::extent_from(4.0, 0.5, 1.0, Axis::Z, None),
            Cylinder::extent_from(4.0, 1.0, Axis::Z, None)
        );
        assert_eq!(
            Capsule_1::extent_from(2.0, 1.0, 0.25, Axis::Y, None),
            Capsule::extent_from(2.0, 1.0, Axis::Y, None)
        );
        // A first radius that is no number is not hidden by the second.
        let [_, max] = Cylinder_1::extent_from(4.0, f64::NAN, 1.0, Axis::Z, None);
        assert!(max.x.is_nan());
        assert_eq!(
            Capsule_1::extent_from(2.0, 1.0, 0.25, Axis::Y, gf::Mat4d::translation([0.0, 5.0, 0.0])),
            extent([-1.0, 3.0, -1.0], [1.0, 7.0, 1.0])
        );
    }

    /// A plane is flat along the axis it faces.
    #[test]
    fn plane_faces_axis() {
        assert_eq!(
            Plane::extent_from(2.0, 4.0, Axis::X, None),
            extent([0.0, -2.0, -1.0], [0.0, 2.0, 1.0])
        );
        assert_eq!(
            Plane::extent_from(2.0, 4.0, Axis::Y, None),
            extent([-1.0, 0.0, -2.0], [1.0, 0.0, 2.0])
        );
        assert_eq!(
            Plane::extent_from(2.0, 4.0, Axis::Z, None),
            extent([-1.0, -2.0, 0.0], [1.0, 2.0, 0.0])
        );
        assert_close(
            Plane::extent_from(2.0, 4.0, Axis::Z, quarter_turn()),
            extent([-2.0, -1.0, 0.0], [2.0, 1.0, 0.0]),
        );
    }

    #[test]
    fn point_based() {
        let points = [
            gf::vec3f(1.0, -2.0, 3.0),
            gf::vec3f(-4.0, 5.0, 0.0),
            gf::vec3f(0.0, 0.0, -6.0),
        ];
        assert_eq!(
            PointBased::extent_from(&points, None),
            extent([-4.0, -2.0, -6.0], [1.0, 5.0, 3.0])
        );
        assert_eq!(
            PointBased::extent_from(&points, gf::Mat4d::scale([2.0, 1.0, -1.0])),
            extent([-8.0, -2.0, -3.0], [2.0, 5.0, 6.0])
        );

        // No points hold nothing.
        let [min, max] = PointBased::extent_from(&[], None);
        assert!(min.x > max.x);
        assert_eq!(gf::Vec3d::from(min), gf::Range3d::EMPTY.min());
    }

    /// Each point reaches half its own width, and a transform stretches the
    /// reach without moving it.
    #[test]
    fn points_with_widths() -> Result<(), SchemaError> {
        let points = [gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(10.0, 0.0, 0.0)];
        let widths = [2.0, 4.0];
        assert_eq!(
            Points::extent_from(&points, &widths, None)?,
            extent([-1.0, -2.0, -2.0], [12.0, 2.0, 2.0])
        );

        let moved = gf::Mat4d::scale([1.0, 3.0, 1.0]) * gf::Mat4d::translation([0.0, 100.0, 0.0]);
        assert_eq!(
            Points::extent_from(&points, &widths, moved)?,
            extent([-1.0, 94.0, -2.0], [12.0, 106.0, 2.0])
        );

        // A turn spreads each sphere's reach over the axes it mixes, as it
        // does the cube that bounds the sphere.
        let turned = gf::Mat4d::rotation_z(45f64.to_radians());
        let [low, high] = Points::extent_from(&points[..1], &widths[..1], turned)?;
        let cube = Sphere::extent_from(1.0, turned);
        assert_close([low, high], cube);

        // A negative width reaches as far as its size, whatever the
        // transform.
        assert_eq!(
            Points::extent_from(&points[..1], &[-2.0], moved)?,
            extent([-1.0, 99.0, -1.0], [1.0, 101.0, 1.0])
        );

        assert!(matches!(
            Points::extent_from(&points, &widths[..1], None),
            Err(SchemaError::WidthCountMismatch { found: 1, expected: 2 })
        ));
        Ok(())
    }

    /// The largest width grows the extent of the points, and no widths grow
    /// it by nothing.
    #[test]
    fn curves_with_widths() {
        let points = [gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(10.0, 0.0, 0.0)];
        assert_eq!(
            Curves::extent_from(&points, &[2.0, 4.0], None),
            extent([-2.0, -2.0, -2.0], [12.0, 2.0, 2.0])
        );
        assert_eq!(
            Curves::extent_from(&points, &[], None),
            PointBased::extent_from(&points, None)
        );

        // A width that is no number is not hidden by the widths after it.
        let [min, _] = Curves::extent_from(&points, &[f32::NAN, 2.0], None);
        assert!(min.x.is_nan());

        let moved = gf::Mat4d::scale([1.0, 3.0, 1.0]) * gf::Mat4d::translation([0.0, 100.0, 0.0]);
        assert_eq!(
            Curves::extent_from(&points, &[2.0, 4.0], moved),
            extent([-2.0, 94.0, -2.0], [12.0, 106.0, 2.0])
        );
    }
}
