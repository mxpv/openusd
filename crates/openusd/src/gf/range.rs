//! `GfRange3d`, `GfRange2d`, `GfRange1d` and `GfRange1f` — an axis-aligned box
//! in three dimensions, a rectangle, and a span on a line.

use std::array;
use std::ops::{Add, Div, Mul, Sub};

use super::{Mat4d, Vec2d, Vec3d, Vec3f};

/// An axis-aligned box given by its minimum and maximum corners (C++
/// `GfRange3d`).
///
/// A range whose minimum exceeds its maximum along any axis is empty: it
/// holds no point, and the [`Default`] range is one. Extending an empty range
/// by a point makes it that point.
///
/// The arithmetic is interval arithmetic: `a + b` holds every sum of a point
/// of `a` and a point of `b`, `a - b` every difference, and `a * m` every
/// point of `a` scaled by `m`. An empty range has no points, so arithmetic
/// on one gives [`Range3d::EMPTY`], where C++ computes with its corners.
///
/// ```
/// use openusd::gf;
///
/// let mut range = gf::Range3d::default();
/// assert!(range.is_empty());
///
/// range.extend_by(gf::vec3d(1.0, 2.0, 3.0));
/// range.extend_by(gf::vec3d(-1.0, 0.0, 5.0));
/// assert_eq!(range.min(), gf::vec3d(-1.0, 0.0, 3.0));
/// assert_eq!(range.size(), gf::vec3d(2.0, 2.0, 2.0));
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Range3d {
    min: Vec3d,
    max: Vec3d,
}

impl Range3d {
    /// The empty range C++ builds by default: the largest `float` as the
    /// minimum and its negation as the maximum, so that the first point it
    /// is extended by replaces both.
    pub const EMPTY: Range3d = Range3d {
        min: Vec3d {
            x: f32::MAX as f64,
            y: f32::MAX as f64,
            z: f32::MAX as f64,
        },
        max: Vec3d {
            x: -(f32::MAX as f64),
            y: -(f32::MAX as f64),
            z: -(f32::MAX as f64),
        },
    };

    /// The cube from the origin to `(1, 1, 1)` (C++ `GfRange3d::UnitCube`).
    pub const UNIT_CUBE: Range3d = Range3d {
        min: Vec3d { x: 0.0, y: 0.0, z: 0.0 },
        max: Vec3d { x: 1.0, y: 1.0, z: 1.0 },
    };

    /// The range from `min` to `max`, which is empty where `min` exceeds
    /// `max` along any axis.
    pub const fn new(min: Vec3d, max: Vec3d) -> Self {
        Range3d { min, max }
    }

    /// The minimum corner (C++ `GetMin`).
    pub const fn min(&self) -> Vec3d {
        self.min
    }

    /// The maximum corner (C++ `GetMax`).
    pub const fn max(&self) -> Vec3d {
        self.max
    }

    /// The extent along each axis (C++ `GetSize`), negative along an axis
    /// the range is empty on.
    pub fn size(&self) -> Vec3d {
        self.max - self.min
    }

    /// The point halfway between the corners (C++ `GetMidpoint`). An empty
    /// range has no meaningful midpoint.
    pub fn midpoint(&self) -> Vec3d {
        self.min * 0.5 + self.max * 0.5
    }

    /// Whether the range holds no point (C++ `IsEmpty`).
    pub fn is_empty(&self) -> bool {
        self.min.x > self.max.x || self.min.y > self.max.y || self.min.z > self.max.z
    }

    /// Grow the range to hold `point` (C++ `ExtendBy`). An empty range
    /// becomes the point, whatever corners it was empty with, where C++
    /// keeps the corners of an empty range that is not the default one.
    pub fn extend_by(&mut self, point: Vec3d) {
        *self = self.union(Range3d::new(point, point));
    }

    /// The smallest range holding this one and `other` (C++ `GetUnion`). An
    /// empty range adds nothing, whatever corners it is empty with, where
    /// C++ merges the corners of an empty range that is not the default one.
    pub fn union(self, other: Range3d) -> Range3d {
        match (self.is_empty(), other.is_empty()) {
            (true, _) => other,
            (_, true) => self,
            _ => Range3d {
                min: self.min.min(other.min),
                max: self.max.max(other.max),
            },
        }
    }

    /// The range both this one and `other` hold (C++ `GetIntersection`),
    /// which is empty where they do not overlap.
    pub fn intersection(self, other: Range3d) -> Range3d {
        Range3d {
            min: self.min.max(other.min),
            max: self.max.min(other.max),
        }
    }

    /// Whether `point` lies in the range, its faces included (C++
    /// `Contains`).
    pub fn contains(&self, point: Vec3d) -> bool {
        (self.min.x..=self.max.x).contains(&point.x)
            && (self.min.y..=self.max.y).contains(&point.y)
            && (self.min.z..=self.max.z).contains(&point.z)
    }

    /// Whether both corners of `other` lie in the range (C++ `Contains` of a
    /// range).
    pub fn contains_range(&self, other: Range3d) -> bool {
        self.contains(other.min) && self.contains(other.max)
    }

    /// Whether `other` lies wholly outside the range along some axis (C++
    /// `IsOutside`).
    pub fn is_outside(&self, other: Range3d) -> bool {
        other.max.x < self.min.x
            || other.min.x > self.max.x
            || other.max.y < self.min.y
            || other.min.y > self.max.y
            || other.max.z < self.min.z
            || other.min.z > self.max.z
    }

    /// The squared distance from `point` to the nearest point of the range
    /// (C++ `GetDistanceSquared`), zero for a point inside.
    pub fn distance_squared(&self, point: Vec3d) -> f64 {
        let along = |p: f64, min: f64, max: f64| match p {
            p if p < min => (min - p) * (min - p),
            p if p > max => (p - max) * (p - max),
            _ => 0.0,
        };
        along(point.x, self.min.x, self.max.x)
            + along(point.y, self.min.y, self.max.y)
            + along(point.z, self.min.z, self.max.z)
    }

    /// The axis-aligned range holding this one once `matrix` is applied to
    /// it, which is this range itself where it is empty.
    ///
    /// Each axis of the result takes, from each axis of this range,
    /// whichever of the two extremes the matrix sends lower for its minimum
    /// and the other for its maximum (James Arvo, Graphics Gems I, pp.
    /// 548-550). The matrix is taken to be affine. A range that is turned
    /// grows. One carried through several transforms is tighter kept as a
    /// [`BBox3d`](super::BBox3d).
    pub fn transformed(self, matrix: Mat4d) -> Range3d {
        if self.is_empty() {
            return self;
        }
        let translation = matrix.extract_translation();
        let (mut min, mut max) = (translation, translation);
        for j in 0..3 {
            for i in 0..3 {
                let a = self.min[i] * matrix[(i, j)];
                let b = self.max[i] * matrix[(i, j)];
                min[j] += a.min(b);
                max[j] += a.max(b);
            }
        }
        Range3d::new(min, max)
    }

    /// The eight corners (C++ `GetCorner`): corner `i` takes its x from the
    /// maximum where bit 0 of `i` is set, its y by bit 1 and its z by bit 2,
    /// so the first is the minimum and the last the maximum.
    pub fn corners(&self) -> [Vec3d; 8] {
        let pick = |from_max: bool, min: f64, max: f64| if from_max { max } else { min };
        array::from_fn(|i| Vec3d {
            x: pick(i & 1 != 0, self.min.x, self.max.x),
            y: pick(i & 2 != 0, self.min.y, self.max.y),
            z: pick(i & 4 != 0, self.min.z, self.max.z),
        })
    }

    /// The eight octants the midpoint divides the range into (C++
    /// `GetOctant`): octant `i` runs from the midpoint to
    /// [corner](Self::corners) `i`. An empty range has eight empty octants,
    /// where C++ orders the corners of each into a range that holds points.
    pub fn octants(&self) -> [Range3d; 8] {
        if self.is_empty() {
            return [Range3d::EMPTY; 8];
        }
        let middle = self.midpoint();
        self.corners()
            .map(|corner| Range3d::new(corner.min(middle), corner.max(middle)))
    }
}

impl Default for Range3d {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl From<[Vec3f; 2]> for Range3d {
    /// The range between two single-precision corners, the minimum first.
    fn from([min, max]: [Vec3f; 2]) -> Self {
        Range3d::new(min.into(), max.into())
    }
}

impl From<Range3d> for [Vec3f; 2] {
    /// The corners of `range` in single precision, the minimum first.
    fn from(range: Range3d) -> Self {
        [range.min.to_f32(), range.max.to_f32()]
    }
}

impl Add for Range3d {
    type Output = Range3d;

    fn add(self, other: Range3d) -> Range3d {
        if self.is_empty() || other.is_empty() {
            return Range3d::EMPTY;
        }
        Range3d::new(self.min + other.min, self.max + other.max)
    }
}

impl Sub for Range3d {
    type Output = Range3d;

    fn sub(self, other: Range3d) -> Range3d {
        if self.is_empty() || other.is_empty() {
            return Range3d::EMPTY;
        }
        Range3d::new(self.min - other.max, self.max - other.min)
    }
}

impl Mul<f64> for Range3d {
    type Output = Range3d;

    /// A negative factor swaps the corners, so the product stays ordered.
    fn mul(self, factor: f64) -> Range3d {
        if self.is_empty() {
            return Range3d::EMPTY;
        }
        match factor > 0.0 {
            true => Range3d::new(self.min * factor, self.max * factor),
            false => Range3d::new(self.max * factor, self.min * factor),
        }
    }
}

impl Mul<Range3d> for f64 {
    type Output = Range3d;

    fn mul(self, range: Range3d) -> Range3d {
        range * self
    }
}

impl Div<f64> for Range3d {
    type Output = Range3d;

    fn div(self, divisor: f64) -> Range3d {
        self * (1.0 / divisor)
    }
}

/// An axis-aligned rectangle given by its minimum and maximum corners (C++
/// `GfRange2d`).
///
/// A range whose minimum exceeds its maximum along either axis is empty, and
/// the [`Default`] range is one. The corners are held as given, so one built
/// with them out of order reads back the same.
///
/// The arithmetic is on the corners, as in C++, whatever order they are in:
/// `a + b` adds minimum to minimum and maximum to maximum, and `a * m` scales
/// both, exchanging them for a factor that is not positive. A window that
/// has been turned over therefore stays turned over, where
/// [`Range3d`]'s arithmetic gives [`Range3d::EMPTY`] for an empty range.
///
/// ```
/// use openusd::gf;
///
/// let window = gf::Range2d::new(gf::vec2d(-1.0, -0.5), gf::vec2d(1.0, 0.5));
/// assert_eq!(window.size(), gf::vec2d(2.0, 1.0));
/// assert!(gf::Range2d::default().is_empty());
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Range2d {
    min: Vec2d,
    max: Vec2d,
}

impl Range2d {
    /// The empty range C++ builds by default: the largest `float` as the
    /// minimum and its negation as the maximum.
    pub const EMPTY: Range2d = Range2d {
        min: Vec2d {
            x: f32::MAX as f64,
            y: f32::MAX as f64,
        },
        max: Vec2d {
            x: -(f32::MAX as f64),
            y: -(f32::MAX as f64),
        },
    };

    /// The range from `min` to `max`, which is empty where `min` exceeds
    /// `max` along either axis.
    pub const fn new(min: Vec2d, max: Vec2d) -> Self {
        Range2d { min, max }
    }

    /// The minimum corner (C++ `GetMin`).
    pub const fn min(&self) -> Vec2d {
        self.min
    }

    /// The maximum corner (C++ `GetMax`).
    pub const fn max(&self) -> Vec2d {
        self.max
    }

    /// The extent along each axis (C++ `GetSize`), negative along an axis
    /// the range is empty on.
    pub fn size(&self) -> Vec2d {
        self.max - self.min
    }

    /// Whether the range holds no point (C++ `IsEmpty`).
    pub fn is_empty(&self) -> bool {
        self.min.x > self.max.x || self.min.y > self.max.y
    }
}

impl Default for Range2d {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl Add for Range2d {
    type Output = Range2d;

    fn add(self, other: Range2d) -> Range2d {
        Range2d::new(self.min + other.min, self.max + other.max)
    }
}

impl Mul<f64> for Range2d {
    type Output = Range2d;

    fn mul(self, factor: f64) -> Range2d {
        match factor > 0.0 {
            true => Range2d::new(self.min * factor, self.max * factor),
            false => Range2d::new(self.max * factor, self.min * factor),
        }
    }
}

impl Div<f64> for Range2d {
    type Output = Range2d;

    fn div(self, divisor: f64) -> Range2d {
        self * (1.0 / divisor)
    }
}

/// A span on a line given by its two ends (C++ `GfRange1d`).
///
/// A range whose minimum exceeds its maximum is empty, and the [`Default`]
/// range is one. `a * m` scales both ends, as in C++, exchanging them for a
/// factor that is not positive.
///
/// ```
/// use openusd::gf;
///
/// let near_far = gf::Range1d::new(1.0, 100.0);
/// assert_eq!(near_far.size(), 99.0);
/// assert!(gf::Range1d::default().is_empty());
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Range1d {
    min: f64,
    max: f64,
}

impl Range1d {
    /// The empty range C++ builds by default: the largest `float` as the
    /// minimum and its negation as the maximum.
    pub const EMPTY: Range1d = Range1d {
        min: f32::MAX as f64,
        max: -(f32::MAX as f64),
    };

    /// The range from `min` to `max`, which is empty where `min` exceeds
    /// `max`.
    pub const fn new(min: f64, max: f64) -> Self {
        Range1d { min, max }
    }

    /// The lower end (C++ `GetMin`).
    pub const fn min(&self) -> f64 {
        self.min
    }

    /// The upper end (C++ `GetMax`).
    pub const fn max(&self) -> f64 {
        self.max
    }

    /// The length (C++ `GetSize`), negative for an empty range.
    pub fn size(&self) -> f64 {
        self.max - self.min
    }

    /// Whether the range holds no value (C++ `IsEmpty`).
    pub fn is_empty(&self) -> bool {
        self.min > self.max
    }
}

impl Default for Range1d {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl Mul<f64> for Range1d {
    type Output = Range1d;

    fn mul(self, factor: f64) -> Range1d {
        match factor > 0.0 {
            true => Range1d::new(self.min * factor, self.max * factor),
            false => Range1d::new(self.max * factor, self.min * factor),
        }
    }
}

/// A span on a line given by its two ends, in single precision (C++
/// `GfRange1f`).
///
/// A range whose minimum exceeds its maximum is empty, and the [`Default`]
/// range is one.
///
/// ```
/// use openusd::gf;
///
/// let near_far = gf::Range1f::new(1.0, 100.0);
/// assert_eq!(near_far.size(), 99.0);
/// assert!(near_far.contains(1.0));
/// assert!(gf::Range1f::default().is_empty());
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Range1f {
    min: f32,
    max: f32,
}

impl Range1f {
    /// The empty range C++ builds by default: the largest `float` as the
    /// minimum and its negation as the maximum.
    pub const EMPTY: Range1f = Range1f {
        min: f32::MAX,
        max: -f32::MAX,
    };

    /// The range from `min` to `max`, which is empty where `min` exceeds
    /// `max`.
    pub const fn new(min: f32, max: f32) -> Self {
        Range1f { min, max }
    }

    /// The lower end (C++ `GetMin`).
    pub const fn min(&self) -> f32 {
        self.min
    }

    /// The upper end (C++ `GetMax`).
    pub const fn max(&self) -> f32 {
        self.max
    }

    /// The length (C++ `GetSize`), negative for an empty range.
    pub fn size(&self) -> f32 {
        self.max - self.min
    }

    /// Whether the range holds no value (C++ `IsEmpty`).
    pub fn is_empty(&self) -> bool {
        self.min > self.max
    }

    /// Whether `value` lies in the range, its ends included (C++
    /// `Contains`).
    pub fn contains(&self, value: f32) -> bool {
        (self.min..=self.max).contains(&value)
    }
}

impl Default for Range1f {
    fn default() -> Self {
        Self::EMPTY
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::{Range1d, Range1f, Range2d, Range3d};
    use crate::gf;

    pub(crate) fn range(min: [f64; 3], max: [f64; 3]) -> Range3d {
        Range3d::new(min.into(), max.into())
    }

    /// A range and a pair of single-precision corners convert both ways,
    /// the empty range included.
    #[test]
    fn corner_pairs() {
        let corners = [gf::vec3f(-1.0, 0.0, 2.5), gf::vec3f(3.0, 2.0, 4.0)];
        let r = Range3d::from(corners);
        assert_eq!(r, range([-1.0, 0.0, 2.5], [3.0, 2.0, 4.0]));
        assert_eq!(<[gf::Vec3f; 2]>::from(r), corners);

        let empty = <[gf::Vec3f; 2]>::from(Range3d::EMPTY);
        assert_eq!(empty, [gf::Vec3f::from([f32::MAX; 3]), gf::Vec3f::from([-f32::MAX; 3])]);
        assert_eq!(Range3d::from(empty), Range3d::EMPTY);
    }

    /// The default range is empty, and a point makes it that point.
    #[test]
    fn empty_until_extended() {
        let mut r = Range3d::default();
        assert!(r.is_empty());
        assert_eq!(r, Range3d::EMPTY);
        assert!(!r.contains(gf::vec3d(0.0, 0.0, 0.0)));

        r.extend_by(gf::vec3d(1.0, 2.0, 3.0));
        assert!(!r.is_empty());
        assert_eq!(r, range([1.0, 2.0, 3.0], [1.0, 2.0, 3.0]));

        // One axis out of order is enough.
        assert!(range([0.0, 1.0, 0.0], [1.0, 0.0, 1.0]).is_empty());
        assert!(!Range3d::UNIT_CUBE.is_empty());
    }

    #[test]
    fn size_and_midpoint() {
        let r = range([-1.0, 0.0, 2.0], [3.0, 2.0, 2.0]);
        assert_eq!(r.size(), gf::vec3d(4.0, 2.0, 0.0));
        assert_eq!(r.midpoint(), gf::vec3d(1.0, 1.0, 2.0));
    }

    /// A union holds both ranges and an empty one adds nothing; an
    /// intersection of ranges that miss each other is empty.
    #[test]
    fn union_and_intersection() {
        let a = range([0.0, 0.0, 0.0], [2.0, 2.0, 2.0]);
        let b = range([1.0, -1.0, 1.0], [3.0, 1.0, 5.0]);
        assert_eq!(a.union(b), range([0.0, -1.0, 0.0], [3.0, 2.0, 5.0]));
        assert_eq!(a.union(Range3d::EMPTY), a);
        assert_eq!(Range3d::EMPTY.union(a), a);
        assert_eq!(a.intersection(b), range([1.0, 0.0, 1.0], [2.0, 1.0, 2.0]));

        let apart = range([5.0, 5.0, 5.0], [6.0, 6.0, 6.0]);
        assert!(a.intersection(apart).is_empty());

        // An empty range adds nothing whatever its corners are.
        let missed = a.intersection(apart);
        assert_ne!(missed, Range3d::EMPTY);
        assert_eq!(missed.union(b), b);
        assert_eq!(b.union(missed), b);
        let mut extended = missed;
        extended.extend_by(gf::vec3d(9.0, 9.0, 9.0));
        assert_eq!(extended, range([9.0; 3], [9.0; 3]));
        assert!(a.is_outside(apart));
        assert!(!a.is_outside(b));
    }

    /// The faces belong to the range.
    #[test]
    fn containment() {
        let r = Range3d::UNIT_CUBE;
        assert!(r.contains(gf::vec3d(0.5, 0.5, 0.5)));
        assert!(r.contains(gf::vec3d(1.0, 0.0, 1.0)));
        assert!(!r.contains(gf::vec3d(1.0, 0.0, 1.1)));
        assert!(r.contains_range(range([0.25, 0.25, 0.25], [1.0, 1.0, 1.0])));
        assert!(!r.contains_range(range([0.25, 0.25, 0.25], [1.0, 2.0, 1.0])));
    }

    #[test]
    fn distance_to_point() {
        let r = Range3d::UNIT_CUBE;
        assert_eq!(r.distance_squared(gf::vec3d(0.5, 0.5, 0.5)), 0.0);
        assert_eq!(r.distance_squared(gf::vec3d(3.0, 0.5, 0.5)), 4.0);
        assert_eq!(r.distance_squared(gf::vec3d(-1.0, -2.0, 3.0)), 1.0 + 4.0 + 4.0);
    }

    /// Corner `i` reads its axes off the bits of `i`, and octant `i` runs
    /// from the midpoint to that corner.
    #[test]
    fn corners_and_octants() {
        let r = range([0.0, 0.0, 0.0], [2.0, 4.0, 6.0]);
        let corners = r.corners();
        assert_eq!(corners[0], r.min());
        assert_eq!(corners[7], r.max());
        assert_eq!(corners[1], gf::vec3d(2.0, 0.0, 0.0));
        assert_eq!(corners[2], gf::vec3d(0.0, 4.0, 0.0));
        assert_eq!(corners[5], gf::vec3d(2.0, 0.0, 6.0));

        let octants = r.octants();
        assert_eq!(octants[0], range([0.0, 0.0, 0.0], [1.0, 2.0, 3.0]));
        assert_eq!(octants[7], range([1.0, 2.0, 3.0], [2.0, 4.0, 6.0]));
        assert_eq!(octants[1], range([1.0, 0.0, 0.0], [2.0, 2.0, 3.0]));
        let whole = octants.into_iter().fold(Range3d::EMPTY, Range3d::union);
        assert_eq!(whole, r);

        for empty in [Range3d::EMPTY, range([3.0; 3], [1.0; 3])] {
            assert!(empty.octants().iter().all(Range3d::is_empty));
        }
    }

    /// A range under a matrix is the aligned range of its moved corners,
    /// and an empty range is left as it is.
    #[test]
    fn transformed_holds_corners() {
        let r = range([0.0, 0.0, 0.0], [1.0, 2.0, 3.0]);
        let matrix = gf::Mat4d::rotation_z(90f64.to_radians()) * gf::Mat4d::translation([10.0, 0.0, 0.0]);
        let moved = r.transformed(matrix);
        let mut expected = Range3d::EMPTY;
        for corner in r.corners() {
            expected.extend_by(matrix.transform(corner));
        }
        assert!((moved.min() - expected.min()).length() < 1e-12, "{moved:?}");
        assert!((moved.max() - expected.max()).length() < 1e-12, "{moved:?}");
        assert_eq!(
            r.transformed(gf::Mat4d::scale([-1.0, 1.0, 1.0])),
            range([-1.0, 0.0, 0.0], [0.0, 2.0, 3.0])
        );

        let empty = range([3.0; 3], [1.0; 3]);
        assert_eq!(empty.transformed(matrix), empty);
    }

    /// The operators are interval arithmetic, and a negative factor keeps
    /// the corners in order.
    #[test]
    fn arithmetic() {
        let a = range([1.0, 2.0, 3.0], [4.0, 5.0, 6.0]);
        let b = range([0.0, 1.0, 2.0], [1.0, 2.0, 3.0]);
        assert_eq!(a + b, range([1.0, 3.0, 5.0], [5.0, 7.0, 9.0]));
        assert_eq!(a - b, range([0.0, 0.0, 0.0], [4.0, 4.0, 4.0]));
        assert_eq!(a * 2.0, range([2.0, 4.0, 6.0], [8.0, 10.0, 12.0]));
        assert_eq!(2.0 * a, a * 2.0);
        assert_eq!(a * -1.0, range([-4.0, -5.0, -6.0], [-1.0, -2.0, -3.0]));
        assert_eq!(a / 2.0, range([0.5, 1.0, 1.5], [2.0, 2.5, 3.0]));

        // Nothing scaled, moved or added to is still nothing.
        let empty = range([3.0; 3], [1.0; 3]);
        for result in [empty * 0.0, empty * -2.0, empty + a, a + empty, a - empty, empty / 2.0] {
            assert_eq!(result, Range3d::EMPTY);
        }
        assert_eq!(a * 0.0, range([0.0; 3], [0.0; 3]));
    }

    /// A rectangle and a span hold their corners as given, and are empty
    /// with any of them out of order.
    #[test]
    fn rectangle_and_span() {
        let r = Range2d::new(gf::vec2d(-1.0, 0.0), gf::vec2d(3.0, 2.0));
        assert_eq!(r.size(), gf::vec2d(4.0, 2.0));
        assert!(!r.is_empty());
        let inverted = Range2d::new(gf::vec2d(1.0, 1.0), gf::vec2d(-1.0, 2.0));
        assert!(inverted.is_empty());
        assert_eq!((inverted.min().x, inverted.max().x), (1.0, -1.0));
        assert!(Range2d::default().is_empty());

        // Arithmetic is on the corners, and a factor that is not positive
        // exchanges them.
        let moved = r + Range2d::new(gf::vec2d(1.0, 1.0), gf::vec2d(1.0, 1.0));
        assert_eq!(moved, Range2d::new(gf::vec2d(0.0, 1.0), gf::vec2d(4.0, 3.0)));
        assert_eq!(r * 2.0, Range2d::new(gf::vec2d(-2.0, 0.0), gf::vec2d(6.0, 4.0)));
        assert_eq!(r * -1.0, Range2d::new(gf::vec2d(-3.0, -2.0), gf::vec2d(1.0, 0.0)));
        assert_eq!(r / 2.0, Range2d::new(gf::vec2d(-0.5, 0.0), gf::vec2d(1.5, 1.0)));
        assert_eq!(inverted * 2.0, Range2d::new(gf::vec2d(2.0, 2.0), gf::vec2d(-2.0, 4.0)));

        let span = Range1d::new(1.0, 10.0);
        assert_eq!(span * 2.0, Range1d::new(2.0, 20.0));
        assert_eq!(span * -1.0, Range1d::new(-10.0, -1.0));
        assert_eq!((span.min(), span.max(), span.size()), (1.0, 10.0, 9.0));
        assert!(Range1d::new(2.0, 1.0).is_empty() && Range1d::default().is_empty());
    }

    /// A span holds its ends, and one whose ends are out of order holds
    /// nothing.
    #[test]
    fn span_ends() {
        let r = Range1f::new(1.0, 4.0);
        assert_eq!((r.min(), r.max(), r.size()), (1.0, 4.0, 3.0));
        assert!(r.contains(1.0) && r.contains(4.0) && !r.contains(4.5));
        assert!(!r.is_empty());

        assert!(Range1f::default().is_empty());
        assert!(Range1f::new(2.0, 1.0).is_empty());
        assert!(!Range1f::new(2.0, 1.0).contains(1.5));
    }
}
