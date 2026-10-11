//! `GfBBox3d` — a box in a space of its own, placed by a matrix.

use super::{Mat4d, Range3d, Vec3d};

/// A [`Range3d`] and the matrix that takes its space to world space (C++
/// `GfBBox3d`).
///
/// The matrix is carried beside the box so that the box stays tight through
/// a hierarchy: an axis-aligned box that is transformed and re-aligned at
/// each level grows at each one.
/// [`aligned_range`](Self::aligned_range) projects into world
/// space once, when the answer is needed.
///
/// Two boxes are equal when their ranges and matrices are, whatever
/// [`has_zero_area_primitives`](Self::has_zero_area_primitives) says of
/// either.
///
/// ```
/// use openusd::gf;
///
/// let unit = gf::Range3d::UNIT_CUBE;
/// let mut bbox = gf::BBox3d::new(unit, gf::Mat4d::scale([2.0, 2.0, 2.0]));
/// bbox.transform(gf::Mat4d::translation([10.0, 0.0, 0.0]));
///
/// let aligned = bbox.aligned_range();
/// assert_eq!(aligned.min(), gf::vec3d(10.0, 0.0, 0.0));
/// assert_eq!(aligned.max(), gf::vec3d(12.0, 2.0, 2.0));
/// assert_eq!(bbox.volume(), 8.0);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct BBox3d {
    range: Range3d,
    matrix: Mat4d,
    /// The inverse of `matrix`, or `None` for a matrix that has none and so
    /// flattens the box.
    inverse: Option<Mat4d>,
    zero_area_primitives: bool,
}

impl BBox3d {
    /// The determinant at or under which a matrix is taken to have no
    /// inverse.
    const PRECISION_LIMIT: f64 = 1.0e-13;

    /// The box `range` placed by `matrix`.
    pub fn new(range: Range3d, matrix: Mat4d) -> Self {
        let mut bbox = BBox3d::from(range);
        bbox.set_matrix(matrix);
        bbox
    }

    /// The box in its own space (C++ `GetRange`).
    pub const fn range(&self) -> Range3d {
        self.range
    }

    /// Replace the box, keeping the matrix (C++ `SetRange`).
    pub fn set_range(&mut self, range: Range3d) {
        self.range = range;
    }

    /// The matrix from the box's space to world space (C++ `GetMatrix`).
    pub const fn matrix(&self) -> Mat4d {
        self.matrix
    }

    /// The inverse of the matrix (C++ `GetInverseMatrix`), the identity
    /// where the matrix has none.
    pub fn inverse_matrix(&self) -> Mat4d {
        self.inverse.unwrap_or(Mat4d::IDENTITY)
    }

    /// Replace the matrix, keeping the box (C++ `SetMatrix`).
    pub fn set_matrix(&mut self, matrix: Mat4d) {
        self.matrix = matrix;
        self.inverse = matrix.inverse_above(Self::PRECISION_LIMIT);
    }

    /// Whether the box bounds a primitive with no area, such as a point or
    /// a camera (C++ `HasZeroAreaPrimitives`). Such a box may be empty and
    /// still mark where something is.
    pub const fn has_zero_area_primitives(&self) -> bool {
        self.zero_area_primitives
    }

    /// Say whether the box bounds a primitive with no area (C++
    /// `SetHasZeroAreaPrimitives`).
    pub fn set_has_zero_area_primitives(&mut self, has: bool) {
        self.zero_area_primitives = has;
    }

    /// The volume of the box in world space (C++ `GetVolume`), zero for an
    /// empty range.
    pub fn volume(&self) -> f64 {
        if self.range.is_empty() {
            return 0.0;
        }
        let size = self.range.size();
        (self.matrix.determinant3() * size.x * size.y * size.z).abs()
    }

    /// Apply `matrix` after the box's own (C++ `Transform`).
    pub fn transform(&mut self, matrix: Mat4d) {
        self.set_matrix(self.matrix * matrix);
    }

    /// The axis-aligned range holding the box in world space (C++
    /// `ComputeAlignedRange`), empty for an empty range.
    pub fn aligned_range(&self) -> Range3d {
        self.range.transformed(self.matrix)
    }

    /// A box holding both `a` and `b` (C++ `Combine`), with zero-area
    /// primitives where either has them.
    ///
    /// An empty box yields the other. Otherwise one box is projected into
    /// the other's space and merged there, which is done both ways round and
    /// the smaller result by volume kept. A box whose matrix has no inverse
    /// is always the one projected, and two such boxes merge as their
    /// aligned ranges.
    pub fn combine(a: &BBox3d, b: &BBox3d) -> BBox3d {
        let mut combined = match (a.range.is_empty(), b.range.is_empty()) {
            (true, _) => *b,
            (_, true) => *a,
            _ => match (a.inverse, b.inverse) {
                (None, None) => BBox3d::from(a.aligned_range().union(b.aligned_range())),
                (None, Some(into_b)) => b.extended_by(a, into_b),
                (Some(into_a), None) => a.extended_by(b, into_a),
                (Some(into_a), Some(into_b)) => {
                    let (first, second) = (a.extended_by(b, into_a), b.extended_by(a, into_b));
                    let (v1, v2) = (first.volume(), second.volume());
                    // Volumes this close count as equal, so the choice does
                    // not turn on rounding.
                    let tolerance = (1e-6 * v1.max(v2).abs()).max(1e-10);
                    match (v1 - v2).abs() <= tolerance || v1 < v2 {
                        true => first,
                        false => second,
                    }
                }
            },
        };
        combined.zero_area_primitives = a.zero_area_primitives || b.zero_area_primitives;
        combined
    }

    /// The center of the box in world space (C++ `ComputeCentroid`): the
    /// image of the range's [midpoint](Range3d::midpoint), which means
    /// nothing for an empty range.
    pub fn centroid(&self) -> Vec3d {
        self.matrix.transform(self.range.midpoint())
    }

    /// This box with its range grown to hold `other`, projected into this
    /// box's space by `inverse`, the inverse of this box's matrix (C++
    /// `_CombineInOrder`).
    fn extended_by(&self, other: &BBox3d, inverse: Mat4d) -> BBox3d {
        let projected = other.range.transformed(other.matrix * inverse);
        BBox3d {
            range: self.range.union(projected),
            ..*self
        }
    }
}

impl Default for BBox3d {
    /// An empty range under the identity matrix.
    fn default() -> Self {
        BBox3d::from(Range3d::EMPTY)
    }
}

impl From<Range3d> for BBox3d {
    /// The box `range` in world space, under the identity matrix.
    fn from(range: Range3d) -> Self {
        BBox3d {
            range,
            matrix: Mat4d::IDENTITY,
            inverse: Some(Mat4d::IDENTITY),
            zero_area_primitives: false,
        }
    }
}

/// Equal ranges and matrices make equal boxes (C++ `operator==`): the
/// zero-area flag is not compared.
impl PartialEq for BBox3d {
    fn eq(&self, other: &Self) -> bool {
        self.range == other.range && self.matrix == other.matrix
    }
}

#[cfg(test)]
mod tests {
    use super::BBox3d;
    use crate::gf::range::tests::range;
    use crate::gf::{self, Mat4d, Range3d, Rotation};

    fn rotation(axis: gf::Vec3d, degrees: f64) -> Mat4d {
        Mat4d::from_quat(Rotation::new(axis, degrees).quat())
    }

    /// Equality reads the range and the matrix, and the flag is left out.
    #[test]
    fn equality() {
        let unit = BBox3d::from(Range3d::UNIT_CUBE);
        assert_eq!(unit, BBox3d::new(Range3d::UNIT_CUBE, Mat4d::IDENTITY));
        assert_ne!(unit, BBox3d::from(range([1.0; 3], [2.0; 3])));
        assert_ne!(unit, BBox3d::new(Range3d::UNIT_CUBE, Mat4d::scale([2.0; 3])));

        let mut flagged = unit;
        flagged.set_has_zero_area_primitives(true);
        assert!(flagged.has_zero_area_primitives());
        assert_eq!(flagged, unit);
    }

    #[test]
    fn default_is_empty() {
        let bbox = BBox3d::default();
        assert!(bbox.range().is_empty());
        assert_eq!(bbox.matrix(), Mat4d::IDENTITY);
        assert!(bbox.aligned_range().is_empty());
        assert_eq!(bbox.volume(), 0.0);
        assert!(!bbox.has_zero_area_primitives());
    }

    /// The inverse follows the matrix, and a matrix with none leaves the
    /// identity.
    #[test]
    fn inverse_follows_matrix() {
        let scale = Mat4d::scale([5.0; 3]);
        let mut bbox = BBox3d::default();
        bbox.set_matrix(scale);
        assert_eq!(bbox.matrix(), scale);
        assert_eq!(Some(bbox.inverse_matrix()), scale.inverse());

        bbox.set_matrix(Mat4d::scale([1.0, 0.0, 1.0]));
        assert_eq!(bbox.inverse_matrix(), Mat4d::IDENTITY);

        bbox.set_range(range([1.0, 2.0, 3.0], [4.0, 5.0, 6.0]));
        assert_eq!(bbox.range(), range([1.0, 2.0, 3.0], [4.0, 5.0, 6.0]));
    }

    #[test]
    fn volume_scales_with_matrix() {
        let two = range([0.0; 3], [2.0; 3]);
        assert_eq!(BBox3d::from(two).volume(), 8.0);
        assert_eq!(BBox3d::new(two, Mat4d::scale([1.0, 2.0, 3.0])).volume(), 48.0);
        assert_eq!(BBox3d::new(two, Mat4d::scale([-1.0, 1.0, 1.0])).volume(), 8.0);
        // Corners out of order hold nothing.
        assert_eq!(BBox3d::from(range([1.0; 3], [0.0; 3])).volume(), 0.0);
    }

    /// A transform multiplies on after the box's own matrix.
    #[test]
    fn transform_composes() {
        let (m1, m2) = (rotation(gf::Vec3d::X_AXIS, 30.0), rotation(gf::Vec3d::Y_AXIS, 60.0));
        let mut bbox = BBox3d::new(Range3d::UNIT_CUBE, m1);
        bbox.transform(m2);
        assert_eq!(bbox.matrix(), m1 * m2);
    }

    #[test]
    fn aligned_range_projects() {
        let cube = range([-1.0; 3], [1.0; 3]);
        let scaled = BBox3d::new(cube, Mat4d::scale([3.0; 3]));
        assert_eq!(scaled.aligned_range().size(), gf::vec3d(6.0, 6.0, 6.0));

        // A cube turned 30 degrees about X widens along the other two axes.
        let angle = 30f64.to_radians();
        let width = 2.0 * (angle.cos() + angle.sin());
        let turned = BBox3d::new(cube, rotation(gf::Vec3d::X_AXIS, 30.0));
        let size = turned.aligned_range().size();
        assert!((size - gf::vec3d(2.0, width, width)).length() < 1e-6, "{size:?}");

        // An aligned range is its own aligned range.
        let aligned = turned.aligned_range();
        assert_eq!(BBox3d::from(aligned).aligned_range(), aligned);

        // A mirror swaps which corner is the minimum.
        let mirrored = BBox3d::new(Range3d::UNIT_CUBE, Mat4d::scale([-2.0, 1.0, 1.0]));
        assert_eq!(mirrored.aligned_range(), range([-2.0, 0.0, 0.0], [0.0, 1.0, 1.0]));
    }

    /// A combined box holds both boxes and takes the flag from either. These
    /// two merge to different volumes in each other's spaces, so either
    /// order settles on the same space.
    #[test]
    fn combine_holds_both() {
        let b1 = BBox3d::new(Range3d::UNIT_CUBE, rotation(gf::Vec3d::X_AXIS, 30.0));
        let mut b2 = BBox3d::new(range([1.0; 3], [2.0; 3]), rotation(gf::Vec3d::Y_AXIS, 60.0));
        assert_eq!(BBox3d::combine(&b1, &b2), BBox3d::combine(&b2, &b1));

        let combined = BBox3d::combine(&b1, &b2).aligned_range();
        for part in [b1, b2] {
            let part = part.aligned_range();
            for corner in part.corners() {
                assert!(
                    combined.distance_squared(corner) < 1e-18,
                    "{corner:?} outside {combined:?}"
                );
            }
        }

        assert!(!BBox3d::combine(&b1, &b2).has_zero_area_primitives());
        b2.set_has_zero_area_primitives(true);
        assert!(BBox3d::combine(&b1, &b2).has_zero_area_primitives());
        assert!(BBox3d::combine(&b2, &b1).has_zero_area_primitives());
    }

    /// An empty box yields the other as it is.
    #[test]
    fn combine_with_empty() {
        let empty = BBox3d::new(range([1.0; 3], [0.0; 3]), Mat4d::scale([2.0; 3]));
        let full = BBox3d::new(range([1.0; 3], [2.0; 3]), Mat4d::scale([3.0; 3]));
        assert_eq!(BBox3d::combine(&empty, &full), full);
        assert_eq!(BBox3d::combine(&full, &empty), full);
        assert!(BBox3d::combine(&empty, &empty).range().is_empty());
    }

    /// A box flattened by its matrix is projected into the other's space,
    /// and two of them merge as their aligned ranges.
    #[test]
    fn combine_degenerate() {
        let flat = Mat4d::scale([1.0, 0.0, 1.0]);
        let flattened = BBox3d::new(range([2.0; 3], [3.0; 3]), flat);
        let solid = BBox3d::new(Range3d::UNIT_CUBE, Mat4d::scale([2.0; 3]));

        for combined in [BBox3d::combine(&flattened, &solid), BBox3d::combine(&solid, &flattened)] {
            assert_eq!(combined.matrix(), solid.matrix());
            assert_eq!(combined.aligned_range(), range([0.0; 3], [3.0, 2.0, 3.0]));
        }

        let other = BBox3d::new(range([-1.0; 3], [0.0; 3]), flat);
        let both = BBox3d::combine(&flattened, &other);
        assert_eq!(both.matrix(), Mat4d::IDENTITY);
        assert_eq!(both.range(), range([-1.0, 0.0, -1.0], [3.0, 0.0, 3.0]));
    }

    #[test]
    fn centroid() {
        assert_eq!(BBox3d::from(Range3d::UNIT_CUBE).centroid(), gf::vec3d(0.5, 0.5, 0.5));
        let turned = BBox3d::new(range([-1.0; 3], [1.0; 3]), rotation(gf::Vec3d::Y_AXIS, 60.0));
        assert_eq!(turned.centroid(), gf::vec3d(0.0, 0.0, 0.0));
        let moved = BBox3d::new(Range3d::UNIT_CUBE, Mat4d::translation([10.0, 0.0, 0.0]));
        assert_eq!(moved.centroid(), gf::vec3d(10.5, 0.5, 0.5));
    }
}
