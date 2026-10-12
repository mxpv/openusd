//! What a projection matrix projects: the kind of projection and the volume
//! of camera space it keeps.

use super::Mat4d;

/// The volume a projection sees, as the numbers a projection matrix is built
/// from and can be read back into.
///
/// The camera looks along −Z from the origin of its own space. `near` and
/// `far` are distances along that line of sight.
///
/// The window is the rectangle the projection sees through, and where it
/// stands depends on the projection. For [`Projection::Perspective`] it
/// stands at a distance of one from the camera, so its size is the tangent
/// of the field of view and moving `near` leaves the field of view alone.
/// That differs from `glFrustum`, whose bounds are on the near plane. For
/// [`Projection::Orthographic`] the window is the same at every distance.
///
/// ```
/// use openusd::gf;
///
/// let params = gf::ProjectionParams {
///     projection: gf::Projection::Perspective,
///     left: -0.5,
///     right: 0.5,
///     bottom: -0.25,
///     top: 0.25,
///     near: 1.0,
///     far: 100.0,
/// };
/// let read = gf::ProjectionParams::from_matrix(params.matrix()).expect("a perspective matrix");
/// assert_eq!(read.projection, gf::Projection::Perspective);
/// assert!((read.right - 0.5).abs() < 1e-12 && (read.far - 100.0).abs() < 1e-9);
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ProjectionParams {
    /// Whether lines of sight meet at the camera.
    pub projection: Projection,
    /// The window's left edge, along +X.
    pub left: f64,
    /// The window's right edge, along +X.
    pub right: f64,
    /// The window's bottom edge, along +Y.
    pub bottom: f64,
    /// The window's top edge, along +Y.
    pub top: f64,
    /// Distance to the near clipping plane.
    pub near: f64,
    /// Distance to the far clipping plane.
    pub far: f64,
}

/// How a camera projects what it sees (C++ `GfCamera::Projection` and
/// `GfFrustum::ProjectionType`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Projection {
    /// Lines of sight meet at the camera.
    #[default]
    Perspective,
    /// Lines of sight are parallel.
    Orthographic,
}

impl ProjectionParams {
    /// How far an element of a matrix may be from the one a projection
    /// holds there and still be read as it, as a fraction of the larger of
    /// the two where that exceeds one.
    const TOLERANCE: f64 = 1e-6;

    /// The matrix that projects this volume: [`Mat4d::perspective`] or
    /// [`Mat4d::orthographic`], by the kind of projection.
    pub fn matrix(&self) -> Mat4d {
        let build = match self.projection {
            Projection::Perspective => Mat4d::perspective,
            Projection::Orthographic => Mat4d::orthographic,
        };
        build(self.left, self.right, self.bottom, self.top, self.near, self.far)
    }

    /// The volume `matrix` projects, or `None` where it is not a projection
    /// this type describes.
    ///
    /// A perspective matrix holds −1 at `(2, 3)` and an orthographic one
    /// holds 0, and a matrix holding anything else there is neither. A
    /// matrix of either kind that gives a window edge or a clipping distance
    /// that is not finite, as one with a zero on its diagonal does, is
    /// `None` as well.
    ///
    /// Every element has to be the one [`matrix`](Self::matrix) builds from
    /// the volume read, to within `1e-6`. A matrix that carries anything
    /// more than the projection, such as a skew, or that holds an element
    /// that is not finite, is therefore `None`: the volume would not give
    /// it back.
    pub fn from_matrix(matrix: Mat4d) -> Option<Self> {
        let m = |r: usize, c: usize| matrix[(r, c)];
        let (width, height) = (2.0 / m(0, 0), 2.0 / m(1, 1));

        // The window's center, and the two clipping distances.
        let (projection, center, near, far) = if (m(2, 3) + 1.0).abs() < Self::TOLERANCE {
            let center = [0.5 * width * m(2, 0), 0.5 * height * m(2, 1)];
            let (near, far) = (m(3, 2) / (m(2, 2) - 1.0), m(3, 2) / (m(2, 2) + 1.0));
            (Projection::Perspective, center, near, far)
        } else if m(2, 3).abs() < Self::TOLERANCE {
            let center = [-0.5 * width * m(3, 0), -0.5 * height * m(3, 1)];
            let half_depth = 1.0 / m(2, 2);
            let middle = half_depth * m(3, 2);
            (
                Projection::Orthographic,
                center,
                middle + half_depth,
                middle - half_depth,
            )
        } else {
            return None;
        };

        let params = ProjectionParams {
            projection,
            left: center[0] - 0.5 * width,
            right: center[0] + 0.5 * width,
            bottom: center[1] - 0.5 * height,
            top: center[1] + 0.5 * height,
            near,
            far,
        };
        let numbers = [
            params.left,
            params.right,
            params.bottom,
            params.top,
            params.near,
            params.far,
        ];
        if !numbers.iter().all(|n| n.is_finite()) {
            return None;
        }
        let rebuilt = params.matrix();
        // An infinite element is turned away by name: against the scaled
        // tolerance it would compare as close to anything.
        let same = |i: usize| {
            let (given, built) = (matrix[i], rebuilt[i]);
            given.is_finite()
                && built.is_finite()
                && (given - built).abs() <= Self::TOLERANCE * given.abs().max(built.abs()).max(1.0)
        };
        (0..16).all(same).then_some(params)
    }
}

#[cfg(test)]
mod tests {
    use super::{Projection, ProjectionParams};
    use crate::gf;

    fn params(projection: Projection) -> ProjectionParams {
        ProjectionParams {
            projection,
            left: -0.2,
            right: 0.4,
            bottom: -0.1,
            top: 0.3,
            near: 2.0,
            far: 50.0,
        }
    }

    fn assert_close(got: ProjectionParams, want: ProjectionParams) {
        assert_eq!(got.projection, want.projection);
        let pairs = [
            (got.left, want.left),
            (got.right, want.right),
            (got.bottom, want.bottom),
            (got.top, want.top),
            (got.near, want.near),
            (got.far, want.far),
        ];
        for (got, want) in pairs {
            assert!((got - want).abs() < 1e-9, "{got} is not {want}");
        }
    }

    /// An off-center volume of either kind comes back from its matrix.
    #[test]
    fn matrix_round_trip() {
        for projection in [Projection::Perspective, Projection::Orthographic] {
            let params = params(projection);
            let read = ProjectionParams::from_matrix(params.matrix()).expect("a projection");
            assert_close(read, params);
        }
    }

    /// The matrices carry the corners of the volume to the corners of clip
    /// space: the near plane to −1 and the far plane to 1.
    #[test]
    fn corners_reach_clip_space() {
        let perspective = params(Projection::Perspective);
        let m = perspective.matrix();
        // The window stands at a distance of one, so a point on the near
        // plane is the window's corner scaled by the near distance.
        let near = perspective.near;
        let corner = gf::vec3d(perspective.right * near, perspective.top * near, -near);
        assert!((m.transform(corner) - gf::vec3d(1.0, 1.0, -1.0)).length() < 1e-12);
        let far = perspective.far;
        let corner = gf::vec3d(perspective.left * far, perspective.bottom * far, -far);
        assert!((m.transform(corner) - gf::vec3d(-1.0, -1.0, 1.0)).length() < 1e-12);

        let orthographic = params(Projection::Orthographic);
        let m = orthographic.matrix();
        let corner = gf::vec3d(orthographic.right, orthographic.top, -orthographic.near);
        assert!((m.transform(corner) - gf::vec3d(1.0, 1.0, -1.0)).length() < 1e-12);
        let corner = gf::vec3d(orthographic.left, orthographic.bottom, -orthographic.far);
        assert!((m.transform(corner) - gf::vec3d(-1.0, -1.0, 1.0)).length() < 1e-12);
    }

    /// Moving the near plane of a perspective volume leaves its window, and
    /// so its field of view, where it was.
    #[test]
    fn near_leaves_window() {
        let wide = params(Projection::Perspective);
        let moved = ProjectionParams { near: 10.0, ..wide };
        let read = ProjectionParams::from_matrix(moved.matrix()).expect("a projection");
        assert_close(read, moved);
        assert_eq!(wide.matrix()[(0, 0)], moved.matrix()[(0, 0)]);
    }

    /// A matrix that is neither kind, or that gives numbers that are not
    /// finite, is no projection.
    #[test]
    fn unusable_matrices() {
        let good = params(Projection::Perspective).matrix();
        let mut neither = good;
        neither[(2, 3)] = -0.5;
        let mut nan = good;
        nan[(2, 3)] = f64::NAN;
        let mut flat = good;
        flat[(0, 0)] = 0.0;
        let mut endless = good;
        endless[(2, 2)] = -1.0;
        for matrix in [neither, nan, flat, endless] {
            assert_eq!(ProjectionParams::from_matrix(matrix), None);
        }
        assert_eq!(ProjectionParams::from_matrix(gf::Mat4d::scale([1.0, 1.0, 0.0])), None);
    }

    /// A matrix that is a projection and something more, or that holds an
    /// element that is not finite anywhere, is no projection: the volume
    /// read from it would not build it again.
    #[test]
    fn stray_elements_refused() {
        // The six elements each kind reads its volume from, as flat indices.
        // Moving one of those gives another projection of the kind.
        let kinds = [
            (Projection::Perspective, [0, 5, 8, 9, 10, 14]),
            (Projection::Orthographic, [0, 5, 10, 12, 13, 14]),
        ];
        for (projection, read) in kinds {
            let good = params(projection).matrix();
            for i in 0..16 {
                let mut skewed = good;
                skewed[i] += 0.5;
                assert_eq!(
                    ProjectionParams::from_matrix(skewed).is_some(),
                    read.contains(&i),
                    "{projection:?} element {i}"
                );

                for infinite in [f64::INFINITY, f64::NEG_INFINITY] {
                    let mut endless = good;
                    endless[i] = infinite;
                    assert_eq!(
                        ProjectionParams::from_matrix(endless),
                        None,
                        "{projection:?} element {i}"
                    );
                }

                let mut nan = good;
                nan[i] = f64::NAN;
                assert_eq!(ProjectionParams::from_matrix(nan), None, "{projection:?} element {i}");
            }
        }
    }

    /// A matrix a hair off the one a volume builds still reads as it.
    #[test]
    fn rounding_tolerated() {
        let params = params(Projection::Perspective);
        let mut matrix = params.matrix();
        for i in 0..16 {
            matrix[i] *= 1.0 + 1e-9;
        }
        let read = ProjectionParams::from_matrix(matrix).expect("a projection");
        assert_eq!(read.projection, Projection::Perspective);
        assert!((read.near - params.near).abs() < 1e-6 && (read.right - params.right).abs() < 1e-6);
    }
}
