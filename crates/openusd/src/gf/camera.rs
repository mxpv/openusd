//! `GfCamera` — a camera as a plain value: where it sits and what it sees.

use super::{Mat4d, Projection, ProjectionParams, Range1f, Vec4f};

/// A camera's placement, projection and lens, with no scene behind it (C++
/// `GfCamera`).
///
/// The camera sits at the origin of its own space, looks along −Z, and has +Y
/// up and +X to the right. [`transform`](Self::transform) carries that space
/// into the world.
///
/// The apertures, their offsets and the focal length are in tenths of a world
/// unit, which is a millimeter on a stage whose world unit is a centimeter.
/// The clipping range and the focus distance are in world units. An angle is
/// in degrees.
///
/// The [`Default`] camera is the one the `Camera` schema's fallbacks
/// describe.
///
/// ```
/// use openusd::gf;
///
/// let mut camera = gf::Camera::default();
/// camera.set_perspective(16.0 / 9.0, 60.0, gf::FovDirection::Horizontal, 36.0);
///
/// let fov = camera.field_of_view(gf::FovDirection::Horizontal);
/// assert!((fov - 60.0).abs() < 1e-4);
/// assert!((camera.aspect_ratio() - 16.0 / 9.0).abs() < 1e-6);
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Camera {
    /// Camera space to world space, in the row-vector convention of
    /// [`gf`](super).
    pub transform: Mat4d,
    /// Whether the camera sees in perspective.
    pub projection: Projection,
    /// Width of the film back, in tenths of a world unit.
    pub horizontal_aperture: f32,
    /// Height of the film back, in tenths of a world unit.
    pub vertical_aperture: f32,
    /// How far the film back is moved to the right of the lens axis, in
    /// tenths of a world unit.
    pub horizontal_aperture_offset: f32,
    /// How far the film back is moved above the lens axis, in tenths of a
    /// world unit.
    pub vertical_aperture_offset: f32,
    /// Distance from the lens to the film back, in tenths of a world unit.
    pub focal_length: f32,
    /// The near and far distances between which the camera sees, in world
    /// units. Held as given: nothing here asks that it be ordered or
    /// positive.
    pub clipping_range: Range1f,
    /// Further planes to clip by, each `(a, b, c, d)` keeping the points of
    /// camera space where `a·x + b·y + c·z + d` is positive.
    pub clipping_planes: Vec<Vec4f>,
    /// Lens aperture as an f-number, where zero is a lens that keeps
    /// everything in focus.
    pub f_stop: f32,
    /// Distance to the plane in focus, in world units.
    pub focus_distance: f32,
}

/// The direction a field of view or an orthographic size is measured in (C++
/// `GfCamera::FOVDirection`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FovDirection {
    /// Across the width of the film back.
    Horizontal,
    /// Across the height of the film back.
    Vertical,
}

impl Camera {
    /// World units in one unit of aperture (C++ `GfCamera::APERTURE_UNIT`).
    pub const APERTURE_UNIT: f64 = 0.1;

    /// World units in one unit of focal length (C++
    /// `GfCamera::FOCAL_LENGTH_UNIT`).
    pub const FOCAL_LENGTH_UNIT: f64 = 0.1;

    /// The horizontal aperture of the default camera (C++
    /// `GfCamera::DEFAULT_HORIZONTAL_APERTURE`): the 0.825 inch width of a
    /// 35mm spherical projector aperture, as `0.825 * 2.54 / APERTURE_UNIT`.
    pub const DEFAULT_HORIZONTAL_APERTURE: f32 = 20.955;

    /// The vertical aperture of the default camera (C++
    /// `GfCamera::DEFAULT_VERTICAL_APERTURE`): the 0.602 inch height of a
    /// 35mm spherical projector aperture, as `0.602 * 2.54 / APERTURE_UNIT`.
    pub const DEFAULT_VERTICAL_APERTURE: f32 = 15.2908;

    /// Width over height of the film back (C++ `GetAspectRatio`), and zero
    /// for a film back of no height.
    pub fn aspect_ratio(&self) -> f32 {
        match self.vertical_aperture == 0.0 {
            true => 0.0,
            false => self.horizontal_aperture / self.vertical_aperture,
        }
    }

    /// The angle the film back spans along `direction`, in degrees (C++
    /// `GetFieldOfView`). A camera of no focal length spans 180 degrees.
    pub fn field_of_view(&self, direction: FovDirection) -> f32 {
        let aperture = f64::from(self.aperture(direction));
        let half = (aperture * Self::APERTURE_UNIT) / (2.0 * f64::from(self.focal_length) * Self::FOCAL_LENGTH_UNIT);
        (2.0 * half.atan()).to_degrees() as f32
    }

    /// Make this a perspective camera whose film back is
    /// `horizontal_aperture` wide with `aspect_ratio`, and whose focal
    /// length gives it `fov_degrees` along `direction` (C++
    /// `SetPerspectiveFromAspectRatioAndFieldOfView`).
    ///
    /// An aspect ratio of zero is read as one. A field of view of zero has
    /// no focal length that gives it, and sets 50.
    pub fn set_perspective(
        &mut self,
        aspect_ratio: f32,
        fov_degrees: f32,
        direction: FovDirection,
        horizontal_aperture: f32,
    ) {
        self.projection = Projection::Perspective;
        self.horizontal_aperture = horizontal_aperture;
        self.vertical_aperture = horizontal_aperture / if aspect_ratio != 0.0 { aspect_ratio } else { 1.0 };

        let tan = (0.5 * f64::from(fov_degrees).to_radians()).tan() as f32;
        if tan == 0.0 {
            self.focal_length = 50.0;
            return;
        }
        let aperture = f64::from(self.aperture(direction));
        self.focal_length = (aperture * Self::APERTURE_UNIT / (2.0 * f64::from(tan)) / Self::FOCAL_LENGTH_UNIT) as f32;
    }

    /// Make this an orthographic camera that sees `size` world units along
    /// `direction`, with `aspect_ratio` (C++
    /// `SetOrthographicFromAspectRatioAndSize`). The focal length, which an
    /// orthographic camera does not use, is set to 50.
    ///
    /// Sized horizontally, an aspect ratio that is not positive gives a
    /// square film back. Sized vertically, the width is the height times the
    /// ratio whatever the ratio is.
    pub fn set_orthographic(&mut self, aspect_ratio: f32, size: f32, direction: FovDirection) {
        self.projection = Projection::Orthographic;
        self.focal_length = 50.0;

        let aperture = (f64::from(size) / Self::APERTURE_UNIT) as f32;
        match direction {
            FovDirection::Horizontal => {
                self.horizontal_aperture = aperture;
                self.vertical_aperture = if aspect_ratio > 0.0 {
                    aperture / aspect_ratio
                } else {
                    aperture
                };
            }
            FovDirection::Vertical => {
                self.vertical_aperture = aperture;
                self.horizontal_aperture = aperture * aspect_ratio;
            }
        }
    }

    /// Set the placement, projection, film back and clipping range from a
    /// view and a projection matrix (C++ `SetFromViewAndProjectionMatrix`).
    /// `focal_length` is given, since the matrices only fix its ratio to the
    /// apertures. The clipping planes, the f-stop and the focus distance are
    /// kept.
    ///
    /// `view` carries the world into camera space. `projection` is a
    /// matrix [`ProjectionParams::from_matrix`] reads: it carries camera
    /// space into OpenGL clip space, where what is seen has `z` between −1
    /// and 1 after the divide.
    ///
    /// Returns `false`, and leaves the camera as it was, for matrices no
    /// camera reproduces: a `view` with no inverse, a `projection` that
    /// reads as no projection, and one whose apertures, offsets or clipping
    /// distances do not fit the single precision a camera holds them in.
    /// C++ sets the camera from all three.
    pub fn set_from_view_and_projection(&mut self, view: Mat4d, projection: Mat4d, focal_length: f32) -> bool {
        let (Some(transform), Some(params)) = (view.inverse(), ProjectionParams::from_matrix(projection)) else {
            return false;
        };
        // A perspective window stands at a distance of one, so the film
        // back is that window at the focal length. An orthographic one is
        // the film back itself.
        let to_aperture = match params.projection {
            Projection::Perspective => f64::from(focal_length) * Self::FOCAL_LENGTH_UNIT / Self::APERTURE_UNIT,
            Projection::Orthographic => 1.0 / Self::APERTURE_UNIT,
        };
        let derived = [
            (params.right - params.left) * to_aperture,
            (params.top - params.bottom) * to_aperture,
            0.5 * (params.right + params.left) * to_aperture,
            0.5 * (params.top + params.bottom) * to_aperture,
            params.near,
            params.far,
        ]
        .map(|v| v as f32);
        if !derived.iter().all(|v| v.is_finite()) {
            return false;
        }
        let [horizontal, vertical, horizontal_offset, vertical_offset, near, far] = derived;

        self.transform = transform;
        self.projection = params.projection;
        self.focal_length = focal_length;
        self.horizontal_aperture = horizontal;
        self.vertical_aperture = vertical;
        self.horizontal_aperture_offset = horizontal_offset;
        self.vertical_aperture_offset = vertical_offset;
        self.clipping_range = Range1f::new(near, far);
        true
    }

    /// The aperture measured along `direction`.
    fn aperture(&self, direction: FovDirection) -> f32 {
        match direction {
            FovDirection::Horizontal => self.horizontal_aperture,
            FovDirection::Vertical => self.vertical_aperture,
        }
    }
}

impl Default for Camera {
    fn default() -> Self {
        Camera {
            transform: Mat4d::IDENTITY,
            projection: Projection::Perspective,
            horizontal_aperture: Self::DEFAULT_HORIZONTAL_APERTURE,
            vertical_aperture: Self::DEFAULT_VERTICAL_APERTURE,
            horizontal_aperture_offset: 0.0,
            vertical_aperture_offset: 0.0,
            focal_length: 50.0,
            clipping_range: Range1f::new(1.0, 1_000_000.0),
            clipping_planes: Vec::new(),
            f_stop: 0.0,
            focus_distance: 0.0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Camera, FovDirection, Projection};
    use crate::gf;
    use crate::gf::matrix::tests::assert_close;

    fn close(got: f32, want: f32) -> bool {
        (got - want).abs() < 1e-5
    }

    /// The default camera is the one C++ builds with no arguments.
    #[test]
    fn default_camera() {
        let camera = Camera::default();
        assert_eq!(camera.transform, gf::Mat4d::IDENTITY);
        assert_eq!(camera.projection, Projection::Perspective);
        assert_eq!(
            camera.horizontal_aperture,
            (0.825 * 2.54 / Camera::APERTURE_UNIT) as f32
        );
        assert_eq!(camera.vertical_aperture, (0.602 * 2.54 / Camera::APERTURE_UNIT) as f32);
        assert_eq!(camera.focal_length, 50.0);
        assert_eq!(camera.clipping_range, gf::Range1f::new(1.0, 1_000_000.0));
        assert!(camera.clipping_planes.is_empty());
        assert_eq!((camera.f_stop, camera.focus_distance), (0.0, 0.0));
    }

    /// The field of view follows from the aperture and the focal length,
    /// and setting it finds the focal length back.
    #[test]
    fn field_of_view() {
        let mut camera = Camera {
            horizontal_aperture: 34.0,
            vertical_aperture: 20.0,
            focal_length: 50.0,
            projection: Projection::Orthographic,
            ..Camera::default()
        };
        assert!(close(camera.field_of_view(FovDirection::Horizontal), 37.556_065));
        assert!(close(camera.field_of_view(FovDirection::Vertical), 22.619_865));

        camera.set_perspective(1.7, 65.0, FovDirection::Horizontal, 34.0);
        assert_eq!(camera.projection, Projection::Perspective);
        assert!(close(camera.focal_length, 26.684_656));
        assert!(close(camera.horizontal_aperture, 34.0));
        assert!(close(camera.aspect_ratio(), 34.0 / 20.0));

        camera.set_perspective(2.4, 29.732_195, FovDirection::Vertical, 34.0);
        assert!(close(camera.aspect_ratio(), 2.4));
        assert!(close(camera.vertical_aperture, 34.0 / 2.4));
        assert!(close(camera.focal_length, 26.684_656));
    }

    /// An orthographic camera is sized in world units along either
    /// direction.
    #[test]
    fn orthographic_size() {
        let mut camera = Camera::default();
        camera.set_orthographic(2.4, 34.0, FovDirection::Horizontal);
        assert_eq!(camera.projection, Projection::Orthographic);
        assert!(close(camera.horizontal_aperture, 340.0));
        assert!(close(camera.vertical_aperture, 340.0 / 2.4));
        assert_eq!(camera.focal_length, 50.0);

        let mut vertical = Camera::default();
        vertical.set_orthographic(2.4, 34.0 / 2.4, FovDirection::Vertical);
        assert!((vertical.horizontal_aperture - 340.0).abs() < 1e-3);
        assert!(close(vertical.vertical_aperture, 340.0 / 2.4));
    }

    /// Each setter has its own reading of an aspect ratio of zero.
    #[test]
    fn zero_aspect_ratio() {
        let mut camera = Camera::default();
        camera.set_perspective(0.0, 60.0, FovDirection::Horizontal, 36.0);
        assert_eq!((camera.horizontal_aperture, camera.vertical_aperture), (36.0, 36.0));

        camera.set_orthographic(0.0, 3.0, FovDirection::Horizontal);
        assert_eq!(camera.horizontal_aperture, camera.vertical_aperture);
        assert!(close(camera.horizontal_aperture, 30.0));

        camera.set_orthographic(0.0, 3.0, FovDirection::Vertical);
        assert!(close(camera.vertical_aperture, 30.0));
        assert_eq!(camera.horizontal_aperture, 0.0);

        camera.vertical_aperture = 0.0;
        assert_eq!(camera.aspect_ratio(), 0.0);
    }

    /// A field of view of zero sets the focal length C++ falls back to, and
    /// a focal length of zero spans half a turn.
    #[test]
    fn degenerate_lens() {
        let mut camera = Camera::default();
        camera.set_perspective(1.0, 0.0, FovDirection::Horizontal, 36.0);
        assert_eq!(camera.focal_length, 50.0);

        camera.focal_length = 0.0;
        assert_eq!(camera.field_of_view(FovDirection::Horizontal), 180.0);
    }

    /// A perspective matrix gives back the window it was built from, as
    /// apertures and offsets about the focal length.
    #[test]
    fn from_perspective_matrices() {
        let placed = gf::Mat4d::rotation_y(0.4) * gf::Mat4d::translation([1.0, 2.0, 3.0]);
        let view = placed.inverse().expect("a rigid transform inverts");
        let mut camera = Camera {
            f_stop: 2.8,
            focus_distance: 7.0,
            ..Camera::default()
        };
        assert!(camera.set_from_view_and_projection(
            view,
            gf::Mat4d::perspective(-0.2, 0.4, -0.1, 0.3, 2.0, 50.0),
            35.0
        ));

        assert_eq!(camera.projection, Projection::Perspective);
        assert_eq!(camera.focal_length, 35.0);
        // A window of 0.6 by 0.4 at a distance of one, 35 away.
        assert!(close(camera.horizontal_aperture, 21.0));
        assert!(close(camera.vertical_aperture, 14.0));
        assert!(close(camera.horizontal_aperture_offset, 3.5));
        assert!(close(camera.vertical_aperture_offset, 3.5));
        assert!(close(camera.clipping_range.min(), 2.0));
        assert!((camera.clipping_range.max() - 50.0).abs() < 1e-3);
        assert_eq!((camera.f_stop, camera.focus_distance), (2.8, 7.0));
        assert_close(camera.transform, placed);
    }

    /// An orthographic matrix gives back its box in tenths of a unit.
    #[test]
    fn from_orthographic_matrices() {
        let mut camera = Camera::default();
        let projection = gf::Mat4d::orthographic(-1.0, 3.0, -2.0, 1.0, 0.5, 20.0);
        assert!(camera.set_from_view_and_projection(gf::Mat4d::IDENTITY, projection, 50.0));

        assert_eq!(camera.projection, Projection::Orthographic);
        assert!(close(camera.horizontal_aperture, 40.0));
        assert!(close(camera.vertical_aperture, 30.0));
        assert!(close(camera.horizontal_aperture_offset, 10.0));
        assert!(close(camera.vertical_aperture_offset, -5.0));
        assert!(close(camera.clipping_range.min(), 0.5));
        assert!(close(camera.clipping_range.max(), 20.0));
    }

    /// Matrices no camera reproduces leave the camera as it was.
    #[test]
    fn unusable_matrices_refused() {
        let good = gf::Mat4d::perspective(-1.0, 1.0, -1.0, 1.0, 1.0, 10.0);
        let before = Camera {
            focal_length: 28.0,
            ..Camera::default()
        };

        let singular = gf::Mat4d::scale([1.0, 0.0, 1.0]);
        let mut neither = good;
        neither[(2, 3)] = -0.5;
        let mut nan = good;
        nan[(2, 3)] = f64::NAN;
        let mut flat = good;
        flat[(0, 0)] = 0.0;
        let mut endless = good;
        endless[(2, 2)] = -1.0;

        // A box that is a projection, and wider than a single-precision
        // aperture can say.
        let vast = gf::Mat4d::orthographic(-1e39, 1e39, -1.0, 1.0, 1.0, 10.0);
        assert!(gf::ProjectionParams::from_matrix(vast).is_some());

        let cases = [
            (singular, good),
            (gf::Mat4d::IDENTITY, neither),
            (gf::Mat4d::IDENTITY, nan),
            (gf::Mat4d::IDENTITY, flat),
            (gf::Mat4d::IDENTITY, endless),
            (gf::Mat4d::IDENTITY, vast),
        ];
        for (view, projection) in cases {
            let mut camera = before.clone();
            assert!(!camera.set_from_view_and_projection(view, projection, 35.0));
            assert_eq!(camera, before);
        }
    }
}
