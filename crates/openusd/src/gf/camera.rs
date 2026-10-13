//! `GfCamera` — a camera as a plain value: where it sits and what it sees.

use super::{Frustum, Mat4d, Projection, ProjectionParams, Range1d, Range1f, Range2d, Vec2d, Vec4f};

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

    /// The volume the camera sees (C++ `GetFrustum`).
    ///
    /// The film back, moved by its offsets, is the frustum's window: as it
    /// is for an orthographic camera, and brought to a distance of one for a
    /// perspective camera, by its focal length. A perspective camera of no
    /// focal length keeps the film back as its window. The frustum is placed
    /// as [`Frustum::set_position_and_rotation`] reads the transform, so a
    /// scale in it is left out.
    pub fn frustum(&self) -> Frustum {
        let half = Vec2d {
            x: f64::from(self.horizontal_aperture / 2.0),
            y: f64::from(self.vertical_aperture / 2.0),
        };
        let offset = Vec2d {
            x: f64::from(self.horizontal_aperture_offset),
            y: f64::from(self.vertical_aperture_offset),
        };
        // The film back about the lens axis, moved by its offsets, in world
        // units.
        let mut window = (Range2d::new(-half, half) + Range2d::new(offset, offset)) * Self::APERTURE_UNIT;
        if self.projection != Projection::Orthographic && self.focal_length != 0.0 {
            window = window / (f64::from(self.focal_length) * Self::FOCAL_LENGTH_UNIT);
        }
        let near_far = Range1d::new(
            f64::from(self.clipping_range.min()),
            f64::from(self.clipping_range.max()),
        );
        Frustum::from_matrix(self.transform, window, near_far, self.projection)
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
    use crate::gf::matrix::tests::{assert_close, turn};

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

    fn assert_corners(camera: &Camera, expected: [[f64; 3]; 8], tolerance: f64) {
        for (corner, expected) in camera.frustum().corners().into_iter().zip(expected) {
            assert!(
                (corner - gf::Vec3d::from(expected)).length() < tolerance,
                "{corner:?} is not {expected:?}"
            );
        }
    }

    /// The corners C++ computes for a camera under a transform that scales,
    /// in perspective and as three orthographic cameras of one size.
    #[test]
    fn frustum_corners_scaled() {
        let transform = turn([1.0, 2.0, 3.0], 20.3)
            * gf::Mat4d::translation([100.0, 123.0, 153.0])
            * gf::Mat4d::scale([2.0, 1.0, 1.3]);
        let mut camera = Camera {
            transform,
            clipping_range: gf::Range1f::new(10.0, 100.0),
            ..Camera::default()
        };
        camera.set_perspective(2.4, 29.732_195, FovDirection::Vertical, 34.0);
        assert_corners(
            &camera,
            [
                [192.846230529544, 118.9700660570964, 189.943705234630],
                [204.624699588231, 123.2629367321672, 187.667234572988],
                [191.159053763979, 123.9580649710064, 190.620399628732],
                [202.937522822666, 128.2509356460773, 188.343928967090],
                [128.462305295447, 82.70066057096416, 109.337052346305],
                [246.246995882312, 125.6293673216727, 86.5723457298875],
                [111.590537639799, 132.5806497100646, 116.103996287320],
                [229.375228226663, 175.5093564607731, 93.3392896709023],
            ],
            1e-6,
        );

        let orthographic = [
            [184.427743371372, 111.227660346205, 191.278291105439],
            [215.858183043795, 122.683038129349, 185.203607422842],
            [179.925570308415, 124.537963573823, 193.084026778878],
            [211.356009980839, 135.993341356968, 187.009343096281],
            [165.454633456322, 116.722168010487, 103.472645013183],
            [196.885073128745, 128.177545793631, 97.3979613305862],
            [160.952460393365, 130.032471238105, 105.278380686621],
            [192.382900065789, 141.487849021250, 99.2036970040248],
        ];
        camera.horizontal_aperture = 340.0;
        camera.vertical_aperture = 340.0 / 2.4;
        camera.projection = Projection::Orthographic;
        assert_corners(&camera, orthographic, 1e-6);

        let sized = |size: f32, direction: FovDirection| {
            let mut camera = Camera {
                transform,
                clipping_range: gf::Range1f::new(10.0, 100.0),
                ..Camera::default()
            };
            camera.set_orthographic(2.4, size, direction);
            camera
        };
        assert_corners(&sized(34.0, FovDirection::Horizontal), orthographic, 1e-6);
        assert_corners(&sized(34.0 / 2.4, FovDirection::Vertical), orthographic, 1e-4);
    }

    /// The corners C++ computes for a camera under a rigid transform.
    #[test]
    fn frustum_corners_rigid() {
        let transform = turn([1.0, -2.0, 3.0], 30.3) * gf::Mat4d::translation([-100.0, 123.0, 153.0]);
        let mut camera = Camera {
            transform,
            clipping_range: gf::Range1f::new(10.0, 100.0),
            ..Camera::default()
        };
        camera.set_perspective(2.4, 29.732_195, FovDirection::Vertical, 34.0);
        assert_corners(
            &camera,
            [
                [-102.032919327869, 120.085637354940, 141.38080336149],
                [-90.9077235508873, 124.991168793969, 145.18989392187],
                [-104.284096916572, 124.876540072942, 141.78585214522],
                [-93.1589011395900, 129.782071511971, 145.59494270559],
                [-120.329193278696, 93.8563735494037, 36.808033614959],
                [-9.07723550887376, 142.911687939691, 74.898939218725],
                [-142.840969165722, 141.765400729428, 40.858521452219],
                [-31.5890113959001, 190.820715119715, 78.949427055984],
            ],
            1e-6,
        );

        camera.horizontal_aperture = 340.0;
        camera.vertical_aperture = 340.0 / 2.4;
        camera.projection = Projection::Orthographic;
        assert_corners(
            &camera,
            [
                [-109.435916189226, 111.996553352311, 137.8652300230474],
                [-79.748713805783, 125.086795317320, 148.0296572052388],
                [-115.443106661676, 124.780913549591, 138.9460888618555],
                [-85.755904278233, 137.871155514600, 149.1105160440469],
                [-87.799108292794, 129.401243253415, 52.2560873249726],
                [-58.111905909352, 142.491485218423, 62.4205145071640],
                [-93.806298765244, 142.185603450695, 53.3369461637807],
                [-64.119096381802, 155.275845415703, 63.5013733459721],
            ],
            1e-6,
        );
    }

    /// An aperture offset moves the window, and the default clipping range
    /// reaches a million units out.
    #[test]
    fn frustum_with_offset() {
        let camera = Camera {
            vertical_aperture_offset: 1.2,
            ..Camera::default()
        };
        assert_corners(
            &camera,
            [
                [-0.20954999923706, -0.128907999992370, -1.0],
                [0.209549999237060, -0.128907999992370, -1.0],
                [-0.20954999923706, 0.1769080018997192, -1.0],
                [0.209549999237060, 0.1769080018997192, -1.0],
                [-209549.999237060, -128907.9999923706, -1000000.0],
                [209549.9992370605, -128907.9999923706, -1000000.0],
                [-209549.999237060, 176908.00189971924, -1000000.0],
                [209549.9992370605, 176908.00189971924, -1000000.0],
            ],
            1e-4,
        );
    }

    /// A camera comes back from the view and projection matrices of its own
    /// frustum.
    #[test]
    fn frustum_matrices_round_trip() {
        for projection in [Projection::Perspective, Projection::Orthographic] {
            let camera = Camera {
                transform: turn([1.0, -2.0, 3.0], 30.3) * gf::Mat4d::translation([-100.0, 123.0, 153.0]),
                projection,
                horizontal_aperture: 36.0,
                vertical_aperture: 24.0,
                horizontal_aperture_offset: 1.5,
                vertical_aperture_offset: -2.5,
                focal_length: 35.0,
                clipping_range: gf::Range1f::new(0.5, 200.0),
                f_stop: 4.0,
                ..Camera::default()
            };
            let frustum = camera.frustum();
            let mut read = Camera {
                f_stop: 4.0,
                ..Camera::default()
            };
            assert!(read.set_from_view_and_projection(frustum.view_matrix(), frustum.projection_matrix(), 35.0));

            assert_close(read.transform, camera.transform);
            assert_eq!(read.projection, projection);
            let pairs = [
                (read.horizontal_aperture, camera.horizontal_aperture),
                (read.vertical_aperture, camera.vertical_aperture),
                (read.horizontal_aperture_offset, camera.horizontal_aperture_offset),
                (read.vertical_aperture_offset, camera.vertical_aperture_offset),
                (read.clipping_range.min(), camera.clipping_range.min()),
                (read.clipping_range.max(), camera.clipping_range.max()),
            ];
            for (got, want) in pairs {
                assert!((got - want).abs() < 1e-3 * want.abs().max(1.0), "{got} is not {want}");
            }
        }
    }
}
