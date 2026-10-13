//! `GfFrustum` — the volume a camera sees.

use super::{
    BBox3d, FovDirection, Mat4d, Plane, Projection, ProjectionParams, Range1d, Range2d, Ray, Rotation, Vec2d, Vec3d,
    Vec4d,
};

/// The volume of space a camera sees, and where it sees it from (C++
/// `GfFrustum`).
///
/// The frustum looks along −Z of its own space with +Y up, from
/// [`position`](Self::position) and turned by [`rotation`](Self::rotation).
/// It sees through [`window`](Self::window), between the distances of
/// [`near_far`](Self::near_far). A perspective window stands at a distance
/// of one from the position, so its size is the tangent of the field of
/// view; an orthographic window is the same at every distance.
///
/// The [`Default`] frustum is a perspective one at the origin, with a window
/// from −1 to 1 each way seen between distances 1 and 10. An angle is in
/// degrees.
///
/// ```
/// use openusd::gf;
///
/// let mut frustum = gf::Frustum::default();
/// frustum.set_perspective(60.0, gf::FovDirection::Vertical, 16.0 / 9.0, 0.1, 100.0);
/// assert!((frustum.fov(gf::FovDirection::Vertical) - 60.0).abs() < 1e-12);
/// assert!((frustum.aspect_ratio() - 16.0 / 9.0).abs() < 1e-12);
///
/// assert!(frustum.intersects_point(gf::vec3d(0.0, 0.0, -5.0)));
/// assert!(!frustum.intersects_point(gf::vec3d(0.0, 0.0, 5.0)));
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Frustum {
    /// Where the frustum sees from, in world space.
    pub position: Vec3d,
    /// The turn from the frustum's own space, looking along −Z, to the
    /// world.
    pub rotation: Rotation,
    /// The rectangle seen through: at a distance of one for a perspective
    /// frustum, and at any distance for an orthographic one.
    pub window: Range2d,
    /// The distances along the line of sight between which it sees.
    pub near_far: Range1d,
    /// The distance to the point looked at, which nothing but
    /// [`look_at_point`](Self::look_at_point) and
    /// [`fit_to_sphere`](Self::fit_to_sphere) reads.
    pub view_distance: f64,
    /// Whether lines of sight meet at the position.
    pub projection: Projection,
}

impl Frustum {
    /// The frustum seeing through `window` between `near_far`, placed by a
    /// matrix that carries its own space into the world (C++ `GfFrustum`'s
    /// matrix constructor). The matrix is read as
    /// [`set_position_and_rotation`](Self::set_position_and_rotation) reads
    /// it.
    pub fn from_matrix(camera_to_world: Mat4d, window: Range2d, near_far: Range1d, projection: Projection) -> Self {
        let mut frustum = Frustum {
            window,
            near_far,
            projection,
            ..Frustum::default()
        };
        frustum.set_position_and_rotation(camera_to_world);
        frustum
    }

    /// Place the frustum by a matrix that carries its own space into the
    /// world (C++ `SetPositionAndRotationFromMatrix`).
    ///
    /// A frustum holds a position and a turn, and nothing else of a matrix.
    /// A left-handed matrix has its X axis reversed, and the axes are then
    /// made orthogonal and of unit length, so a scale or a shear is left
    /// out.
    pub fn set_position_and_rotation(&mut self, camera_to_world: Mat4d) {
        let mut conformed = camera_to_world;
        if !conformed.is_right_handed() {
            conformed = Mat4d::scale([-1.0, 1.0, 1.0]) * conformed;
        }
        conformed.orthonormalize();
        self.rotation = conformed.extract_rotation();
        self.position = conformed.extract_translation();
    }

    /// Make this a perspective frustum spanning `fov_degrees` along
    /// `direction`, with `aspect_ratio` and the clipping distances given
    /// (C++ `SetPerspective`). An aspect ratio of zero is read as one.
    pub fn set_perspective(
        &mut self,
        fov_degrees: f64,
        direction: FovDirection,
        aspect_ratio: f64,
        near: f64,
        far: f64,
    ) {
        let aspect_ratio = if aspect_ratio == 0.0 { 1.0 } else { aspect_ratio };
        let half = (fov_degrees / 2.0).to_radians().tan();
        let (x, y) = match direction {
            FovDirection::Vertical => (half * aspect_ratio, half),
            FovDirection::Horizontal => (half, half / aspect_ratio),
        };
        self.projection = Projection::Perspective;
        self.window = Range2d::new(Vec2d { x: -x, y: -y }, Vec2d { x, y });
        self.near_far = Range1d::new(near, far);
    }

    /// Make this an orthographic frustum seeing the box from
    /// `(left, bottom)` to `(right, top)` between `near` and `far` (C++
    /// `SetOrthographic`).
    pub fn set_orthographic(&mut self, left: f64, right: f64, bottom: f64, top: f64, near: f64, far: f64) {
        self.projection = Projection::Orthographic;
        self.window = Range2d::new(Vec2d { x: left, y: bottom }, Vec2d { x: right, y: top });
        self.near_far = Range1d::new(near, far);
    }

    /// The angle the window spans along `direction`, in degrees (C++
    /// `GetFOV`), and zero for an orthographic frustum, which spans none.
    pub fn fov(&self, direction: FovDirection) -> f64 {
        if self.projection != Projection::Perspective {
            return 0.0;
        }
        let size = self.window.size();
        let extent = match direction {
            FovDirection::Horizontal => size.x,
            FovDirection::Vertical => size.y,
        };
        2.0 * (extent / 2.0).atan().to_degrees()
    }

    /// Width over height of the window (C++ `ComputeAspectRatio`), as a
    /// magnitude, and zero for a window of no height.
    pub fn aspect_ratio(&self) -> f64 {
        let size = self.window.size();
        match size.y == 0.0 {
            true => 0.0,
            false => (size.x / size.y).abs(),
        }
    }

    /// Move the frustum back along its line of sight until it holds the
    /// sphere at `center`, and set its clipping distances `slack` clear of
    /// the sphere on both sides (C++ `FitToSphere`).
    ///
    /// An orthographic frustum takes a square window of the sphere's size.
    /// A perspective one keeps its window, and stands where the narrower of
    /// its two spans touches the sphere.
    pub fn fit_to_sphere(&mut self, center: Vec3d, radius: f64, slack: f64) {
        match self.projection {
            Projection::Orthographic => {
                self.view_distance = radius + slack;
                self.window = Range2d::new(Vec2d { x: -radius, y: -radius }, Vec2d { x: radius, y: radius });
            }
            Projection::Perspective => {
                // The narrower span, and of its two edges the one further
                // from the line of sight.
                let axis = if self.aspect_ratio() > 1.0 { 1 } else { 0 };
                let (min, max) = (self.window.min()[axis], self.window.max()[axis]);
                let edge = if min > 0.0 {
                    max
                } else if max < 0.0 || -min > max {
                    min
                } else {
                    max
                };
                let half = if edge == 0.0 { 1.0 } else { edge.abs() };
                self.view_distance = radius / half * half.hypot(self.near_far.min());
            }
        }
        let near = self.view_distance - (radius + slack);
        self.near_far = Range1d::new(near, near + 2.0 * (radius + slack));
        self.position = center - self.view_direction() * self.view_distance;
    }

    /// Carry the frustum through `matrix` (C++ `Transform`).
    ///
    /// The position moves as a point and the line of sight and the up
    /// vector as directions. The clipping distances and the view distance
    /// are scaled by how much the line of sight is stretched, and the window
    /// is the one its corners move to. A matrix that mirrors leaves the
    /// window with its edges in order.
    pub fn transform(&mut self, matrix: Mat4d) {
        let turn = Mat4d::from(self.rotation);
        let position = matrix.transform(self.position);
        let view = matrix.transform_dir(turn.transform_dir(-Vec3d::Z_AXIS));
        let scale = view.length();
        let view = view.normalize();
        let up = matrix.transform_dir(turn.transform_dir(Vec3d::Y_AXIS)).normalize();
        let right = view.cross(up).normalize();

        let mut frame = Mat4d::IDENTITY;
        for (r, axis) in [right, up, -view].into_iter().enumerate() {
            frame[(r, 0)] = axis.x;
            frame[(r, 1)] = axis.y;
            frame[(r, 2)] = axis.z;
        }
        let rotation = frame.extract_rotation();

        // A corner of the window, moved with the frustum and read back in
        // the space the new rotation gives it. The moved corner stands at
        // the stretched distance, and a perspective window at a distance of
        // one.
        let back = Mat4d::from(rotation.inverse());
        let corner = |at: Vec2d| {
            let moved = matrix.transform(
                self.position
                    + turn.transform_dir(Vec3d {
                        x: at.x,
                        y: at.y,
                        z: -1.0,
                    }),
            );
            let local = back.transform_dir(moved - position) * (1.0 / self.spread(scale));
            Vec2d { x: local.x, y: local.y }
        };
        let (a, b) = (corner(self.window.min()), corner(self.window.max()));

        *self = Frustum {
            position,
            rotation,
            window: Range2d::new(a.min(b), a.max(b)),
            near_far: self.near_far * scale,
            view_distance: self.view_distance * scale,
            projection: self.projection,
        };
    }

    /// The unit direction the frustum looks along, in world space (C++
    /// `ComputeViewDirection`).
    pub fn view_direction(&self) -> Vec3d {
        self.rotation.transform_dir(-Vec3d::Z_AXIS)
    }

    /// The unit direction that is up to the frustum, in world space (C++
    /// `ComputeUpVector`).
    pub fn up_vector(&self) -> Vec3d {
        self.rotation.transform_dir(Vec3d::Y_AXIS)
    }

    /// The frustum's axes in world space, as `(side, up, view)` (C++
    /// `ComputeViewFrame`): the direction to its right, its up vector and
    /// its line of sight.
    pub fn view_frame(&self) -> (Vec3d, Vec3d, Vec3d) {
        let (up, view) = (self.up_vector(), self.view_direction());
        (view.cross(up), up, view)
    }

    /// The point [`view_distance`](Self::view_distance) along the line of
    /// sight (C++ `ComputeLookAtPoint`).
    pub fn look_at_point(&self) -> Vec3d {
        self.position + self.view_direction() * self.view_distance
    }

    /// The matrix from world space to the frustum's own (C++
    /// `ComputeViewMatrix`).
    pub fn view_matrix(&self) -> Mat4d {
        Mat4d::look_at(self.position, self.rotation)
    }

    /// The matrix from the frustum's own space to the world (C++
    /// `ComputeViewInverse`).
    pub fn view_inverse(&self) -> Mat4d {
        let mut to_world = Mat4d::from(self.rotation);
        to_world.set_translation(self.position);
        to_world
    }

    /// The matrix from the frustum's own space to OpenGL clip space (C++
    /// `ComputeProjectionMatrix`).
    pub fn projection_matrix(&self) -> Mat4d {
        let (min, max) = (self.window.min(), self.window.max());
        ProjectionParams {
            projection: self.projection,
            left: min.x,
            right: max.x,
            bottom: min.y,
            top: max.y,
            near: self.near_far.min(),
            far: self.near_far.max(),
        }
        .matrix()
    }

    /// The eight corners of the volume in world space (C++
    /// `ComputeCorners`): the four of the near plane, then the four of the
    /// far plane, each as left-bottom, right-bottom, left-top, right-top.
    pub fn corners(&self) -> [Vec3d; 8] {
        let to_world = self.view_inverse();
        let [n0, n1, n2, n3] = self.corners_in(to_world, self.near_far.min());
        let [f0, f1, f2, f3] = self.corners_in(to_world, self.near_far.max());
        [n0, n1, n2, n3, f0, f1, f2, f3]
    }

    /// The four corners of the volume `distance` along the line of sight,
    /// in world space (C++ `ComputeCornersAtDistance`), as left-bottom,
    /// right-bottom, left-top, right-top.
    pub fn corners_at(&self, distance: f64) -> [Vec3d; 4] {
        self.corners_in(self.view_inverse(), distance)
    }

    /// The frustum narrowed to see about a place in its window (C++
    /// `ComputeNarrowedFrustum` of a window position).
    ///
    /// `window_pos` places it, with −1 at the left or bottom edge and 1 at
    /// the right or top, and `size` is the width and height to keep as
    /// fractions of the window's. The narrowed window stays inside this one.
    pub fn narrowed(&self, window_pos: Vec2d, size: Vec2d) -> Frustum {
        self.narrowed_about(self.window_point(window_pos), size)
    }

    /// The frustum narrowed to see about a point in the world (C++
    /// `ComputeNarrowedFrustum` of a world point), on the terms of
    /// [`narrowed`](Self::narrowed). A point at or behind the position has
    /// no place in the window, and the frustum comes back as it is.
    pub fn narrowed_to(&self, world_point: Vec3d, size: Vec2d) -> Frustum {
        let local = self.view_matrix().transform(world_point);
        if local.z >= 0.0 {
            return *self;
        }
        let spread = self.spread(-local.z);
        self.narrowed_about(
            Vec2d {
                x: local.x / spread,
                y: local.y / spread,
            },
            size,
        )
    }

    /// The ray from the position through a place in the window, in world
    /// space (C++ `ComputeRay` of a window position), with −1 at the left
    /// or bottom edge and 1 at the right or top. A perspective ray starts at
    /// the position. An orthographic one starts on the near plane.
    pub fn ray(&self, window_pos: Vec2d) -> Ray {
        let point = self.window_point(window_pos);
        let (x, y) = (point.x, point.y);
        let local = match self.projection {
            Projection::Perspective => Ray::new(Vec3d::default(), Vec3d { x, y, z: -1.0 }.normalize()),
            Projection::Orthographic => Ray::new(
                Vec3d {
                    x,
                    y,
                    z: -self.near_far.min(),
                },
                -Vec3d::Z_AXIS,
            ),
        };
        local.transformed(self.view_inverse())
    }

    /// The ray from the position toward a point in the world (C++
    /// `ComputeRay` of a world point). An orthographic ray starts abreast
    /// of the point, on the plane through the position.
    pub fn ray_to(&self, world_point: Vec3d) -> Ray {
        let toward = self.view_matrix().transform(world_point);
        let local = match self.projection {
            Projection::Perspective => Ray::new(Vec3d::default(), toward.normalize()),
            Projection::Orthographic => Ray::new(Vec3d { z: 0.0, ..toward }, -Vec3d::Z_AXIS),
        };
        local.transformed(self.view_inverse())
    }

    /// [`ray`](Self::ray), started the near distance further along so that
    /// it meets nothing the frustum clips away (C++ `ComputePickRay` of a
    /// window position).
    pub fn pick_ray(&self, window_pos: Vec2d) -> Ray {
        self.past_near(self.ray(window_pos))
    }

    /// [`ray_to`](Self::ray_to), started the near distance further along
    /// (C++ `ComputePickRay` of a world point).
    pub fn pick_ray_to(&self, world_point: Vec3d) -> Ray {
        self.past_near(self.ray_to(world_point))
    }

    /// The six planes that bound the volume, each facing into it: left,
    /// right, bottom, top, near and far.
    // TODO(perf): the planes depend on the frustum's fields alone, and each
    // `intersects_*` test builds them again. A caller testing many boxes or
    // points against one frustum would build them once if the tests were
    // offered over a `[Plane; 6]` it holds.
    pub fn planes(&self) -> [Plane; 6] {
        let (near, far) = (self.near_far.min(), self.near_far.max());
        let [lb, rb, lt, rt] = self.corners_at(near);

        let sides = match self.projection {
            // Each side runs from the position through an edge of the near
            // rectangle.
            Projection::Perspective => {
                let eye = self.position;
                [
                    Plane::from_points(eye, lb, lt),
                    Plane::from_points(eye, rt, rb),
                    Plane::from_points(eye, rb, lb),
                    Plane::from_points(eye, lt, rt),
                ]
            }
            // Each side runs from an edge of the near rectangle along the
            // line of sight.
            Projection::Orthographic => {
                let view = self.view_direction();
                [
                    Plane::from_points(lt + view, lt, lb),
                    Plane::from_points(rb + view, rb, rt),
                    Plane::from_points(lb + view, lb, rb),
                    Plane::from_points(rt + view, rt, lt),
                ]
            }
        };
        let near_plane = Plane::from_points(rb, lb, lt);
        let far_plane = Plane::new(
            -near_plane.normal(),
            -(near_plane.distance_from_origin() + (far - near)),
        );
        [sides[0], sides[1], sides[2], sides[3], near_plane, far_plane]
    }

    /// Whether any of `bbox` is inside the volume (C++ `Intersects` of a
    /// box). An empty box is not.
    ///
    /// The box is turned away only when it is wholly behind one of the six
    /// planes, so a box near a corner of the volume can be reported inside
    /// when it is just outside. A box whose matrix has no inverse is tested
    /// as its range stands, with no matrix.
    pub fn intersects_bbox(&self, bbox: &BBox3d) -> bool {
        let range = bbox.range();
        // Each plane is brought into the box's own space, where the box is
        // aligned to the axes, by the inverse of the matrix that takes the
        // world there.
        let to_world = bbox.inverse_matrix().inverse().unwrap_or(Mat4d::IDENTITY);
        !range.is_empty()
            && self
                .planes()
                .iter()
                .all(|plane| plane.under_inverse(to_world).reaches_positive_side(range))
    }

    /// Whether `point` is inside the volume or on its boundary (C++
    /// `Intersects` of a point).
    pub fn intersects_point(&self, point: Vec3d) -> bool {
        self.planes().iter().all(|plane| plane.on_positive_side(point))
    }

    /// Whether any of the segment from `p0` to `p1` is inside the volume
    /// (C++ `Intersects` of a segment).
    pub fn intersects_segment(&self, p0: Vec3d, p1: Vec3d) -> bool {
        let planes = self.planes();
        segment_intersects(&planes, (p0, inside_mask(&planes, p0)), (p1, inside_mask(&planes, p1)))
    }

    /// Whether any of the triangle of three points is inside the volume
    /// (C++ `Intersects` of a triangle).
    pub fn intersects_triangle(&self, p0: Vec3d, p1: Vec3d, p2: Vec3d) -> bool {
        let planes = self.planes();
        let corners = [p0, p1, p2].map(|p| (p, inside_mask(&planes, p)));
        let masks = corners.map(|(_, mask)| mask);

        // All three behind one plane.
        if masks.iter().fold(0, |all, mask| all | mask) != ALL_PLANES {
            return false;
        }
        if masks.contains(&ALL_PLANES) {
            return true;
        }
        if (0..3).any(|i| segment_intersects(&planes, corners[i], corners[(i + 1) % 3])) {
            return true;
        }

        // What is left is a triangle that surrounds the volume, which a
        // line of sight along one of its corners then passes through. One
        // corner settles it where the triangle lies between the near and far
        // planes. Where one of those planes cuts it, all four are tried.
        let between = masks.iter().all(|mask| mask & NEAR_AND_FAR == NEAR_AND_FAR);
        let lines = [(-1.0, -1.0), (-1.0, 1.0), (1.0, 1.0), (1.0, -1.0)];
        lines[..if between { 1 } else { 4 }]
            .iter()
            .any(|&(x, y)| self.pick_ray(Vec2d { x, y }).intersect_triangle(p0, p1, p2).is_some())
    }

    /// Whether any of `bbox` is inside the volume a view-projection matrix
    /// sees (C++ `IntersectsViewVolume`), where `view_projection` carries
    /// world space into clip space.
    ///
    /// The box is outside when its eight corners are all beyond one side of
    /// clip space, which also holds for the volumes with a slanted near or
    /// far plane that no frustum describes.
    pub fn intersects_view_volume(bbox: &BBox3d, view_projection: Mat4d) -> bool {
        let to_clip = bbox.matrix() * view_projection;
        let corners = bbox.range().corners().map(|corner| {
            let clip = to_clip.transform_homogeneous(Vec4d {
                x: corner.x,
                y: corner.y,
                z: corner.z,
                w: 1.0,
            });
            ([clip.x, clip.y, clip.z], clip.w)
        });
        // Along each axis some corner has to be inside each of the two
        // bounds, which are the homogeneous coordinate and its negation.
        (0..3).all(|axis| {
            corners.iter().any(|(clip, w)| clip[axis] < *w) && corners.iter().any(|(clip, w)| clip[axis] > -*w)
        })
    }

    /// The point of the window that `window_pos` names, with −1 at its left
    /// or bottom edge and 1 at its right or top.
    fn window_point(&self, window_pos: Vec2d) -> Vec2d {
        let (min, size) = (self.window.min(), self.window.size());
        Vec2d {
            x: min.x + 0.5 * (1.0 + window_pos.x) * size.x,
            y: min.y + 0.5 * (1.0 + window_pos.y) * size.y,
        }
    }

    /// This frustum with its window narrowed to `size` of itself about
    /// `point`, kept inside the window it has.
    fn narrowed_about(&self, point: Vec2d, size: Vec2d) -> Frustum {
        let (min, max, extent) = (self.window.min(), self.window.max(), self.window.size());
        let half = Vec2d {
            x: 0.5 * size.x * extent.x,
            y: 0.5 * size.y * extent.y,
        };
        let window = Range2d::new((point - half).max(min), (point + half).min(max));
        Frustum { window, ..*self }
    }

    /// What a window coordinate is multiplied by to stand `distance` along
    /// the line of sight: the distance itself for a perspective frustum,
    /// whose window stands at a distance of one, and one for an orthographic
    /// frustum.
    fn spread(&self, distance: f64) -> f64 {
        match self.projection {
            Projection::Perspective => distance,
            Projection::Orthographic => 1.0,
        }
    }

    /// The four corners of the volume `distance` along the line of sight,
    /// carried into the world by `to_world`.
    fn corners_in(&self, to_world: Mat4d, distance: f64) -> [Vec3d; 4] {
        let (min, max) = (self.window.min(), self.window.max());
        let spread = self.spread(distance);
        [(min.x, min.y), (max.x, min.y), (min.x, max.y), (max.x, max.y)].map(|(x, y)| {
            to_world.transform(Vec3d {
                x: x * spread,
                y: y * spread,
                z: -distance,
            })
        })
    }

    /// `ray` started the near distance further along itself.
    fn past_near(&self, ray: Ray) -> Ray {
        Ray::new(ray.point(self.near_far.min()), ray.direction)
    }
}

impl Default for Frustum {
    fn default() -> Self {
        Frustum {
            position: Vec3d::default(),
            rotation: Rotation::IDENTITY,
            window: Range2d::new(Vec2d { x: -1.0, y: -1.0 }, Vec2d { x: 1.0, y: 1.0 }),
            near_far: Range1d::new(1.0, 10.0),
            view_distance: 5.0,
            projection: Projection::Perspective,
        }
    }
}

/// The mask of a point inside all six planes.
const ALL_PLANES: u32 = 0x3f;

/// The bits of the near and far planes, the fifth and sixth of
/// [`Frustum::planes`].
const NEAR_AND_FAR: u32 = 0x30;

/// One bit for each of `planes` that `point` is on the inner side of.
fn inside_mask(planes: &[Plane; 6], point: Vec3d) -> u32 {
    planes.iter().enumerate().fold(0, |mask, (i, plane)| {
        mask | (u32::from(plane.on_positive_side(point)) << i)
    })
}

/// Whether any of the segment between two points, each with its
/// [`inside_mask`], is inside all of `planes`.
fn segment_intersects(planes: &[Plane; 6], (p0, mask0): (Vec3d, u32), (p1, mask1): (Vec3d, u32)) -> bool {
    // Both ends behind one plane.
    if mask0 | mask1 != ALL_PLANES {
        return false;
    }
    if mask0 == ALL_PLANES || mask1 == ALL_PLANES {
        return true;
    }
    // Both ends are outside, behind different planes. The segment is cut by
    // each plane it crosses, as a span of the parameter that runs from zero
    // at `p0` to one at `p1`, and is inside where something is left.
    let along = p1 - p0;
    let (mut start, mut end) = (0.0_f64, 1.0_f64);
    for (i, plane) in planes.iter().enumerate() {
        let (in0, in1) = (mask0 & (1 << i) != 0, mask1 & (1 << i) != 0);
        if in0 == in1 {
            continue;
        }
        let crossing = -plane.distance(p0) / plane.normal().dot(along);
        match in0 {
            true => end = end.min(crossing),
            false => start = start.max(crossing),
        }
        if start > end {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::Frustum;
    use crate::gf::matrix::tests::turn;
    use crate::gf::{self, FovDirection, Projection};

    fn window(min: [f64; 2], max: [f64; 2]) -> gf::Range2d {
        gf::Range2d::new(min.into(), max.into())
    }

    fn close(got: gf::Vec3d, want: [f64; 3], tolerance: f64) -> bool {
        (got - gf::Vec3d::from(want)).length() < tolerance
    }

    fn orthographic() -> Frustum {
        Frustum {
            projection: Projection::Orthographic,
            ..Frustum::default()
        }
    }

    /// The default frustum looks down −Z from the origin.
    #[test]
    fn default_frame() {
        let f = Frustum::default();
        assert_eq!(f.view_direction(), gf::vec3d(0.0, 0.0, -1.0));
        assert_eq!(f.up_vector(), gf::vec3d(0.0, 1.0, 0.0));
        assert_eq!(
            f.view_frame(),
            (gf::Vec3d::X_AXIS, gf::Vec3d::Y_AXIS, gf::vec3d(0.0, 0.0, -1.0))
        );
        assert_eq!(f.look_at_point(), gf::vec3d(0.0, 0.0, -5.0));
        assert_eq!(orthographic().look_at_point(), gf::vec3d(0.0, 0.0, -5.0));
        assert_ne!(
            Frustum {
                position: gf::Vec3d::X_AXIS,
                ..f
            },
            f
        );
    }

    /// A perspective frustum is set by its field of view along either
    /// direction, and an orthographic one by its box.
    #[test]
    fn projection_setters() {
        let mut f = Frustum::default();
        f.set_perspective(10.0, FovDirection::Vertical, 20.0, 30.0, 40.0);
        assert!((f.fov(FovDirection::Vertical) - 10.0).abs() < 1e-12);
        assert!((f.aspect_ratio() - 20.0).abs() < 1e-12);
        assert_eq!(f.near_far, gf::Range1d::new(30.0, 40.0));

        f.set_perspective(10.0, FovDirection::Horizontal, 20.0, 30.0, 40.0);
        assert!((f.fov(FovDirection::Horizontal) - 10.0).abs() < 1e-12);
        assert!((f.aspect_ratio() - 20.0).abs() < 1e-12);

        f.set_orthographic(10.0, 20.0, 30.0, 40.0, 50.0, 60.0);
        assert_eq!(f.projection, Projection::Orthographic);
        assert_eq!(f.window, window([10.0, 30.0], [20.0, 40.0]));
        assert_eq!(f.near_far, gf::Range1d::new(50.0, 60.0));
        assert_eq!(f.fov(FovDirection::Vertical), 0.0);
        assert_eq!(f.fov(FovDirection::Horizontal), 0.0);

        f.set_perspective(10.0, FovDirection::Vertical, 0.0, 1.0, 2.0);
        assert!((f.aspect_ratio() - 1.0).abs() < 1e-12);
    }

    /// A transform turns the line of sight and the up vector with it.
    #[test]
    fn transform_turns_frame() {
        let mut f = Frustum::default();
        f.transform(turn([1.0, 1.0, 1.0], 30.0));
        assert!(close(f.view_direction(), [-0.333333, 0.244017, -0.910684], 1e-4));
        assert!(close(f.up_vector(), [-0.244017, 0.910684, 0.333333], 1e-4));
    }

    /// A scale stretches the clipping distances with the line of sight, and
    /// a mirror leaves the window's edges in order.
    #[test]
    fn transform_scales() {
        let mut f = Frustum::default();
        f.transform(gf::Mat4d::scale([2.0, 2.0, 2.0]));
        assert_eq!(f.near_far, gf::Range1d::new(2.0, 20.0));
        assert_eq!(f.view_distance, 10.0);

        f.transform(gf::Mat4d::scale([-2.0, -2.0, -2.0]));
        assert!(!f.window.is_empty());
        f.window = window([1.0, 1.0], [-1.0, -1.0]);
        f.transform(gf::Mat4d::IDENTITY);
        assert!(!f.window.is_empty());
    }

    /// The view matrix undoes the transform a frustum was carried through.
    #[test]
    fn view_matrices() {
        let turned = turn([1.0, 1.0, 1.0], 60.0);
        let mut f = Frustum::default();
        f.transform(turned);
        let point = gf::vec3d(1.0, 2.0, 3.0);
        let back = turned.inverse().expect("a rotation inverts");
        assert!((f.view_matrix().transform(point) - back.transform(point)).length() < 1e-4);
        assert!((f.view_inverse().transform(point) - turned.transform(point)).length() < 1e-4);
        gf::matrix::tests::assert_close(f.view_matrix() * f.view_inverse(), gf::Mat4d::IDENTITY);
    }

    /// A scaled perspective frustum has its window scaled, and its corners
    /// spread with the distance.
    #[test]
    fn perspective_corners() {
        let mut f = Frustum::default();
        f.transform(gf::Mat4d::scale([3.0, 2.0, 1.0]));
        assert_eq!(f.aspect_ratio(), 1.5);
        let expected = [
            [-3.0, -2.0, -1.0],
            [3.0, -2.0, -1.0],
            [-3.0, 2.0, -1.0],
            [3.0, 2.0, -1.0],
            [-30.0, -20.0, -10.0],
            [30.0, -20.0, -10.0],
            [-30.0, 20.0, -10.0],
            [30.0, 20.0, -10.0],
        ];
        for (corner, expected) in f.corners().into_iter().zip(expected) {
            assert_eq!(corner, gf::Vec3d::from(expected));
        }
    }

    /// An orthographic frustum's corners are the same rectangle near and
    /// far.
    #[test]
    fn orthographic_corners() {
        let mut f = orthographic();
        f.transform(gf::Mat4d::scale([3.0, 2.0, 1.0]));
        let expected = [
            [-3.0, -2.0, -1.0],
            [3.0, -2.0, -1.0],
            [-3.0, 2.0, -1.0],
            [3.0, 2.0, -1.0],
            [-3.0, -2.0, -10.0],
            [3.0, -2.0, -10.0],
            [-3.0, 2.0, -10.0],
            [3.0, 2.0, -10.0],
        ];
        for (corner, expected) in f.corners().into_iter().zip(expected) {
            assert_eq!(corner, gf::Vec3d::from(expected));
        }
    }

    /// A frustum placed by a matrix has the corners C++ computes for it,
    /// and its corners at a distance run between them.
    #[test]
    fn corners_from_matrix() {
        let m = gf::Mat4d([
            0.9987016645043332,
            -0.035803686178599,
            -0.036236464677155,
            0.0,
            0.0362364646771555,
            0.999278702502407,
            0.011357524061459,
            0.0,
            0.0358036861785999,
            -0.012655859557126,
            0.999278702502407,
            0.0,
            3.0,
            -6.0,
            5.0,
            1.0,
        ]);
        let f = Frustum::from_matrix(
            m,
            window([-0.22, -0.2], [0.2, 0.33]),
            gf::Range1d::new(20.0, 90.0),
            Projection::Perspective,
        );
        let expected = [
            [-2.255306906099, -9.58646139968125, -14.8715637017144],
            [6.133787075736, -9.88721236358150, -15.1759500050026],
            [-1.871200380521, 1.00589284684426, -14.7511739466630],
            [6.517893601314, 0.70514188294401, -15.0555602499511],
            [-20.648881077448, -22.13907629856565, -84.4220366577152],
            [17.102041840815, -23.49245563611677, -85.7917750225117],
            [-18.920401712348, 25.52651781079917, -83.8802827599836],
            [18.830521205915, 24.17313847324806, -85.2500211247801],
        ];
        let corners = f.corners();
        for (corner, expected) in corners.into_iter().zip(expected) {
            assert!(close(corner, expected, 1e-4), "{corner:?}");
        }
        assert_eq!(f.corners_at(20.0), corners[..4]);
        assert_eq!(f.corners_at(90.0), corners[4..]);
        for (i, corner) in f.corners_at(55.0).into_iter().enumerate() {
            assert!((corner - (corners[i] + corners[i + 4]) * 0.5).length() < 1e-9);
        }
    }

    /// A matrix that scales or mirrors places the frustum by its position
    /// and its turn alone.
    #[test]
    fn matrix_conformed() {
        let turned = turn([0.0, 1.0, 0.0], 40.0) * gf::Mat4d::translation([1.0, 2.0, 3.0]);
        let plain = Frustum::from_matrix(
            turned,
            Frustum::default().window,
            gf::Range1d::new(1.0, 10.0),
            Projection::Perspective,
        );
        let scaled = Frustum::from_matrix(
            gf::Mat4d::scale([2.0, 3.0, 4.0]) * turned,
            plain.window,
            plain.near_far,
            plain.projection,
        );
        assert_eq!(scaled.position, plain.position);
        assert!((scaled.view_direction() - plain.view_direction()).length() < 1e-12);
        assert!((scaled.up_vector() - plain.up_vector()).length() < 1e-12);

        let mirrored = Frustum::from_matrix(
            gf::Mat4d::scale([-1.0, 1.0, 1.0]) * turned,
            plain.window,
            plain.near_far,
            plain.projection,
        );
        assert!((mirrored.view_direction() - plain.view_direction()).length() < 1e-12);
        assert!((mirrored.up_vector() - plain.up_vector()).length() < 1e-12);
    }

    /// The projection matrix carries the corners of the volume to the
    /// corners of clip space.
    #[test]
    fn projection_reaches_clip_space() {
        for mut f in [Frustum::default(), orthographic()] {
            f.window = window([-0.5, -0.25], [1.5, 0.75]);
            f.transform(turn([1.0, 2.0, 3.0], 35.0) * gf::Mat4d::translation([4.0, 5.0, 6.0]));
            let to_clip = f.view_matrix() * f.projection_matrix();
            let corners = f.corners();
            assert!(close(to_clip.transform(corners[0]), [-1.0, -1.0, -1.0], 1e-9));
            assert!(close(to_clip.transform(corners[3]), [1.0, 1.0, -1.0], 1e-9));
            assert!(close(to_clip.transform(corners[4]), [-1.0, -1.0, 1.0], 1e-9));
            assert!(close(to_clip.transform(corners[7]), [1.0, 1.0, 1.0], 1e-9));
        }
    }

    /// A frustum fit to a sphere holds every point of it.
    #[test]
    fn fit_to_sphere() {
        let mut f = orthographic();
        f.fit_to_sphere(gf::Vec3d::default(), 1.0, 0.0);
        for axis in 0..3 {
            for sign in [-0.9, 0.9] {
                let mut point = gf::Vec3d::default();
                point[axis] = sign;
                assert!(f.intersects_point(point), "{point:?}");
            }
        }
        assert!(f.intersects_point(gf::Vec3d::default()));

        let mut f = Frustum::default();
        f.fit_to_sphere(gf::vec3d(1.0, 1.0, 1.0), 1.0, 0.2);
        assert!(f.intersects_point(gf::vec3d(1.0, 1.0, 1.0)));
        for axis in 0..3 {
            for reach in [-1.1, 1.1] {
                let mut point = gf::vec3d(1.0, 1.0, 1.0);
                point[axis] += reach;
                assert!(f.intersects_point(point), "{point:?}");
            }
        }
    }

    /// Fitting takes whichever window edge is further from the line of
    /// sight, and a window of no size as one of size one.
    #[test]
    fn fit_off_center_window() {
        let cases = [
            (window([10.0, 20.0], [30.0, 40.0]), 30.0),
            (window([-30.0, -40.0], [10.0, 20.0]), 30.0),
            (window([-30.0, -40.0], [-10.0, -20.0]), 30.0),
            (window([0.0, 0.0], [0.0, 0.0]), 1.0),
        ];
        for (window, half) in cases {
            let mut f = Frustum {
                window,
                ..Frustum::default()
            };
            f.fit_to_sphere(gf::Vec3d::default(), 1.0, 0.0);
            let expected = 1.0 / half * f64::hypot(half, 1.0);
            assert!((f.view_distance - expected).abs() < 1e-12, "{window:?}");
            assert_eq!(f.position, gf::vec3d(0.0, 0.0, f.view_distance));
        }
    }

    /// A narrowed frustum keeps a fraction of the window about a place in
    /// it, or about a point in the world.
    #[test]
    fn narrowed_window() {
        let near = |got: gf::Range2d, min: [f64; 2], max: [f64; 2]| {
            (got.min() - gf::Vec2d::from(min)).x.abs() < 1e-4
                && (got.min() - gf::Vec2d::from(min)).y.abs() < 1e-4
                && (got.max() - gf::Vec2d::from(max)).x.abs() < 1e-4
                && (got.max() - gf::Vec2d::from(max)).y.abs() < 1e-4
        };
        let size = gf::vec2d(0.1, 0.1);
        let mut f = orthographic();
        f.transform(gf::Mat4d::scale([3.0, 2.0, 1.0]));

        let narrow = f.narrowed(gf::vec2d(0.0, 0.0), size);
        assert!(near(narrow.window, [-0.3, -0.2], [0.3, 0.2]));
        let narrow = f.narrowed_to(gf::vec3d(0.0, 0.0, -1.0), size);
        assert!(near(narrow.window, [-0.3, -0.2], [0.3, 0.2]));
        let narrow = f.narrowed_to(gf::vec3d(0.1, 0.2, -5.0), size);
        assert!(near(narrow.window, [-0.2, 0.0], [0.4, 0.4]));

        f.projection = Projection::Perspective;
        let narrow = f.narrowed_to(gf::vec3d(0.0, 0.0, -1.0), size);
        assert!(near(narrow.window, [-0.3, -0.2], [0.3, 0.2]));
        let narrow = f.narrowed_to(gf::vec3d(0.1, 0.2, -5.0), size);
        assert!(near(narrow.window, [-0.28, -0.16], [0.32, 0.24]));

        // A point behind the position narrows nothing.
        assert_eq!(f.narrowed_to(gf::vec3d(0.0, 0.0, 1.0), size), f);

        // The narrowed window stays inside the one it came from.
        let wide = Frustum {
            window: window([3.0, 3.0], [4.0, 4.0]),
            ..Frustum::default()
        };
        assert_eq!(
            wide.narrowed(gf::vec2d(3.0, 3.0), gf::vec2d(100.0, 100.0)).window,
            wide.window
        );
    }

    /// A pick ray starts on the near plane, toward a place in the window or
    /// a point in the world.
    #[test]
    fn pick_rays() {
        let third = 1.0 / 3.0;
        let r = Frustum::default().pick_ray(gf::vec2d(2.0, 2.0));
        assert!(close(r.start, [2.0 * third, 2.0 * third, -third], 1e-5));
        assert!(close(r.direction, [2.0 * third, 2.0 * third, -third], 1e-5));

        let r = orthographic().pick_ray(gf::vec2d(2.0, 2.0));
        assert!(close(r.start, [2.0, 2.0, -2.0], 1e-5));
        assert!(close(r.direction, [0.0, 0.0, -1.0], 1e-5));

        let r = Frustum::default().pick_ray_to(gf::vec3d(0.0, 0.0, -2.0));
        assert!(close(r.start, [0.0, 0.0, -1.0], 1e-5));
        assert!(close(r.direction, [0.0, 0.0, -1.0], 1e-5));

        let r = Frustum::default().pick_ray_to(gf::vec3d(2.0, 2.0, -1.0));
        assert!(close(r.start, [2.0 * third, 2.0 * third, -third], 1e-5));
        assert!(close(r.direction, [2.0 * third, 2.0 * third, -third], 1e-5));

        let r = orthographic().pick_ray_to(gf::vec3d(2.0, 2.0, -2.0));
        assert!(close(r.start, [2.0, 2.0, -1.0], 1e-5));
        assert!(close(r.direction, [0.0, 0.0, -1.0], 1e-5));
    }

    /// A ray starts at the position, or on the near plane for an
    /// orthographic frustum seeing through its window.
    #[test]
    fn rays_from_position() {
        let mut f = Frustum {
            position: gf::vec3d(1.0, 2.0, 3.0),
            ..Frustum::default()
        };
        let r = f.ray(gf::vec2d(0.0, 0.0));
        assert_eq!(r.start, f.position);
        assert!(close(r.direction, [0.0, 0.0, -1.0], 1e-12));
        let r = f.ray_to(gf::vec3d(1.0, 2.0, -4.0));
        assert_eq!(r.start, f.position);
        assert!(close(r.direction, [0.0, 0.0, -1.0], 1e-12));

        f.projection = Projection::Orthographic;
        let r = f.ray(gf::vec2d(1.0, 1.0));
        assert!(close(r.start, [2.0, 3.0, 2.0], 1e-12));
        let r = f.ray_to(gf::vec3d(5.0, 6.0, -4.0));
        assert!(close(r.start, [5.0, 6.0, 3.0], 1e-12));
        assert!(close(r.direction, [0.0, 0.0, -1.0], 1e-12));
    }

    /// Boxes, points, segments and triangles against the default frustum.
    #[test]
    fn intersections() {
        let f = Frustum::default();
        let v = |x: f64, y: f64, z: f64| gf::vec3d(x, y, z);

        assert!(!f.intersects_bbox(&gf::BBox3d::default()));
        let unit = gf::Range3d::new(v(-1.0, -1.0, -1.0), v(1.0, 1.0, 1.0));
        assert!(f.intersects_bbox(&gf::BBox3d::from(unit)));
        // A box the frustum only reaches once its matrix has moved it.
        let moved = gf::BBox3d::new(unit, gf::Mat4d::translation([0.0, 0.0, 20.0]));
        assert!(!f.intersects_bbox(&moved));
        let moved = gf::BBox3d::new(unit, gf::Mat4d::translation([0.0, 0.0, -5.0]));
        assert!(f.intersects_bbox(&moved));
        // A matrix with no inverse leaves the range to be tested as it is.
        let flat = gf::Mat4d::scale([1.0, 0.0, 1.0]) * gf::Mat4d::translation([0.0, 0.0, 20.0]);
        assert!(f.intersects_bbox(&gf::BBox3d::new(unit, flat)));

        assert!(f.intersects_point(v(0.0, 0.0, -1.0)));
        assert!(!f.intersects_point(v(0.0, 0.0, 0.0)));

        let origin = v(0.0, 0.0, 0.0);
        assert!(!f.intersects_triangle(origin, v(1.0, 1.0, 1.0), v(0.0, 0.0, 1.0)));
        assert!(f.intersects_triangle(origin, v(-1.0, -1.0, -1.0), v(0.0, 0.0, 1.0)));
        assert!(!f.intersects_triangle(v(0.0, 100.0, -100.0), v(-100.0, -100.0, 100.0), v(100.0, -100.0, 100.0)));
        // A triangle that surrounds the volume, cut by the near plane.
        assert!(f.intersects_triangle(v(0.0, 10.0, 100.0), v(-100.0, -10.0, -10.0), v(100.0, -10.0, -10.0)));
        assert!(f.intersects_triangle(v(0.0, 1.0, 1.0), v(50.0, 0.0, -50.0), v(-50.0, 0.0, -50.0)));
        // One that surrounds it between the near and far planes.
        assert!(f.intersects_triangle(v(0.0, 100.0, -5.0), v(-100.0, -100.0, -5.0), v(100.0, -100.0, -5.0)));

        assert!(f.intersects_segment(origin, v(1.0, 1.0, -1.0)));
        assert!(f.intersects_segment(v(-100.0, 0.0, -1.0), v(100.0, 0.0, -1.0)));
        assert!(f.intersects_segment(v(0.0, 100.0, -1.0), v(0.0, -100.0, -1.0)));
        assert!(!f.intersects_segment(v(-100.0, 0.0, 1.0), v(100.0, 0.0, -1.0)));
        assert!(!f.intersects_segment(origin, v(1.0, 1.0, 1.0)));
    }

    /// The planes face into the volume, in the order the masks read them.
    #[test]
    fn planes_face_inward() {
        for f in [Frustum::default(), orthographic()] {
            let inside = gf::vec3d(0.0, 0.0, -5.0);
            let planes = f.planes();
            assert!(planes.iter().all(|plane| plane.distance(inside) > 0.0));
            let outside = [
                [-20.0, 0.0, -5.0],
                [20.0, 0.0, -5.0],
                [0.0, -20.0, -5.0],
                [0.0, 20.0, -5.0],
                [0.0, 0.0, -0.5],
                [0.0, 0.0, -11.0],
            ];
            for (i, point) in outside.into_iter().enumerate() {
                let behind: Vec<usize> = (0..6).filter(|&p| planes[p].distance(point.into()) < 0.0).collect();
                assert_eq!(behind, [i], "{:?}", f.projection);
            }
        }
    }

    /// A box against the volume a view-projection matrix sees.
    #[test]
    fn view_volume() {
        // A perspective camera looking down Y at the origin.
        let view = gf::Mat4d([
            1.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, -20.0, 1.0,
        ]);
        let projection = gf::Mat4d([
            4.241894005673533,
            0.0,
            0.0,
            0.0,
            0.0,
            4.241_894_058_697_207,
            0.0,
            0.0,
            0.0,
            0.0,
            -1.0,
            -1.0,
            0.0,
            0.0,
            -20.0,
            0.0,
        ]);
        let view_projection = view * projection;
        let boxed = |min: [f64; 3], max: [f64; 3]| gf::BBox3d::from(gf::Range3d::new(min.into(), max.into()));

        assert!(Frustum::intersects_view_volume(
            &boxed([0.0; 3], [1.0; 3]),
            view_projection
        ));
        assert!(!Frustum::intersects_view_volume(
            &boxed([100.0, 0.0, 0.0], [101.0, 1.0, 1.0]),
            view_projection
        ));
        assert!(Frustum::intersects_view_volume(
            &boxed([-1e9; 3], [1e9; 3]),
            view_projection
        ));
    }
}
