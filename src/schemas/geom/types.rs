//! Decoded structs and enums returned by [`super::read`] functions.

use super::tokens::*;

/// `UsdGeomImageable.visibility` token values. The spec default
/// (unauthored) is [`Visibility::Inherited`] — children inherit
/// their parent's effective visibility.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Visibility {
    #[default]
    Inherited,
    Invisible,
}

impl Visibility {
    pub fn as_token(self) -> &'static str {
        match self {
            Visibility::Inherited => VISIBILITY_INHERITED,
            Visibility::Invisible => VISIBILITY_INVISIBLE,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            VISIBILITY_INHERITED => Visibility::Inherited,
            VISIBILITY_INVISIBLE => Visibility::Invisible,
            _ => return None,
        })
    }
}

/// `UsdGeomImageable.purpose` token values. The spec default
/// (unauthored) is [`Purpose::Default`] — included in every traversal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Purpose {
    #[default]
    Default,
    Render,
    Proxy,
    Guide,
}

impl Purpose {
    pub fn as_token(self) -> &'static str {
        match self {
            Purpose::Default => PURPOSE_DEFAULT,
            Purpose::Render => PURPOSE_RENDER,
            Purpose::Proxy => PURPOSE_PROXY,
            Purpose::Guide => PURPOSE_GUIDE,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            PURPOSE_DEFAULT => Purpose::Default,
            PURPOSE_RENDER => Purpose::Render,
            PURPOSE_PROXY => Purpose::Proxy,
            PURPOSE_GUIDE => Purpose::Guide,
            _ => return None,
        })
    }
}

/// Authored winding rule on a `UsdGeomGprim`. Renderers use this to
/// decide which face is "front" — `LeftHanded` flips the convention.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Orientation {
    #[default]
    RightHanded,
    LeftHanded,
}

impl Orientation {
    pub fn as_token(self) -> &'static str {
        match self {
            Orientation::RightHanded => ORIENTATION_RIGHT_HANDED,
            Orientation::LeftHanded => ORIENTATION_LEFT_HANDED,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            ORIENTATION_RIGHT_HANDED => Orientation::RightHanded,
            ORIENTATION_LEFT_HANDED => Orientation::LeftHanded,
            _ => return None,
        })
    }
}

/// `axis` token authored on radial shapes (Cylinder / Capsule / Cone)
/// and on Plane. Per Pixar's spec the default is `Z`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Axis {
    X,
    Y,
    #[default]
    Z,
}

impl Axis {
    pub fn as_token(self) -> &'static str {
        match self {
            Axis::X => AXIS_X,
            Axis::Y => AXIS_Y,
            Axis::Z => AXIS_Z,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            AXIS_X => Axis::X,
            AXIS_Y => Axis::Y,
            AXIS_Z => Axis::Z,
            _ => return None,
        })
    }
}

/// Decoded `UsdGeomCube`. The cube spans `[-size/2, size/2]` on every
/// axis; defaults to `size = 2` per Pixar.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ReadCube {
    pub size: f64,
}

impl Default for ReadCube {
    fn default() -> Self {
        Self { size: 2.0 }
    }
}

/// Decoded `UsdGeomSphere`. Centred at the origin; `radius` defaults
/// to `1.0`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ReadSphere {
    pub radius: f64,
}

impl Default for ReadSphere {
    fn default() -> Self {
        Self { radius: 1.0 }
    }
}

/// Decoded `UsdGeomCylinder`. `height` is along `axis`; the two
/// end-caps are positioned at `±height/2` along that axis.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ReadCylinder {
    pub radius: f64,
    pub height: f64,
    pub axis: Axis,
}

impl Default for ReadCylinder {
    fn default() -> Self {
        Self {
            radius: 1.0,
            height: 2.0,
            axis: Axis::default(),
        }
    }
}

/// Decoded `UsdGeomCapsule`. Like a cylinder but with hemispherical
/// end-caps of the same radius.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ReadCapsule {
    pub radius: f64,
    pub height: f64,
    pub axis: Axis,
}

impl Default for ReadCapsule {
    fn default() -> Self {
        Self {
            radius: 0.5,
            height: 1.0,
            axis: Axis::default(),
        }
    }
}

/// Decoded `UsdGeomCone`. `height` is the spine length along `axis`;
/// the cone's apex points along `+axis`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ReadCone {
    pub radius: f64,
    pub height: f64,
    pub axis: Axis,
}

impl Default for ReadCone {
    fn default() -> Self {
        Self {
            radius: 1.0,
            height: 2.0,
            axis: Axis::default(),
        }
    }
}

/// Decoded `UsdGeomPlane`. `axis` selects which axis the plane's
/// surface normal aligns to. `width` / `length` measure the plane's
/// extent in the two axes orthogonal to `axis`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ReadPlane {
    pub width: f64,
    pub length: f64,
    pub axis: Axis,
}

impl Default for ReadPlane {
    fn default() -> Self {
        Self {
            width: 2.0,
            length: 2.0,
            axis: Axis::default(),
        }
    }
}

/// `UsdGeomCamera.projection` token values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Projection {
    #[default]
    Perspective,
    Orthographic,
}

impl Projection {
    pub fn as_token(self) -> &'static str {
        match self {
            Projection::Perspective => PROJECTION_PERSPECTIVE,
            Projection::Orthographic => PROJECTION_ORTHOGRAPHIC,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            PROJECTION_PERSPECTIVE => Projection::Perspective,
            PROJECTION_ORTHOGRAPHIC => Projection::Orthographic,
            _ => return None,
        })
    }
}

/// `UsdGeomCamera.stereoRole` token values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum StereoRole {
    #[default]
    Mono,
    Left,
    Right,
}

impl StereoRole {
    pub fn as_token(self) -> &'static str {
        match self {
            StereoRole::Mono => STEREO_ROLE_MONO,
            StereoRole::Left => STEREO_ROLE_LEFT,
            StereoRole::Right => STEREO_ROLE_RIGHT,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            STEREO_ROLE_MONO => StereoRole::Mono,
            STEREO_ROLE_LEFT => StereoRole::Left,
            STEREO_ROLE_RIGHT => StereoRole::Right,
            _ => return None,
        })
    }
}

/// Decoded `UsdGeomCamera`.
///
/// Pixar's convention: focal length and aperture values are in
/// *tenths of a scene unit* (typically millimetres for a metres-per-unit
/// stage). Clipping ranges are in scene units. Convenience helpers
/// [`ReadCamera::vertical_fov_rad`] / `horizontal_fov_rad` derive the
/// field of view from focal length and aperture.
///
/// Defaults match Pixar exactly so unauthored fields project as a
/// 50 mm lens with 35 mm-equivalent aperture, perspective projection,
/// and an open shutter at frame time 0.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadCamera {
    pub focal_length: f32,
    pub horizontal_aperture: f32,
    pub vertical_aperture: f32,
    pub horizontal_aperture_offset: f32,
    pub vertical_aperture_offset: f32,
    pub f_stop: f32,
    pub focus_distance: f32,
    pub projection: Projection,
    /// `(near, far)` in scene units.
    pub clipping_range: [f32; 2],
    /// Each entry is a `float4` plane equation `(n.x, n.y, n.z, d)`
    /// in camera-local space.
    pub clipping_planes: Vec<[f32; 4]>,
    pub shutter_open: f32,
    pub shutter_close: f32,
    pub exposure: f32,
    pub exposure_iso: f32,
    pub exposure_time: f32,
    pub exposure_f_stop: f32,
    pub exposure_responsivity: f32,
    pub stereo_role: StereoRole,
}

impl Default for ReadCamera {
    fn default() -> Self {
        Self {
            focal_length: 50.0,
            horizontal_aperture: 20.955,
            vertical_aperture: 15.2908,
            horizontal_aperture_offset: 0.0,
            vertical_aperture_offset: 0.0,
            f_stop: 1.0,
            focus_distance: 0.0,
            projection: Projection::Perspective,
            clipping_range: [1.0, 1_000_000.0],
            clipping_planes: Vec::new(),
            shutter_open: 0.0,
            shutter_close: 0.0,
            exposure: 0.0,
            exposure_iso: 100.0,
            exposure_time: 1.0,
            exposure_f_stop: 1.0,
            exposure_responsivity: 1.0,
            stereo_role: StereoRole::Mono,
        }
    }
}

impl ReadCamera {
    /// Vertical field of view in radians, computed from
    /// `vertical_aperture` and `focal_length`:
    ///
    /// `fov_v = 2 · atan(v_aperture / (2 · focal_length))`
    pub fn vertical_fov_rad(&self) -> f32 {
        2.0 * (self.vertical_aperture / (2.0 * self.focal_length.max(f32::EPSILON))).atan()
    }

    /// Horizontal field of view in radians:
    ///
    /// `fov_h = 2 · atan(h_aperture / (2 · focal_length))`
    pub fn horizontal_fov_rad(&self) -> f32 {
        2.0 * (self.horizontal_aperture / (2.0 * self.focal_length.max(f32::EPSILON))).atan()
    }

    /// Aspect ratio (`h_aperture / v_aperture`).
    pub fn aspect_ratio(&self) -> f32 {
        self.horizontal_aperture / self.vertical_aperture.max(f32::EPSILON)
    }
}

/// `UsdGeomMesh.subdivisionScheme` token values. The Pixar default
/// is [`SubdivisionScheme::CatmullClark`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SubdivisionScheme {
    None,
    #[default]
    CatmullClark,
    Loop,
    Bilinear,
}

impl SubdivisionScheme {
    pub fn as_token(self) -> &'static str {
        match self {
            SubdivisionScheme::None => SUBDIV_SCHEME_NONE,
            SubdivisionScheme::CatmullClark => SUBDIV_SCHEME_CATMULL_CLARK,
            SubdivisionScheme::Loop => SUBDIV_SCHEME_LOOP,
            SubdivisionScheme::Bilinear => SUBDIV_SCHEME_BILINEAR,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            SUBDIV_SCHEME_NONE => SubdivisionScheme::None,
            SUBDIV_SCHEME_CATMULL_CLARK => SubdivisionScheme::CatmullClark,
            SUBDIV_SCHEME_LOOP => SubdivisionScheme::Loop,
            SUBDIV_SCHEME_BILINEAR => SubdivisionScheme::Bilinear,
            _ => return None,
        })
    }

    /// `true` when the scheme actually requests subdivision (i.e. not
    /// [`SubdivisionScheme::None`]).
    pub fn is_subdivision(self) -> bool {
        !matches!(self, SubdivisionScheme::None)
    }
}

/// Primvar interpolation modes from UsdGeomPrimvar.
///
/// `Constant` is one value for the whole prim. `Uniform` is per-face.
/// `Varying` / `Vertex` are both per-point (with subtle subdivision
/// differences). `FaceVarying` is per face-vertex (the canonical
/// case for texture coordinates with seams).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Interpolation {
    Constant,
    Uniform,
    Varying,
    #[default]
    Vertex,
    FaceVarying,
}

impl Interpolation {
    pub fn as_token(self) -> &'static str {
        match self {
            Interpolation::Constant => INTERP_CONSTANT,
            Interpolation::Uniform => INTERP_UNIFORM,
            Interpolation::Varying => INTERP_VARYING,
            Interpolation::Vertex => INTERP_VERTEX,
            Interpolation::FaceVarying => INTERP_FACE_VARYING,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            INTERP_CONSTANT => Interpolation::Constant,
            INTERP_UNIFORM => Interpolation::Uniform,
            INTERP_VARYING => Interpolation::Varying,
            INTERP_VERTEX => Interpolation::Vertex,
            INTERP_FACE_VARYING => Interpolation::FaceVarying,
            _ => return None,
        })
    }
}

/// `UsdGeomSubset.elementType` — what kind of mesh component the
/// subset enumerates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ElementType {
    #[default]
    Face,
    Point,
    Edge,
    Tetrahedron,
}

impl ElementType {
    pub fn as_token(self) -> &'static str {
        match self {
            ElementType::Face => ELEMENT_TYPE_FACE,
            ElementType::Point => ELEMENT_TYPE_POINT,
            ElementType::Edge => ELEMENT_TYPE_EDGE,
            ElementType::Tetrahedron => ELEMENT_TYPE_TETRAHEDRON,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            ELEMENT_TYPE_FACE => ElementType::Face,
            ELEMENT_TYPE_POINT => ElementType::Point,
            ELEMENT_TYPE_EDGE => ElementType::Edge,
            ELEMENT_TYPE_TETRAHEDRON => ElementType::Tetrahedron,
            _ => return None,
        })
    }
}

/// Decoded `UsdGeomSubset`. A face-element subset (the most common
/// kind) enumerates a set of face indices into a parent mesh; the
/// `family_name` groups subsets that collectively partition the
/// mesh (e.g. `"materialBind"`).
#[derive(Debug, Clone, Default)]
pub struct ReadSubset {
    pub path: String,
    pub family_name: Option<String>,
    pub element_type: ElementType,
    pub indices: Vec<i32>,
}

/// One authored primvar — the values plus the metadata that controls
/// how to interpret them (interpolation mode, optional indices for
/// indexed primvars, per-element stride).
#[derive(Debug, Clone, Default)]
pub struct Primvar<T> {
    pub values: Vec<T>,
    pub interpolation: Interpolation,
    /// Optional `<name>:indices` companion — when non-empty,
    /// `effective[i] = values[indices[i]]`.
    pub indices: Vec<i32>,
    /// `elementSize` metadata — how many `T`s per logical element.
    /// Defaults to `1`.
    pub element_size: i32,
}

/// Decoded `UsdGeomMesh`.
///
/// Required attributes: `points`, `faceVertexCounts`,
/// `faceVertexIndices`. Everything else is optional and surfaced
/// only when authored.
///
/// `subsets` lists every `GeomSubset` child whose `familyName ==
/// "materialBind"` (the canonical material-partition family). Other
/// families are accessible via [`super::find_geom_prims`] + the
/// generic [`super::read_subset`] reader.
#[derive(Debug, Clone, Default)]
pub struct ReadMesh {
    pub path: String,
    pub points: Vec<[f32; 3]>,
    pub face_vertex_counts: Vec<i32>,
    pub face_vertex_indices: Vec<i32>,
    pub normals: Option<Primvar<[f32; 3]>>,
    /// `primvars:st` (texture coords). Read as Vec2f; `st0` is also
    /// honoured as a fallback name.
    pub uvs: Option<Primvar<[f32; 2]>>,
    /// `velocities` from PointBased — per-point linear velocity in
    /// scene units per `timeCodesPerSecond`. Used for motion blur.
    pub velocities: Vec<[f32; 3]>,
    /// `accelerations` — per-point second derivative for higher-order
    /// motion integration.
    pub accelerations: Vec<[f32; 3]>,
    pub orientation: Orientation,
    pub double_sided: bool,
    pub extent: Option<[[f32; 3]; 2]>,
    pub subdivision_scheme: SubdivisionScheme,
    pub interpolate_boundary: Option<String>,
    pub face_varying_linear_interpolation: Option<String>,
    pub triangle_subdivision_rule: Option<String>,
    pub hole_indices: Vec<i32>,
    pub corner_indices: Vec<i32>,
    pub corner_sharpnesses: Vec<f32>,
    pub crease_indices: Vec<i32>,
    pub crease_lengths: Vec<i32>,
    pub crease_sharpnesses: Vec<f32>,
    pub display_color: Option<Primvar<[f32; 3]>>,
    pub display_opacity: Option<Primvar<f32>>,
    /// Material-bind GeomSubsets. Empty when the mesh isn't
    /// subdivided into per-material groups.
    pub subsets: Vec<ReadSubset>,
}

/// Result of [`super::read::find_geom_prims`] — a single-pass stage
/// walk that returns categorised path lists. Saves callers from
/// re-walking the stage for each schema family.
///
/// `imageables` collects every prim whose `typeName` is recognised
/// as a UsdGeom type (concrete shapes + camera + point instancer +
/// Xform + Scope). Schema-specific buckets (`meshes`, `cameras`, …)
/// fill in alongside.
#[derive(Debug, Clone, Default)]
pub struct GeomPrims {
    pub xforms: Vec<String>,
    pub scopes: Vec<String>,
    pub meshes: Vec<String>,
    pub cubes: Vec<String>,
    pub spheres: Vec<String>,
    pub cylinders: Vec<String>,
    pub capsules: Vec<String>,
    pub cones: Vec<String>,
    pub planes: Vec<String>,
    pub basis_curves: Vec<String>,
    pub nurbs_curves: Vec<String>,
    pub nurbs_patches: Vec<String>,
    pub hermite_curves: Vec<String>,
    pub points: Vec<String>,
    pub tet_meshes: Vec<String>,
    pub geom_subsets: Vec<String>,
    pub cameras: Vec<String>,
    pub point_instancers: Vec<String>,
    /// Every prim that participates in geometry processing (union of
    /// all the above plus any other Imageable subclass that authors a
    /// `visibility` / `purpose` opinion).
    pub imageables: Vec<String>,
}
