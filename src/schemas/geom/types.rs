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
