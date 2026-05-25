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
