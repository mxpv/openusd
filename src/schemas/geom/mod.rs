//! UsdGeom schema views.
//!
//! Typed value-views over a composed [`crate::Stage`], mirroring Pixar's
//! `UsdGeom` class hierarchy. Each concrete prim type (`Mesh`, `Sphere`,
//! `Camera`, …) is a newtype wrapping a [`crate::usd::Prim`] and gains its
//! property accessors from a chain of schema traits:
//!
//! ```text
//! SchemaBase
//!  └ Imageable                 (visibility / purpose / proxyPrim)
//!     ├ Scope                   (pure grouping; not transformable)
//!     └ Xformable               (xformOpOrder transform stack)
//!        ├ Xform                (transformable grouping)
//!        ├ Camera               (lens / aperture / shutter)
//!        └ Boundable            (extent)
//!           ├ PointInstancer    (vectorized instancing)
//!           └ Gprim             (doubleSided / orientation / display*)
//!              ├ Cube / Sphere / Cone / Cylinder / Capsule / Plane
//!              └ PointBased     (points / normals / velocities)
//!                 ├ Mesh
//!                 ├ Points
//!                 ├ NurbsPatch / TetMesh
//!                 └ Curves      (curveVertexCounts / widths)
//!                    └ BasisCurves / NurbsCurves / HermiteCurves
//! ```
//!
//! # Conventions
//!
//! Property accessors mirror the C++ `Get*Attr` / `Create*Attr` pair: a
//! `foo_attr()` returns an [`crate::usd::Attribute`] handle whose `get()`
//! yields the authored value (or `None` — there is no schema registry yet to
//! supply fallbacks), and `create_foo_attr()` authors the attribute with its
//! schema-declared type / variability and returns the handle. `GeomSubset`
//! is the lone typed-but-not-imageable schema.
//!
//! Token-valued attributes (`visibility`, `purpose`, `projection`, `axis`,
//! `subdivisionScheme`, …) decode through the token enums defined at the end
//! of this module, which carry `from_token` / `as_token`. `visibility` and
//! `purpose` are inherited down namespace;
//! [`Imageable::compute_visibility`] / [`Imageable::compute_purpose`] resolve
//! the effective value walking ancestors.
//!
//! # Primvars
//!
//! Primvar attributes (`primvars:*`, plus the primvar-like `normals` /
//! `widths`) are reached today through the raw [`crate::usd::Attribute`]
//! handles — their `interpolation` / `elementSize` / `<name>:indices`
//! companion metadata is read via [`crate::usd::Attribute::get_metadata`]. The
//! convenience accessors (`Gprim::display_color_attr`, …) return the bare
//! attribute. TODO: model `UsdGeomPrimvar` / `UsdGeomPrimvarsAPI` so primvars
//! get a typed view that bundles values with interpolation and resolves
//! indexed primvars, rather than callers reading the metadata by hand.

pub mod tokens;

mod boundable;
mod camera;
mod curves;
mod gprim;
mod grouping;
mod imageable;
mod instancer;
mod internal;
mod mesh;
mod pointbased;
mod points;
mod shapes;
mod xformable;

use tokens::*;

pub use boundable::Boundable;
pub use camera::Camera;
pub use curves::{BasisCurves, Curves, HermiteCurves, NurbsCurves, NurbsPatch};
pub use gprim::Gprim;
pub use grouping::{Scope, Xform};
pub use imageable::Imageable;
pub use instancer::PointInstancer;
pub use mesh::{GeomSubset, Mesh};
pub use pointbased::PointBased;
pub use points::{Points, TetMesh};
pub use shapes::{Capsule, Cone, Cube, Cylinder, Plane, Sphere};
pub use xformable::Xformable;

/// Implement the schema-trait chain for a concrete `struct $ty(Prim)` newtype,
/// up to the membership named by the first token. Every concrete UsdGeom view
/// declares its chain through this macro; the single hand-written `SchemaBase`
/// method is `prim`, and the intermediate traits are empty memberships. Each
/// arm extends the next-weaker one, so the chain order lives in one place; the
/// traits it pulls in — plus `SchemaBase`, `SchemaKind`, and `Prim` — must be
/// in scope at the call site.
///
/// - `typed` stops at [`SchemaBase`] (a typed prim that is not `Imageable`,
///   e.g. `GeomSubset`).
/// - `imageable` adds [`Imageable`] (e.g. `Scope`).
/// - `xformable` adds [`Xformable`] (e.g. `Xform`, `Camera`).
/// - `boundable` adds [`Boundable`] (a `Boundable` that is not a `Gprim`,
///   e.g. `PointInstancer`).
/// - `gprim` adds [`Gprim`] (the intrinsic shapes).
/// - `pointbased` adds [`PointBased`] (`Mesh`, `Points`, `NurbsPatch`, …).
/// - `curves` adds [`Curves`] (`BasisCurves`, `NurbsCurves`, `HermiteCurves`).
macro_rules! impl_geom_schema {
    (typed $ty:ident) => {
        impl SchemaBase for $ty {
            const KIND: SchemaKind = SchemaKind::ConcreteTyped;

            fn prim(&self) -> &Prim {
                &self.0
            }
        }
    };
    (imageable $ty:ident) => {
        impl_geom_schema!(typed $ty);
        impl Imageable for $ty {}
    };
    (xformable $ty:ident) => {
        impl_geom_schema!(imageable $ty);
        impl Xformable for $ty {}
    };
    (boundable $ty:ident) => {
        impl_geom_schema!(xformable $ty);
        impl Boundable for $ty {}
    };
    (gprim $ty:ident) => {
        impl_geom_schema!(boundable $ty);
        impl Gprim for $ty {}
    };
    (pointbased $ty:ident) => {
        impl_geom_schema!(gprim $ty);
        impl PointBased for $ty {}
    };
    (curves $ty:ident) => {
        impl_geom_schema!(pointbased $ty);
        impl Curves for $ty {}
    };
}

pub(crate) use impl_geom_schema;

// ── Token-valued attribute enums ────────────────────────────────────────
//
// Each enum decodes one `allowedTokens` attribute via `from_token` /
// `as_token`, with the Pixar default as its `Default`. The view types expose
// the raw `Attribute` handles; pass the handle's token through these to
// classify it.

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

/// `UsdGeomMesh.interpolateBoundary` token values. Pixar's spec
/// default is [`InterpolateBoundary::EdgeAndCorner`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InterpolateBoundary {
    None,
    EdgeOnly,
    #[default]
    EdgeAndCorner,
}

impl InterpolateBoundary {
    pub fn as_token(self) -> &'static str {
        match self {
            InterpolateBoundary::None => INTERPOLATE_BOUNDARY_NONE,
            InterpolateBoundary::EdgeOnly => INTERPOLATE_BOUNDARY_EDGE_ONLY,
            InterpolateBoundary::EdgeAndCorner => INTERPOLATE_BOUNDARY_EDGE_AND_CORNER,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            INTERPOLATE_BOUNDARY_NONE => InterpolateBoundary::None,
            INTERPOLATE_BOUNDARY_EDGE_ONLY => InterpolateBoundary::EdgeOnly,
            INTERPOLATE_BOUNDARY_EDGE_AND_CORNER => InterpolateBoundary::EdgeAndCorner,
            _ => return None,
        })
    }
}

/// `UsdGeomMesh.faceVaryingLinearInterpolation` token values. Pixar's
/// spec default is [`FaceVaryingLinearInterpolation::CornersPlus1`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum FaceVaryingLinearInterpolation {
    None,
    CornersOnly,
    #[default]
    CornersPlus1,
    CornersPlus2,
    Boundaries,
    All,
}

impl FaceVaryingLinearInterpolation {
    pub fn as_token(self) -> &'static str {
        match self {
            FaceVaryingLinearInterpolation::None => FV_LINEAR_INTERP_NONE,
            FaceVaryingLinearInterpolation::CornersOnly => FV_LINEAR_INTERP_CORNERS_ONLY,
            FaceVaryingLinearInterpolation::CornersPlus1 => FV_LINEAR_INTERP_CORNERS_PLUS_1,
            FaceVaryingLinearInterpolation::CornersPlus2 => FV_LINEAR_INTERP_CORNERS_PLUS_2,
            FaceVaryingLinearInterpolation::Boundaries => FV_LINEAR_INTERP_BOUNDARIES,
            FaceVaryingLinearInterpolation::All => FV_LINEAR_INTERP_ALL,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            FV_LINEAR_INTERP_NONE => FaceVaryingLinearInterpolation::None,
            FV_LINEAR_INTERP_CORNERS_ONLY => FaceVaryingLinearInterpolation::CornersOnly,
            FV_LINEAR_INTERP_CORNERS_PLUS_1 => FaceVaryingLinearInterpolation::CornersPlus1,
            FV_LINEAR_INTERP_CORNERS_PLUS_2 => FaceVaryingLinearInterpolation::CornersPlus2,
            FV_LINEAR_INTERP_BOUNDARIES => FaceVaryingLinearInterpolation::Boundaries,
            FV_LINEAR_INTERP_ALL => FaceVaryingLinearInterpolation::All,
            _ => return None,
        })
    }
}

/// `UsdGeomMesh.triangleSubdivisionRule` token values. Pixar's spec
/// default is [`TriangleSubdivisionRule::CatmullClark`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TriangleSubdivisionRule {
    #[default]
    CatmullClark,
    Smooth,
}

impl TriangleSubdivisionRule {
    pub fn as_token(self) -> &'static str {
        match self {
            TriangleSubdivisionRule::CatmullClark => TRIANGLE_SUBDIV_RULE_CATMULL_CLARK,
            TriangleSubdivisionRule::Smooth => TRIANGLE_SUBDIV_RULE_SMOOTH,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            TRIANGLE_SUBDIV_RULE_CATMULL_CLARK => TriangleSubdivisionRule::CatmullClark,
            TRIANGLE_SUBDIV_RULE_SMOOTH => TriangleSubdivisionRule::Smooth,
            _ => return None,
        })
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
    // Pixar's UsdGeomPrimvar default for unauthored `interpolation`
    // metadata is `constant`.
    #[default]
    Constant,
    Uniform,
    Varying,
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

/// `UsdGeomBasisCurves.type` token values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CurveType {
    #[default]
    Cubic,
    Linear,
}

impl CurveType {
    pub fn as_token(self) -> &'static str {
        match self {
            CurveType::Cubic => CURVE_TYPE_CUBIC,
            CurveType::Linear => CURVE_TYPE_LINEAR,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            CURVE_TYPE_CUBIC => CurveType::Cubic,
            CURVE_TYPE_LINEAR => CurveType::Linear,
            _ => return None,
        })
    }
}

/// `UsdGeomBasisCurves.basis` — the basis matrix for cubic curves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CurveBasis {
    #[default]
    Bezier,
    Bspline,
    CatmullRom,
    Hermite,
}

impl CurveBasis {
    pub fn as_token(self) -> &'static str {
        match self {
            CurveBasis::Bezier => CURVE_BASIS_BEZIER,
            CurveBasis::Bspline => CURVE_BASIS_BSPLINE,
            CurveBasis::CatmullRom => CURVE_BASIS_CATMULL_ROM,
            CurveBasis::Hermite => CURVE_BASIS_HERMITE,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            CURVE_BASIS_BEZIER => CurveBasis::Bezier,
            CURVE_BASIS_BSPLINE => CurveBasis::Bspline,
            CURVE_BASIS_CATMULL_ROM => CurveBasis::CatmullRom,
            CURVE_BASIS_HERMITE => CurveBasis::Hermite,
            _ => return None,
        })
    }
}

/// `UsdGeomBasisCurves.wrap` — whether curves form closed loops.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CurveWrap {
    #[default]
    Nonperiodic,
    Periodic,
    Pinned,
}

impl CurveWrap {
    pub fn as_token(self) -> &'static str {
        match self {
            CurveWrap::Nonperiodic => CURVE_WRAP_NONPERIODIC,
            CurveWrap::Periodic => CURVE_WRAP_PERIODIC,
            CurveWrap::Pinned => CURVE_WRAP_PINNED,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            CURVE_WRAP_NONPERIODIC => CurveWrap::Nonperiodic,
            CURVE_WRAP_PERIODIC => CurveWrap::Periodic,
            CURVE_WRAP_PINNED => CurveWrap::Pinned,
            _ => return None,
        })
    }
}

/// `UsdGeomNurbsPatch.uForm` / `vForm` token values. Each axis
/// independently describes whether the surface is open (default),
/// closed (control points wrap, knot vector does not), or periodic
/// (both control points and knots wrap).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PatchForm {
    #[default]
    Open,
    Closed,
    Periodic,
}

impl PatchForm {
    pub fn as_token(self) -> &'static str {
        match self {
            PatchForm::Open => PATCH_FORM_OPEN,
            PatchForm::Closed => PATCH_FORM_CLOSED,
            PatchForm::Periodic => PATCH_FORM_PERIODIC,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            PATCH_FORM_OPEN => PatchForm::Open,
            PATCH_FORM_CLOSED => PatchForm::Closed,
            PATCH_FORM_PERIODIC => PatchForm::Periodic,
            _ => return None,
        })
    }
}
