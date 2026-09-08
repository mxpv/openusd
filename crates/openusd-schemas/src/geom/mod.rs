//! UsdGeom schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdGeom` class hierarchy. Each concrete prim type (`Mesh`, `Sphere`,
//! `Camera`, …) is a newtype wrapping a [`openusd::usd::Prim`] and gains its
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
//! # Example
//!
//! ```
//! // A view's own accessors live on its `<Class>Schema` trait, and the ones it
//! // inherits on the trait of the class that declared them.
//! use openusd_schemas::geom::{self, Imageable, MeshSchema};
//! use openusd::usd;
//!
//! // The registry is what makes a prim a `Mesh` and what resolves the
//! // fallbacks its schema declares.
//! let stage = usd::Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("scene.usda")
//!     .unwrap();
//!
//! // Token enums convert straight to a value via `From`, so they pass to
//! // `set` directly.
//! let mesh = geom::Mesh::define(&stage, "/World/Mesh").unwrap();
//! mesh.create_subdivision_scheme_attr().unwrap().set(geom::SubdivisionScheme::Loop).unwrap();
//! mesh.create_visibility_attr().unwrap().set(geom::Visibility::Invisible).unwrap();
//!
//! // Read it back through a fresh view; the token decodes straight to its enum.
//! let mesh = geom::Mesh::get(&stage, "/World/Mesh").unwrap().expect("Mesh");
//! let scheme = mesh.subdivision_scheme_attr().get::<geom::SubdivisionScheme>().unwrap();
//! assert_eq!(scheme, Some(geom::SubdivisionScheme::Loop));
//! ```
//!
//! # Conventions
//!
//! Property accessors mirror the C++ `Get*Attr` / `Create*Attr` pair: a
//! `foo_attr()` returns an [`openusd::usd::Attribute`] handle whose `get()`
//! yields the authored value, or the fallback the schema declares when
//! nothing is authored (see [`openusd::usd::SchemaRegistry`]), and `create_foo_attr()` authors
//! the attribute with its schema-declared type / variability and returns the
//! handle. `Subset` is the lone typed-but-not-imageable schema.
//!
//! Token-valued attributes (`visibility`, `purpose`, `projection`, `axis`,
//! `subdivisionScheme`, …) decode through the token enums defined at the end
//! of this module, which carry `from_token` / `as_token`. `visibility` and
//! `purpose` are inherited down namespace;
//! [`ImageableExt::compute_visibility`] / [`ImageableExt::compute_purpose`] resolve
//! the effective value walking ancestors.
//!
//! # Primvars
//!
//! Primvar attributes (`primvars:*`, plus the primvar-like `normals` /
//! `widths`) are reached today through the raw [`openusd::usd::Attribute`]
//! handles — their `interpolation` / `elementSize` / `<name>:indices`
//! companion metadata is read via [`openusd::usd::Attribute::get_metadata`]. The
//! convenience accessors (`Gprim::display_color_attr`, …) return the bare
//! attribute. TODO: model `UsdGeomPrimvar` / `UsdGeomPrimvarsAPI` so primvars
//! get a typed view that bundles values with interpolation and resolves
//! indexed primvars, rather than callers reading the metadata by hand.

openusd::include_schema!("usdGeom");

mod imageable;
mod xformable;

// The token enums below name the generated constants directly.
use openusd::tf;
use tokens::*;

pub use imageable::ImageableExt;
pub use xformable::{XformOpPrecision, XformableExt};

// Each enum decodes one `allowedTokens` attribute via `from_token` /
// `as_token`, with the Pixar default as its `Default`. The view types expose
// the raw `Attribute` handles; pass the handle's token through these to
// classify it.

/// The namespace a primvar is authored under: a primvar named `st` is the
/// attribute `primvars:st`.
pub const PRIMVARS_NAMESPACE: &str = "primvars:";

/// The prim metadata naming a model's role in the hierarchy (`component`,
/// `assembly`, `group`). It is metadata rather than a property, so no schema
/// declares it.
pub const META_KIND: &str = "kind";

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
            Visibility::Inherited => INHERITED,
            Visibility::Invisible => INVISIBLE,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            INHERITED => Visibility::Inherited,
            INVISIBLE => Visibility::Invisible,
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
            Purpose::Default => DEFAULT_,
            Purpose::Render => RENDER,
            Purpose::Proxy => PROXY,
            Purpose::Guide => GUIDE,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            DEFAULT_ => Purpose::Default,
            RENDER => Purpose::Render,
            PROXY => Purpose::Proxy,
            GUIDE => Purpose::Guide,
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
            Orientation::RightHanded => RIGHT_HANDED,
            Orientation::LeftHanded => LEFT_HANDED,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            RIGHT_HANDED => Orientation::RightHanded,
            LEFT_HANDED => Orientation::LeftHanded,
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
            Axis::X => X,
            Axis::Y => Y,
            Axis::Z => Z,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            X => Axis::X,
            Y => Axis::Y,
            Z => Axis::Z,
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
            Projection::Perspective => PERSPECTIVE,
            Projection::Orthographic => ORTHOGRAPHIC,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            PERSPECTIVE => Projection::Perspective,
            ORTHOGRAPHIC => Projection::Orthographic,
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
            StereoRole::Mono => MONO,
            StereoRole::Left => LEFT,
            StereoRole::Right => RIGHT,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            MONO => StereoRole::Mono,
            LEFT => StereoRole::Left,
            RIGHT => StereoRole::Right,
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
            SubdivisionScheme::None => NONE,
            SubdivisionScheme::CatmullClark => CATMULL_CLARK,
            SubdivisionScheme::Loop => LOOP,
            SubdivisionScheme::Bilinear => BILINEAR,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            NONE => SubdivisionScheme::None,
            CATMULL_CLARK => SubdivisionScheme::CatmullClark,
            LOOP => SubdivisionScheme::Loop,
            BILINEAR => SubdivisionScheme::Bilinear,
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
            InterpolateBoundary::None => NONE,
            InterpolateBoundary::EdgeOnly => EDGE_ONLY,
            InterpolateBoundary::EdgeAndCorner => EDGE_AND_CORNER,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            NONE => InterpolateBoundary::None,
            EDGE_ONLY => InterpolateBoundary::EdgeOnly,
            EDGE_AND_CORNER => InterpolateBoundary::EdgeAndCorner,
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
            FaceVaryingLinearInterpolation::None => NONE,
            FaceVaryingLinearInterpolation::CornersOnly => CORNERS_ONLY,
            FaceVaryingLinearInterpolation::CornersPlus1 => CORNERS_PLUS1,
            FaceVaryingLinearInterpolation::CornersPlus2 => CORNERS_PLUS2,
            FaceVaryingLinearInterpolation::Boundaries => BOUNDARIES,
            FaceVaryingLinearInterpolation::All => ALL,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            NONE => FaceVaryingLinearInterpolation::None,
            CORNERS_ONLY => FaceVaryingLinearInterpolation::CornersOnly,
            CORNERS_PLUS1 => FaceVaryingLinearInterpolation::CornersPlus1,
            CORNERS_PLUS2 => FaceVaryingLinearInterpolation::CornersPlus2,
            BOUNDARIES => FaceVaryingLinearInterpolation::Boundaries,
            ALL => FaceVaryingLinearInterpolation::All,
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
            TriangleSubdivisionRule::CatmullClark => CATMULL_CLARK,
            TriangleSubdivisionRule::Smooth => SMOOTH,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            CATMULL_CLARK => TriangleSubdivisionRule::CatmullClark,
            SMOOTH => TriangleSubdivisionRule::Smooth,
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
            Interpolation::Constant => CONSTANT,
            Interpolation::Uniform => UNIFORM,
            Interpolation::Varying => VARYING,
            Interpolation::Vertex => VERTEX,
            Interpolation::FaceVarying => FACE_VARYING,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            CONSTANT => Interpolation::Constant,
            UNIFORM => Interpolation::Uniform,
            VARYING => Interpolation::Varying,
            VERTEX => Interpolation::Vertex,
            FACE_VARYING => Interpolation::FaceVarying,
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
            ElementType::Face => FACE,
            ElementType::Point => POINT,
            ElementType::Edge => EDGE,
            ElementType::Tetrahedron => TETRAHEDRON,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            FACE => ElementType::Face,
            POINT => ElementType::Point,
            EDGE => ElementType::Edge,
            TETRAHEDRON => ElementType::Tetrahedron,
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
            CurveType::Cubic => CUBIC,
            CurveType::Linear => LINEAR,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            CUBIC => CurveType::Cubic,
            LINEAR => CurveType::Linear,
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
            CurveBasis::Bezier => BEZIER,
            CurveBasis::Bspline => BSPLINE,
            CurveBasis::CatmullRom => CATMULL_ROM,
            CurveBasis::Hermite => HERMITE,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            BEZIER => CurveBasis::Bezier,
            BSPLINE => CurveBasis::Bspline,
            CATMULL_ROM => CurveBasis::CatmullRom,
            HERMITE => CurveBasis::Hermite,
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
            CurveWrap::Nonperiodic => NONPERIODIC,
            CurveWrap::Periodic => PERIODIC,
            CurveWrap::Pinned => PINNED,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            NONPERIODIC => CurveWrap::Nonperiodic,
            PERIODIC => CurveWrap::Periodic,
            PINNED => CurveWrap::Pinned,
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
            PatchForm::Open => OPEN,
            PatchForm::Closed => CLOSED,
            PatchForm::Periodic => PERIODIC,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            OPEN => PatchForm::Open,
            CLOSED => PatchForm::Closed,
            PERIODIC => PatchForm::Periodic,
            _ => return None,
        })
    }
}

// Bidirectional `From`/`TryFrom<Value>` for each token enum, so they pass
// straight to `Attribute::set` / `get::<Enum>()`. See the macro's own docs.
use crate::token_value::impl_token_value;

impl_token_value!(
    Visibility,
    Purpose,
    Orientation,
    Axis,
    Projection,
    StereoRole,
    SubdivisionScheme,
    InterpolateBoundary,
    FaceVaryingLinearInterpolation,
    TriangleSubdivisionRule,
    Interpolation,
    ElementType,
    CurveType,
    CurveBasis,
    CurveWrap,
    PatchForm,
);

#[cfg(test)]
mod tests {
    use super::*;
    use openusd::sdf::Value;

    #[test]
    fn token_value_round_trip() {
        // `From` authors a token; `TryFrom` decodes it back.
        let value = Value::from(SubdivisionScheme::Loop);
        assert_eq!(value, Value::Token(LOOP.into()));
        assert_eq!(SubdivisionScheme::try_from(value).unwrap(), SubdivisionScheme::Loop);
    }

    #[test]
    fn token_value_errors() {
        // A non-token value and an unknown token both fail.
        assert!(Visibility::try_from(Value::Int(1)).is_err());
        assert!(Purpose::try_from(Value::Token("bogus".into())).is_err());
    }
}
