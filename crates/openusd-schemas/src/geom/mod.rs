//! UsdGeom schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdGeom` class hierarchy. Each prim type (`Mesh`, `Sphere`, `Camera`, …) is
//! a newtype wrapping a [`openusd::usd::Prim`] and gains its property accessors
//! from a chain of schema traits. So is each class the prim types derive from
//! (`Imageable`, `Gprim`, …), which views a prim of any type under it:
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
//! use openusd_schemas::geom::{self, ImageableSchema, MeshSchema};
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

// The enums still written by hand name the generated constants directly.
use tokens::*;

pub use imageable::ImageableExt;
pub use xformable::{XformOpPrecision, XformableExt};

/// The namespace a primvar is authored under: a primvar named `st` is the
/// attribute `primvars:st`.
pub const PRIMVARS_NAMESPACE: &str = "primvars:";

/// The prim metadata naming a model's role in the hierarchy (`component`,
/// `assembly`, `group`). It is metadata rather than a property, so no schema
/// declares it.
pub const META_KIND: &str = "kind";

impl SubdivisionScheme {
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

    pub fn from_token(token: impl AsRef<str>) -> Option<Self> {
        Some(match token.as_ref() {
            CONSTANT => Interpolation::Constant,
            UNIFORM => Interpolation::Uniform,
            VARYING => Interpolation::Varying,
            VERTEX => Interpolation::Vertex,
            FACE_VARYING => Interpolation::FaceVarying,
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

    pub fn from_token(token: impl AsRef<str>) -> Option<Self> {
        Some(match token.as_ref() {
            BEZIER => CurveBasis::Bezier,
            BSPLINE => CurveBasis::Bspline,
            CATMULL_ROM => CurveBasis::CatmullRom,
            HERMITE => CurveBasis::Hermite,
            _ => return None,
        })
    }
}

// Bidirectional `From`/`TryFrom<Value>` for each token enum, so they pass
// straight to `Attribute::set` / `get::<Enum>()`. See the macro's own docs.
openusd::sdf::impl_token_value!(Interpolation, CurveBasis);

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
