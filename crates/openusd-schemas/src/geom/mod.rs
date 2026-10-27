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
//! `subdivisionScheme`, …) decode through generated token enums, which carry
//! `from_token` / `as_token`; `Interpolation` and `CurveBasis`, whose values no
//! single property declares, are written by hand at the end of this module.
//! The purpose visibilities (`guideVisibility`, `proxyVisibility`,
//! `renderVisibility`) share [`PurposeVisibility`], which derives no `Default`
//! because their fallbacks differ; a model's `model:drawMode` and
//! `model:cardGeometry` decode to [`DrawMode`] and [`CardGeometry`].
//! `visibility`, `purpose` and the purpose visibilities are inherited down
//! namespace. [`ImageableExt::compute_visibility`],
//! [`ImageableExt::effective_visibility`] and
//! [`ImageableExt::compute_purpose`] resolve the effective value by walking
//! imageable ancestors. A purpose visibility counts only where
//! [`VisibilityAPI`] is applied. [`ImageableExt::make_visible`] authors
//! visibility with that inheritance in mind, and
//! [`ImageableExt::proxy_prim`] finds the `proxy` prim standing in
//! for a `render` one. The motion settings
//! ([`MotionAPI::compute_motion_blur_scale`] and its siblings) are inherited
//! the same way, from the nearest prim that applies [`MotionAPI`].
//!
//! # Transforms
//!
//! An `Xformable` prim's local transform is its `xformOpOrder` stack, read
//! through [`XformableExt`] one prim at a time or through an [`XformQuery`]
//! that keeps the ordered ops for evaluation at many times. [`XformCache`]
//! accumulates those local transforms into world-space ones across the
//! hierarchy at one time, reusing each ancestor's answer;
//! [`ImageableExt::local_to_world_transform`] answers once, without
//! a cache.
//!
//! [`XformableExt::add_xform_op`] declares one op of any [`XformOpKind`],
//! optionally inverted, and hands back the [`XformOp`] to set its value
//! through. [`XformCommonAPI`] reads and authors the stack as one translate,
//! one rotate, one scale and a pivot ([`XformVectors`]), for the stacks that
//! have that shape.
//!
//! # Cameras
//!
//! A [`Camera`] prim reads as one [`openusd::gf::Camera`] value, placed in
//! the world, through [`Camera::camera_at`], and [`Camera::set_from_camera`]
//! authors one back as a single edit. The volume it sees is that value's
//! [`frustum`](openusd::gf::Camera::frustum).
//! [`Camera::linear_exposure_scale`] is the factor its exposure attributes
//! scale an image by.
//!
//! # Stage metrics
//!
//! The axis a stage calls up and the length of its unit are stage metadata.
//! [`StageMetadata`] reads and authors them as the token and the number they
//! are, and [`stage_up_axis`] and [`set_stage_up_axis`] as an [`UpAxis`].
//! [`linear_units`] names the common units.
//!
//! # Bounds
//!
//! A boundable prim's `extent` is the box around its own geometry, in its
//! own space. [`BoundableExt::compute_extent`] reads the authored one, or
//! else computes it from the attributes that size the prim's type, which
//! [`BoundableExt::shape_extent`] does on its own. The functions that do the
//! computing take those sizes as plain values: `Sphere::extent_from`,
//! `PointBased::extent_from` and the rest, each answering an [`Extent`]. An
//! [`ExtentRegistry`] says which function bounds which type, and takes the
//! functions of types declared elsewhere. A point instancer's extent is the
//! box around its instances, which [`PointInstancer::extent_at`] computes
//! from the bounds of its prototypes.
//!
//! A model caches the extent of everything beneath it, for each purpose, in
//! its `extentsHint`: [`ModelAPI::extents_hint_at`] reads it,
//! [`ModelAPI::set_extents_hint`] authors it and
//! [`ModelAPI::compute_extents_hint`] computes what to author.
//!
//! The bound of a prim is the box around the extents at and beneath it. A
//! [`BBoxCache`] answers it at one time and for a set of purposes, in the
//! prim's own space, its parent's, an ancestor's or the world's, and keeps
//! the box of each prim it resolves for the queries that follow. It bounds
//! the instances of a point instancer one by one, and a model by its hint
//! where asked to. For one bound of one prim,
//! [`ImageableExt::world_bound`], [`local_bound`](ImageableExt::local_bound)
//! and [`untransformed_bound`](ImageableExt::untransformed_bound) ask a
//! cache made for the call.
//!
//! # Models
//!
//! A model is drawn in full or as a stand-in, by its `model:drawMode` and
//! that of the models above it: [`ModelAPI::compute_model_draw_mode`]
//! resolves the mode a prim is drawn in.
//!
//! A model publishes named frames for other prims to follow, each a
//! matrix-valued attribute in the `constraintTargets` namespace.
//! [`ConstraintTarget`] reads and authors one, and
//! [`ModelAPI::create_constraint_target`] and
//! [`ModelAPI::constraint_targets`] create and list a model's.
//!
//! # Primvars
//!
//! A `primvars:*` attribute is read through [`Primvar`], which bundles its
//! values with its `interpolation`, its `elementSize` and the
//! `<name>:indices` attribute that may index them;
//! [`Primvar::flattened`] applies the indices. [`PrimvarsAPI`] views
//! any prim: it creates, lists, blocks and removes the prim's primvars, and
//! answers which ones reach it from its ancestors, since a constant primvar
//! is inherited down namespace. [`PrimvarBuilder`] authors a primvar with its
//! metadata and indices as one edit.
//!
//! The schema accessors that name a primvar (`Gprim::display_color_attr`, …)
//! return the bare attribute, which [`Primvar::from_attribute`] wraps. The
//! primvar-like `normals` and `widths` are plain attributes outside the
//! namespace: they carry an `interpolation`, read through
//! [`AttributeMetadata`], and take no indices.

openusd::include_schema!("usdGeom");

mod bbox_cache;
pub(crate) mod boundable;
mod camera;
mod constraint_target;
mod curves;
mod extent;
mod gprim;
mod imageable;
mod mesh;
mod metrics;
mod model_api;
mod motion_api;
mod point_instancer;
mod points;
mod primvar;
mod primvars_api;
mod sampling;
pub(crate) mod subset;
mod tet_mesh;
mod visibility_api;
mod xform;
mod xform_cache;
mod xform_op;
mod xformable;

use openusd::Result;
use openusd::{sdf, tf, usd};

// The enums still written by hand name the generated constants directly.
use tokens::*;

pub use bbox_cache::BBoxCache;
pub use boundable::{BoundableExt, ExtentContext, ExtentFn, ExtentRegistry};
pub use constraint_target::ConstraintTarget;
pub use curves::{CurvesExt, PointsAndTangents};
pub use extent::Extent;
pub use gprim::GprimExt;
pub use imageable::{ImageableExt, PurposeInfo};
pub use mesh::MeshTopologyError;
pub use metrics::{UpAxis, fallback_up_axis, linear_units, set_stage_up_axis, stage_meters_per_unit, stage_up_axis};
pub use point_instancer::{InstanceArrays, MaskApplication, ProtoXformInclusion};
pub use points::PointBasedExt;
pub use primvar::{Primvar, PrimvarDeclaration};
pub use primvars_api::PrimvarBuilder;
pub use subset::FamilyType;
pub use xform::{CommonXformOp, CommonXformOps, RotationOrder, XformVectors};
pub use xform_cache::XformCache;
#[cfg(feature = "skel")]
pub(crate) use xform_op::TOKEN_RESET_XFORM_STACK;
pub use xform_op::{XformOp, XformOpKind};
pub use xformable::{XformOpPrecision, XformQuery, XformableExt};

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

impl Purpose {
    /// Every purpose, in the order a purpose-driven listing presents them
    /// (C++ `UsdGeomImageable::GetOrderedPurposeTokens`).
    pub const ORDERED: [Purpose; 4] = [Purpose::Default, Purpose::Render, Purpose::Proxy, Purpose::Guide];
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

/// The value type `attr` is declared with, whatever its spelling, or `None`
/// where nothing declares the attribute.
fn declared_type(attr: &usd::Attribute) -> Result<Option<sdf::ValueTypeName>> {
    Ok(attr
        .metadata::<tf::Token>(sdf::FieldKey::TypeName.as_str())?
        .map(sdf::ValueTypeName::from))
}

/// The length of the array an attribute read, zero where it read no value.
// TODO(perf): the caller reads the whole array for its length; a composed
// array-length query on usd::Attribute would answer without copying the
// value.
fn array_len<T>(values: Option<Vec<T>>) -> usize {
    values.map_or(0, |values| values.len())
}

/// Visit `prim` and then each of its ancestors below the pseudo-root, seen
/// through `view`, and return the first `Some` that `visit` answers for a
/// prim `view` sees. The walk the inherited `UsdGeom` and `UsdSkel` queries
/// share, each with the schema whose opinions it reads.
pub(crate) fn nearest<V, T>(
    prim: &usd::Prim,
    view: impl Fn(usd::Prim) -> Result<Option<V>>,
    mut visit: impl FnMut(&V) -> Result<Option<T>>,
) -> Result<Option<T>> {
    for prim in prim.ancestors() {
        if let Some(viewed) = view(prim)?
            && let Some(found) = visit(&viewed)?
        {
            return Ok(Some(found));
        }
    }
    Ok(None)
}

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
