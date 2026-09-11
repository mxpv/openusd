//! Typed views for USD's standard schemas, over a composed
//! [`Stage`](openusd::usd::Stage).
//!
//! Ask a `Mesh` for its points, a `Camera` for its focal length, a `Material`
//! for the shader on its surface output, a `Skeleton` for its joints and
//! skinning weights — as Rust types, rather than by attribute name and hand
//! decoding. Every view authors as well as reads.
//!
//! Every view is generated from the schema definitions this crate vendors, by
//! [`openusd-build`](https://docs.rs/openusd-build) at build time: a family's
//! views, the tokens it names things by, and the schema data a registry reads
//! its fallbacks and inheritance from. What is hand-written beside them is
//! what a property cannot say — a transform stack, a skinning topology, a
//! render spec.
//!
//! Each family is feature-gated, so a caller compiles only the domains it
//! reads. A family that builds on another's views enables it:
//!
//! | Feature | Module | Schemas | Beyond the views |
//! |---------|--------|---------|------------------|
//! | `geom`    | `geom`    | `UsdGeom`     | `ImageableExt` (visibility / purpose down namespace), `XformableExt` (the transform stack), the token enums |
//! | `lux`     | `lux`     | `UsdLux`      | the token enums; needs `geom` |
//! | `media`   | `media`   | `UsdMedia`    | asset-preview thumbnails, which live in `assetInfo`; needs `geom` |
//! | `physics` | `physics` | `UsdPhysics`  | the token enums; needs `geom` |
//! | `proc`    | `proc`    | `UsdProc`     | needs `geom` |
//! | `render`  | `render`  | `UsdRender`   | the computed render spec, aperture conforming, the stage's settings prim |
//! | `shade`   | `shade`   | `UsdShade`    | the `Connectable` interface, connection resolution, material terminals, the `UsdPreviewSurface` reader |
//! | `skel`    | `skel`    | `UsdSkel`     | the skinning toolkit: topology, animation mapping, resolvers, pure-math LBS; needs `geom` |
//! | `ui`      | `ui`      | `UsdUI`       | |
//! | `vol`     | `vol`     | `UsdVol`      | a volume's field relationships, which no property declares; needs `geom` |
//!
//! # The registry
//!
//! A view answers through the stage's [`SchemaRegistry`]: it is what makes a
//! prim a `Mesh`, what resolves the fallback a schema declares for an
//! unauthored property, and what answers
//! [`is_a`](openusd::usd::Prim::is_a) along a schema's inheritance. Hand
//! [`schema_registry`] to the stage, or register [`ALL`] on a builder of your
//! own where a caller adds families beside these. A stage opened without it
//! knows only the core `usd` family, so the typed `get` constructors answer
//! `None`.
//!
//! # Conventions
//!
//! Every schema is a view named after it and a `<Class>Schema` trait carrying
//! its own accessors, so `Mesh` reads through `MeshSchema` and inherits the
//! rest from the trait of each class behind it: reading `mesh.points_attr()`
//! needs `PointBasedSchema` in scope. A property is reached through a
//! `foo_attr()` / `create_foo_attr()` pair, named by the schema's own
//! `apiName`. An applied API schema is applied to a prim
//! (`TagAPI::apply(&prim)`) and read back with `get` — or, where it takes an
//! instance name, `get_instance(&prim, "front")`.
//!
//! An abstract class — `Gprim`, `Imageable`, `Xformable` — has a view of its
//! own, for a prim whose concrete type a caller does not care about:
//! `Gprim::get(&stage, path)` answers for a prim of any type under it, and
//! reads the properties they all share. It defines nothing, no prim being of
//! that type itself.

use std::sync::{Arc, OnceLock};

use openusd::sdf;
use openusd::usd::{self, SchemaRegistry};

// The macros below generate paths into the core crate. Reaching it through
// `$crate::openusd` keeps them bound to this crate's dependency rather than
// to whatever `openusd` names at the expansion site.
pub(crate) use ::openusd;

// The families that name a token-valued enum. The three others that use the
// macro — `physics`, `skel` and `vol` — enable `geom`, which is already here.
#[cfg(any(feature = "geom", feature = "render", feature = "shade", feature = "ui"))]
mod token_value;

/// Any failure a schema view can report: a schema-domain failure of its own,
/// or a core failure ([`Core`](Self::Core)) from the composed queries and
/// authoring calls the view is built on.
///
/// The schemas module is layered on the core the way a separate crate would
/// be, so the core's [`Error`](openusd::Error) knows nothing of this type; this
/// enum wraps the core error instead.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SchemaError {
    /// A core failure underneath the schema view.
    #[error(transparent)]
    Core(#[from] openusd::Error),

    /// An xformOp names no kind this schema knows, so it has no value type
    /// and would contribute nothing to the transform stack.
    #[error("`{op}` is not an xformOp kind")]
    UnknownXformOp {
        /// The kind the op token named, with its `xformOp:` prefix and any
        /// `:suffix` removed.
        op: String,
    },

    /// An xformOp's matrix is singular, so the transform stack cannot be
    /// inverted through it.
    #[error("xformOp `{op}` matrix is singular and cannot be inverted")]
    SingularTransform {
        /// The offending op's attribute name.
        op: String,
    },

    /// `!resetXformStack!` appears past the front of `xformOpOrder`, where it
    /// no longer means anything.
    #[error("xformOpOrder on `{prim}`: `!resetXformStack!` is only valid at index 0, found at index {index}")]
    InvalidOpOrder {
        /// The prim whose order is malformed.
        prim: sdf::Path,
        /// Where the reset token was found.
        index: usize,
    },

    /// A shading connection chain exceeds the resolver's depth bound,
    /// indicating a cycle or a pathologically deep graph.
    #[error("connection chain at {attribute} is deeper than {max} hops")]
    ConnectionDepthExceeded {
        /// The attribute whose resolution hit the bound.
        attribute: sdf::Path,
        /// The bound that was hit.
        max: usize,
    },

    /// A volume field relationship needs a non-empty field name.
    #[error("Volume field name must not be empty")]
    EmptyFieldName,

    /// A render context that is neither the universal context nor a
    /// namespaced identifier.
    #[error("invalid render context {context:?}")]
    InvalidRenderContext {
        /// The rejected context string.
        context: String,
    },
}

/// Stage-tier authoring failures route through [`SchemaError::Core`], so a
/// schema authoring helper propagates them with one `?`.
impl From<openusd::usd::StageAuthoringError> for SchemaError {
    fn from(error: openusd::usd::StageAuthoringError) -> Self {
        Self::Core(error.into())
    }
}

/// Composed-query failures route through [`SchemaError::Core`] likewise.
impl From<openusd::pcp::QueryError> for SchemaError {
    fn from(error: openusd::pcp::QueryError) -> Self {
        Self::Core(error.into())
    }
}

/// Path-parse failures route through [`SchemaError::Core`] likewise.
impl From<sdf::PathParseError> for SchemaError {
    fn from(error: sdf::PathParseError) -> Self {
        Self::Core(error.into())
    }
}

/// Cast failures route through [`SchemaError::Core`] likewise.
impl From<sdf::CastError> for SchemaError {
    fn from(error: sdf::CastError) -> Self {
        Self::Core(error.into())
    }
}

/// A value that does not fit an attribute's declared type surfaces as the
/// authoring error it is.
impl From<sdf::ValueTypeError> for SchemaError {
    fn from(error: sdf::ValueTypeError) -> Self {
        Self::Core(openusd::usd::StageAuthoringError::from(error).into())
    }
}

#[cfg(feature = "geom")]
pub mod geom;
#[cfg(feature = "lux")]
pub mod lux;
#[cfg(feature = "media")]
pub mod media;
#[cfg(feature = "physics")]
pub mod physics;
#[cfg(feature = "proc")]
pub mod proc;
#[cfg(feature = "render")]
pub mod render;
#[cfg(feature = "shade")]
pub mod shade;
#[cfg(feature = "skel")]
pub mod skel;
#[cfg(feature = "ui")]
pub mod ui;
#[cfg(feature = "vol")]
pub mod vol;

/// Every family this build enables, ready to register.
///
/// Register each on a builder to make a registry of your own;
/// [`schema_registry`] is the shared one built from exactly this. Each family declares the schema data generated from its
/// own vendored definitions: the fallbacks a stage resolves, and the
/// inheritance it answers [`is_a`](openusd::usd::Prim::is_a) along.
///
/// A single family registers the same way, through the `SCHEMAS` its module
/// exposes:
///
/// ```
/// # #[cfg(feature = "geom")]
/// # fn main() -> Result<(), openusd::usd::SchemaRegistryError> {
/// use openusd::usd::SchemaRegistry;
///
/// let registry = SchemaRegistry::builder().register(openusd_schemas::geom::SCHEMAS).build()?;
/// # Ok(())
/// # }
/// # #[cfg(not(feature = "geom"))]
/// # fn main() {}
/// ```
pub static ALL: &[&usd::SchemaFamily<'static>] = &[
    #[cfg(feature = "geom")]
    geom::SCHEMAS,
    #[cfg(feature = "lux")]
    lux::SCHEMAS,
    #[cfg(feature = "media")]
    media::SCHEMAS,
    #[cfg(feature = "physics")]
    physics::SCHEMAS,
    #[cfg(feature = "proc")]
    proc::SCHEMAS,
    #[cfg(feature = "render")]
    render::SCHEMAS,
    #[cfg(feature = "shade")]
    shade::SCHEMAS,
    #[cfg(feature = "skel")]
    skel::SCHEMAS,
    #[cfg(feature = "ui")]
    ui::SCHEMAS,
    #[cfg(feature = "vol")]
    vol::SCHEMAS,
];

/// The registry of every enabled family, built once and shared.
///
/// Hand it to [`usd::StageBuilder::schema_registry`](openusd::usd::StageBuilder::schema_registry):
/// a stage opened without it knows only the core `usd` family, so the typed
/// `get` constructors answer `None` and no schema fallback resolves.
///
/// ```no_run
/// use openusd::usd::Stage;
///
/// let stage = Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .open("scene.usda")?;
/// # Ok::<(), openusd::Error>(())
/// ```
///
/// # Panics
///
/// If the generated schema data does not register or compose, which is a bug
/// in this crate rather than anything a caller can cause.
pub fn schema_registry() -> Arc<SchemaRegistry> {
    static REGISTRY: OnceLock<Arc<SchemaRegistry>> = OnceLock::new();
    REGISTRY
        .get_or_init(|| {
            ALL.iter()
                .fold(SchemaRegistry::builder(), |builder, family| builder.register(family))
                .build()
                .expect("the generated schema data registers and composes")
        })
        .clone()
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    use openusd::Result;
    use openusd::usd::Stage;

    /// An in-memory stage carrying every enabled family's schema data, which
    /// is what makes a prim its type and resolves the fallbacks a schema
    /// declares. Reached from a family's own tests as
    /// `crate::tests::stage("anon.usda")`.
    #[allow(
        dead_code,
        reason = "which families' tests reach for it depends on the features enabled"
    )]
    pub(crate) fn stage(name: &str) -> Result<Stage> {
        Stage::builder().schema_registry(schema_registry()).in_memory(name)
    }
}
