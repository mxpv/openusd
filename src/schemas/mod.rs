//! Domain-schema readers — the non-core extensions that ride on top
//! of the spec-level `sdf` / `usd` machinery.
//!
//! The AOUSD core specification (see `docs/aousd_core_spec_1.0.1.pdf`)
//! covers composition, value resolution, and the file formats; it
//! does NOT define UsdGeom, UsdPhysics, UsdSkel, UsdShade, UsdLux,
//! and friends. Pixar ships those as schemas layered on top, and
//! consumers wire them up through reader / writer helpers like the
//! ones here.
//!
//! Each sub-module is feature-gated so callers only compile what
//! they need:
//!
//! | Feature | Module | Status |
//! |---------|--------|--------|
//! | `geom`    | `geom`    | `UsdGeom` reader (cross-cutting Imageable / Boundable today; full surface incoming). |
//! | `physics` | `physics` | `UsdPhysics` reader (8 prim types, 7 single-apply APIs, multi-apply `LimitAPI` / `DriveAPI`). |
//! | `skel`    | `skel`    | `UsdSkel` trait-views (SkelRoot / Skeleton as geom `Boundable`, SkelAnimation / BlendShape typed, SkelBindingAPI single-apply) + skinning toolkit (Topology, AnimMapper, SkeletonResolver, SkinningResolver, pure-math LBS); builds on the `geom` trait chain. |
//! | `lux`     | `lux`     | `UsdLux` trait-views (8 concrete light prims + LightFilter + LightAPI / ShapingAPI / ShadowAPI / LightListAPI); builds on the `geom` trait chain. |
//! | `shade`   | `shade`   | `UsdShade` trait-views (Shader / NodeGraph / Material via the `Connectable` interface, MaterialBindingAPI, UsdPreviewSurface reader). |
//! | `render`  | `render`  | `UsdRender` trait-views (RenderSettings / Product via the `RenderSettingsBase` interface, Var / Pass / DenoisePass) + the computed render spec. |
//! | `ui`      | `ui`      | `UsdUI` trait-views (typed `Backdrop` + single-apply `SceneGraphPrimAPI` / `NodeGraphNodeAPI`). |
//! | `vol`     | `vol`     | `UsdVol` trait-views (`Volume` + `OpenVDBAsset` / `Field3DAsset`); builds on the `geom` trait chain. |
//! | `media`   | `media`   | `UsdMedia` trait-views (`SpatialAudio` + `AssetPreviewsAPI`); builds on the `geom` trait chain. |
//! | `proc`    | `proc`    | `UsdProc` trait-view (`GenerativeProcedural`, a `geom::Boundable`); builds on the `geom` trait chain. |
//!
//! These views read and author opinions; the property fallbacks a schema
//! declares come from [`crate::usd::SchemaRegistry`].

use crate::sdf;

#[cfg(any(
    feature = "geom",
    feature = "lux",
    feature = "media",
    feature = "physics",
    feature = "proc",
    feature = "render",
    feature = "shade",
    feature = "skel",
    feature = "ui",
    feature = "vol"
))]
mod common;

/// Any failure a schema view can report: a schema-domain failure of its own,
/// or a core failure ([`Core`](Self::Core)) from the composed queries and
/// authoring calls the view is built on.
///
/// The schemas module is layered on the core the way a separate crate would
/// be, so the core's [`Error`](crate::Error) knows nothing of this type; this
/// enum wraps the core error instead.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SchemaError {
    /// A core failure underneath the schema view.
    #[error(transparent)]
    Core(#[from] crate::Error),

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
impl From<crate::usd::StageAuthoringError> for SchemaError {
    fn from(error: crate::usd::StageAuthoringError) -> Self {
        Self::Core(error.into())
    }
}

/// Composed-query failures route through [`SchemaError::Core`] likewise.
impl From<crate::pcp::QueryError> for SchemaError {
    fn from(error: crate::pcp::QueryError) -> Self {
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
