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
//! | `skel`    | `skel`    | `UsdSkel` reader + skinning toolkit (Topology, AnimMapper, SkeletonResolver, SkinningResolver, pure-math LBS). |
//! | `lux`     | `lux`     | `UsdLux` trait-views (8 concrete light prims + LightFilter + LightAPI / ShapingAPI / ShadowAPI / LightListAPI); builds on the `geom` trait chain. |
//! | `shade`   | `shade`   | `UsdShade` reader + authoring (Material / NodeGraph / Shader, connectable inputs / outputs, MaterialBindingAPI, UsdPreviewSurface). |
//! | `render`  | `render`  | `UsdRender` reader + authoring (RenderSettings / Product / Var / Pass + the computed render spec). |
//! | `ui`      | `ui`      | `UsdUI` reader + authoring (SceneGraphPrimAPI / NodeGraphNodeAPI / Backdrop). |
//! | `vol`     | `vol`     | `UsdVol` trait-views (`Volume` + `OpenVDBAsset` / `Field3DAsset`); builds on the `geom` trait chain. |
//! | `media`   | `media`   | `UsdMedia` trait-views (`SpatialAudio` + `AssetPreviewsAPI`); builds on the `geom` trait chain. |
//! | `proc`    | `proc`    | `UsdProc` trait-view (`GenerativeProcedural`, a `geom::Boundable`); builds on the `geom` trait chain. |
//!
//! See [`registry`] for the eventual schema-registry surface
//! (currently a stub).

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

pub mod registry;
