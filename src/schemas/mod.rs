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
//! | `lux`     | `lux`     | `UsdLux` reader (8 concrete light prims + LightAPI / ShapingAPI / ShadowAPI / LightListAPI). |
//! | `shade`   | `shade`   | `UsdShade` reader + authoring (Material / NodeGraph / Shader, connectable inputs / outputs, MaterialBindingAPI, UsdPreviewSurface). |
//!
//! See [`registry`] for the eventual schema-registry surface
//! (currently a stub).

#[cfg(any(
    feature = "geom",
    feature = "lux",
    feature = "physics",
    feature = "shade",
    feature = "skel"
))]
mod common;

#[cfg(feature = "geom")]
pub mod geom;
#[cfg(feature = "lux")]
pub mod lux;
#[cfg(feature = "physics")]
pub mod physics;
#[cfg(feature = "shade")]
pub mod shade;
#[cfg(feature = "skel")]
pub mod skel;

pub mod registry;
