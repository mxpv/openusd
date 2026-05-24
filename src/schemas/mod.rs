//! Domain-schema readers — the non-core extensions that ride on top
//! of the spec-level `sdf` / `stage` machinery.
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
//! | `physics` | [`physics`] | `UsdPhysics` reader (8 prim types, 7 single-apply APIs, multi-apply `LimitAPI` / `DriveAPI`). |
//! | `skel`    | [`skel`]    | `UsdSkel` reader + skinning toolkit (Topology, AnimMapper, SkeletonResolver, SkinningResolver, pure-math LBS). |
//!
//! See [`registry`] for the eventual schema-registry surface
//! (currently a stub).

#[cfg(feature = "physics")]
pub mod physics;

pub mod registry;

#[cfg(feature = "skel")]
pub mod skel;
