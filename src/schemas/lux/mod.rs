//! UsdLux schema reader.
//!
//! Decodes Pixar's `UsdLux` schema family from a composed
//! [`crate::Stage`]. Covers the canonical light prims plus the
//! `LightAPI` / `ShapingAPI` / `ShadowAPI` / `LightListAPI`
//! applied schemas:
//!
//! Concrete light prims:
//! - [`tokens::T_DISTANT_LIGHT`] — sun-style parallel light.
//! - [`tokens::T_SPHERE_LIGHT`] — point / spherical area light.
//! - [`tokens::T_RECT_LIGHT`] — rectangular area light.
//! - [`tokens::T_DISK_LIGHT`] — circular area light.
//! - [`tokens::T_CYLINDER_LIGHT`] — tube / strip light.
//! - [`tokens::T_DOME_LIGHT`] / [`tokens::T_DOME_LIGHT_1`] —
//!   image-based environment light.
//! - [`tokens::T_GEOMETRY_LIGHT`] — uses an arbitrary mesh as the
//!   emissive surface.
//! - [`tokens::T_PORTAL_LIGHT`] — aperture for sampling a parent
//!   DomeLight more efficiently.
//!
//! Applied APIs:
//! - [`tokens::API_LIGHT`] — implicit on every concrete light prim.
//!   Surfaces intensity / exposure / colour / temperature, etc.
//! - [`tokens::API_SHAPING`] — focus + cone + IES profile.
//! - [`tokens::API_SHADOW`] — shadow casting controls.
//! - [`tokens::API_LIGHT_LIST`] — cached light-list on a parent prim.
//!
//! # Defaults
//!
//! Each `Read*` struct's `Default` impl matches Pixar's `schema.usda`
//! defaults exactly. Unauthored attributes fall back to those values
//! without the consumer needing `Option<f32>` plumbing — callers can
//! always `unwrap_or_default()` if they want a spec-correct fallback.
//!
//! `DistantLight` overrides `LightAPI.inputs:intensity = 1` with
//! `50000` (per Pixar's schema), modelling the sun reaching Earth at
//! ~50000 lux.

pub mod tokens;

mod read;
mod types;

pub use read::{
    find_lux_prims, is_light_type, read_cylinder_light, read_disk_light, read_distant_light, read_dome_light,
    read_geometry_light, read_light, read_light_api, read_light_list, read_portal_light, read_rect_light, read_shadow,
    read_shaping, read_sphere_light,
};
pub use types::{
    LightListCacheBehavior, LuxPrims, ReadAnyLight, ReadCylinderLight, ReadDiskLight, ReadDistantLight, ReadDomeLight,
    ReadGeometryLight, ReadLight, ReadLightList, ReadPortalLight, ReadRectLight, ReadShadow, ReadShaping,
    ReadSphereLight, TextureFormat,
};
