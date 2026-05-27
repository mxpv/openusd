//! Authoring helpers for the [UsdLux](super) schema family.
//!
//! Same shape as the [`super::read`] surface, in reverse: each
//! `define_*_light` / `apply_*` helper writes a typed prim or an applied
//! API schema in the form the corresponding reader decodes losslessly.
//!
//! The helpers wrap [`crate::usd::Stage`]'s authoring entry points; they
//! only know which type tokens, attribute names, type names, and metadata
//! keys Pixar's `usdLux/schema.usda` requires. Everything else
//! (composition, layer routing, save) flows through the public
//! [`crate::usd::Stage`] / [`crate::sdf::Layer`] APIs.
//!
//! Each helper writes opinions to the stage's current edit target. Layer
//! routing is the caller's job via
//! [`Stage::set_edit_target`](crate::usd::Stage::set_edit_target).

mod boundable;
mod common;
mod dome;
mod light_api;
mod nonboundable;
mod shaping;

pub use boundable::{
    define_cylinder_light, define_disk_light, define_portal_light, define_rect_light, define_sphere_light,
    CylinderLightAuthor, DiskLightAuthor, PortalLightAuthor, RectLightAuthor, SphereLightAuthor,
};
pub use dome::{define_dome_light, define_dome_light_1, DomeLight1Author, DomeLightAuthor};
pub use light_api::{apply_light_api, LightApiSetters, LightAuthor};
pub use nonboundable::{define_distant_light, define_geometry_light, DistantLightAuthor, GeometryLightAuthor};
pub use shaping::{apply_shadow, apply_shaping, ShadowAuthor, ShapingAuthor};
