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

mod common;
mod light_api;

pub use light_api::{apply_light_api, LightApiSetters, LightAuthor};
