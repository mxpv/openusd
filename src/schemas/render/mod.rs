//! UsdRender schema reader + authoring.
//!
//! Decodes and authors Pixar's `UsdRender` schema family — the
//! description of *what* to render and *how* the output is framed and
//! split into channels — on top of a composed [`crate::Stage`].
//!
//! Schema types (`pxr/usd/usdRender`):
//! - [`tokens::T_RENDER_SETTINGS_BASE`] — abstract base carrying the
//!   shared camera + framing attributes.
//! - [`tokens::T_RENDER_SETTINGS`] — top-level render configuration;
//!   enumerates the products to produce.
//! - [`tokens::T_RENDER_PRODUCT`] — one output artifact (image / deep
//!   image); inherits the base and may override it.
//! - [`tokens::T_RENDER_VAR`] — one output channel (AOV).
//! - [`tokens::T_RENDER_PASS`] — a node in a multi-pass render graph.
//! - [`tokens::T_RENDER_DENOISE_PASS`] — a denoise pass (`dev`-era).
//!
//! The centrepiece is the computed *render spec*: a `RenderSettings`
//! prim, its products, vars, and camera are flattened into a
//! self-contained, fallback-resolved value (product attributes
//! overriding settings, the aspect-ratio conform policy applied, vars
//! de-duplicated). That computation is the spec-faithful crux and is
//! built up across the following commits.
//!
//! # Defaults
//!
//! Each decoded enum and `Read*` struct's `Default` matches Pixar's
//! `usdRender/schema.usda` fallbacks exactly, so callers can
//! `unwrap_or_default()` for a spec-correct fallback.

pub mod spec;
pub mod tokens;

mod author;
mod compute;
mod conform;
mod read;
mod types;

pub use author::{
    define_render_product, define_render_settings, define_render_var, RenderProductAuthor, RenderSettingsAuthor,
    RenderVarAuthor, SettingsBaseSetters,
};
pub use compute::compute_render_spec;
pub use conform::{apply_aspect_ratio_policy, ConformedAperture};
pub use read::{
    read_base_overriding, read_camera_aperture, read_render_product, read_render_settings, read_render_var,
    read_settings_base,
};
pub use types::{
    AspectRatioConformPolicy, ProductType, ReadRenderProduct, ReadRenderSettings, ReadRenderVar, ReadSettingsBase,
    SourceType,
};
