//! Authoring helpers for the [UsdRender](super) schema family.
//!
//! Same shape as the [`super::read`] surface, in reverse: each helper
//! writes a typed prim or attribute in the form the corresponding reader
//! decodes losslessly. Helpers wrap [`crate::usd::Stage`]'s authoring
//! entry points and only know the type tokens / attribute names / type
//! names / variability that Pixar's `usdRender/schema.usda` requires.
//!
//! Opinions land in the stage's current edit target; layer routing is the
//! caller's job via
//! [`Stage::set_edit_target`](crate::usd::Stage::set_edit_target).

mod base;
mod product;
mod settings;
mod var;

pub use base::SettingsBaseSetters;
pub use product::{define_render_product, RenderProductAuthor};
pub use settings::{define_render_settings, RenderSettingsAuthor};
pub use var::{define_render_var, RenderVarAuthor};
