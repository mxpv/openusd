//! Authoring helpers for the [UsdSkel](super) schema family.
//!
//! Mirrors the per-schema reader surface in [`super::read`] with the inverse
//! direction — each `define_*` / `apply_*` helper authors a typed prim or an
//! applied API schema onto a [`crate::usd::Stage`] in a form that the
//! corresponding reader will decode losslessly.
//!
//! The helpers are thin wrappers over the generic
//! [`Stage::define_prim`](crate::usd::Stage::define_prim) and
//! [`Layer::create_attribute`](crate::sdf::Layer::create_attribute) machinery:
//! they only know which type tokens, attribute names, type names, and
//! metadata keys Pixar's `usdSkel/schema.usda` requires. Everything else
//! (composition, layer routing, save) goes through the same APIs a hand-rolled
//! authoring call would use.
//!
//! Each helper writes opinions to the stage's current edit target. Author
//! across multiple layers by setting the edit target via
//! [`Stage::set_edit_target`](crate::usd::Stage::set_edit_target) between
//! calls.

mod binding;
mod blend_shape;
mod common;
mod skel_animation;
mod skel_root;
mod skeleton;

pub use binding::{apply_skel_binding, SkelBindingAuthor};
pub use blend_shape::{define_blend_shape, BlendShapeAuthor};
pub use skel_animation::{define_skel_animation, SkelAnimationAuthor};
pub use skel_root::define_skel_root;
pub use skeleton::{define_skeleton, SkeletonAuthor};
