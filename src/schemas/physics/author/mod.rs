//! Authoring helpers for the [UsdPhysics](super) schema family.
//!
//! Mirrors the per-schema reader surface in [`super::read`] with the inverse
//! direction — each `define_*` / `apply_*` helper authors a typed prim or an
//! applied API schema in the form the corresponding reader decodes losslessly.
//!
//! The helpers wrap [`crate::usd::Stage`]'s authoring entry points; they only
//! know which type tokens, attribute names, type names, and token-allowed
//! values Pixar's `usdPhysics/schema.usda` requires. Composition, layer
//! routing, and save flow through the same APIs a hand-rolled authoring call
//! would use.
//!
//! `PhysicsLimitAPI` and `PhysicsDriveAPI` are multi-apply schemas: their
//! `apply_*` helpers take a [`super::Dof`] instance and author the
//! correctly-namespaced `apiSchemas` token plus the namespaced attribute set
//! (`limit:<dof>:physics:*` / `drive:<dof>:physics:*`).

mod common;
mod rigid_body;
mod scene;

pub use rigid_body::{apply_mass, apply_rigid_body, MassAuthor, RigidBodyAuthor};
pub use scene::{define_physics_scene, PhysicsSceneAuthor};
