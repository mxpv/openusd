//! UsdSkel schema reader and skinning toolkit.
//!
//! Decodes Pixar's `UsdSkel` schema family from a composed
//! [`crate::usd::Stage`], plus the time-independent half of Pixar's
//! UsdSkel object model: topology, animation-to-skeleton mappers,
//! per-mesh skinning resolvers, and pure-math helpers for linear
//! blend skinning and blend-shape application.
//!
//! Time-sampled SkelAnimation evaluation is handled by
//! [`SkelAnimQuery`], which delegates to [`crate::usd::Stage::value_at`]
//! and inherits the stage's interpolation mode (AOUSD §12.5 — linear
//! by default, with per-joint slerp for `rotations`). The static
//! resolvers below take pre-evaluated joint poses, so callers
//! typically wire `SkelAnimQuery` into them at each frame.
//!
//! # Schemas
//!
//! Concrete prim types:
//! - [`tokens::T_SKEL_ROOT`] — encapsulating scope for skeletal
//!   processing; carries an authored `extent`.
//! - [`tokens::T_SKELETON`] — joint topology + bind / rest poses.
//! - [`tokens::T_SKEL_ANIMATION`] — time-sampled joint transforms and
//!   blend-shape weights.
//! - [`tokens::T_BLEND_SHAPE`] — per-vertex position / normal offsets
//!   with optional inbetween shapes.
//!
//! API schemas:
//! - [`tokens::API_SKEL_BINDING`] — applied to skinnable prims
//!   (typically Meshes) to wire joint influences, blend shapes,
//!   `skel:skeleton`, and `skel:animationSource`.
//!
//! # Conventions
//!
//! Reader functions return values in the scene's authored units:
//! - Matrices are row-major flattened 4×4 (`[f64; 16]`).
//! - Quaternions stay in USD's textual `(w, x, y, z)` order.
//! - Half-precision storage (`half3[] scales`, `quath[] rotations`) is
//!   widened to `f32` so callers don't need to depend on the `half`
//!   crate transitively.
//! - `bindTransforms` are world-space; `restTransforms` are joint-local
//!   space (parent-relative).
//!
//! # Inheritance
//!
//! `skel:skeleton` and `skel:animationSource` are inheritable down
//! namespace. [`read_skel_binding`] reports only the values authored
//! directly on the queried prim; use [`read_inherited_skeleton`] /
//! [`read_inherited_animation_source`] to resolve the nearest-ancestor
//! binding. [`discover_bindings`] does that walk for every skinnable
//! prim under a SkelRoot in one pass.
//!
//! # Example
//!
//! ```ignore
//! use openusd::{sdf, skel, usd};
//!
//! let stage = usd::Stage::open("character.usda")?;
//! for root in skel::find_skel_roots(&stage)? {
//!     let root = sdf::path(&root)?;
//!     for b in skel::discover_bindings(&stage, &root)? {
//!         println!("{} bound to {:?}", b.prim, b.skeleton);
//!     }
//! }
//! # anyhow::Ok(())
//! ```

pub mod tokens;

mod anim_mapper;
mod anim_query;
mod author;
mod binding;
mod read;
mod skeleton_query;
pub mod skinning;
mod skinning_query;
mod topology;
mod types;

pub use anim_mapper::{AnimMapper, MISSING};
pub use anim_query::{JointTransformComponents, SkelAnimQuery};
pub use author::{
    apply_skel_binding, define_blend_shape, define_skel_animation, define_skel_root, define_skeleton, BlendShapeAuthor,
    SkelAnimationAuthor, SkelBindingAuthor, SkeletonAuthor,
};
pub use binding::{discover_bindings, discover_skeletons, find_skel_roots, SkelBinding};
pub use read::{
    find_skel_prims, read_blend_shape, read_inherited_animation_source, read_inherited_skeleton, read_skel_animation,
    read_skel_binding, read_skel_root, read_skeleton,
};
pub use skeleton_query::SkeletonResolver;
pub use skinning_query::SkinningResolver;
pub use topology::{Topology, TopologyError, NO_PARENT};
pub use types::{
    InfluenceInterpolation, ReadBlendShape, ReadInbetween, ReadSkelAnimation, ReadSkelBinding, ReadSkelRoot,
    ReadSkeleton, SkelPrims, SkinningMethod,
};
