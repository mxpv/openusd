//! UsdSkel schema reader and skinning toolkit.
//!
//! Decodes Pixar's `UsdSkel` schema family from a composed
//! [`crate::Stage`], plus the time-independent half of Pixar's
//! UsdSkel object model: topology, animation-to-skeleton mappers,
//! per-mesh skinning resolvers, and pure-math helpers for linear
//! blend skinning and blend-shape application.
//!
//! Time-dependent evaluation (interpolating SkelAnimation samples at
//! a stage time, computing per-frame skinning transforms) is the job
//! of the upcoming `anim` layer. The resolvers here are designed to
//! plug straight into that work — every API that would need a
//! `UsdTimeCode` instead takes the already-evaluated joint poses.
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
//! use openusd::{skel, sdf, Stage};
//!
//! let stage = Stage::open("character.usda")?;
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
mod binding;
mod read;
mod skeleton_query;
pub mod skinning;
mod skinning_query;
mod topology;
mod types;

pub use anim_mapper::{AnimMapper, MISSING};
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
