//! UsdSkel schema views and skinning toolkit.
//!
//! Typed value-views over a composed [`crate::usd::Stage`], mirroring Pixar's
//! `UsdSkel` family, plus the time-independent half of Pixar's UsdSkel object
//! model: topology, animation-to-skeleton mappers, per-mesh skinning
//! resolvers, and pure-math helpers for linear blend skinning and blend-shape
//! application.
//!
//! ```text
//! geom::Boundable
//!  ├ SkelRoot                       (encapsulating scope; authored extent)
//!  └ Skeleton                       (joint topology + bind / rest poses)
//! SchemaBase
//!  ├ SkelAnimation   (typed; time-sampled joint transforms + weights)
//!  ├ BlendShape      (typed; per-vertex offsets + inbetweens)
//!  └ SkelBindingAPI  (single-apply; joint influences + skel: bindings)
//! ```
//!
//! [`SkelRoot`] and [`Skeleton`] are [`geom::Boundable`](crate::schemas::geom)
//! prims, so `skel` enables the `geom` feature. Time-sampled SkelAnimation
//! evaluation is handled by [`SkelAnimQuery`], which delegates to
//! [`crate::usd::Stage::value_at`] and inherits the stage's interpolation mode
//! (AOUSD §12.5 — linear by default, with per-joint slerp for `rotations`).
//! The static resolvers ([`SkeletonResolver`] / [`SkinningResolver`]) take
//! pre-evaluated joint poses, so callers typically wire `SkelAnimQuery` into
//! them at each frame. [`discover_bindings`] walks a `SkelRoot` subtree and
//! resolves every skinnable prim's inherited skeleton + animation source
//! (C++ `UsdSkelCache::ComputeSkelBindings`).
//!
//! # Conventions
//!
//! Decoded getters return values in the scene's authored units: matrices are
//! row-major flattened 4×4 (`[f64; 16]`), quaternions stay in USD's
//! `(w, x, y, z)` order, half-precision storage is widened to `f32`,
//! `bindTransforms` are world-space, and `restTransforms` are joint-local
//! (parent-relative).
//!
//! # Example
//!
//! ```
//! use openusd::schemas::skel::{self, Skeleton, SkeletonResolver};
//! use openusd::usd::Stage;
//!
//! let stage = Stage::builder().in_memory("rig.usda").unwrap();
//! let skel = Skeleton::define(&stage, "/Rig").unwrap();
//! skel.create_joints_attr().unwrap()
//!     .set(openusd::sdf::Value::TokenVec(vec!["Root".into(), "Root/Hip".into()])).unwrap();
//!
//! let skel = Skeleton::get(&stage, "/Rig").unwrap().expect("Skeleton");
//! let resolver = SkeletonResolver::from_skeleton(&skel).unwrap();
//! assert_eq!(resolver.topology().num_joints(), 2);
//! ```

pub mod tokens;

mod anim_mapper;
mod anim_query;
mod binding;
mod schema;
mod skeleton_query;
pub mod skinning;
mod skinning_query;
mod topology;

pub use anim_mapper::{AnimMapper, MISSING};
pub use anim_query::{JointTransformComponents, SkelAnimQuery};
pub use binding::{discover_bindings, SkelBinding};
pub use schema::{BlendShape, Inbetween, SkelAnimation, SkelBindingAPI, SkelRoot, Skeleton};
pub use skeleton_query::SkeletonResolver;
pub use skinning_query::SkinningResolver;
pub use topology::{Topology, TopologyError, NO_PARENT};

use tokens::*;

/// Implement the schema-trait chain for a concrete UsdSkel view. All trait
/// paths are fully qualified, so the call site only needs the macro in scope.
///
/// - `boundable` is a [`geom::Boundable`](crate::schemas::geom::Boundable) prim
///   ([`SkelRoot`], [`Skeleton`]).
/// - `typed` is a concrete typed prim ([`SkelAnimation`], [`BlendShape`]).
/// - `single_api` is a single-apply API schema ([`SkelBindingAPI`]).
macro_rules! impl_skel_schema {
    (boundable $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::ConcreteTyped;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
        impl $crate::schemas::geom::Imageable for $ty {}
        impl $crate::schemas::geom::Xformable for $ty {}
        impl $crate::schemas::geom::Boundable for $ty {}
    };
    (typed $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::ConcreteTyped;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
    };
    (single_api $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::SingleApplyApi;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
    };
}

pub(crate) use impl_skel_schema;

/// `primvars:skel:skinningMethod` token values on [`SkelBindingAPI`]. The
/// default when unauthored is [`SkinningMethod::ClassicLinear`] — standard
/// linear blend skinning. [`SkinningMethod::DualQuaternion`] is the only other
/// Pixar-defined value; consumers without DQ support typically fall back to
/// classic LBS.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SkinningMethod {
    #[default]
    ClassicLinear,
    DualQuaternion,
}

impl SkinningMethod {
    pub fn as_token(self) -> &'static str {
        match self {
            SkinningMethod::ClassicLinear => SKINNING_METHOD_CLASSIC_LINEAR,
            SkinningMethod::DualQuaternion => SKINNING_METHOD_DUAL_QUATERNION,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            SKINNING_METHOD_CLASSIC_LINEAR => SkinningMethod::ClassicLinear,
            SKINNING_METHOD_DUAL_QUATERNION => SkinningMethod::DualQuaternion,
            _ => return None,
        })
    }
}

/// Authored `interpolation` on the joint-influence primvars. `Constant`
/// encodes rigid skinning (one set of weights for the whole prim); `Vertex` is
/// per-point weights — the unauthored default and the only interpolation that
/// generally makes sense for per-vertex influence lists.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InfluenceInterpolation {
    Constant,
    #[default]
    Vertex,
}

impl InfluenceInterpolation {
    pub fn as_token(self) -> &'static str {
        match self {
            InfluenceInterpolation::Constant => INTERP_CONSTANT,
            InfluenceInterpolation::Vertex => INTERP_VERTEX,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            INTERP_CONSTANT => InfluenceInterpolation::Constant,
            INTERP_VERTEX => InfluenceInterpolation::Vertex,
            _ => return None,
        })
    }
}

// `From`/`TryFrom<Value>` for the token-valued enums, so they pass straight to
// `Attribute::set` / `get::<Enum>()` and the primvar-metadata accessors.
crate::schemas::common::impl_token_value!(SkinningMethod, InfluenceInterpolation);
