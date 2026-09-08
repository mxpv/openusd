//! UsdSkel schema views and skinning toolkit.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdSkel` family, plus the time-independent half of Pixar's UsdSkel object
//! model: topology, animation-to-skeleton mappers, per-mesh skinning
//! resolvers, and pure-math helpers for linear blend skinning and blend-shape
//! application.
//!
//! ```text
//! geom::Boundable
//!  ├ Root                       (encapsulating scope; authored extent)
//!  └ Skeleton                       (joint topology + bind / rest poses)
//! SchemaBase
//!  ├ Animation   (typed; time-sampled joint transforms + weights)
//!  ├ BlendShape      (typed; per-vertex offsets + inbetweens)
//!  └ BindingAPI  (single-apply; joint influences + skel: bindings)
//! ```
//!
//! [`Root`] and [`Skeleton`] are [`geom::Boundable`](crate::geom)
//! prims, so `skel` enables the `geom` feature. Time-sampled Animation
//! evaluation is handled by [`SkelAnimQuery`], which delegates to
//! [`openusd::usd::Attribute::get`] and inherits the stage's interpolation mode
//! (AOUSD §12.5 — linear by default, with per-joint slerp for `rotations`).
//! The static resolvers ([`SkeletonResolver`] / [`SkinningResolver`]) take
//! pre-evaluated joint poses, so callers typically wire `SkelAnimQuery` into
//! them at each frame. [`discover_bindings`] walks a `Root` subtree and
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
//! use openusd_schemas::skel::{self, Skeleton, SkeletonResolver, SkeletonSchema};
//! use openusd::usd::Stage;
//!
//! let stage = Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("rig.usda").unwrap();
//! let skel = Skeleton::define(&stage, "/Rig").unwrap();
//! skel.create_joints_attr().unwrap()
//!     .set(openusd::sdf::Value::TokenVec(vec!["Root".into(), "Root/Hip".into()])).unwrap();
//!
//! let skel = Skeleton::get(&stage, "/Rig").unwrap().expect("Skeleton");
//! let resolver = SkeletonResolver::from_skeleton(&skel).unwrap();
//! assert_eq!(resolver.topology().num_joints(), 2);
//! ```

openusd::include_schema!("usdSkel");

mod anim_mapper;
mod anim_query;
mod binding;
mod decode;
mod skeleton_query;
pub mod skinning;
mod skinning_query;
mod topology;

pub use anim_mapper::{AnimMapper, MISSING};
pub use anim_query::{JointTransformComponents, SkelAnimQuery};
pub use binding::{SkelBinding, discover_bindings};
pub use decode::{INBETWEENS_NAMESPACE, Inbetween};
pub use skeleton_query::SkeletonResolver;
pub use skinning_query::SkinningResolver;
pub use topology::{NO_PARENT, Topology, TopologyError};

use openusd::tf;

use tokens::*;

/// `primvars:skel:skinningMethod` token values on [`BindingAPI`]. The
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
            SkinningMethod::ClassicLinear => CLASSIC_LINEAR,
            SkinningMethod::DualQuaternion => DUAL_QUATERNION,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            CLASSIC_LINEAR => SkinningMethod::ClassicLinear,
            DUAL_QUATERNION => SkinningMethod::DualQuaternion,
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
            InfluenceInterpolation::Constant => crate::geom::tokens::CONSTANT,
            InfluenceInterpolation::Vertex => crate::geom::tokens::VERTEX,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            crate::geom::tokens::CONSTANT => InfluenceInterpolation::Constant,
            crate::geom::tokens::VERTEX => InfluenceInterpolation::Vertex,
            _ => return None,
        })
    }
}

// `From`/`TryFrom<Value>` for the token-valued enums, so they pass straight to
// `Attribute::set` / `get::<Enum>()` and the primvar-metadata accessors.
crate::token_value::impl_token_value!(SkinningMethod, InfluenceInterpolation);
