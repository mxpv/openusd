//! UsdSkel schema views and skinning toolkit.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdSkel` family, plus Pixar's UsdSkel object model: topology,
//! animation-to-skeleton mappers, the skeleton query, per-mesh skinning
//! queries, and pure-math helpers for linear blend skinning and blend-shape
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
//! evaluation is handled by [`AnimQuery`], which delegates to
//! [`openusd::usd::Attribute::get`] and inherits the stage's interpolation mode
//! (AOUSD §12.5 — linear by default, with per-joint slerp for `rotations`).
//! [`SkeletonQuery`] binds a skeleton to the animation it inherits and poses
//! it at any time; [`SkinningQuery`] takes the skinning transforms it
//! answers. [`discover_bindings`] walks a `Root` subtree and
//! resolves every skinnable prim's inherited skeleton and binding properties,
//! with the animation bound to that skeleton
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
//! use openusd_schemas::skel::{self, Skeleton, SkeletonQuery, SkeletonSchema};
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
//! let query = SkeletonQuery::new(&skel).unwrap().expect("valid topology");
//! assert_eq!(query.topology().joint_count(), 2);
//! ```

openusd::include_schema!("usdSkel");

mod anim_mapper;
mod anim_query;
mod binding;
mod blend_shape_query;
mod decode;
mod inbetween;
mod skeleton_query;
pub mod skinning;
mod skinning_query;
mod topology;

pub use anim_mapper::{AnimMapper, MISSING};
pub use anim_query::AnimQuery;
pub use binding::{SkelBinding, discover_bindings, is_skinnable};
pub use blend_shape_query::{BlendShapeQuery, SubShapeWeight};
pub use inbetween::{INBETWEENS_NAMESPACE, InbetweenShape};
pub use skeleton_query::SkeletonQuery;
pub use skinning_query::{JointInfluences, SkinningQuery};
pub use topology::{NO_PARENT, Topology, TopologyError};

/// The `interpolation` of the joint-influence primvars. `Constant` encodes
/// rigid skinning, one set of weights for the whole prim, and is what a
/// primvar with no authored interpolation has; `Vertex` is per-point weights.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InfluenceInterpolation {
    #[default]
    Constant,
    Vertex,
}

impl InfluenceInterpolation {
    pub fn as_token(self) -> &'static str {
        match self {
            InfluenceInterpolation::Constant => crate::geom::tokens::CONSTANT,
            InfluenceInterpolation::Vertex => crate::geom::tokens::VERTEX,
        }
    }

    pub fn from_token(token: impl AsRef<str>) -> Option<Self> {
        Some(match token.as_ref() {
            crate::geom::tokens::CONSTANT => InfluenceInterpolation::Constant,
            crate::geom::tokens::VERTEX => InfluenceInterpolation::Vertex,
            _ => return None,
        })
    }
}

// `From`/`TryFrom<Value>` for the token-valued enums, so they pass straight to
// `Attribute::set` / `get::<Enum>()` and the primvar-metadata accessors.
openusd::sdf::impl_token_value!(InfluenceInterpolation);
