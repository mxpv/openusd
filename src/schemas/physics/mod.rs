//! UsdPhysics schema views.
//!
//! Typed value-views over a composed [`crate::usd::Stage`], mirroring Pixar's
//! `UsdPhysics` family — rigid-body dynamics, collision, and joints. Unlike the
//! UsdGeom-derived families these are not geom prims: the typed prims
//! ([`Scene`], [`CollisionGroup`], [`Joint`] and its subtypes) derive `UsdTyped`
//! directly, and the rest are API schemas applied onto existing prims.
//!
//! ```text
//! SchemaBase
//!  ├ Scene / CollisionGroup                 (typed simulation prims)
//!  ├ Joint  (+ JointBase interface)         (typed; two-body constraint)
//!  │  └ FixedJoint / RevoluteJoint / PrismaticJoint / SphericalJoint / DistanceJoint
//!  ├ single-apply APIs                       RigidBodyAPI / MassAPI / CollisionAPI /
//!  │                                         MeshCollisionAPI / MaterialAPI /
//!  │                                         ArticulationRootAPI / FilteredPairsAPI
//!  └ multi-apply APIs (one instance per DOF) DriveAPI / LimitAPI
//! ```
//!
//! Joints share the [`JointBase`] attribute interface (the two attached bodies
//! and their local frames). The multi-apply [`DriveAPI`] and [`LimitAPI`] carry
//! a degree-of-freedom instance name (e.g. `rotX`, `linear`): they apply as
//! `PhysicsDriveAPI:<dof>` / `PhysicsLimitAPI:<dof>` and their attributes live at
//! `drive:<dof>:physics:*` / `limit:<dof>:physics:*`.
//!
//! Authored values are in the scene's units (linear in scene units, mass in
//! scene mass units, angles in degrees, quaternions in `(w, x, y, z)` order).
//!
//! # Example
//!
//! ```
//! use openusd::schemas::physics::{self, JointBase};
//! use openusd::{sdf, usd};
//!
//! let stage = usd::Stage::builder().in_memory("scene.usda").unwrap();
//!
//! let scene = physics::Scene::define(&stage, "/World/Scene").unwrap();
//! scene.create_gravity_magnitude_attr().unwrap().set(981.0_f32).unwrap();
//!
//! // A hinge: a RevoluteJoint adds `axis`/limits; `breakForce` is inherited
//! // from the shared JointBase interface.
//! let hinge = physics::RevoluteJoint::define(&stage, "/World/Hinge").unwrap();
//! hinge.create_axis_attr().unwrap().set(physics::JointAxis::Z).unwrap();
//! hinge.create_break_force_attr().unwrap().set(500.0_f32).unwrap();
//!
//! // A rigid body is a single-apply API applied onto an existing prim.
//! let body = physics::RigidBodyAPI::apply(&stage, "/World/Box").unwrap();
//! body.create_rigid_body_enabled_attr().unwrap().set(true).unwrap();
//!
//! assert_eq!(hinge.axis_attr().get::<physics::JointAxis>().unwrap(), Some(physics::JointAxis::Z));
//! ```

pub mod tokens;

mod schema;
mod traits;

pub use schema::{
    ArticulationRootAPI, CollisionAPI, CollisionGroup, DistanceJoint, DriveAPI, FilteredPairsAPI, FixedJoint, Joint,
    LimitAPI, MassAPI, MaterialAPI, MeshCollisionAPI, PrismaticJoint, RevoluteJoint, RigidBodyAPI, Scene,
    SphericalJoint,
};
pub use traits::JointBase;

use crate::tf;
use tokens::*;

/// Implement the `SchemaBase` (and, for joints, [`JointBase`]) memberships for a
/// concrete physics view. All trait paths are fully qualified, so the call site
/// only needs the macro in scope.
///
/// - `typed` is a concrete typed prim (`Scene`, `CollisionGroup`).
/// - `joint` is a typed prim that also implements [`JointBase`] (the joints).
/// - `single_api` is a single-apply API schema (the `*API` views).
/// - `multi_api` is a multiple-apply API schema carrying a `name` instance
///   (`DriveAPI`, `LimitAPI`); its `prim` lives in a named field.
macro_rules! impl_physics_schema {
    (typed $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::ConcreteTyped;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
    };
    (joint $ty:ident) => {
        impl_physics_schema!(typed $ty);
        impl $crate::schemas::physics::JointBase for $ty {}
    };
    (single_api $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::SingleApplyApi;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
    };
    (multi_api $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::MultipleApplyApi;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.prim
            }
        }
    };
}

pub(crate) use impl_physics_schema;

/// The axis a single-axis joint acts about (`physics:axis` on revolute /
/// prismatic / spherical joints). Pixar's spec default is [`JointAxis::X`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum JointAxis {
    #[default]
    X,
    Y,
    Z,
}

impl JointAxis {
    pub fn as_token(self) -> &'static str {
        match self {
            JointAxis::X => AXIS_X,
            JointAxis::Y => AXIS_Y,
            JointAxis::Z => AXIS_Z,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            AXIS_X => JointAxis::X,
            AXIS_Y => JointAxis::Y,
            AXIS_Z => JointAxis::Z,
            _ => return None,
        })
    }
}

/// `drive:<dof>:physics:type` token values — whether a drive applies a force or
/// a mass-independent acceleration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DriveType {
    #[default]
    Force,
    Acceleration,
}

impl DriveType {
    pub fn as_token(self) -> &'static str {
        match self {
            DriveType::Force => DRIVE_TYPE_FORCE,
            DriveType::Acceleration => DRIVE_TYPE_ACCELERATION,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            DRIVE_TYPE_FORCE => DriveType::Force,
            DRIVE_TYPE_ACCELERATION => DriveType::Acceleration,
            _ => return None,
        })
    }
}

/// `physics:approximation` token values on [`MeshCollisionAPI`] — how a mesh's
/// collision shape is approximated for the simulator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CollisionApprox {
    /// Default — engine-specific fallback (a convex hull for dynamic bodies, a
    /// trimesh for static ones).
    #[default]
    None,
    ConvexHull,
    ConvexDecomposition,
    BoundingSphere,
    BoundingCube,
    MeshSimplification,
}

impl CollisionApprox {
    pub fn as_token(self) -> &'static str {
        match self {
            CollisionApprox::None => APPROX_NONE,
            CollisionApprox::ConvexHull => APPROX_CONVEX_HULL,
            CollisionApprox::ConvexDecomposition => APPROX_CONVEX_DECOMPOSITION,
            CollisionApprox::BoundingSphere => APPROX_BOUNDING_SPHERE,
            CollisionApprox::BoundingCube => APPROX_BOUNDING_CUBE,
            CollisionApprox::MeshSimplification => APPROX_MESH_SIMPLIFICATION,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            APPROX_NONE => CollisionApprox::None,
            APPROX_CONVEX_HULL => CollisionApprox::ConvexHull,
            APPROX_CONVEX_DECOMPOSITION => CollisionApprox::ConvexDecomposition,
            APPROX_BOUNDING_SPHERE => CollisionApprox::BoundingSphere,
            APPROX_BOUNDING_CUBE => CollisionApprox::BoundingCube,
            APPROX_MESH_SIMPLIFICATION => CollisionApprox::MeshSimplification,
            _ => return None,
        })
    }
}

/// A joint degree of freedom, used as the multi-apply instance name on
/// [`DriveAPI`] / [`LimitAPI`] (`transX`..`rotZ` for generic joints; `linear` /
/// `angular` / `distance` are the shorthand some tools emit on single-axis
/// joints). It names a schema instance rather than an attribute value, so —
/// unlike [`JointAxis`] / [`DriveType`] / [`CollisionApprox`] — it has no
/// `Value` conversion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dof {
    TransX,
    TransY,
    TransZ,
    RotX,
    RotY,
    RotZ,
    Linear,
    Angular,
    Distance,
}

impl Dof {
    pub fn as_token(self) -> &'static str {
        match self {
            Dof::TransX => DOF_TRANS_X,
            Dof::TransY => DOF_TRANS_Y,
            Dof::TransZ => DOF_TRANS_Z,
            Dof::RotX => DOF_ROT_X,
            Dof::RotY => DOF_ROT_Y,
            Dof::RotZ => DOF_ROT_Z,
            Dof::Linear => DOF_LINEAR,
            Dof::Angular => DOF_ANGULAR,
            Dof::Distance => DOF_DISTANCE,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            DOF_TRANS_X => Dof::TransX,
            DOF_TRANS_Y => Dof::TransY,
            DOF_TRANS_Z => Dof::TransZ,
            DOF_ROT_X => Dof::RotX,
            DOF_ROT_Y => Dof::RotY,
            DOF_ROT_Z => Dof::RotZ,
            DOF_LINEAR => Dof::Linear,
            DOF_ANGULAR => Dof::Angular,
            DOF_DISTANCE => Dof::Distance,
            _ => return None,
        })
    }
}

// `From`/`TryFrom<Value>` for the token-valued enums, so they pass straight to
// `Attribute::set` / `get::<Enum>()`.
crate::schemas::common::impl_token_value!(JointAxis, DriveType, CollisionApprox);
