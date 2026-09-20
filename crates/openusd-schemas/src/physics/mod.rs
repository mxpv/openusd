//! UsdPhysics schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdPhysics` family — rigid-body dynamics, collision, and joints. A joint is
//! a `UsdGeom` [`Imageable`](crate::geom::Imageable), which is why this family
//! enables `geom`; [`Scene`] and [`CollisionGroup`] derive `UsdTyped` directly,
//! and the rest are API schemas applied onto existing prims.
//!
//! ```text
//! SchemaBase
//!  ├ Scene / CollisionGroup                 (typed simulation prims)
//!  ├ Joint  (+ JointSchema accessors)       (typed; two-body constraint)
//!  │  └ FixedJoint / RevoluteJoint / PrismaticJoint / SphericalJoint / DistanceJoint
//!  ├ single-apply APIs                       RigidBodyAPI / MassAPI / CollisionAPI /
//!  │                                         MeshCollisionAPI / MaterialAPI /
//!  │                                         ArticulationRootAPI / FilteredPairsAPI
//!  └ multi-apply APIs (one instance per DOF) DriveAPI / LimitAPI
//! ```
//!
//! Joints share the [`JointSchema`] attribute interface (the two attached bodies
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
//! use openusd_schemas::physics::{self, JointSchema, RevoluteJointSchema, SceneSchema};
//! use openusd::{sdf, usd};
//!
//! let stage = usd::Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("scene.usda").unwrap();
//!
//! let scene = physics::Scene::define(&stage, "/World/Scene").unwrap();
//! scene.create_gravity_magnitude_attr().unwrap().set(981.0_f32).unwrap();
//!
//! // A hinge: a RevoluteJoint adds `axis`/limits; `breakForce` is inherited
//! // from the shared JointSchema accessors.
//! let hinge = physics::RevoluteJoint::define(&stage, "/World/Hinge").unwrap();
//! hinge.create_axis_attr().unwrap().set(physics::JointAxis::Z).unwrap();
//! hinge.create_break_force_attr().unwrap().set(500.0_f32).unwrap();
//!
//! // A rigid body is a single-apply API applied onto an existing prim.
//! let box_prim = stage.define_prim("/World/Box").unwrap();
//! let body = physics::RigidBodyAPI::apply(&box_prim).unwrap();
//! body.create_rigid_body_enabled_attr().unwrap().set(true).unwrap();
//!
//! assert_eq!(hinge.axis_attr().get::<physics::JointAxis>().unwrap(), Some(physics::JointAxis::Z));
//! ```

openusd::include_schema!("usdPhysics");

mod collision_group;

use tokens::*;

/// The physics-specific material binding, which is `material:binding` under
/// the `physics` purpose.
pub const REL_MATERIAL_BINDING_PHYSICS: &str = "material:binding:physics";

// What a `PhysicsDriveAPI` instance's properties are called after the instance
// name: a drive is `drive:<name>:targetPosition`, and the schema declares the
// template rather than any of these tails.
pub const DRIVE_SUB_TARGET_POSITION: &str = "targetPosition";
pub const DRIVE_SUB_TARGET_VELOCITY: &str = "targetVelocity";
pub const DRIVE_SUB_DAMPING: &str = "damping";
pub const DRIVE_SUB_STIFFNESS: &str = "stiffness";
pub const DRIVE_SUB_MAX_FORCE: &str = "maxForce";

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
            Dof::TransX => TRANS_X,
            Dof::TransY => TRANS_Y,
            Dof::TransZ => TRANS_Z,
            Dof::RotX => ROT_X,
            Dof::RotY => ROT_Y,
            Dof::RotZ => ROT_Z,
            Dof::Linear => LINEAR,
            Dof::Angular => ANGULAR,
            Dof::Distance => DISTANCE,
        }
    }

    pub fn from_token(token: impl AsRef<str>) -> Option<Self> {
        Some(match token.as_ref() {
            TRANS_X => Dof::TransX,
            TRANS_Y => Dof::TransY,
            TRANS_Z => Dof::TransZ,
            ROT_X => Dof::RotX,
            ROT_Y => Dof::RotY,
            ROT_Z => Dof::RotZ,
            LINEAR => Dof::Linear,
            ANGULAR => Dof::Angular,
            DISTANCE => Dof::Distance,
            _ => return None,
        })
    }
}
