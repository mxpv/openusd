//! UsdPhysics schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdPhysics` family — rigid-body dynamics, collision, and joints. A joint is
//! a `UsdGeom` [`Imageable`](crate::geom::Imageable), which is why this family
//! enables `geom`; [`Scene`] and [`CollisionGroup`] derive `UsdTyped` directly,
//! and the rest are API schemas applied onto existing prims. A body's mass
//! reads the material bound for the `physics` purpose, which is why the
//! family enables `shade`.
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
//! The mass unit is the stage's `kilogramsPerUnit`, which [`StageMetadata`]
//! reads and authors; [`mass_units`] names the common ones. A body's mass,
//! inertia tensor and center of mass travel together as a
//! [`MassProperties`], and [`RigidBodyAPI::mass_properties`] computes a
//! body's from its colliders, whose shapes the caller describes through a
//! [`MassInformation`].
//!
//! [`parse`] walks a stage's physics objects into the [`desc`] descriptors
//! a simulator is set up from (C++ `UsdPhysicsLoadStageFromPrimRange`).
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
pub mod desc;
mod mass_properties;
pub mod mass_units;
mod material;
mod parse;
mod rigid_body;

pub use collision_group::{CollisionGroupTable, collision_group_table};
pub use mass_properties::MassProperties;
pub use parse::{CustomTokens, ParseDiagnostic, ParseOptions, Parsed, parse};
pub use rigid_body::{BodyMass, MassInformation};

use tokens::*;

/// The material-binding purpose a collider's physics material is bound
/// under (C++ `_physicsPurposeTokens->materialPurposePhysics`).
pub const MATERIAL_PURPOSE: &str = "physics";

// What a `PhysicsDriveAPI` instance's properties are called after the instance
// name: a drive is `drive:<name>:targetPosition`, and the schema declares the
// template rather than any of these tails.
pub const DRIVE_SUB_TARGET_POSITION: &str = "targetPosition";
pub const DRIVE_SUB_TARGET_VELOCITY: &str = "targetVelocity";
pub const DRIVE_SUB_DAMPING: &str = "damping";
pub const DRIVE_SUB_STIFFNESS: &str = "stiffness";
pub const DRIVE_SUB_MAX_FORCE: &str = "maxForce";

/// A joint degree of freedom (C++ `UsdPhysicsJointDOF`): the instance name
/// a [`LimitAPI`] or [`DriveAPI`] on a generic joint is applied under, in
/// the order C++ enumerates them. A single-axis joint's drive is applied
/// under [`tokens::LINEAR`] or [`tokens::ANGULAR`], which are not degrees
/// of freedom. It names a schema instance, not an attribute value, and has
/// no `Value` conversion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dof {
    Distance,
    TransX,
    TransY,
    TransZ,
    RotX,
    RotY,
    RotZ,
}

impl Dof {
    /// Every degree of freedom, in the order C++ enumerates them.
    pub const ALL: [Dof; 7] = [
        Dof::Distance,
        Dof::TransX,
        Dof::TransY,
        Dof::TransZ,
        Dof::RotX,
        Dof::RotY,
        Dof::RotZ,
    ];

    /// The instance name.
    pub fn as_token(self) -> &'static str {
        match self {
            Dof::Distance => DISTANCE,
            Dof::TransX => TRANS_X,
            Dof::TransY => TRANS_Y,
            Dof::TransZ => TRANS_Z,
            Dof::RotX => ROT_X,
            Dof::RotY => ROT_Y,
            Dof::RotZ => ROT_Z,
        }
    }

    /// The degree of freedom `token` names, if any.
    pub fn from_token(token: impl AsRef<str>) -> Option<Self> {
        Some(match token.as_ref() {
            DISTANCE => Dof::Distance,
            TRANS_X => Dof::TransX,
            TRANS_Y => Dof::TransY,
            TRANS_Z => Dof::TransZ,
            ROT_X => Dof::RotX,
            ROT_Y => Dof::RotY,
            ROT_Z => Dof::RotZ,
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{Dof, tokens};

    /// Each degree of freedom round-trips through its token; the drive
    /// instance names of single-axis joints are no degree of freedom.
    #[test]
    fn dof_tokens() {
        for dof in Dof::ALL {
            assert_eq!(Dof::from_token(dof.as_token()), Some(dof));
        }
        assert_eq!(Dof::from_token(tokens::LINEAR), None);
        assert_eq!(Dof::from_token(tokens::ANGULAR), None);
    }
}
