//! UsdPhysics schema reader.
//!
//! Decodes Pixar's `UsdPhysics` schema family from a composed
//! [`crate::usd::Stage`]. Mirrors the C++ surface in
//! `pxr/usd/usdPhysics/`:
//!
//! Concrete prim types:
//! - [`tokens::T_PHYSICS_SCENE`] — simulation-wide settings (gravity).
//! - [`tokens::T_PHYSICS_JOINT`] — generic 6-DOF joint base.
//! - [`tokens::T_PHYSICS_FIXED_JOINT`] — locks all DOFs.
//! - [`tokens::T_PHYSICS_REVOLUTE_JOINT`] — single-axis rotation.
//! - [`tokens::T_PHYSICS_PRISMATIC_JOINT`] — single-axis translation.
//! - [`tokens::T_PHYSICS_SPHERICAL_JOINT`] — ball joint with cone limits.
//! - [`tokens::T_PHYSICS_DISTANCE_JOINT`] — min/max distance constraint.
//! - [`tokens::T_PHYSICS_COLLISION_GROUP`] — coarse collision filtering.
//!
//! Single-apply API schemas:
//! - [`tokens::API_RIGID_BODY`] — mark prim as physics-driven.
//! - [`tokens::API_MASS`] — explicit mass / inertia / centre-of-mass.
//! - [`tokens::API_COLLISION`] — enable collision on a prim.
//! - [`tokens::API_MESH_COLLISION`] — mesh shape approximation token.
//! - [`tokens::API_PHYSICS_MATERIAL`] — friction / restitution / density.
//! - [`tokens::API_ARTICULATION_ROOT`] — mark a reduced-coordinate articulation.
//! - [`tokens::API_FILTERED_PAIRS`] — fine-grained pair filtering.
//!
//! Multi-apply API schemas (one instance per DOF):
//! - [`tokens::API_LIMIT`] — per-DOF lock / range.
//! - [`tokens::API_DRIVE`] — per-DOF spring-damper actuator.
//!
//! ## Conventions
//!
//! Reader functions return values in the scene's authored units:
//! - Linear values stay in scene units (caller applies `metersPerUnit`).
//! - Mass values stay in scene mass units (caller applies `kilogramsPerUnit`).
//! - Rotational values stay in degrees (USD's authoring convention).
//! - Quaternions stay in USD's textual `(w, x, y, z)` order.
//! - `lower > upper` on any limit encodes a locked DOF.
//!
//! ## Example
//!
//! ```ignore
//! use openusd::{physics, usd};
//!
//! let stage = usd::Stage::open("scene.usd")?;
//! let physics = physics::find_physics_prims(&stage)?;
//! for joint_path in &physics.joints {
//!     let path = openusd::sdf::path(joint_path)?;
//!     if let Some(joint) = physics::read_joint(&stage, &path)? {
//!         println!("{}: {:?} body0={:?} body1={:?}",
//!             joint.path, joint.kind, joint.body0, joint.body1);
//!     }
//! }
//! # anyhow::Ok(())
//! ```

pub mod tokens;

mod author;
mod read;
mod types;

pub use author::{
    apply_articulation_root, apply_collision, apply_filtered_pairs, apply_mass, apply_mesh_collision,
    apply_physics_material, apply_rigid_body, define_collision_group, define_physics_scene, CollisionAuthor,
    CollisionGroupAuthor, FilteredPairsAuthor, MassAuthor, MaterialAuthor, MeshCollisionAuthor, PhysicsSceneAuthor,
    RigidBodyAuthor,
};
pub use read::{
    find_physics_prims, read_collision_group, read_collision_shape, read_filtered_pairs, read_has_articulation_root,
    read_has_collision, read_has_rigid_body, read_is_physics_scene, read_joint, read_joint_drives, read_joint_limits,
    read_mass, read_physics_material, read_physics_scene, read_rigid_body,
};
pub use types::{
    CollisionApprox, Dof, DriveType, JointKind, PhysicsPrims, ReadCollisionGroup, ReadCollisionShape, ReadDrive,
    ReadFilteredPairs, ReadJoint, ReadLimit, ReadMass, ReadPhysicsMaterial, ReadPhysicsScene, ReadRigidBody,
};
