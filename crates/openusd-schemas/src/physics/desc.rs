//! The descriptors [`parse`](super::parse) reports, one per physics object
//! (C++ `parseDesc.h`). C++ derives a struct per kind from a base with a
//! type tag; here each family is one struct and the per-kind part an enum:
//! [`Shape`] with [`Geometry`], [`Joint`] with [`JointKind`].
//!
//! Values keep the C++ widths, `f32` with [`gf::Vec3f`] and [`gf::Quatf`]: every
//! physics attribute they come from is float-typed. Transforms are computed
//! in `f64` and narrowed once, here.
//!
//! A path the C++ descriptors leave empty for "none" is an `Option` here:
//! a static collider's [`Shape::rigid_body`], a joint's missing body, and
//! the world among an [`Articulation`]'s bodies.

use openusd::gf;
use openusd::sdf::Path;
use openusd::tf;

use super::{Dof, JointAxis};
use crate::geom;

/// A physics scene (C++ `UsdPhysicsSceneDesc`).
#[derive(Debug, Clone, PartialEq)]
pub struct Scene {
    /// The `PhysicsScene` prim.
    pub path: Path,
    /// The gravity direction, normalized; the negative stage up axis where
    /// the scene authors none.
    pub gravity_direction: gf::Vec3f,
    /// The gravity magnitude; Earth's in stage units where the scene authors
    /// none.
    pub gravity_magnitude: f32,
}

/// A collision group (C++ `UsdPhysicsCollisionGroupDesc`). Groups sharing a
/// `mergeGroupName` are reported as one, the first the merge loop reaches,
/// which lists the others in [`merged_groups`](Self::merged_groups).
#[derive(Debug, Clone, PartialEq)]
pub struct CollisionGroup {
    /// The `PhysicsCollisionGroup` prim.
    pub path: Path,
    /// Whether `filtered_groups` lists the groups this one collides with;
    /// `false` lists the ones it does not, and is what an unauthored flag
    /// reads as.
    pub invert_filtered_groups: bool,
    /// The `physics:filteredGroups` targets, with those of the merged groups
    /// appended in merge order.
    pub filtered_groups: Vec<Path>,
    /// The `physics:mergeGroupName` value, empty where the group merges with
    /// nothing.
    pub merge_group_name: String,
    /// The groups merged into this one, itself first; empty for a group that
    /// merges with nothing.
    pub merged_groups: Vec<Path>,
}

/// A physics material (C++ `UsdPhysicsRigidBodyMaterialDesc`): the
/// `PhysicsMaterialAPI` attributes of a prim.
#[derive(Debug, Clone, PartialEq)]
pub struct Material {
    /// The prim carrying `PhysicsMaterialAPI`.
    pub path: Path,
    /// `physics:staticFriction`.
    pub static_friction: f32,
    /// `physics:dynamicFriction`.
    pub dynamic_friction: f32,
    /// `physics:restitution`.
    pub restitution: f32,
    /// `physics:density`, in the stage's mass units per cubic distance unit.
    pub density: f32,
}

/// A collider (C++ `UsdPhysicsShapeDesc`): a prim with `PhysicsCollisionAPI`
/// whose gprim type gives its [`Geometry`]. The sizes already contain the
/// prim's world scale, which physics engines do not carry; a mesh reports
/// the scale instead.
#[derive(Debug, Clone, PartialEq)]
pub struct Shape {
    /// The collider prim.
    pub path: Path,
    /// The body the collider belongs to, the nearest ancestor-or-self among
    /// the parsed bodies; `None` is a static collider.
    pub rigid_body: Option<Path>,
    /// The collider's position in the body's frame, scaled by the body's
    /// world scale.
    pub local_pos: gf::Vec3f,
    /// The collider's orientation in the body's frame.
    pub local_rot: gf::Quatf,
    /// The collider's scale in the body's frame.
    pub local_scale: gf::Vec3f,
    /// The physics materials bound to the collider: a mesh's face subsets'
    /// first, then the prim's own.
    pub materials: Vec<Path>,
    /// The `physics:simulationOwner` targets.
    pub simulation_owners: Vec<Path>,
    /// The `physics:filteredPairs` targets.
    pub filtered_collisions: Vec<Path>,
    /// The collision groups whose colliders collection holds the prim, in
    /// group path order.
    pub collision_groups: Vec<Path>,
    /// The `physics:collisionEnabled` value.
    pub collision_enabled: bool,
    /// What the collider is, by its gprim type.
    pub geometry: Geometry,
}

/// What a [`Shape`] is, by its gprim type (the C++ shape descriptors).
///
/// A radius or half height is the attribute scaled by the prim's world scale
/// along the axes it spans; a `half_height` is half the `height` attribute.
#[derive(Debug, Clone, PartialEq)]
pub enum Geometry {
    /// `UsdGeomSphere` (C++ `UsdPhysicsSphereShapeDesc`).
    Sphere { radius: f32 },
    /// `UsdGeomCube` (C++ `UsdPhysicsCubeShapeDesc`): half the `size` along
    /// each axis, scaled, keeping the scale's sign.
    Cube { half_extents: gf::Vec3f },
    /// `UsdGeomCapsule` (C++ `UsdPhysicsCapsuleShapeDesc`).
    Capsule {
        radius: f32,
        half_height: f32,
        axis: geom::Axis,
    },
    /// `UsdGeomCapsule_1` (C++ `UsdPhysicsCapsule1ShapeDesc`).
    Capsule1 {
        top_radius: f32,
        bottom_radius: f32,
        half_height: f32,
        axis: geom::Axis,
    },
    /// `UsdGeomCylinder` (C++ `UsdPhysicsCylinderShapeDesc`).
    Cylinder {
        radius: f32,
        half_height: f32,
        axis: geom::Axis,
    },
    /// `UsdGeomCylinder_1` (C++ `UsdPhysicsCylinder1ShapeDesc`).
    Cylinder1 {
        top_radius: f32,
        bottom_radius: f32,
        half_height: f32,
        axis: geom::Axis,
    },
    /// `UsdGeomCone` (C++ `UsdPhysicsConeShapeDesc`).
    Cone {
        radius: f32,
        half_height: f32,
        axis: geom::Axis,
    },
    /// `UsdGeomPlane` (C++ `UsdPhysicsPlaneShapeDesc`).
    Plane { axis: geom::Axis },
    /// `UsdGeomMesh` (C++ `UsdPhysicsMeshShapeDesc`).
    Mesh {
        /// The `physics:approximation` token of the prim's
        /// `PhysicsMeshCollisionAPI`, `none` where it has none.
        approximation: tf::Token,
        /// The prim's world scale.
        scale: gf::Vec3f,
        double_sided: bool,
    },
    /// `UsdGeomPoints` (C++ `UsdPhysicsSpherePointsShapeDesc`): one sphere
    /// per point.
    SpherePoints(Vec<SpherePoint>),
    /// A custom shape (C++ `UsdPhysicsCustomShapeDesc`): the applied schema
    /// or type name among the caller's shape tokens that matched.
    Custom(tf::Token),
}

/// One sphere of a [`Geometry::SpherePoints`] (C++ `UsdPhysicsSpherePoint`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SpherePoint {
    /// The point, in the prim's frame.
    pub center: gf::Vec3f,
    /// Half the point's width, scaled by the prim's largest world scale.
    pub radius: f32,
}

/// A rigid body (C++ `UsdPhysicsRigidBodyDesc`): a prim with
/// `PhysicsRigidBodyAPI`.
#[derive(Debug, Clone, PartialEq)]
pub struct RigidBody {
    /// The body prim.
    pub path: Path,
    /// The colliders that belong to the body, kind by kind in the order of
    /// [`Geometry`]'s variants and by path within a kind, as C++ reports them.
    pub collisions: Vec<Path>,
    /// The `physics:filteredPairs` targets.
    pub filtered_collisions: Vec<Path>,
    /// The `physics:simulationOwner` targets.
    pub simulation_owners: Vec<Path>,
    /// The body's world position.
    pub position: gf::Vec3f,
    /// The body's world orientation.
    pub rotation: gf::Quatf,
    /// The body's world scale.
    pub scale: gf::Vec3f,
    /// `physics:rigidBodyEnabled`; a disabled body is static.
    pub enabled: bool,
    /// `physics:kinematicEnabled`.
    pub kinematic: bool,
    /// `physics:startsAsleep`.
    pub starts_asleep: bool,
    /// `physics:velocity`.
    pub linear_velocity: gf::Vec3f,
    /// `physics:angularVelocity`.
    pub angular_velocity: gf::Vec3f,
}

/// An articulation (C++ `UsdPhysicsArticulationDesc`): a prim with
/// `PhysicsArticulationRootAPI` and the bodies and joints reached from it.
#[derive(Debug, Clone, PartialEq)]
pub struct Articulation {
    /// The prim carrying the API.
    pub path: Path,
    /// Where the articulation's topology starts (C++ `rootPrims`): the body
    /// or joint the API is on, or the roots chosen per chain of linked
    /// bodies under it.
    pub roots: Vec<Path>,
    /// The `physics:filteredPairs` targets.
    pub filtered_collisions: Vec<Path>,
    /// The joints linking the bodies, sorted (C++ `articulatedJoints`).
    pub joints: Vec<Path>,
    /// The bodies linked, sorted, `None` first for the world where a joint
    /// with one body reaches it (C++ `articulatedBodies`).
    pub bodies: Vec<Option<Path>>,
}

/// A joint (C++ `UsdPhysicsJointDesc`): a `PhysicsJoint` prim.
#[derive(Debug, Clone, PartialEq)]
pub struct Joint {
    /// The joint prim.
    pub path: Path,
    /// The first `physics:body0` target.
    pub rel0: Option<Path>,
    /// The first `physics:body1` target.
    pub rel1: Option<Path>,
    /// The body `rel0` reaches: the target or its nearest ancestor with
    /// `PhysicsRigidBodyAPI`, else the topmost such with `PhysicsCollisionAPI`.
    pub body0: Option<Path>,
    /// The body `rel1` reaches, as `body0`.
    pub body1: Option<Path>,
    /// The anchor on `body0`, in its frame and scaled by its world scale.
    pub local_pos0: gf::Vec3f,
    /// The anchor's orientation on `body0`, in its frame.
    pub local_rot0: gf::Quatf,
    /// The anchor on `body1`, as `local_pos0`.
    pub local_pos1: gf::Vec3f,
    /// The anchor's orientation on `body1`, in its frame.
    pub local_rot1: gf::Quatf,
    /// `physics:jointEnabled`.
    pub enabled: bool,
    /// `physics:collisionEnabled`, between the jointed bodies.
    pub collision_enabled: bool,
    /// `physics:breakForce`.
    pub break_force: f32,
    /// `physics:breakTorque`.
    pub break_torque: f32,
    /// `physics:excludeFromArticulation`.
    pub exclude_from_articulation: bool,
    /// What the joint is, by its schema type.
    pub kind: JointKind,
}

/// What a [`Joint`] is, by its schema type (the C++ joint descriptors). A
/// `PhysicsJoint` of no more specific type is `D6`.
#[derive(Debug, Clone, PartialEq)]
pub enum JointKind {
    /// `PhysicsFixedJoint` (C++ `UsdPhysicsFixedJointDesc`).
    Fixed,
    /// `PhysicsRevoluteJoint` (C++ `UsdPhysicsRevoluteJointDesc`): the limit
    /// is `lowerLimit` / `upperLimit`, enabled when both are bounds by
    /// [`Limit::SENTINEL`]; the drive is the `angular` instance.
    Revolute {
        axis: JointAxis,
        limit: Limit,
        drive: Option<Drive>,
    },
    /// `PhysicsPrismaticJoint` (C++ `UsdPhysicsPrismaticJointDesc`): the
    /// limit is `lowerLimit` / `upperLimit`, enabled when either is a bound
    /// by [`Limit::SENTINEL`]; the drive is the `linear` instance.
    Prismatic {
        axis: JointAxis,
        limit: Limit,
        drive: Option<Drive>,
    },
    /// `PhysicsSphericalJoint` (C++ `UsdPhysicsSphericalJointDesc`): the
    /// limit is `coneAngle0Limit` / `coneAngle1Limit`, enabled when both are
    /// finite and not negative.
    Spherical { axis: JointAxis, limit: Limit },
    /// `PhysicsDistanceJoint` (C++ `UsdPhysicsDistanceJointDesc`): the limit
    /// is `minDistance` / `maxDistance`, each enabled on its own when not
    /// negative; `limit.enabled` is unused.
    Distance {
        min_enabled: bool,
        max_enabled: bool,
        limit: Limit,
    },
    /// A generic `PhysicsJoint` (C++ `UsdPhysicsD6JointDesc`): one limit per
    /// `PhysicsLimitAPI` instance and one drive per `PhysicsDriveAPI`
    /// instance, in [`Dof::ALL`] order.
    D6 {
        limits: Vec<(Dof, Limit)>,
        drives: Vec<(Dof, Drive)>,
    },
    /// A joint whose type is among the caller's joint tokens (C++
    /// `UsdPhysicsCustomJointDesc`).
    Custom,
}

/// A joint limit (C++ `UsdPhysicsJointLimit`). The C++ struct names the
/// bounds `angle0` / `lower` / `minDist` and `angle1` / `upper` / `maxDist`
/// through unions; here they are one pair, and [`JointKind`] says what each
/// kind reads into them.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Limit {
    /// Whether the limit is in force, by the rule of the joint's kind.
    pub enabled: bool,
    /// The lower bound: degrees for an angle, stage units for a distance.
    pub lower: f32,
    /// The upper bound, in the units of `lower`.
    pub upper: f32,
}

impl Limit {
    /// A lower bound at or below the negation of this, or an upper bound at
    /// or above it, is no bound, as is an infinite one (C++
    /// `usdPhysicsSentinelLimit`).
    pub const SENTINEL: f32 = 0.5e38;
}

/// A joint drive (C++ `UsdPhysicsJointDrive`), one `PhysicsDriveAPI`
/// instance. Its force is `stiffness * (target_position - position) +
/// damping * (target_velocity - velocity)`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Drive {
    /// `targetPosition`: degrees for an angular drive, stage units for a
    /// linear one.
    pub target_position: f32,
    /// `targetVelocity`, in the units of `target_position` per second.
    pub target_velocity: f32,
    /// The `physics:maxForce` value (C++ `forceLimit`).
    pub force_limit: f32,
    /// `stiffness`, the spring term.
    pub stiffness: f32,
    /// `damping`, the velocity term.
    pub damping: f32,
    /// Whether the drive's `type` is `acceleration`.
    pub acceleration: bool,
}
