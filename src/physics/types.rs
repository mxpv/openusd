//! Decoded structs and enums returned by [`super::read`] functions.

use super::tokens::*;

/// Joint prim types recognised by [`super::read::read_joint`].
/// `Generic` is `PhysicsJoint` (no built-in axis), typically paired
/// with multi-apply [`super::read::read_joint_limits`] entries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JointKind {
    Fixed,
    Revolute,
    Prismatic,
    Spherical,
    Distance,
    Generic,
}

/// Joint DOF tokens used by multi-apply `PhysicsLimitAPI` and
/// `PhysicsDriveAPI`. `Linear` / `Angular` / `Distance` are the
/// shorthand instance names some authoring tools emit on single-axis
/// joints; `TransX..RotZ` are the canonical six DOFs on generic joints.
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

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
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

/// `PhysicsDriveAPI:<dof>:physics:type` token values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DriveType {
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

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            DRIVE_TYPE_FORCE => DriveType::Force,
            DRIVE_TYPE_ACCELERATION => DriveType::Acceleration,
            _ => return None,
        })
    }
}

/// `physics:approximation` token values on `PhysicsMeshCollisionAPI`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CollisionApprox {
    /// Default — engine-specific fallback. For dynamic bodies an
    /// importer typically substitutes [`CollisionApprox::ConvexHull`];
    /// for static bodies, a trimesh.
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

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
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

/// Decoded `PhysicsRigidBodyAPI` state.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadRigidBody {
    /// `physics:rigidBodyEnabled`, defaults to `true` when unauthored.
    pub rigid_body_enabled: bool,
    pub kinematic_enabled: bool,
    pub starts_asleep: bool,
    pub velocity: Option<[f32; 3]>,
    /// USD authors `physics:angularVelocity` in degrees per second.
    pub angular_velocity: Option<[f32; 3]>,
    /// `physics:simulationOwner` rel target — composed prim path of
    /// the `PhysicsScene` this body belongs to.
    pub simulation_owner: Option<String>,
}

/// Decoded inertial properties from a prim with `PhysicsMassAPI` applied.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadMass {
    pub mass: Option<f32>,
    pub center_of_mass: Option<[f32; 3]>,
    pub diagonal_inertia: Option<[f32; 3]>,
    /// Quaternion `(w, x, y, z)` of the principal-axes frame.
    pub principal_axes: Option<[f32; 4]>,
    /// `physics:density`, used as a fallback when `mass` is absent.
    pub density: Option<f32>,
}

/// Decoded `UsdPhysicsScene`. `gravity_direction` is a free vector
/// (typically a unit vector pointing in the direction of gravity);
/// `gravity_magnitude` scales it. Both default to `None` when the
/// scene prim authored only the type but no attributes.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadPhysicsScene {
    pub path: String,
    pub gravity_direction: Option<[f32; 3]>,
    pub gravity_magnitude: Option<f32>,
}

/// Decoded `PhysicsCollisionAPI` (plus optional `PhysicsMeshCollisionAPI`)
/// state on a prim.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadCollisionShape {
    pub has_collision_api: bool,
    pub has_mesh_collision_api: bool,
    /// `physics:collisionEnabled`, defaults to `true` when unauthored
    /// (Pixar spec: CollisionAPI applied implies enabled).
    pub collision_enabled: bool,
    pub approximation: Option<CollisionApprox>,
    pub simulation_owner: Option<String>,
    /// Resolved through `material:binding:physics` first, then
    /// `material:binding`. Empty when no material is bound.
    pub physics_material_path: Option<String>,
}

/// Decoded `PhysicsMaterialAPI` on a `Material` prim.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadPhysicsMaterial {
    pub path: String,
    pub static_friction: Option<f32>,
    pub dynamic_friction: Option<f32>,
    pub restitution: Option<f32>,
    pub density: Option<f32>,
}

/// One entry from a multi-apply `PhysicsLimitAPI:<dof>` schema.
/// `lower > upper` encodes a locked DOF (canonical USD convention).
#[derive(Debug, Clone, PartialEq)]
pub struct ReadLimit {
    pub dof: Dof,
    pub low: f32,
    pub high: f32,
}

/// One entry from a multi-apply `PhysicsDriveAPI:<dof>` schema.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadDrive {
    pub dof: Dof,
    pub drive_type: DriveType,
    pub target_position: Option<f32>,
    pub target_velocity: Option<f32>,
    pub damping: f32,
    pub stiffness: f32,
    pub max_force: Option<f32>,
}

/// Decoded `Physics*Joint` prim. `axis` is `"X" | "Y" | "Z"` when
/// set; `lower_limit` / `upper_limit` are the built-in single-axis
/// limits authored on `PhysicsRevoluteJoint` / `PhysicsPrismaticJoint`
/// (revolute in degrees, prismatic in scene distance units).
///
/// `limits` and `drives` carry multi-apply `PhysicsLimitAPI:<dof>` /
/// `PhysicsDriveAPI:<dof>` opinions, used on generic joints to lock /
/// limit / drive specific DOFs.
#[derive(Debug, Clone)]
pub struct ReadJoint {
    pub path: String,
    pub kind: JointKind,
    pub body0: Option<String>,
    pub body1: Option<String>,
    pub local_pos0: [f32; 3],
    pub local_rot0: [f32; 4],
    pub local_pos1: [f32; 3],
    pub local_rot1: [f32; 4],
    pub axis: Option<String>,
    pub lower_limit: Option<f32>,
    pub upper_limit: Option<f32>,
    pub collision_enabled: bool,
    pub joint_enabled: bool,
    pub exclude_from_articulation: bool,
    pub break_force: Option<f32>,
    pub break_torque: Option<f32>,
    /// `physics:minDistance` / `maxDistance` on `PhysicsDistanceJoint`.
    pub min_distance: Option<f32>,
    pub max_distance: Option<f32>,
    /// `physics:coneAngle0Limit` / `coneAngle1Limit` on
    /// `PhysicsSphericalJoint` (degrees, `-1.0` = unlimited).
    pub cone_angle_0: Option<f32>,
    pub cone_angle_1: Option<f32>,
    pub limits: Vec<ReadLimit>,
    pub drives: Vec<ReadDrive>,
}

/// Decoded `PhysicsCollisionGroup`. `members` is the raw list of
/// `collection:colliders:includes` targets — full collection-rule
/// flattening is left to a follow-up.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadCollisionGroup {
    pub path: String,
    pub members: Vec<String>,
    pub filtered_groups: Vec<String>,
    pub merge_group: Option<String>,
    pub invert_filtered_groups: bool,
}

/// Decoded `PhysicsFilteredPairsAPI` on a body prim.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadFilteredPairs {
    pub path: String,
    pub filtered: Vec<String>,
}

/// Result of [`super::read::find_physics_prims`] — a single-pass
/// stage walk that returns categorised path lists. Saves the caller
/// from re-walking the stage for each schema family.
#[derive(Debug, Clone, Default)]
pub struct PhysicsPrims {
    pub scenes: Vec<String>,
    pub rigid_bodies: Vec<String>,
    pub articulation_roots: Vec<String>,
    pub colliders: Vec<String>,
    pub joints: Vec<String>,
    pub materials: Vec<String>,
    pub collision_groups: Vec<String>,
    pub filtered_pairs: Vec<String>,
}
