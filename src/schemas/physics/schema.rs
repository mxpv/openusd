//! The UsdPhysics prim and API-schema views.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, Relationship, Stage};

use super::impl_physics_schema;
use super::tokens as tok;
use crate::schemas::common::{get_typed, get_with_api};

/// A physics simulation scene (C++ `UsdPhysicsScene`) — simulation-wide
/// settings such as gravity. Bodies point at it via `physics:simulationOwner`.
#[derive(Clone, derive_more::Deref)]
pub struct Scene(Prim);

impl Scene {
    /// Author a `def PhysicsScene` prim at `path` (C++ `UsdPhysicsScene::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_PHYSICS_SCENE)?))
    }

    /// Wrap `path` as a `Scene` if it is typed `PhysicsScene`
    /// (C++ `UsdPhysicsScene::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_PHYSICS_SCENE).map(|o| o.map(Self))
    }

    /// The direction gravity pulls in, as a (typically unit) vector; its length
    /// is scaled by `gravityMagnitude`. C++ `UsdPhysicsScene::GetGravityDirectionAttr`.
    ///
    /// Type `vector3f`. Fetch with `get::<[f32; 3]>()?`.
    pub fn gravity_direction_attr(&self) -> Attribute {
        self.attribute(tok::A_GRAVITY_DIRECTION)
    }

    /// Author `physics:gravityDirection` (`vector3f`) (C++ `CreateGravityDirectionAttr`).
    pub fn create_gravity_direction_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_GRAVITY_DIRECTION, "vector3f")?
            .set_custom(false)?)
    }

    /// The magnitude of gravity in scene units per second squared, applied along
    /// `gravityDirection`. C++ `UsdPhysicsScene::GetGravityMagnitudeAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn gravity_magnitude_attr(&self) -> Attribute {
        self.attribute(tok::A_GRAVITY_MAGNITUDE)
    }

    /// Author `physics:gravityMagnitude` (`float`) (C++ `CreateGravityMagnitudeAttr`).
    pub fn create_gravity_magnitude_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_GRAVITY_MAGNITUDE, "float")?
            .set_custom(false)?)
    }
}

impl_physics_schema!(typed Scene);

/// A collision group (C++ `UsdPhysicsCollisionGroup`) — a named set of colliders
/// (via its `CollectionAPI`) with group-vs-group collision filtering.
#[derive(Clone, derive_more::Deref)]
pub struct CollisionGroup(Prim);

impl CollisionGroup {
    /// Author a `def PhysicsCollisionGroup` prim at `path`
    /// (C++ `UsdPhysicsCollisionGroup::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.define_prim(path)?.set_type_name(tok::T_PHYSICS_COLLISION_GROUP)?,
        ))
    }

    /// Wrap `path` as a `CollisionGroup` if it is typed `PhysicsCollisionGroup`
    /// (C++ `UsdPhysicsCollisionGroup::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_PHYSICS_COLLISION_GROUP).map(|o| o.map(Self))
    }

    /// The groups whose members this group will not collide with (collision
    /// filtering is symmetric). C++ `UsdPhysicsCollisionGroup::GetFilteredGroupsRel`.
    pub fn filtered_groups_rel(&self) -> Relationship {
        self.relationship(tok::A_FILTERED_GROUPS)
    }

    /// Author the `physics:filteredGroups` relationship
    /// (C++ `CreateFilteredGroupsRel`).
    pub fn create_filtered_groups_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::A_FILTERED_GROUPS)?.set_custom(false)?)
    }

    /// An identifier that merges all groups sharing it into one logical group;
    /// empty (unauthored) means no merging. C++ `UsdPhysicsCollisionGroup::GetMergeGroupNameAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<String>()?`.
    pub fn merge_group_attr(&self) -> Attribute {
        self.attribute(tok::A_MERGE_GROUP)
    }

    /// Author `physics:mergeGroup` (`uniform token`) (C++ `CreateMergeGroupNameAttr`).
    pub fn create_merge_group_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_MERGE_GROUP, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// When `true`, inverts the filter so this group collides only with the
    /// listed `filteredGroups`. C++ `UsdPhysicsCollisionGroup::GetInvertFilteredGroupsAttr`.
    ///
    /// Type `uniform bool`. Fetch with `get::<bool>()?`.
    pub fn invert_filtered_groups_attr(&self) -> Attribute {
        self.attribute(tok::A_INVERT_FILTERED_GROUPS)
    }

    /// Author `physics:invertFilteredGroups` (`uniform bool`)
    /// (C++ `CreateInvertFilteredGroupsAttr`).
    pub fn create_invert_filtered_groups_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_INVERT_FILTERED_GROUPS, "bool")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_physics_schema!(typed CollisionGroup);

/// A generic configurable joint (C++ `UsdPhysicsJoint`) — the base two-body
/// constraint. On its own it locks the relative pose; per-DOF freedom is added
/// with multi-apply [`LimitAPI`] / [`DriveAPI`]. Shares the [`JointBase`](super::JointBase)
/// attribute surface with the concrete joint subtypes.
#[derive(Clone, derive_more::Deref)]
pub struct Joint(Prim);

impl Joint {
    /// Author a `def PhysicsJoint` prim at `path` (C++ `UsdPhysicsJoint::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_PHYSICS_JOINT)?))
    }

    /// Wrap `path` as a `Joint` if it is typed `PhysicsJoint`
    /// (C++ `UsdPhysicsJoint::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_PHYSICS_JOINT).map(|o| o.map(Self))
    }
}

impl_physics_schema!(joint Joint);

/// A joint that locks all six relative degrees of freedom (C++
/// `UsdPhysicsFixedJoint`). Carries only the shared [`JointBase`](super::JointBase)
/// attributes.
#[derive(Clone, derive_more::Deref)]
pub struct FixedJoint(Prim);

impl FixedJoint {
    /// Author a `def PhysicsFixedJoint` prim at `path`
    /// (C++ `UsdPhysicsFixedJoint::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.define_prim(path)?.set_type_name(tok::T_PHYSICS_FIXED_JOINT)?,
        ))
    }

    /// Wrap `path` as a `FixedJoint` if it is typed `PhysicsFixedJoint`
    /// (C++ `UsdPhysicsFixedJoint::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_PHYSICS_FIXED_JOINT).map(|o| o.map(Self))
    }
}

impl_physics_schema!(joint FixedJoint);

/// A hinge that rotates about a single axis (C++ `UsdPhysicsRevoluteJoint`),
/// optionally limited to an angular range.
#[derive(Clone, derive_more::Deref)]
pub struct RevoluteJoint(Prim);

impl RevoluteJoint {
    /// Author a `def PhysicsRevoluteJoint` prim at `path`
    /// (C++ `UsdPhysicsRevoluteJoint::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.define_prim(path)?.set_type_name(tok::T_PHYSICS_REVOLUTE_JOINT)?,
        ))
    }

    /// Wrap `path` as a `RevoluteJoint` if it is typed `PhysicsRevoluteJoint`
    /// (C++ `UsdPhysicsRevoluteJoint::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_PHYSICS_REVOLUTE_JOINT).map(|o| o.map(Self))
    }

    /// The body-0-local axis the joint rotates about (`X`, `Y`, or `Z`).
    /// C++ `UsdPhysicsRevoluteJoint::GetAxisAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<`[`JointAxis`](super::JointAxis)`>()?`.
    pub fn axis_attr(&self) -> Attribute {
        self.attribute(tok::A_AXIS)
    }

    /// Author `physics:axis` (`uniform token`) (C++ `CreateAxisAttr`).
    pub fn create_axis_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_AXIS, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The lower rotation limit in degrees; if it exceeds the upper limit the
    /// rotation is unlimited. C++ `UsdPhysicsRevoluteJoint::GetLowerLimitAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn lower_limit_attr(&self) -> Attribute {
        self.attribute(tok::A_LOWER_LIMIT)
    }

    /// Author `physics:lowerLimit` (`float`, degrees) (C++ `CreateLowerLimitAttr`).
    pub fn create_lower_limit_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_LOWER_LIMIT, "float")?.set_custom(false)?)
    }

    /// The upper rotation limit in degrees. C++ `UsdPhysicsRevoluteJoint::GetUpperLimitAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn upper_limit_attr(&self) -> Attribute {
        self.attribute(tok::A_UPPER_LIMIT)
    }

    /// Author `physics:upperLimit` (`float`, degrees) (C++ `CreateUpperLimitAttr`).
    pub fn create_upper_limit_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_UPPER_LIMIT, "float")?.set_custom(false)?)
    }
}

impl_physics_schema!(joint RevoluteJoint);

/// A slider that translates along a single axis (C++ `UsdPhysicsPrismaticJoint`),
/// optionally limited to a distance range.
#[derive(Clone, derive_more::Deref)]
pub struct PrismaticJoint(Prim);

impl PrismaticJoint {
    /// Author a `def PhysicsPrismaticJoint` prim at `path`
    /// (C++ `UsdPhysicsPrismaticJoint::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.define_prim(path)?.set_type_name(tok::T_PHYSICS_PRISMATIC_JOINT)?,
        ))
    }

    /// Wrap `path` as a `PrismaticJoint` if it is typed `PhysicsPrismaticJoint`
    /// (C++ `UsdPhysicsPrismaticJoint::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_PHYSICS_PRISMATIC_JOINT).map(|o| o.map(Self))
    }

    /// The body-0-local axis the joint slides along (`X`, `Y`, or `Z`).
    /// C++ `UsdPhysicsPrismaticJoint::GetAxisAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<`[`JointAxis`](super::JointAxis)`>()?`.
    pub fn axis_attr(&self) -> Attribute {
        self.attribute(tok::A_AXIS)
    }

    /// Author `physics:axis` (`uniform token`) (C++ `CreateAxisAttr`).
    pub fn create_axis_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_AXIS, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The lower translation limit in scene units; if it exceeds the upper limit
    /// the translation is unlimited. C++ `UsdPhysicsPrismaticJoint::GetLowerLimitAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn lower_limit_attr(&self) -> Attribute {
        self.attribute(tok::A_LOWER_LIMIT)
    }

    /// Author `physics:lowerLimit` (`float`, scene units) (C++ `CreateLowerLimitAttr`).
    pub fn create_lower_limit_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_LOWER_LIMIT, "float")?.set_custom(false)?)
    }

    /// The upper translation limit in scene units.
    /// C++ `UsdPhysicsPrismaticJoint::GetUpperLimitAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn upper_limit_attr(&self) -> Attribute {
        self.attribute(tok::A_UPPER_LIMIT)
    }

    /// Author `physics:upperLimit` (`float`, scene units) (C++ `CreateUpperLimitAttr`).
    pub fn create_upper_limit_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_UPPER_LIMIT, "float")?.set_custom(false)?)
    }
}

impl_physics_schema!(joint PrismaticJoint);

/// A ball joint that removes the linear DOFs, leaving rotation constrained by a
/// cone (C++ `UsdPhysicsSphericalJoint`).
#[derive(Clone, derive_more::Deref)]
pub struct SphericalJoint(Prim);

impl SphericalJoint {
    /// Author a `def PhysicsSphericalJoint` prim at `path`
    /// (C++ `UsdPhysicsSphericalJoint::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.define_prim(path)?.set_type_name(tok::T_PHYSICS_SPHERICAL_JOINT)?,
        ))
    }

    /// Wrap `path` as a `SphericalJoint` if it is typed `PhysicsSphericalJoint`
    /// (C++ `UsdPhysicsSphericalJoint::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_PHYSICS_SPHERICAL_JOINT).map(|o| o.map(Self))
    }

    /// The cone's primary axis, about which the two cone-angle limits are
    /// measured. C++ `UsdPhysicsSphericalJoint::GetAxisAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<`[`JointAxis`](super::JointAxis)`>()?`.
    pub fn axis_attr(&self) -> Attribute {
        self.attribute(tok::A_AXIS)
    }

    /// Author `physics:axis` (`uniform token`) (C++ `CreateAxisAttr`).
    pub fn create_axis_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_AXIS, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The cone half-angle limit (degrees) in the first swing direction; `-1`
    /// means unlimited. C++ `UsdPhysicsSphericalJoint::GetConeAngle0LimitAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn cone_angle0_limit_attr(&self) -> Attribute {
        self.attribute(tok::A_CONE_ANGLE_0_LIMIT)
    }

    /// Author `physics:coneAngle0Limit` (`float`, degrees) (C++ `CreateConeAngle0LimitAttr`).
    pub fn create_cone_angle0_limit_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CONE_ANGLE_0_LIMIT, "float")?
            .set_custom(false)?)
    }

    /// The cone half-angle limit (degrees) in the second swing direction; `-1`
    /// means unlimited. C++ `UsdPhysicsSphericalJoint::GetConeAngle1LimitAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn cone_angle1_limit_attr(&self) -> Attribute {
        self.attribute(tok::A_CONE_ANGLE_1_LIMIT)
    }

    /// Author `physics:coneAngle1Limit` (`float`, degrees) (C++ `CreateConeAngle1LimitAttr`).
    pub fn create_cone_angle1_limit_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CONE_ANGLE_1_LIMIT, "float")?
            .set_custom(false)?)
    }
}

impl_physics_schema!(joint SphericalJoint);

/// A joint that keeps two attachment points within a distance range (C++
/// `UsdPhysicsDistanceJoint`).
#[derive(Clone, derive_more::Deref)]
pub struct DistanceJoint(Prim);

impl DistanceJoint {
    /// Author a `def PhysicsDistanceJoint` prim at `path`
    /// (C++ `UsdPhysicsDistanceJoint::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.define_prim(path)?.set_type_name(tok::T_PHYSICS_DISTANCE_JOINT)?,
        ))
    }

    /// Wrap `path` as a `DistanceJoint` if it is typed `PhysicsDistanceJoint`
    /// (C++ `UsdPhysicsDistanceJoint::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_PHYSICS_DISTANCE_JOINT).map(|o| o.map(Self))
    }

    /// The minimum allowed distance between the attachment points; a negative
    /// value disables the minimum. C++ `UsdPhysicsDistanceJoint::GetMinDistanceAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn min_distance_attr(&self) -> Attribute {
        self.attribute(tok::A_MIN_DISTANCE)
    }

    /// Author `physics:minDistance` (`float`) (C++ `CreateMinDistanceAttr`).
    pub fn create_min_distance_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_MIN_DISTANCE, "float")?.set_custom(false)?)
    }

    /// The maximum allowed distance between the attachment points; a negative
    /// value disables the maximum. C++ `UsdPhysicsDistanceJoint::GetMaxDistanceAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn max_distance_attr(&self) -> Attribute {
        self.attribute(tok::A_MAX_DISTANCE)
    }

    /// Author `physics:maxDistance` (`float`) (C++ `CreateMaxDistanceAttr`).
    pub fn create_max_distance_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_MAX_DISTANCE, "float")?.set_custom(false)?)
    }
}

impl_physics_schema!(joint DistanceJoint);

/// Marks a prim as a rigid body driven by the simulation (C++
/// `UsdPhysicsRigidBodyAPI`, applied to a `UsdGeomXformable`).
#[derive(Clone, derive_more::Deref)]
pub struct RigidBodyAPI(Prim);

impl RigidBodyAPI {
    /// Apply `PhysicsRigidBodyAPI` to the prim at `path`
    /// (C++ `UsdPhysicsRigidBodyAPI::Apply`). The prim is opened as `over`.
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.override_prim(path)?.add_applied_schema(tok::API_RIGID_BODY)?,
        ))
    }

    /// Wrap `path` as a `RigidBodyAPI` if it carries `PhysicsRigidBodyAPI` in its
    /// `apiSchemas` (C++ `UsdPhysicsRigidBodyAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_RIGID_BODY]).map(|o| o.map(Self))
    }

    /// Whether the body participates in dynamics; `false` leaves it in the scene
    /// but inert. C++ `UsdPhysicsRigidBodyAPI::GetRigidBodyEnabledAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    pub fn rigid_body_enabled_attr(&self) -> Attribute {
        self.attribute(tok::A_RIGID_BODY_ENABLED)
    }

    /// Author `physics:rigidBodyEnabled` (`bool`) (C++ `CreateRigidBodyEnabledAttr`).
    pub fn create_rigid_body_enabled_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_RIGID_BODY_ENABLED, "bool")?
            .set_custom(false)?)
    }

    /// Whether the body is kinematic — moved by its animated transform and not
    /// by forces. C++ `UsdPhysicsRigidBodyAPI::GetKinematicEnabledAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    pub fn kinematic_enabled_attr(&self) -> Attribute {
        self.attribute(tok::A_KINEMATIC_ENABLED)
    }

    /// Author `physics:kinematicEnabled` (`bool`) (C++ `CreateKinematicEnabledAttr`).
    pub fn create_kinematic_enabled_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_KINEMATIC_ENABLED, "bool")?
            .set_custom(false)?)
    }

    /// Whether the body starts the simulation asleep (inactive until disturbed).
    /// C++ `UsdPhysicsRigidBodyAPI::GetStartsAsleepAttr`.
    ///
    /// Type `uniform bool`. Fetch with `get::<bool>()?`.
    pub fn starts_asleep_attr(&self) -> Attribute {
        self.attribute(tok::A_STARTS_ASLEEP)
    }

    /// Author `physics:startsAsleep` (`uniform bool`) (C++ `CreateStartsAsleepAttr`).
    pub fn create_starts_asleep_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_STARTS_ASLEEP, "bool")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The body's initial linear velocity in scene units per second.
    /// C++ `UsdPhysicsRigidBodyAPI::GetVelocityAttr`.
    ///
    /// Type `vector3f`. Fetch with `get::<[f32; 3]>()?`.
    pub fn velocity_attr(&self) -> Attribute {
        self.attribute(tok::A_VELOCITY)
    }

    /// Author `physics:velocity` (`vector3f`) (C++ `CreateVelocityAttr`).
    pub fn create_velocity_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_VELOCITY, "vector3f")?.set_custom(false)?)
    }

    /// The body's initial angular velocity in degrees per second.
    /// C++ `UsdPhysicsRigidBodyAPI::GetAngularVelocityAttr`.
    ///
    /// Type `vector3f`. Fetch with `get::<[f32; 3]>()?`.
    pub fn angular_velocity_attr(&self) -> Attribute {
        self.attribute(tok::A_ANGULAR_VELOCITY)
    }

    /// Author `physics:angularVelocity` (`vector3f`, deg/s)
    /// (C++ `CreateAngularVelocityAttr`).
    pub fn create_angular_velocity_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_ANGULAR_VELOCITY, "vector3f")?
            .set_custom(false)?)
    }

    /// The `PhysicsScene`(s) that simulate this body; empty means any scene may
    /// claim it. C++ `UsdPhysicsRigidBodyAPI::GetSimulationOwnerRel`.
    pub fn simulation_owner_rel(&self) -> Relationship {
        self.relationship(tok::A_SIMULATION_OWNER)
    }

    /// Author the `physics:simulationOwner` relationship
    /// (C++ `CreateSimulationOwnerRel`).
    pub fn create_simulation_owner_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::A_SIMULATION_OWNER)?.set_custom(false)?)
    }
}

impl_physics_schema!(single_api RigidBodyAPI);

/// Explicit mass properties for a body (C++ `UsdPhysicsMassAPI`); unauthored
/// values are derived from the collision geometry and density.
#[derive(Clone, derive_more::Deref)]
pub struct MassAPI(Prim);

impl MassAPI {
    /// Apply `PhysicsMassAPI` to the prim at `path` (C++ `UsdPhysicsMassAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.override_prim(path)?.add_applied_schema(tok::API_MASS)?))
    }

    /// Wrap `path` as a `MassAPI` if it carries `PhysicsMassAPI`
    /// (C++ `UsdPhysicsMassAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_MASS]).map(|o| o.map(Self))
    }

    /// The body's mass in scene mass units; overrides the density-derived mass.
    /// C++ `UsdPhysicsMassAPI::GetMassAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn mass_attr(&self) -> Attribute {
        self.attribute(tok::A_MASS)
    }

    /// Author `physics:mass` (`float`) (C++ `CreateMassAttr`).
    pub fn create_mass_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_MASS, "float")?.set_custom(false)?)
    }

    /// Material density used to derive mass when `mass` is unauthored, in scene
    /// mass units per cubed scene unit. C++ `UsdPhysicsMassAPI::GetDensityAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn density_attr(&self) -> Attribute {
        self.attribute(tok::A_DENSITY)
    }

    /// Author `physics:density` (`float`) (C++ `CreateDensityAttr`).
    pub fn create_density_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_DENSITY, "float")?.set_custom(false)?)
    }

    /// The center of mass in the body's local space.
    /// C++ `UsdPhysicsMassAPI::GetCenterOfMassAttr`.
    ///
    /// Type `point3f`. Fetch with `get::<[f32; 3]>()?`.
    pub fn center_of_mass_attr(&self) -> Attribute {
        self.attribute(tok::A_CENTER_OF_MASS)
    }

    /// Author `physics:centerOfMass` (`point3f`) (C++ `CreateCenterOfMassAttr`).
    pub fn create_center_of_mass_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CENTER_OF_MASS, "point3f")?
            .set_custom(false)?)
    }

    /// The diagonal of the inertia tensor in the principal-axes frame.
    /// C++ `UsdPhysicsMassAPI::GetDiagonalInertiaAttr`.
    ///
    /// Type `float3`. Fetch with `get::<[f32; 3]>()?`.
    pub fn diagonal_inertia_attr(&self) -> Attribute {
        self.attribute(tok::A_DIAGONAL_INERTIA)
    }

    /// Author `physics:diagonalInertia` (`float3`) (C++ `CreateDiagonalInertiaAttr`).
    pub fn create_diagonal_inertia_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_DIAGONAL_INERTIA, "float3")?
            .set_custom(false)?)
    }

    /// The orientation of the principal-axes (inertia) frame, as a quaternion.
    /// C++ `UsdPhysicsMassAPI::GetPrincipalAxesAttr`.
    ///
    /// Type `quatf`. Fetch with `get::<[f32; 4]>()?` (a `(w, x, y, z)` quat).
    pub fn principal_axes_attr(&self) -> Attribute {
        self.attribute(tok::A_PRINCIPAL_AXES)
    }

    /// Author `physics:principalAxes` (`quatf`) (C++ `CreatePrincipalAxesAttr`).
    pub fn create_principal_axes_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_PRINCIPAL_AXES, "quatf")?
            .set_custom(false)?)
    }
}

impl_physics_schema!(single_api MassAPI);

/// Enables collision on a prim's geometry (C++ `UsdPhysicsCollisionAPI`, applied
/// to a `UsdGeomGprim`).
#[derive(Clone, derive_more::Deref)]
pub struct CollisionAPI(Prim);

impl CollisionAPI {
    /// Apply `PhysicsCollisionAPI` to the prim at `path`
    /// (C++ `UsdPhysicsCollisionAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.override_prim(path)?.add_applied_schema(tok::API_COLLISION)?))
    }

    /// Wrap `path` as a `CollisionAPI` if it carries `PhysicsCollisionAPI`
    /// (C++ `UsdPhysicsCollisionAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_COLLISION]).map(|o| o.map(Self))
    }

    /// Whether collision is active for this geometry; applying the API implies
    /// enabled unless set `false`. C++ `UsdPhysicsCollisionAPI::GetCollisionEnabledAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    pub fn collision_enabled_attr(&self) -> Attribute {
        self.attribute(tok::A_COLLISION_ENABLED)
    }

    /// Author `physics:collisionEnabled` (`bool`) (C++ `CreateCollisionEnabledAttr`).
    pub fn create_collision_enabled_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_COLLISION_ENABLED, "bool")?
            .set_custom(false)?)
    }
}

impl_physics_schema!(single_api CollisionAPI);

/// Controls how a mesh's collision shape is approximated (C++
/// `UsdPhysicsMeshCollisionAPI`, applied alongside `CollisionAPI` on a `Mesh`).
#[derive(Clone, derive_more::Deref)]
pub struct MeshCollisionAPI(Prim);

impl MeshCollisionAPI {
    /// Apply `PhysicsMeshCollisionAPI` to the prim at `path`
    /// (C++ `UsdPhysicsMeshCollisionAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.override_prim(path)?.add_applied_schema(tok::API_MESH_COLLISION)?,
        ))
    }

    /// Wrap `path` as a `MeshCollisionAPI` if it carries `PhysicsMeshCollisionAPI`
    /// (C++ `UsdPhysicsMeshCollisionAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_MESH_COLLISION]).map(|o| o.map(Self))
    }

    /// The strategy used to turn the mesh into a collision shape (e.g. a convex
    /// hull, a convex decomposition, or a bounding primitive).
    /// C++ `UsdPhysicsMeshCollisionAPI::GetApproximationAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<`[`CollisionApprox`](super::CollisionApprox)`>()?`.
    pub fn approximation_attr(&self) -> Attribute {
        self.attribute(tok::A_APPROXIMATION)
    }

    /// Author `physics:approximation` (`uniform token`) (C++ `CreateApproximationAttr`).
    pub fn create_approximation_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_APPROXIMATION, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_physics_schema!(single_api MeshCollisionAPI);

/// Physics material properties (C++ `UsdPhysicsMaterialAPI`, applied to a
/// `UsdShadeMaterial`) — friction, restitution, and density.
#[derive(Clone, derive_more::Deref)]
pub struct MaterialAPI(Prim);

impl MaterialAPI {
    /// Apply `PhysicsMaterialAPI` to the prim at `path`
    /// (C++ `UsdPhysicsMaterialAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage
                .override_prim(path)?
                .add_applied_schema(tok::API_PHYSICS_MATERIAL)?,
        ))
    }

    /// Wrap `path` as a `MaterialAPI` if it carries `PhysicsMaterialAPI`
    /// (C++ `UsdPhysicsMaterialAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_PHYSICS_MATERIAL]).map(|o| o.map(Self))
    }

    /// The kinetic friction coefficient applied while surfaces slide.
    /// C++ `UsdPhysicsMaterialAPI::GetDynamicFrictionAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn dynamic_friction_attr(&self) -> Attribute {
        self.attribute(tok::A_DYNAMIC_FRICTION)
    }

    /// Author `physics:dynamicFriction` (`float`) (C++ `CreateDynamicFrictionAttr`).
    pub fn create_dynamic_friction_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_DYNAMIC_FRICTION, "float")?
            .set_custom(false)?)
    }

    /// The static friction coefficient resisting the onset of sliding.
    /// C++ `UsdPhysicsMaterialAPI::GetStaticFrictionAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn static_friction_attr(&self) -> Attribute {
        self.attribute(tok::A_STATIC_FRICTION)
    }

    /// Author `physics:staticFriction` (`float`) (C++ `CreateStaticFrictionAttr`).
    pub fn create_static_friction_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_STATIC_FRICTION, "float")?
            .set_custom(false)?)
    }

    /// The bounciness of the material, from `0` (no bounce) to `1` (elastic).
    /// C++ `UsdPhysicsMaterialAPI::GetRestitutionAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn restitution_attr(&self) -> Attribute {
        self.attribute(tok::A_RESTITUTION)
    }

    /// Author `physics:restitution` (`float`) (C++ `CreateRestitutionAttr`).
    pub fn create_restitution_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_RESTITUTION, "float")?.set_custom(false)?)
    }

    /// The material's mass density, used to derive body mass from collision
    /// volume. C++ `UsdPhysicsMaterialAPI::GetDensityAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn density_attr(&self) -> Attribute {
        self.attribute(tok::A_DENSITY)
    }

    /// Author `physics:density` (`float`) (C++ `CreateDensityAttr`).
    pub fn create_density_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_DENSITY, "float")?.set_custom(false)?)
    }
}

impl_physics_schema!(single_api MaterialAPI);

/// Marks the root of a subtree the simulator should treat as a reduced-coordinate
/// articulation (C++ `UsdPhysicsArticulationRootAPI`). A marker schema with no
/// attributes of its own.
#[derive(Clone, derive_more::Deref)]
pub struct ArticulationRootAPI(Prim);

impl ArticulationRootAPI {
    /// Apply `PhysicsArticulationRootAPI` to the prim at `path`
    /// (C++ `UsdPhysicsArticulationRootAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage
                .override_prim(path)?
                .add_applied_schema(tok::API_ARTICULATION_ROOT)?,
        ))
    }

    /// Wrap `path` as an `ArticulationRootAPI` if it carries
    /// `PhysicsArticulationRootAPI` (C++ `UsdPhysicsArticulationRootAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_ARTICULATION_ROOT]).map(|o| o.map(Self))
    }
}

impl_physics_schema!(single_api ArticulationRootAPI);

/// Disables collision between specific prim pairs (C++ `UsdPhysicsFilteredPairsAPI`).
#[derive(Clone, derive_more::Deref)]
pub struct FilteredPairsAPI(Prim);

impl FilteredPairsAPI {
    /// Apply `PhysicsFilteredPairsAPI` to the prim at `path`
    /// (C++ `UsdPhysicsFilteredPairsAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.override_prim(path)?.add_applied_schema(tok::API_FILTERED_PAIRS)?,
        ))
    }

    /// Wrap `path` as a `FilteredPairsAPI` if it carries `PhysicsFilteredPairsAPI`
    /// (C++ `UsdPhysicsFilteredPairsAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_FILTERED_PAIRS]).map(|o| o.map(Self))
    }

    /// The prims this prim should never collide with (filtering is symmetric).
    /// C++ `UsdPhysicsFilteredPairsAPI::GetFilteredPairsRel`.
    pub fn filtered_pairs_rel(&self) -> Relationship {
        self.relationship(tok::A_FILTERED_PAIRS)
    }

    /// Author the `physics:filteredPairs` relationship (C++ `CreateFilteredPairsRel`).
    pub fn create_filtered_pairs_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::A_FILTERED_PAIRS)?.set_custom(false)?)
    }
}

impl_physics_schema!(single_api FilteredPairsAPI);

/// A spring-damper actuator on one joint degree of freedom (C++
/// `UsdPhysicsDriveAPI`, multiple-apply). The instance name is the DOF (e.g.
/// `rotX`, `linear`); it applies as `PhysicsDriveAPI:<dof>` and its attributes
/// live at `drive:<dof>:physics:*`.
#[derive(Clone, derive_more::Deref)]
pub struct DriveAPI {
    #[deref]
    prim: Prim,
    name: String,
}

impl DriveAPI {
    /// Apply `PhysicsDriveAPI:<name>` to the prim at `path`
    /// (C++ `UsdPhysicsDriveAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>, name: &str) -> Result<Self> {
        let prim = stage
            .override_prim(path)?
            .add_applied_schema(format!("{}:{name}", tok::API_DRIVE))?;
        Ok(Self {
            prim,
            name: name.to_string(),
        })
    }

    /// Wrap `path` as a `DriveAPI` for instance `name` if the prim carries
    /// `PhysicsDriveAPI:<name>` (C++ `UsdPhysicsDriveAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>, name: &str) -> Result<Option<Self>> {
        let api = format!("{}:{name}", tok::API_DRIVE);
        Ok(get_with_api(stage, path, &[api.as_str()])?.map(|prim| Self {
            prim,
            name: name.to_string(),
        }))
    }

    /// Every `PhysicsDriveAPI` instance applied to the prim at `path`, one per
    /// driven DOF (C++ `UsdPhysicsDriveAPI::GetAll`).
    pub fn get_all(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Vec<Self>> {
        let path = path.into();
        let prefix = format!("{}:", tok::API_DRIVE);
        Ok(stage
            .api_schemas(&path)?
            .into_iter()
            .filter_map(|s| s.strip_prefix(&prefix).map(str::to_string))
            .map(|name| Self {
                prim: stage.prim_at_path(path.clone()),
                name,
            })
            .collect())
    }

    /// The DOF instance name this drive acts on, e.g. `rotX`
    /// (C++ `UsdPhysicsDriveAPI::GetName`).
    pub fn name(&self) -> &str {
        &self.name
    }

    fn prop(&self, sub: &str) -> String {
        format!("drive:{}:physics:{sub}", self.name)
    }

    /// Whether the drive applies a `force` or a mass-independent `acceleration`.
    /// C++ `UsdPhysicsDriveAPI::GetTypeAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<`[`DriveType`](super::DriveType)`>()?`.
    pub fn type_attr(&self) -> Attribute {
        self.attribute(&self.prop(tok::DRIVE_SUB_TYPE))
    }

    /// Author `drive:<dof>:physics:type` (`uniform token`) (C++ `CreateTypeAttr`).
    pub fn create_type_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim
            .create_attribute(&self.prop(tok::DRIVE_SUB_TYPE), "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The drive's target position the spring pulls the DOF toward (degrees for
    /// angular DOFs, scene units for linear). C++ `UsdPhysicsDriveAPI::GetTargetPositionAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn target_position_attr(&self) -> Attribute {
        self.attribute(&self.prop(tok::DRIVE_SUB_TARGET_POSITION))
    }

    /// Author `drive:<dof>:physics:targetPosition` (`float`) (C++ `CreateTargetPositionAttr`).
    pub fn create_target_position_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim
            .create_attribute(&self.prop(tok::DRIVE_SUB_TARGET_POSITION), "float")?
            .set_custom(false)?)
    }

    /// The drive's target velocity the damper drives the DOF toward.
    /// C++ `UsdPhysicsDriveAPI::GetTargetVelocityAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn target_velocity_attr(&self) -> Attribute {
        self.attribute(&self.prop(tok::DRIVE_SUB_TARGET_VELOCITY))
    }

    /// Author `drive:<dof>:physics:targetVelocity` (`float`) (C++ `CreateTargetVelocityAttr`).
    pub fn create_target_velocity_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim
            .create_attribute(&self.prop(tok::DRIVE_SUB_TARGET_VELOCITY), "float")?
            .set_custom(false)?)
    }

    /// The damper gain — force per unit velocity error.
    /// C++ `UsdPhysicsDriveAPI::GetDampingAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn damping_attr(&self) -> Attribute {
        self.attribute(&self.prop(tok::DRIVE_SUB_DAMPING))
    }

    /// Author `drive:<dof>:physics:damping` (`float`) (C++ `CreateDampingAttr`).
    pub fn create_damping_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim
            .create_attribute(&self.prop(tok::DRIVE_SUB_DAMPING), "float")?
            .set_custom(false)?)
    }

    /// The spring gain — force per unit position error.
    /// C++ `UsdPhysicsDriveAPI::GetStiffnessAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn stiffness_attr(&self) -> Attribute {
        self.attribute(&self.prop(tok::DRIVE_SUB_STIFFNESS))
    }

    /// Author `drive:<dof>:physics:stiffness` (`float`) (C++ `CreateStiffnessAttr`).
    pub fn create_stiffness_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim
            .create_attribute(&self.prop(tok::DRIVE_SUB_STIFFNESS), "float")?
            .set_custom(false)?)
    }

    /// The maximum force the drive may apply (default infinity — unlimited).
    /// C++ `UsdPhysicsDriveAPI::GetMaxForceAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn max_force_attr(&self) -> Attribute {
        self.attribute(&self.prop(tok::DRIVE_SUB_MAX_FORCE))
    }

    /// Author `drive:<dof>:physics:maxForce` (`float`) (C++ `CreateMaxForceAttr`).
    pub fn create_max_force_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim
            .create_attribute(&self.prop(tok::DRIVE_SUB_MAX_FORCE), "float")?
            .set_custom(false)?)
    }
}

impl_physics_schema!(multi_api DriveAPI);

/// A motion limit on one joint degree of freedom (C++ `UsdPhysicsLimitAPI`,
/// multiple-apply). The instance name is the DOF; it applies as
/// `PhysicsLimitAPI:<dof>` with attributes at `limit:<dof>:physics:*`.
/// `low > high` locks the DOF.
#[derive(Clone, derive_more::Deref)]
pub struct LimitAPI {
    #[deref]
    prim: Prim,
    name: String,
}

impl LimitAPI {
    /// Apply `PhysicsLimitAPI:<name>` to the prim at `path`
    /// (C++ `UsdPhysicsLimitAPI::Apply`).
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>, name: &str) -> Result<Self> {
        let prim = stage
            .override_prim(path)?
            .add_applied_schema(format!("{}:{name}", tok::API_LIMIT))?;
        Ok(Self {
            prim,
            name: name.to_string(),
        })
    }

    /// Wrap `path` as a `LimitAPI` for instance `name` if the prim carries
    /// `PhysicsLimitAPI:<name>` (C++ `UsdPhysicsLimitAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>, name: &str) -> Result<Option<Self>> {
        let api = format!("{}:{name}", tok::API_LIMIT);
        Ok(get_with_api(stage, path, &[api.as_str()])?.map(|prim| Self {
            prim,
            name: name.to_string(),
        }))
    }

    /// Every `PhysicsLimitAPI` instance applied to the prim at `path`, one per
    /// limited DOF (C++ `UsdPhysicsLimitAPI::GetAll`).
    pub fn get_all(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Vec<Self>> {
        let path = path.into();
        let prefix = format!("{}:", tok::API_LIMIT);
        Ok(stage
            .api_schemas(&path)?
            .into_iter()
            .filter_map(|s| s.strip_prefix(&prefix).map(str::to_string))
            .map(|name| Self {
                prim: stage.prim_at_path(path.clone()),
                name,
            })
            .collect())
    }

    /// The DOF instance name this limit acts on, e.g. `rotX`
    /// (C++ `UsdPhysicsLimitAPI::GetName`).
    pub fn name(&self) -> &str {
        &self.name
    }

    fn prop(&self, sub: &str) -> String {
        format!("limit:{}:physics:{sub}", self.name)
    }

    /// The lower bound of the DOF's allowed range (default -inf, no lower limit).
    /// C++ `UsdPhysicsLimitAPI::GetLowAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn low_attr(&self) -> Attribute {
        self.attribute(&self.prop(tok::LIMIT_SUB_LOW))
    }

    /// Author `limit:<dof>:physics:low` (`float`) (C++ `CreateLowAttr`).
    pub fn create_low_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim
            .create_attribute(&self.prop(tok::LIMIT_SUB_LOW), "float")?
            .set_custom(false)?)
    }

    /// The upper bound of the DOF's allowed range (default +inf, no upper limit).
    /// C++ `UsdPhysicsLimitAPI::GetHighAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    pub fn high_attr(&self) -> Attribute {
        self.attribute(&self.prop(tok::LIMIT_SUB_HIGH))
    }

    /// Author `limit:<dof>:physics:high` (`float`) (C++ `CreateHighAttr`).
    pub fn create_high_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim
            .create_attribute(&self.prop(tok::LIMIT_SUB_HIGH), "float")?
            .set_custom(false)?)
    }
}

impl_physics_schema!(multi_api LimitAPI);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::physics::{CollisionApprox, DriveType, JointAxis, JointBase};

    #[test]
    fn scene_and_joint_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;

        let scene = Scene::define(&stage, "/World/Scene")?;
        scene.create_gravity_magnitude_attr()?.set(981.0_f32)?;

        let hinge = RevoluteJoint::define(&stage, "/World/Hinge")?;
        hinge.create_axis_attr()?.set(JointAxis::Z)?;
        // Inherited from JointBase.
        hinge.create_break_force_attr()?.set(500.0_f32)?;

        let scene = Scene::get(&stage, "/World/Scene")?.expect("Scene");
        assert_eq!(scene.gravity_magnitude_attr().get::<f32>()?, Some(981.0));

        let hinge = RevoluteJoint::get(&stage, "/World/Hinge")?.expect("RevoluteJoint");
        assert_eq!(hinge.axis_attr().get::<JointAxis>()?, Some(JointAxis::Z));
        assert_eq!(hinge.break_force_attr().get::<f32>()?, Some(500.0));

        // A RevoluteJoint is not a Joint, Scene, or other typed prim.
        assert!(Joint::get(&stage, "/World/Hinge")?.is_none());
        Ok(())
    }

    #[test]
    fn applied_apis_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/World/Box")?.set_type_name("Cube")?;

        let body = RigidBodyAPI::apply(&stage, "/World/Box")?;
        body.create_rigid_body_enabled_attr()?.set(true)?;
        MassAPI::apply(&stage, "/World/Box")?.create_mass_attr()?.set(2.5_f32)?;
        MeshCollisionAPI::apply(&stage, "/World/Box")?
            .create_approximation_attr()?
            .set(CollisionApprox::ConvexHull)?;

        let body = RigidBodyAPI::get(&stage, "/World/Box")?.expect("RigidBodyAPI");
        assert_eq!(body.rigid_body_enabled_attr().get::<bool>()?, Some(true));
        assert_eq!(
            MassAPI::get(&stage, "/World/Box")?
                .expect("MassAPI")
                .mass_attr()
                .get::<f32>()?,
            Some(2.5)
        );
        assert_eq!(
            MeshCollisionAPI::get(&stage, "/World/Box")?
                .expect("MeshCollisionAPI")
                .approximation_attr()
                .get::<CollisionApprox>()?,
            Some(CollisionApprox::ConvexHull)
        );

        // Not applied → None.
        assert!(CollisionAPI::get(&stage, "/World/Box")?.is_none());
        Ok(())
    }

    #[test]
    fn multi_apply_drive_and_limit() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let joint = Joint::define(&stage, "/World/D6")?;

        DriveAPI::apply(&stage, joint.path().clone(), "rotX")?
            .create_type_attr()?
            .set(DriveType::Acceleration)?;
        DriveAPI::apply(&stage, "/World/D6", "rotY")?
            .create_target_position_attr()?
            .set(45.0_f32)?;

        let limit = LimitAPI::apply(&stage, "/World/D6", "rotX")?;
        limit.create_low_attr()?.set(-30.0_f32)?;
        limit.create_high_attr()?.set(30.0_f32)?;

        let drive = DriveAPI::get(&stage, "/World/D6", "rotX")?.expect("DriveAPI:rotX");
        assert_eq!(drive.name(), "rotX");
        assert_eq!(drive.type_attr().get::<DriveType>()?, Some(DriveType::Acceleration));

        let limit = LimitAPI::get(&stage, "/World/D6", "rotX")?.expect("LimitAPI:rotX");
        assert_eq!(limit.low_attr().get::<f32>()?, Some(-30.0));
        assert_eq!(limit.high_attr().get::<f32>()?, Some(30.0));

        // `get_all` enumerates every applied instance.
        let mut drives: Vec<String> = DriveAPI::get_all(&stage, "/World/D6")?
            .iter()
            .map(|d| d.name().to_string())
            .collect();
        drives.sort();
        assert_eq!(drives, vec!["rotX".to_string(), "rotY".to_string()]);
        assert_eq!(LimitAPI::get_all(&stage, "/World/D6")?.len(), 1);

        // A different DOF instance is absent.
        assert!(DriveAPI::get(&stage, "/World/D6", "rotZ")?.is_none());
        Ok(())
    }
}
