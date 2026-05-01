//! Token constants for the [UsdPhysics](super) schema family.
//!
//! Centralised so consumers can match against canonical strings instead of
//! retyping literals. Mirrors the grouping in Pixar's
//! `pxr/usd/usdPhysics/tokens.h`.

// Concrete prim type names.
pub const T_PHYSICS_SCENE: &str = "PhysicsScene";
pub const T_PHYSICS_JOINT: &str = "PhysicsJoint";
pub const T_PHYSICS_FIXED_JOINT: &str = "PhysicsFixedJoint";
pub const T_PHYSICS_REVOLUTE_JOINT: &str = "PhysicsRevoluteJoint";
pub const T_PHYSICS_PRISMATIC_JOINT: &str = "PhysicsPrismaticJoint";
pub const T_PHYSICS_SPHERICAL_JOINT: &str = "PhysicsSphericalJoint";
pub const T_PHYSICS_DISTANCE_JOINT: &str = "PhysicsDistanceJoint";
pub const T_PHYSICS_COLLISION_GROUP: &str = "PhysicsCollisionGroup";

// API schemas (single-apply unless noted).
pub const API_RIGID_BODY: &str = "PhysicsRigidBodyAPI";
pub const API_MASS: &str = "PhysicsMassAPI";
pub const API_COLLISION: &str = "PhysicsCollisionAPI";
pub const API_MESH_COLLISION: &str = "PhysicsMeshCollisionAPI";
pub const API_ARTICULATION_ROOT: &str = "PhysicsArticulationRootAPI";
pub const API_PHYSICS_MATERIAL: &str = "PhysicsMaterialAPI";
pub const API_FILTERED_PAIRS: &str = "PhysicsFilteredPairsAPI";
/// Multi-apply: applied as `PhysicsLimitAPI:<dof>` per DOF.
pub const API_LIMIT: &str = "PhysicsLimitAPI";
/// Multi-apply: applied as `PhysicsDriveAPI:<dof>` per DOF.
pub const API_DRIVE: &str = "PhysicsDriveAPI";

// Stage metadata.
pub const STAGE_KILOGRAMS_PER_UNIT: &str = "kilogramsPerUnit";

// PhysicsScene attribute names.
pub const A_GRAVITY_DIRECTION: &str = "physics:gravityDirection";
pub const A_GRAVITY_MAGNITUDE: &str = "physics:gravityMagnitude";

// PhysicsRigidBodyAPI attribute names.
pub const A_RIGID_BODY_ENABLED: &str = "physics:rigidBodyEnabled";
pub const A_KINEMATIC_ENABLED: &str = "physics:kinematicEnabled";
pub const A_STARTS_ASLEEP: &str = "physics:startsAsleep";
pub const A_VELOCITY: &str = "physics:velocity";
pub const A_ANGULAR_VELOCITY: &str = "physics:angularVelocity";
pub const A_SIMULATION_OWNER: &str = "physics:simulationOwner";

// PhysicsMassAPI attribute names.
pub const A_MASS: &str = "physics:mass";
pub const A_DENSITY: &str = "physics:density";
pub const A_CENTER_OF_MASS: &str = "physics:centerOfMass";
pub const A_DIAGONAL_INERTIA: &str = "physics:diagonalInertia";
pub const A_PRINCIPAL_AXES: &str = "physics:principalAxes";

// PhysicsCollisionAPI / PhysicsMeshCollisionAPI attribute names.
pub const A_COLLISION_ENABLED: &str = "physics:collisionEnabled";
pub const A_APPROXIMATION: &str = "physics:approximation";

// PhysicsMaterialAPI attribute names.
pub const A_DYNAMIC_FRICTION: &str = "physics:dynamicFriction";
pub const A_STATIC_FRICTION: &str = "physics:staticFriction";
pub const A_RESTITUTION: &str = "physics:restitution";

// Joint base attribute names.
pub const A_BODY0: &str = "physics:body0";
pub const A_BODY1: &str = "physics:body1";
pub const A_LOCAL_POS_0: &str = "physics:localPos0";
pub const A_LOCAL_ROT_0: &str = "physics:localRot0";
pub const A_LOCAL_POS_1: &str = "physics:localPos1";
pub const A_LOCAL_ROT_1: &str = "physics:localRot1";
pub const A_JOINT_ENABLED: &str = "physics:jointEnabled";
/// On a joint, allow collision between the two attached bodies (default false).
pub const A_JOINT_COLLISION_ENABLED: &str = "physics:collisionEnabled";
pub const A_EXCLUDE_FROM_ARTICULATION: &str = "physics:excludeFromArticulation";
pub const A_BREAK_FORCE: &str = "physics:breakForce";
pub const A_BREAK_TORQUE: &str = "physics:breakTorque";

// Single-axis joints (revolute / prismatic).
pub const A_AXIS: &str = "physics:axis";
pub const A_LOWER_LIMIT: &str = "physics:lowerLimit";
pub const A_UPPER_LIMIT: &str = "physics:upperLimit";

// PhysicsSphericalJoint cone limit attribute names.
pub const A_CONE_ANGLE_0_LIMIT: &str = "physics:coneAngle0Limit";
pub const A_CONE_ANGLE_1_LIMIT: &str = "physics:coneAngle1Limit";

// PhysicsDistanceJoint attribute names.
pub const A_MIN_DISTANCE: &str = "physics:minDistance";
pub const A_MAX_DISTANCE: &str = "physics:maxDistance";

// PhysicsCollisionGroup attribute names.
pub const A_FILTERED_GROUPS: &str = "physics:filteredGroups";
pub const A_MERGE_GROUP: &str = "physics:mergeGroup";
pub const A_INVERT_FILTERED_GROUPS: &str = "physics:invertFilteredGroups";

// PhysicsFilteredPairsAPI attribute names.
pub const A_FILTERED_PAIRS: &str = "physics:filteredPairs";

// Material binding relationships. UsdPhysics looks up
// `material:binding:physics` first and falls back to `material:binding`.
pub const REL_MATERIAL_BINDING: &str = "material:binding";
pub const REL_MATERIAL_BINDING_PHYSICS: &str = "material:binding:physics";

// DOF tokens — used as multi-apply instance names on
// `PhysicsLimitAPI:<dof>` and `PhysicsDriveAPI:<dof>`, and as the
// segment in `limit:<dof>:physics:*` / `drive:<dof>:physics:*`.
pub const DOF_TRANS_X: &str = "transX";
pub const DOF_TRANS_Y: &str = "transY";
pub const DOF_TRANS_Z: &str = "transZ";
pub const DOF_ROT_X: &str = "rotX";
pub const DOF_ROT_Y: &str = "rotY";
pub const DOF_ROT_Z: &str = "rotZ";
pub const DOF_LINEAR: &str = "linear";
pub const DOF_ANGULAR: &str = "angular";
pub const DOF_DISTANCE: &str = "distance";

// Collision-approximation tokens authored on `PhysicsMeshCollisionAPI`.
pub const APPROX_NONE: &str = "none";
pub const APPROX_CONVEX_HULL: &str = "convexHull";
pub const APPROX_CONVEX_DECOMPOSITION: &str = "convexDecomposition";
pub const APPROX_BOUNDING_SPHERE: &str = "boundingSphere";
pub const APPROX_BOUNDING_CUBE: &str = "boundingCube";
pub const APPROX_MESH_SIMPLIFICATION: &str = "meshSimplification";

// Joint axis tokens (single-axis joints).
pub const AXIS_X: &str = "X";
pub const AXIS_Y: &str = "Y";
pub const AXIS_Z: &str = "Z";

// Drive type tokens (`PhysicsDriveAPI:<dof>:physics:type`).
pub const DRIVE_TYPE_FORCE: &str = "force";
pub const DRIVE_TYPE_ACCELERATION: &str = "acceleration";

// Drive sub-attribute names. Drives are authored as
// `drive:<dof>:physics:<sub>` per the Pixar spec.
pub const DRIVE_SUB_TYPE: &str = "type";
pub const DRIVE_SUB_TARGET_POSITION: &str = "targetPosition";
pub const DRIVE_SUB_TARGET_VELOCITY: &str = "targetVelocity";
pub const DRIVE_SUB_DAMPING: &str = "damping";
pub const DRIVE_SUB_STIFFNESS: &str = "stiffness";
pub const DRIVE_SUB_MAX_FORCE: &str = "maxForce";

// Limit sub-attribute names (`limit:<dof>:physics:<sub>`).
pub const LIMIT_SUB_LOW: &str = "low";
pub const LIMIT_SUB_HIGH: &str = "high";
