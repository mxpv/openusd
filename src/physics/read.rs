//! Reader functions for the [UsdPhysics](super) schema family.
//!
//! Each `read_*` helper takes a composed [`Stage`] plus the prim
//! [`Path`] to inspect, returns the decoded struct (or [`None`] when
//! the schema isn't applied / the prim isn't of the expected type),
//! or surfaces a `Result` for IO / decode errors.
//!
//! All numeric values stay in the scene's authored units. Quaternions
//! stay in USD's textual `(w, x, y, z)` order. Angles stay in degrees
//! (as USD authors them). Callers apply `metersPerUnit` /
//! `kilogramsPerUnit` and degrees-to-radians at the import boundary.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::Stage;

use super::tokens::*;
use super::types::*;

/// Flattened list of API schemas applied to `prim`.
pub fn read_api_schemas(stage: &Stage, prim: &Path) -> Result<Vec<String>> {
    let raw = stage.field::<Value>(prim.clone(), "apiSchemas")?;
    Ok(match raw {
        Some(Value::TokenListOp(op)) => op.flatten(),
        Some(Value::TokenVec(v)) => v,
        _ => Vec::new(),
    })
}

/// Returns `true` when `PhysicsRigidBodyAPI` is applied to the prim.
pub fn read_has_rigid_body(stage: &Stage, prim: &Path) -> Result<bool> {
    Ok(read_api_schemas(stage, prim)?.iter().any(|s| s == API_RIGID_BODY))
}

/// Returns `true` when `PhysicsCollisionAPI` is applied to the prim.
pub fn read_has_collision(stage: &Stage, prim: &Path) -> Result<bool> {
    Ok(read_api_schemas(stage, prim)?.iter().any(|s| s == API_COLLISION))
}

/// Returns `true` when `PhysicsArticulationRootAPI` is applied to the prim.
pub fn read_has_articulation_root(stage: &Stage, prim: &Path) -> Result<bool> {
    Ok(read_api_schemas(stage, prim)?
        .iter()
        .any(|s| s == API_ARTICULATION_ROOT))
}

/// Returns `true` when the prim is typed `PhysicsScene`. Predicate kept
/// for callers that don't need the gravity attributes; otherwise prefer
/// [`read_physics_scene`].
pub fn read_is_physics_scene(stage: &Stage, prim: &Path) -> Result<bool> {
    Ok(stage.field::<String>(prim.clone(), "typeName")?.as_deref() == Some(T_PHYSICS_SCENE))
}

/// Read `PhysicsRigidBodyAPI` state from a prim. Returns `None` when
/// the API isn't applied.
pub fn read_rigid_body(stage: &Stage, prim: &Path) -> Result<Option<ReadRigidBody>> {
    if !read_api_schemas(stage, prim)?.iter().any(|s| s == API_RIGID_BODY) {
        return Ok(None);
    }
    Ok(Some(ReadRigidBody {
        rigid_body_enabled: read_bool(stage, prim, A_RIGID_BODY_ENABLED)?.unwrap_or(true),
        kinematic_enabled: read_bool(stage, prim, A_KINEMATIC_ENABLED)?.unwrap_or(false),
        starts_asleep: read_bool(stage, prim, A_STARTS_ASLEEP)?.unwrap_or(false),
        velocity: read_vec3f(stage, prim, A_VELOCITY)?,
        angular_velocity: read_vec3f(stage, prim, A_ANGULAR_VELOCITY)?,
        simulation_owner: read_rel_first_target(stage, prim, A_SIMULATION_OWNER)?,
    }))
}

/// Read `PhysicsMassAPI` attributes. Returns `None` when the prim
/// hasn't applied `MassAPI` (so callers can distinguish "unauthored"
/// from "zero mass").
pub fn read_mass(stage: &Stage, prim: &Path) -> Result<Option<ReadMass>> {
    if !read_api_schemas(stage, prim)?.iter().any(|s| s == API_MASS) {
        return Ok(None);
    }
    Ok(Some(ReadMass {
        mass: read_scalar_f32(stage, prim, A_MASS)?,
        center_of_mass: read_vec3f(stage, prim, A_CENTER_OF_MASS)?,
        diagonal_inertia: read_vec3f(stage, prim, A_DIAGONAL_INERTIA)?,
        principal_axes: read_quatf(stage, prim, A_PRINCIPAL_AXES)?,
        density: read_scalar_f32(stage, prim, A_DENSITY)?,
    }))
}

/// Read a `PhysicsScene` prim. Returns `None` when the prim is not
/// typed `PhysicsScene`.
pub fn read_physics_scene(stage: &Stage, prim: &Path) -> Result<Option<ReadPhysicsScene>> {
    if !read_is_physics_scene(stage, prim)? {
        return Ok(None);
    }
    Ok(Some(ReadPhysicsScene {
        path: prim.as_str().to_string(),
        gravity_direction: read_vec3f(stage, prim, A_GRAVITY_DIRECTION)?,
        gravity_magnitude: read_scalar_f32(stage, prim, A_GRAVITY_MAGNITUDE)?,
    }))
}

/// Read `PhysicsCollisionAPI` (plus optional `PhysicsMeshCollisionAPI`)
/// state on a prim. Returns `None` when CollisionAPI isn't applied.
///
/// `approximation` is `Some` only when MeshCollisionAPI is applied;
/// otherwise the prim is a primitive shape and the engine uses its
/// native collider type.
///
/// `physics_material_path` is resolved through `material:binding:physics`
/// first, then plain `material:binding`.
pub fn read_collision_shape(stage: &Stage, prim: &Path) -> Result<Option<ReadCollisionShape>> {
    let api = read_api_schemas(stage, prim)?;
    if !api.iter().any(|s| s == API_COLLISION) {
        return Ok(None);
    }
    let has_mesh_collision = api.iter().any(|s| s == API_MESH_COLLISION);
    let collision_enabled = match read_attr_value(stage, prim, A_COLLISION_ENABLED)? {
        Some(Value::Bool(b)) => b,
        _ => true,
    };
    let approximation = if has_mesh_collision {
        read_token(stage, prim, A_APPROXIMATION)?.and_then(|s| CollisionApprox::from_token(&s))
    } else {
        None
    };
    let simulation_owner = read_rel_first_target(stage, prim, A_SIMULATION_OWNER)?;
    let physics_material_path = read_rel_first_target(stage, prim, REL_MATERIAL_BINDING_PHYSICS)?
        .or(read_rel_first_target(stage, prim, REL_MATERIAL_BINDING)?);
    Ok(Some(ReadCollisionShape {
        has_collision_api: true,
        has_mesh_collision_api: has_mesh_collision,
        collision_enabled,
        approximation,
        simulation_owner,
        physics_material_path,
    }))
}

/// Read `PhysicsMaterialAPI` from a prim. Returns `None` unless the
/// API is applied (regardless of the prim's typeName, so non-Material
/// prims that carry it are also accepted).
pub fn read_physics_material(stage: &Stage, prim: &Path) -> Result<Option<ReadPhysicsMaterial>> {
    if !read_api_schemas(stage, prim)?.iter().any(|s| s == API_PHYSICS_MATERIAL) {
        return Ok(None);
    }
    Ok(Some(ReadPhysicsMaterial {
        path: prim.as_str().to_string(),
        static_friction: read_scalar_f32(stage, prim, A_STATIC_FRICTION)?,
        dynamic_friction: read_scalar_f32(stage, prim, A_DYNAMIC_FRICTION)?,
        restitution: read_scalar_f32(stage, prim, A_RESTITUTION)?,
        density: read_scalar_f32(stage, prim, A_DENSITY)?,
    }))
}

/// Decode every multi-apply `PhysicsLimitAPI:<dof>` instance on a joint.
pub fn read_joint_limits(stage: &Stage, prim: &Path) -> Result<Vec<ReadLimit>> {
    let api = read_api_schemas(stage, prim)?;
    let mut out = Vec::new();
    for name in api {
        let Some(rest) = name.strip_prefix(API_LIMIT) else {
            continue;
        };
        let Some(dof_token) = rest.strip_prefix(':') else {
            continue;
        };
        let Some(dof) = Dof::from_token(dof_token) else {
            continue;
        };
        let low = read_scalar_f32(stage, prim, &format!("limit:{dof_token}:physics:{LIMIT_SUB_LOW}"))?.unwrap_or(0.0);
        let high = read_scalar_f32(stage, prim, &format!("limit:{dof_token}:physics:{LIMIT_SUB_HIGH}"))?.unwrap_or(0.0);
        out.push(ReadLimit { dof, low, high });
    }
    Ok(out)
}

/// Decode every multi-apply `PhysicsDriveAPI:<dof>` instance on a joint.
pub fn read_joint_drives(stage: &Stage, prim: &Path) -> Result<Vec<ReadDrive>> {
    let api = read_api_schemas(stage, prim)?;
    let mut out = Vec::new();
    for name in api {
        let Some(rest) = name.strip_prefix(API_DRIVE) else {
            continue;
        };
        let Some(dof_token) = rest.strip_prefix(':') else {
            continue;
        };
        let Some(dof) = Dof::from_token(dof_token) else {
            continue;
        };
        let drive_type = read_token(stage, prim, &format!("drive:{dof_token}:physics:{DRIVE_SUB_TYPE}"))?
            .and_then(|s| DriveType::from_token(&s))
            .unwrap_or(DriveType::Force);
        let target_position = read_scalar_f32(
            stage,
            prim,
            &format!("drive:{dof_token}:physics:{DRIVE_SUB_TARGET_POSITION}"),
        )?;
        let target_velocity = read_scalar_f32(
            stage,
            prim,
            &format!("drive:{dof_token}:physics:{DRIVE_SUB_TARGET_VELOCITY}"),
        )?;
        let damping =
            read_scalar_f32(stage, prim, &format!("drive:{dof_token}:physics:{DRIVE_SUB_DAMPING}"))?.unwrap_or(0.0);
        let stiffness =
            read_scalar_f32(stage, prim, &format!("drive:{dof_token}:physics:{DRIVE_SUB_STIFFNESS}"))?.unwrap_or(0.0);
        let max_force = read_scalar_f32(stage, prim, &format!("drive:{dof_token}:physics:{DRIVE_SUB_MAX_FORCE}"))?;
        out.push(ReadDrive {
            dof,
            drive_type,
            target_position,
            target_velocity,
            damping,
            stiffness,
            max_force,
        });
    }
    Ok(out)
}

/// Read any `Physics*Joint` prim. Returns `None` when the prim's
/// typeName isn't a known joint type.
pub fn read_joint(stage: &Stage, prim: &Path) -> Result<Option<ReadJoint>> {
    let type_name = stage.field::<String>(prim.clone(), "typeName")?.unwrap_or_default();
    let kind = match type_name.as_str() {
        T_PHYSICS_FIXED_JOINT => JointKind::Fixed,
        T_PHYSICS_REVOLUTE_JOINT => JointKind::Revolute,
        T_PHYSICS_PRISMATIC_JOINT => JointKind::Prismatic,
        T_PHYSICS_SPHERICAL_JOINT => JointKind::Spherical,
        T_PHYSICS_DISTANCE_JOINT => JointKind::Distance,
        T_PHYSICS_JOINT => JointKind::Generic,
        _ => return Ok(None),
    };
    let body0 = read_rel_first_target(stage, prim, A_BODY0)?;
    let body1 = read_rel_first_target(stage, prim, A_BODY1)?;
    let local_pos0 = read_vec3f(stage, prim, A_LOCAL_POS_0)?.unwrap_or([0.0; 3]);
    let local_pos1 = read_vec3f(stage, prim, A_LOCAL_POS_1)?.unwrap_or([0.0; 3]);
    let local_rot0 = read_quatf(stage, prim, A_LOCAL_ROT_0)?.unwrap_or([1.0, 0.0, 0.0, 0.0]);
    let local_rot1 = read_quatf(stage, prim, A_LOCAL_ROT_1)?.unwrap_or([1.0, 0.0, 0.0, 0.0]);
    let axis = read_token(stage, prim, A_AXIS)?;
    let lower_limit = read_scalar_f32(stage, prim, A_LOWER_LIMIT)?;
    let upper_limit = read_scalar_f32(stage, prim, A_UPPER_LIMIT)?;
    let collision_enabled = matches!(
        read_attr_value(stage, prim, A_JOINT_COLLISION_ENABLED)?,
        Some(Value::Bool(true))
    );
    let joint_enabled = match read_attr_value(stage, prim, A_JOINT_ENABLED)? {
        Some(Value::Bool(b)) => b,
        _ => true,
    };
    let exclude_from_articulation = matches!(
        read_attr_value(stage, prim, A_EXCLUDE_FROM_ARTICULATION)?,
        Some(Value::Bool(true))
    );
    let break_force = read_scalar_f32(stage, prim, A_BREAK_FORCE)?;
    let break_torque = read_scalar_f32(stage, prim, A_BREAK_TORQUE)?;
    let min_distance = read_scalar_f32(stage, prim, A_MIN_DISTANCE)?;
    let max_distance = read_scalar_f32(stage, prim, A_MAX_DISTANCE)?;
    let cone_angle_0 = read_scalar_f32(stage, prim, A_CONE_ANGLE_0_LIMIT)?;
    let cone_angle_1 = read_scalar_f32(stage, prim, A_CONE_ANGLE_1_LIMIT)?;
    let limits = read_joint_limits(stage, prim)?;
    let drives = read_joint_drives(stage, prim)?;

    Ok(Some(ReadJoint {
        path: prim.as_str().to_string(),
        kind,
        body0,
        body1,
        local_pos0,
        local_rot0,
        local_pos1,
        local_rot1,
        axis,
        lower_limit,
        upper_limit,
        collision_enabled,
        joint_enabled,
        exclude_from_articulation,
        break_force,
        break_torque,
        min_distance,
        max_distance,
        cone_angle_0,
        cone_angle_1,
        limits,
        drives,
    }))
}

/// Read a `PhysicsCollisionGroup` prim. Returns `None` when the
/// typeName doesn't match.
///
/// Note: full UsdCollectionAPI rule evaluation (includes / excludes /
/// expansion-rule semantics) is left to a follow-up; for now the
/// reader returns the explicit `collection:colliders:includes` target
/// list, adequate for the common authoring pattern.
pub fn read_collision_group(stage: &Stage, prim: &Path) -> Result<Option<ReadCollisionGroup>> {
    let type_name = stage.field::<String>(prim.clone(), "typeName")?.unwrap_or_default();
    if type_name != T_PHYSICS_COLLISION_GROUP {
        return Ok(None);
    }
    let members = read_rel_all_targets(stage, prim, "collection:colliders:includes")?;
    let filtered_groups = read_rel_all_targets(stage, prim, A_FILTERED_GROUPS)?;
    let merge_group = read_token(stage, prim, A_MERGE_GROUP)?;
    let invert_filtered_groups = matches!(
        read_attr_value(stage, prim, A_INVERT_FILTERED_GROUPS)?,
        Some(Value::Bool(true))
    );
    Ok(Some(ReadCollisionGroup {
        path: prim.as_str().to_string(),
        members,
        filtered_groups,
        merge_group,
        invert_filtered_groups,
    }))
}

/// Read `PhysicsFilteredPairsAPI` from a body prim. Returns `None`
/// unless the API is applied.
pub fn read_filtered_pairs(stage: &Stage, prim: &Path) -> Result<Option<ReadFilteredPairs>> {
    if !read_api_schemas(stage, prim)?.iter().any(|s| s == API_FILTERED_PAIRS) {
        return Ok(None);
    }
    let filtered = read_rel_all_targets(stage, prim, A_FILTERED_PAIRS)?;
    Ok(Some(ReadFilteredPairs {
        path: prim.as_str().to_string(),
        filtered,
    }))
}

/// Walk the entire stage once and return categorised path lists.
/// Saves callers from re-walking for every schema family.
pub fn find_physics_prims(stage: &Stage) -> Result<PhysicsPrims> {
    let mut out = PhysicsPrims::default();
    stage.traverse(|path| {
        if let Ok(Some(type_name)) = stage.field::<String>(path.clone(), "typeName") {
            match type_name.as_str() {
                T_PHYSICS_SCENE => out.scenes.push(path.as_str().to_string()),
                T_PHYSICS_JOINT
                | T_PHYSICS_FIXED_JOINT
                | T_PHYSICS_REVOLUTE_JOINT
                | T_PHYSICS_PRISMATIC_JOINT
                | T_PHYSICS_SPHERICAL_JOINT
                | T_PHYSICS_DISTANCE_JOINT => out.joints.push(path.as_str().to_string()),
                T_PHYSICS_COLLISION_GROUP => out.collision_groups.push(path.as_str().to_string()),
                _ => {}
            }
        }
        if let Ok(api) = read_api_schemas(stage, path) {
            let p = path.as_str().to_string();
            if api.iter().any(|s| s == API_RIGID_BODY) {
                out.rigid_bodies.push(p.clone());
            }
            if api.iter().any(|s| s == API_ARTICULATION_ROOT) {
                out.articulation_roots.push(p.clone());
            }
            if api.iter().any(|s| s == API_COLLISION) {
                out.colliders.push(p.clone());
            }
            if api.iter().any(|s| s == API_PHYSICS_MATERIAL) {
                out.materials.push(p.clone());
            }
            if api.iter().any(|s| s == API_FILTERED_PAIRS) {
                out.filtered_pairs.push(p);
            }
        }
    })?;
    Ok(out)
}

// ────────────────────────────────────────────────────────────────────────
// internal value helpers
// ────────────────────────────────────────────────────────────────────────

fn read_attr_value(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    let attr_path = prim.append_property(name)?;
    stage.field::<Value>(attr_path, "default")
}

fn read_bool(stage: &Stage, prim: &Path, name: &str) -> Result<Option<bool>> {
    Ok(match read_attr_value(stage, prim, name)? {
        Some(Value::Bool(b)) => Some(b),
        _ => None,
    })
}

fn read_scalar_f32(stage: &Stage, prim: &Path, name: &str) -> Result<Option<f32>> {
    Ok(match read_attr_value(stage, prim, name)? {
        Some(Value::Float(f)) => Some(f),
        Some(Value::Double(d)) => Some(d as f32),
        _ => None,
    })
}

fn read_vec3f(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[f32; 3]>> {
    Ok(match read_attr_value(stage, prim, name)? {
        Some(Value::Vec3f(a)) => Some(a),
        Some(Value::Vec3d(a)) => Some([a[0] as f32, a[1] as f32, a[2] as f32]),
        _ => None,
    })
}

fn read_quatf(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[f32; 4]>> {
    Ok(match read_attr_value(stage, prim, name)? {
        Some(Value::Quatf(q)) => Some(q),
        Some(Value::Quatd(q)) => Some([q[0] as f32, q[1] as f32, q[2] as f32, q[3] as f32]),
        _ => None,
    })
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match read_attr_value(stage, prim, name)? {
        Some(Value::Token(s)) | Some(Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_rel_first_target(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Option<String>> {
    Ok(read_rel_all_targets(stage, prim, rel_name)?.into_iter().next())
}

fn read_rel_all_targets(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Vec<String>> {
    let rel_path = prim.append_property(rel_name)?;
    let raw = stage.field::<Value>(rel_path, "targetPaths")?;
    let paths = match raw {
        Some(Value::PathListOp(op)) => op.flatten(),
        Some(Value::PathVec(v)) => v,
        _ => Vec::new(),
    };
    Ok(paths.into_iter().map(|p| p.as_str().to_string()).collect())
}
