//! `PhysicsLimitAPI` and `PhysicsDriveAPI` multi-apply schema
//! authoring.
//!
//! Per `usdPhysics/schema.usda`, both are `multipleApply` schemas with
//! a token instance name (typically a [`Dof`] like `transX` / `rotY`
//! or a joint-specific alias like `linear` / `angular` / `distance`).
//!
//! - `PhysicsLimitAPI:<dof>` → attrs at `limit:<dof>:physics:low` / `high`
//! - `PhysicsDriveAPI:<dof>` → attrs at `drive:<dof>:physics:type` /
//!   `targetPosition` / `targetVelocity` / `damping` / `stiffness` /
//!   `maxForce`
//!
//! `apply_limit(stage, joint, dof)` / `apply_drive(stage, joint, dof)`
//! write the namespaced apiSchemas token and return chainable
//! authors for the per-instance attributes.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::physics::tokens::{
    API_DRIVE, API_LIMIT, DRIVE_SUB_DAMPING, DRIVE_SUB_MAX_FORCE, DRIVE_SUB_STIFFNESS, DRIVE_SUB_TARGET_POSITION,
    DRIVE_SUB_TARGET_VELOCITY, DRIVE_SUB_TYPE, LIMIT_SUB_HIGH, LIMIT_SUB_LOW,
};
use crate::schemas::physics::types::{Dof, DriveType};

use super::common::{author_float, author_uniform_token};

// ── PhysicsLimitAPI ─────────────────────────────────────────────────

/// Apply `PhysicsLimitAPI:<dof>` to the joint at `path` and return a
/// chainable [`LimitAuthor`] for the per-DOF `low` / `high` attrs.
pub fn apply_limit<'s>(stage: &'s Stage, path: impl Into<Path>, dof: Dof) -> Result<LimitAuthor<'s>> {
    let api_name = format!("{API_LIMIT}:{}", dof.as_token());
    let prim = stage.override_prim(path)?.add_applied_schema(api_name)?;
    Ok(LimitAuthor { prim, dof })
}

pub struct LimitAuthor<'s> {
    prim: Prim<'s>,
    dof: Dof,
}

impl<'s> LimitAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `limit:<dof>:physics:low` (spec default -inf — no lower limit).
    pub fn set_low(self, value: f32) -> Result<Self> {
        author_float(
            self.prim.stage(),
            self.prim.path(),
            &limit_attr_name(self.dof, LIMIT_SUB_LOW),
            value,
        )?;
        Ok(self)
    }

    /// Set `limit:<dof>:physics:high` (spec default +inf — no upper limit).
    pub fn set_high(self, value: f32) -> Result<Self> {
        author_float(
            self.prim.stage(),
            self.prim.path(),
            &limit_attr_name(self.dof, LIMIT_SUB_HIGH),
            value,
        )?;
        Ok(self)
    }
}

fn limit_attr_name(dof: Dof, sub: &str) -> String {
    format!("limit:{}:physics:{sub}", dof.as_token())
}

// ── PhysicsDriveAPI ─────────────────────────────────────────────────

/// Apply `PhysicsDriveAPI:<dof>` to the joint at `path` and return a
/// chainable [`DriveAuthor`] for the per-DOF drive attrs.
pub fn apply_drive<'s>(stage: &'s Stage, path: impl Into<Path>, dof: Dof) -> Result<DriveAuthor<'s>> {
    let api_name = format!("{API_DRIVE}:{}", dof.as_token());
    let prim = stage.override_prim(path)?.add_applied_schema(api_name)?;
    Ok(DriveAuthor { prim, dof })
}

pub struct DriveAuthor<'s> {
    prim: Prim<'s>,
    dof: Dof,
}

impl<'s> DriveAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `drive:<dof>:physics:type` (uniform token, `force` / `acceleration`).
    pub fn set_type(self, drive_type: DriveType) -> Result<Self> {
        author_uniform_token(
            self.prim.stage(),
            self.prim.path(),
            &drive_attr_name(self.dof, DRIVE_SUB_TYPE),
            drive_type.as_token(),
        )?;
        Ok(self)
    }

    /// Set `drive:<dof>:physics:targetPosition`.
    pub fn set_target_position(self, value: f32) -> Result<Self> {
        author_float(
            self.prim.stage(),
            self.prim.path(),
            &drive_attr_name(self.dof, DRIVE_SUB_TARGET_POSITION),
            value,
        )?;
        Ok(self)
    }

    /// Set `drive:<dof>:physics:targetVelocity`.
    pub fn set_target_velocity(self, value: f32) -> Result<Self> {
        author_float(
            self.prim.stage(),
            self.prim.path(),
            &drive_attr_name(self.dof, DRIVE_SUB_TARGET_VELOCITY),
            value,
        )?;
        Ok(self)
    }

    /// Set `drive:<dof>:physics:damping`.
    pub fn set_damping(self, value: f32) -> Result<Self> {
        author_float(
            self.prim.stage(),
            self.prim.path(),
            &drive_attr_name(self.dof, DRIVE_SUB_DAMPING),
            value,
        )?;
        Ok(self)
    }

    /// Set `drive:<dof>:physics:stiffness`.
    pub fn set_stiffness(self, value: f32) -> Result<Self> {
        author_float(
            self.prim.stage(),
            self.prim.path(),
            &drive_attr_name(self.dof, DRIVE_SUB_STIFFNESS),
            value,
        )?;
        Ok(self)
    }

    /// Set `drive:<dof>:physics:maxForce` (spec default +inf — unlimited).
    pub fn set_max_force(self, value: f32) -> Result<Self> {
        author_float(
            self.prim.stage(),
            self.prim.path(),
            &drive_attr_name(self.dof, DRIVE_SUB_MAX_FORCE),
            value,
        )?;
        Ok(self)
    }
}

fn drive_attr_name(dof: Dof, sub: &str) -> String {
    format!("drive:{}:physics:{sub}", dof.as_token())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::physics::{define_revolute_joint, JointAxis, JointSetters};
    use crate::sdf;

    #[test]
    fn limit_api_authors_per_dof_attrs() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_revolute_joint(&stage, sdf::path("/Hinge")?)?.set_enabled(true)?;
        apply_limit(&stage, sdf::path("/Hinge")?, Dof::RotZ)?
            .set_low(-45.0)?
            .set_high(45.0)?;

        let limits = crate::schemas::physics::read_joint_limits(&stage, &sdf::path("/Hinge")?)?;
        assert_eq!(limits.len(), 1);
        assert_eq!(limits[0].dof, Dof::RotZ);
        assert!((limits[0].low - -45.0).abs() < 1e-3);
        assert!((limits[0].high - 45.0).abs() < 1e-3);
        Ok(())
    }

    #[test]
    fn drive_api_authors_per_dof_attrs() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_revolute_joint(&stage, sdf::path("/Hinge")?)?.set_axis(JointAxis::Z)?;
        apply_drive(&stage, sdf::path("/Hinge")?, Dof::Angular)?
            .set_type(DriveType::Force)?
            .set_target_position(0.0)?
            .set_target_velocity(10.0)?
            .set_damping(0.5)?
            .set_stiffness(100.0)?
            .set_max_force(1000.0)?;

        let drives = crate::schemas::physics::read_joint_drives(&stage, &sdf::path("/Hinge")?)?;
        assert_eq!(drives.len(), 1);
        assert_eq!(drives[0].dof, Dof::Angular);
        assert_eq!(drives[0].drive_type, DriveType::Force);
        assert!((drives[0].damping - 0.5).abs() < 1e-3);
        assert!((drives[0].stiffness - 100.0).abs() < 1e-3);
        assert!((drives[0].max_force.unwrap() - 1000.0).abs() < 1e-3);
        Ok(())
    }

    #[test]
    fn full_scene_roundtrip_authoring_to_reader() -> Result<()> {
        use crate::schemas::physics::{
            apply_articulation_root, apply_collision, apply_filtered_pairs, apply_mass, apply_mesh_collision,
            apply_physics_material, apply_rigid_body, define_collision_group, define_distance_joint,
            define_physics_scene, CollisionApprox,
        };

        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/World")?.set_type_name("Xform")?;
        stage.define_prim("/World/Box")?.set_type_name("Cube")?;
        stage.define_prim("/World/Ball")?.set_type_name("Sphere")?;
        stage.define_prim("/World/Material")?.set_type_name("Material")?;

        // Scene + simulationOwner
        define_physics_scene(&stage, sdf::path("/World/Scene")?)?.set_gravity_magnitude(9.81)?;

        // RigidBody + Mass + Collision on the cube.
        apply_rigid_body(&stage, sdf::path("/World/Box")?)?.set_simulation_owner(sdf::path("/World/Scene")?)?;
        apply_mass(&stage, sdf::path("/World/Box")?)?.set_mass(1.0)?;
        apply_collision(&stage, sdf::path("/World/Box")?)?;
        apply_mesh_collision(&stage, sdf::path("/World/Box")?)?.set_approximation(CollisionApprox::BoundingCube)?;

        apply_collision(&stage, sdf::path("/World/Ball")?)?;
        apply_physics_material(&stage, sdf::path("/World/Material")?)?
            .set_static_friction(0.5)?
            .set_restitution(0.3)?;

        // Articulation root + filtered pair.
        apply_articulation_root(&stage, sdf::path("/World")?)?;
        apply_filtered_pairs(&stage, sdf::path("/World/Box")?)?.set_filtered_pairs([sdf::path("/World/Ball")?])?;

        // Collision group.
        define_collision_group(&stage, sdf::path("/World/StaticGroup")?)?.set_merge_group("static")?;

        // Distance joint between bodies + Limit + Drive on a separate D6 joint.
        define_distance_joint(&stage, sdf::path("/World/Rope")?)?
            .set_body0(sdf::path("/World/Box")?)?
            .set_body1(sdf::path("/World/Ball")?)?
            .set_min_distance(0.5)?
            .set_max_distance(2.0)?;
        super::super::define_joint(&stage, sdf::path("/World/D6")?)?.set_enabled(true)?;
        apply_limit(&stage, sdf::path("/World/D6")?, Dof::TransX)?
            .set_low(-1.0)?
            .set_high(1.0)?;
        apply_drive(&stage, sdf::path("/World/D6")?, Dof::TransX)?
            .set_type(DriveType::Force)?
            .set_stiffness(50.0)?
            .set_damping(2.0)?;

        // Roundtrip via the reader.
        let scene =
            crate::schemas::physics::read_physics_scene(&stage, &sdf::path("/World/Scene")?)?.expect("PhysicsScene");
        assert!((scene.gravity_magnitude.unwrap() - 9.81).abs() < 1e-3);

        assert!(crate::schemas::physics::read_has_articulation_root(
            &stage,
            &sdf::path("/World")?,
        )?);
        assert!(crate::schemas::physics::read_rigid_body(&stage, &sdf::path("/World/Box")?)?.is_some());
        assert!(crate::schemas::physics::read_mass(&stage, &sdf::path("/World/Box")?)?.is_some());

        let limits = crate::schemas::physics::read_joint_limits(&stage, &sdf::path("/World/D6")?)?;
        assert_eq!(limits.len(), 1);
        let drives = crate::schemas::physics::read_joint_drives(&stage, &sdf::path("/World/D6")?)?;
        assert_eq!(drives.len(), 1);
        Ok(())
    }
}
