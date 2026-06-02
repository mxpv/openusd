//! `PhysicsRigidBodyAPI` and `PhysicsMassAPI` authoring.
//!
//! `apply_rigid_body` adds the API to any UsdGeomXformable; the chain
//! exposes the 6 spec'd attributes. `apply_mass` does the same for
//! `PhysicsMassAPI` (5 attrs).

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::physics::tokens::{
    API_MASS, API_RIGID_BODY, A_ANGULAR_VELOCITY, A_CENTER_OF_MASS, A_DENSITY, A_DIAGONAL_INERTIA, A_KINEMATIC_ENABLED,
    A_MASS, A_PRINCIPAL_AXES, A_RIGID_BODY_ENABLED, A_SIMULATION_OWNER, A_STARTS_ASLEEP, A_VELOCITY,
};

use super::common::{
    author_bool, author_float, author_float3, author_point3f, author_quatf, author_rel_targets, author_uniform_bool,
    author_vector3f,
};

// ── PhysicsRigidBodyAPI ─────────────────────────────────────────────

/// Apply `PhysicsRigidBodyAPI` to the prim at `path` and return a
/// chainable [`RigidBodyAuthor`] for the 6 spec-defined attrs plus the
/// `simulationOwner` relationship.
pub fn apply_rigid_body(stage: &Stage, path: impl Into<Path>) -> Result<RigidBodyAuthor> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_RIGID_BODY)?;
    Ok(RigidBodyAuthor { prim })
}

pub struct RigidBodyAuthor {
    prim: Prim,
}

impl RigidBodyAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:rigidBodyEnabled` (spec default true).
    pub fn set_enabled(self, enabled: bool) -> Result<Self> {
        author_bool(self.prim.stage(), self.prim.path(), A_RIGID_BODY_ENABLED, enabled)?;
        Ok(self)
    }

    /// Set `physics:kinematicEnabled` (spec default false). A kinematic
    /// body is moved through animated poses; the simulator derives
    /// velocities from the motion rather than integrating forces.
    pub fn set_kinematic(self, kinematic: bool) -> Result<Self> {
        author_bool(self.prim.stage(), self.prim.path(), A_KINEMATIC_ENABLED, kinematic)?;
        Ok(self)
    }

    /// Set `physics:startsAsleep` (uniform bool, spec default false).
    pub fn set_starts_asleep(self, asleep: bool) -> Result<Self> {
        author_uniform_bool(self.prim.stage(), self.prim.path(), A_STARTS_ASLEEP, asleep)?;
        Ok(self)
    }

    /// Set `physics:velocity` in distance/second.
    pub fn set_velocity(self, velocity: [f32; 3]) -> Result<Self> {
        author_vector3f(self.prim.stage(), self.prim.path(), A_VELOCITY, velocity)?;
        Ok(self)
    }

    /// Set `physics:angularVelocity` in degrees/second.
    pub fn set_angular_velocity(self, angular_velocity: [f32; 3]) -> Result<Self> {
        author_vector3f(
            self.prim.stage(),
            self.prim.path(),
            A_ANGULAR_VELOCITY,
            angular_velocity,
        )?;
        Ok(self)
    }

    /// Set `physics:simulationOwner` — relationship to the
    /// `PhysicsScene` driving this body.
    pub fn set_simulation_owner(self, scene: impl Into<Path>) -> Result<Self> {
        author_rel_targets(self.prim.stage(), self.prim.path(), A_SIMULATION_OWNER, [scene.into()])?;
        Ok(self)
    }
}

// ── PhysicsMassAPI ──────────────────────────────────────────────────

/// Apply `PhysicsMassAPI` to the prim at `path` and return a chainable
/// [`MassAuthor`] for the 5 spec-defined attrs.
pub fn apply_mass(stage: &Stage, path: impl Into<Path>) -> Result<MassAuthor> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_MASS)?;
    Ok(MassAuthor { prim })
}

pub struct MassAuthor {
    prim: Prim,
}

impl MassAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:mass` (spec default 0.0 — meaning "ignored, derive
    /// from density × volume"). Per spec, parent's mass overrides
    /// child's.
    pub fn set_mass(self, mass: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_MASS, mass)?;
        Ok(self)
    }

    /// Set `physics:density` (spec default 0.0 — ignored). Child's
    /// density overrides parent's (opposite precedence vs `mass`).
    pub fn set_density(self, density: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_DENSITY, density)?;
        Ok(self)
    }

    /// Set `physics:centerOfMass` in the prim's local space.
    pub fn set_center_of_mass(self, center: [f32; 3]) -> Result<Self> {
        author_point3f(self.prim.stage(), self.prim.path(), A_CENTER_OF_MASS, center)?;
        Ok(self)
    }

    /// Set `physics:diagonalInertia` along the principal axes.
    pub fn set_diagonal_inertia(self, inertia: [f32; 3]) -> Result<Self> {
        author_float3(self.prim.stage(), self.prim.path(), A_DIAGONAL_INERTIA, inertia)?;
        Ok(self)
    }

    /// Set `physics:principalAxes` orientation. Quat order `(w, x, y, z)`.
    pub fn set_principal_axes(self, quat: [f32; 4]) -> Result<Self> {
        author_quatf(self.prim.stage(), self.prim.path(), A_PRINCIPAL_AXES, quat)?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn rigid_body_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Body")?.set_type_name("Xform")?;
        stage.define_prim("/Scene")?.set_type_name("PhysicsScene")?;
        apply_rigid_body(&stage, sdf::path("/Body")?)?
            .set_enabled(true)?
            .set_kinematic(false)?
            .set_starts_asleep(true)?
            .set_velocity([1.0, 0.0, 0.0])?
            .set_angular_velocity([0.0, 0.0, 30.0])?
            .set_simulation_owner(sdf::path("/Scene")?)?;

        let body =
            crate::schemas::physics::read_rigid_body(&stage, &sdf::path("/Body")?)?.expect("PhysicsRigidBodyAPI");
        assert!(body.rigid_body_enabled);
        assert!(!body.kinematic_enabled);
        assert!(body.starts_asleep);
        assert_eq!(body.velocity, Some([1.0, 0.0, 0.0]));
        assert_eq!(body.angular_velocity, Some([0.0, 0.0, 30.0]));
        assert_eq!(body.simulation_owner.as_deref(), Some("/Scene"));
        Ok(())
    }

    #[test]
    fn mass_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Body")?.set_type_name("Xform")?;
        apply_mass(&stage, sdf::path("/Body")?)?
            .set_mass(10.0)?
            .set_density(1000.0)?
            .set_center_of_mass([0.0, 0.5, 0.0])?
            .set_diagonal_inertia([1.0, 2.0, 3.0])?
            .set_principal_axes([1.0, 0.0, 0.0, 0.0])?;

        let mass = crate::schemas::physics::read_mass(&stage, &sdf::path("/Body")?)?.expect("PhysicsMassAPI");
        assert_eq!(mass.mass, Some(10.0));
        assert_eq!(mass.density, Some(1000.0));
        assert_eq!(mass.center_of_mass, Some([0.0, 0.5, 0.0]));
        assert_eq!(mass.diagonal_inertia, Some([1.0, 2.0, 3.0]));
        assert_eq!(mass.principal_axes, Some([1.0, 0.0, 0.0, 0.0]));
        Ok(())
    }
}
