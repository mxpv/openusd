//! `PhysicsCollisionAPI`, `PhysicsMeshCollisionAPI`, and
//! `PhysicsMaterialAPI` authoring.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::physics::tokens::{
    API_COLLISION, API_MESH_COLLISION, API_PHYSICS_MATERIAL, A_APPROXIMATION, A_COLLISION_ENABLED, A_DENSITY,
    A_DYNAMIC_FRICTION, A_RESTITUTION, A_SIMULATION_OWNER, A_STATIC_FRICTION,
};
use crate::schemas::physics::types::CollisionApprox;

use super::common::{author_bool, author_float, author_rel_targets, author_uniform_token};

// ── PhysicsCollisionAPI ─────────────────────────────────────────────

/// Apply `PhysicsCollisionAPI` to the prim at `path` and return a
/// chainable [`CollisionAuthor`].
pub fn apply_collision(stage: &Stage, path: impl Into<Path>) -> Result<CollisionAuthor> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_COLLISION)?;
    Ok(CollisionAuthor { prim })
}

pub struct CollisionAuthor {
    prim: Prim,
}

impl CollisionAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:collisionEnabled` (spec default true).
    pub fn set_enabled(self, enabled: bool) -> Result<Self> {
        author_bool(self.prim.stage(), self.prim.path(), A_COLLISION_ENABLED, enabled)?;
        Ok(self)
    }

    /// Set `physics:simulationOwner` — relationship to the
    /// `PhysicsScene` driving this collider.
    pub fn set_simulation_owner(self, scene: impl Into<Path>) -> Result<Self> {
        author_rel_targets(self.prim.stage(), self.prim.path(), A_SIMULATION_OWNER, [scene.into()])?;
        Ok(self)
    }
}

// ── PhysicsMeshCollisionAPI ─────────────────────────────────────────

/// Apply `PhysicsMeshCollisionAPI` to a Mesh prim at `path` and return
/// a chainable [`MeshCollisionAuthor`]. Per spec, this API must be
/// applied alongside `PhysicsCollisionAPI` on a `UsdGeomMesh`.
pub fn apply_mesh_collision(stage: &Stage, path: impl Into<Path>) -> Result<MeshCollisionAuthor> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_MESH_COLLISION)?;
    Ok(MeshCollisionAuthor { prim })
}

pub struct MeshCollisionAuthor {
    prim: Prim,
}

impl MeshCollisionAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:approximation` (uniform token). The
    /// [`CollisionApprox`] enum enforces the spec's allowedTokens
    /// (`none` / `convexDecomposition` / `convexHull` /
    /// `boundingSphere` / `boundingCube` / `meshSimplification`).
    pub fn set_approximation(self, approx: CollisionApprox) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_APPROXIMATION, approx.as_token())?;
        Ok(self)
    }
}

// ── PhysicsMaterialAPI ──────────────────────────────────────────────

/// Apply `PhysicsMaterialAPI` to a Material prim at `path` and return
/// a chainable [`MaterialAuthor`].
pub fn apply_physics_material(stage: &Stage, path: impl Into<Path>) -> Result<MaterialAuthor> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_PHYSICS_MATERIAL)?;
    Ok(MaterialAuthor { prim })
}

pub struct MaterialAuthor {
    prim: Prim,
}

impl MaterialAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:dynamicFriction` (spec default 0.0).
    pub fn set_dynamic_friction(self, mu: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_DYNAMIC_FRICTION, mu)?;
        Ok(self)
    }

    /// Set `physics:staticFriction` (spec default 0.0).
    pub fn set_static_friction(self, mu: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_STATIC_FRICTION, mu)?;
        Ok(self)
    }

    /// Set `physics:restitution` (spec default 0.0).
    pub fn set_restitution(self, e: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_RESTITUTION, e)?;
        Ok(self)
    }

    /// Set `physics:density` (spec default 0.0 — ignored).
    pub fn set_density(self, density: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_DENSITY, density)?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn collision_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Box")?.set_type_name("Cube")?;
        stage.define_prim("/Scene")?.set_type_name("PhysicsScene")?;
        apply_collision(&stage, sdf::path("/Box")?)?
            .set_enabled(true)?
            .set_simulation_owner(sdf::path("/Scene")?)?;

        let shape =
            crate::schemas::physics::read_collision_shape(&stage, &sdf::path("/Box")?)?.expect("PhysicsCollisionAPI");
        assert!(shape.has_collision_api);
        assert!(shape.collision_enabled);
        assert_eq!(shape.simulation_owner.as_deref(), Some("/Scene"));
        Ok(())
    }

    #[test]
    fn mesh_collision_writes_approximation_token() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Body")?.set_type_name("Mesh")?;
        apply_collision(&stage, sdf::path("/Body")?)?;
        apply_mesh_collision(&stage, sdf::path("/Body")?)?.set_approximation(CollisionApprox::ConvexHull)?;

        let shape = crate::schemas::physics::read_collision_shape(&stage, &sdf::path("/Body")?)?.expect("CollisionAPI");
        assert!(shape.has_mesh_collision_api);
        assert_eq!(shape.approximation, Some(CollisionApprox::ConvexHull));
        Ok(())
    }

    #[test]
    fn material_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Mat")?.set_type_name("Material")?;
        apply_physics_material(&stage, sdf::path("/Mat")?)?
            .set_static_friction(0.6)?
            .set_dynamic_friction(0.4)?
            .set_restitution(0.2)?
            .set_density(1000.0)?;

        let mat =
            crate::schemas::physics::read_physics_material(&stage, &sdf::path("/Mat")?)?.expect("PhysicsMaterialAPI");
        assert!((mat.static_friction.unwrap() - 0.6).abs() < 1e-3);
        assert!((mat.dynamic_friction.unwrap() - 0.4).abs() < 1e-3);
        assert!((mat.restitution.unwrap() - 0.2).abs() < 1e-3);
        assert!((mat.density.unwrap() - 1000.0).abs() < 1e-3);
        Ok(())
    }
}
