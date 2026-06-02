//! `PhysicsScene` prim authoring.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::physics::tokens::{A_GRAVITY_DIRECTION, A_GRAVITY_MAGNITUDE, T_PHYSICS_SCENE};

use super::common::{author_float, author_vector3f};

/// Author a `def PhysicsScene` prim at `path` and return a chainable
/// [`PhysicsSceneAuthor`] for the two simulation-wide attributes the
/// spec defines.
///
/// Per `usdPhysics/schema.usda`, `gravityDirection = (0, 0, 0)` is a
/// request to use the negative `upAxis`, and `gravityMagnitude < 0` is
/// a request to use the renderer's Earth-gravity equivalent — both
/// remain valid authored opinions, the helper just exposes them.
pub fn define_physics_scene(stage: &Stage, path: impl Into<Path>) -> Result<PhysicsSceneAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_PHYSICS_SCENE)?;
    Ok(PhysicsSceneAuthor { prim })
}

pub struct PhysicsSceneAuthor {
    prim: Prim,
}

impl PhysicsSceneAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:gravityDirection` (spec default (0, 0, 0) — i.e. use
    /// negative `upAxis`).
    pub fn set_gravity_direction(self, direction: [f32; 3]) -> Result<Self> {
        author_vector3f(self.prim.stage(), self.prim.path(), A_GRAVITY_DIRECTION, direction)?;
        Ok(self)
    }

    /// Set `physics:gravityMagnitude` in distance/second² (spec
    /// default `-inf` — i.e. use Earth gravity equivalent).
    pub fn set_gravity_magnitude(self, magnitude: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_GRAVITY_MAGNITUDE, magnitude)?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn physics_scene_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_physics_scene(&stage, sdf::path("/Scene")?)?
            .set_gravity_direction([0.0, -1.0, 0.0])?
            .set_gravity_magnitude(9.81)?;

        let scene = crate::schemas::physics::read_physics_scene(&stage, &sdf::path("/Scene")?)?.expect("PhysicsScene");
        assert_eq!(scene.gravity_direction, Some([0.0, -1.0, 0.0]));
        assert!((scene.gravity_magnitude.unwrap() - 9.81).abs() < 1e-3);
        Ok(())
    }
}
