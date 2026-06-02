//! Authoring helpers for the nonboundable concrete light prims:
//! `DistantLight` and `GeometryLight`.
//!
//! Both inherit `NonboundableLightBase` per
//! `usdLux/schema.usda` and auto-apply `LightAPI`. `DistantLight`
//! additionally overrides `LightAPI.inputs:intensity = 1` with
//! `50000` — modelling the sun reaching Earth at ~50000 lux.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::lux::tokens::{A_ANGLE, REL_GEOMETRY, T_DISTANT_LIGHT, T_GEOMETRY_LIGHT};

use super::common::{author_input_float, author_rel_targets};
use super::light_api::LightApiSetters;

/// Author a `def DistantLight` prim at `path`. Returns a chainable
/// [`DistantLightAuthor`] exposing LightAPI setters via
/// [`LightApiSetters`] plus the DistantLight-specific `inputs:angle`.
///
/// Per Pixar's `usdLux/schema.usda`, DistantLight overrides LightAPI's
/// default intensity of `1` with `50000`. The schema declares it as a
/// schema-registry fallback (`apiSchemaOverride = true`) — Pixar's
/// `UsdLuxDistantLight::Define()` does not author an explicit opinion,
/// and our reader's [`ReadDistantLight::default`] already returns 50000
/// for unauthored intensity. The helper mirrors that contract: no
/// implicit write. Callers chain [`LightApiSetters::set_intensity`]
/// only when they need a non-sun value.
///
/// [`ReadDistantLight::default`]: crate::schemas::lux::ReadDistantLight
pub fn define_distant_light(stage: &Stage, path: impl Into<Path>) -> Result<DistantLightAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_DISTANT_LIGHT)?;
    Ok(DistantLightAuthor { prim })
}

pub struct DistantLightAuthor {
    prim: Prim,
}

impl DistantLightAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `inputs:angle` — angular diameter of the light in degrees.
    /// Spec default is `0.53` (approximately the sun as seen from
    /// Earth); higher values broaden the light and soften shadow edges.
    pub fn set_angle_deg(self, angle: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_ANGLE, angle)?;
        Ok(self)
    }
}

impl LightApiSetters for DistantLightAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── GeometryLight ───────────────────────────────────────────────────

/// Author a `def GeometryLight` prim at `path`. Returns a chainable
/// [`GeometryLightAuthor`] that wires the required `geometry` rel.
///
/// Per the schema, GeometryLight uses an arbitrary geometric prim
/// (typically a Mesh) as the emissive surface. The `geometry` rel must
/// point at that source prim.
pub fn define_geometry_light(stage: &Stage, path: impl Into<Path>) -> Result<GeometryLightAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_GEOMETRY_LIGHT)?;
    Ok(GeometryLightAuthor { prim })
}

pub struct GeometryLightAuthor {
    prim: Prim,
}

impl GeometryLightAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set the `geometry` rel target — path to the gprim acting as the
    /// emissive surface.
    pub fn set_geometry(self, geometry: impl Into<Path>) -> Result<Self> {
        author_rel_targets(self.prim.stage(), self.prim.path(), REL_GEOMETRY, [geometry.into()])?;
        Ok(self)
    }
}

impl LightApiSetters for GeometryLightAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn distant_light_defaults_intensity_to_50000_per_spec() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_distant_light(&stage, sdf::path("/Sun")?)?.set_angle_deg(0.53)?;

        let light = crate::schemas::lux::read_distant_light(&stage, &sdf::path("/Sun")?)?.expect("DistantLight");
        assert!((light.common.intensity - 50000.0).abs() < 1e-3);
        assert!((light.angle_deg - 0.53).abs() < 1e-3);
        Ok(())
    }

    #[test]
    fn distant_light_caller_intensity_override() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_distant_light(&stage, sdf::path("/Sun")?)?
            .set_intensity(12000.0)?
            .set_angle_deg(2.0)?;

        let light = crate::schemas::lux::read_distant_light(&stage, &sdf::path("/Sun")?)?.expect("DistantLight");
        assert!((light.common.intensity - 12000.0).abs() < 1e-3);
        assert!((light.angle_deg - 2.0).abs() < 1e-3);
        Ok(())
    }

    #[test]
    fn geometry_light_links_source_mesh() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/World/Emitter")?.set_type_name("Mesh")?;
        define_geometry_light(&stage, sdf::path("/World/Light")?)?
            .set_geometry(sdf::path("/World/Emitter")?)?
            .set_intensity(200.0)?;

        let light =
            crate::schemas::lux::read_geometry_light(&stage, &sdf::path("/World/Light")?)?.expect("GeometryLight");
        assert_eq!(light.geometry.as_deref(), Some("/World/Emitter"));
        assert!((light.common.intensity - 200.0).abs() < 1e-3);
        Ok(())
    }
}
