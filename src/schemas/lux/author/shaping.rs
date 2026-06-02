//! `ShapingAPI` and `ShadowAPI` applied schema authoring.
//!
//! Both schemas are applied via `apiSchemas +=` and then set their
//! `inputs:shaping:*` / `inputs:shadow:*` attributes on the host light
//! prim per `usdLux/schema.usda`.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::lux::tokens::{
    API_SHADOW, API_SHAPING, A_SHADOW_COLOR, A_SHADOW_DISTANCE, A_SHADOW_ENABLE, A_SHADOW_FALLOFF,
    A_SHADOW_FALLOFF_GAMMA, A_SHAPING_CONE_ANGLE, A_SHAPING_CONE_SOFTNESS, A_SHAPING_FOCUS, A_SHAPING_FOCUS_TINT,
    A_SHAPING_IES_ANGLE_SCALE, A_SHAPING_IES_FILE, A_SHAPING_IES_NORMALIZE,
};

use super::common::{author_input_asset, author_input_bool, author_input_color3f, author_input_float};

// ── ShapingAPI ──────────────────────────────────────────────────────

/// Apply `ShapingAPI` to the prim at `path` and return a chainable
/// [`ShapingAuthor`] for the 7 spec-defined inputs (focus + focusTint,
/// cone angle/softness, IES file/angleScale/normalize).
pub fn apply_shaping(stage: &Stage, path: impl Into<Path>) -> Result<ShapingAuthor> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_SHAPING)?;
    Ok(ShapingAuthor { prim })
}

pub struct ShapingAuthor {
    prim: Prim,
}

impl ShapingAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `inputs:shaping:focus` (spec default 0).
    pub fn set_focus(self, focus: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_SHAPING_FOCUS, focus)?;
        Ok(self)
    }

    /// Set `inputs:shaping:focusTint` (spec default (0, 0, 0)).
    pub fn set_focus_tint(self, tint: [f32; 3]) -> Result<Self> {
        author_input_color3f(self.prim.stage(), self.prim.path(), A_SHAPING_FOCUS_TINT, tint)?;
        Ok(self)
    }

    /// Set `inputs:shaping:cone:angle` in degrees (spec default 90).
    pub fn set_cone_angle_deg(self, angle: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_SHAPING_CONE_ANGLE, angle)?;
        Ok(self)
    }

    /// Set `inputs:shaping:cone:softness` (spec default 0).
    pub fn set_cone_softness(self, softness: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_SHAPING_CONE_SOFTNESS, softness)?;
        Ok(self)
    }

    /// Set `inputs:shaping:ies:file` — path to an IES light profile.
    pub fn set_ies_file(self, path: impl Into<String>) -> Result<Self> {
        author_input_asset(self.prim.stage(), self.prim.path(), A_SHAPING_IES_FILE, path)?;
        Ok(self)
    }

    /// Set `inputs:shaping:ies:angleScale` (spec default 0).
    pub fn set_ies_angle_scale(self, scale: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_SHAPING_IES_ANGLE_SCALE, scale)?;
        Ok(self)
    }

    /// Set `inputs:shaping:ies:normalize` (spec default false).
    pub fn set_ies_normalize(self, normalize: bool) -> Result<Self> {
        author_input_bool(self.prim.stage(), self.prim.path(), A_SHAPING_IES_NORMALIZE, normalize)?;
        Ok(self)
    }
}

// ── ShadowAPI ───────────────────────────────────────────────────────

/// Apply `ShadowAPI` to the prim at `path` and return a chainable
/// [`ShadowAuthor`] for the 5 spec-defined inputs.
pub fn apply_shadow(stage: &Stage, path: impl Into<Path>) -> Result<ShadowAuthor> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_SHADOW)?;
    Ok(ShadowAuthor { prim })
}

pub struct ShadowAuthor {
    prim: Prim,
}

impl ShadowAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `inputs:shadow:enable` (spec default true).
    pub fn set_enable(self, enable: bool) -> Result<Self> {
        author_input_bool(self.prim.stage(), self.prim.path(), A_SHADOW_ENABLE, enable)?;
        Ok(self)
    }

    /// Set `inputs:shadow:color` (spec default (0, 0, 0)).
    pub fn set_color(self, color: [f32; 3]) -> Result<Self> {
        author_input_color3f(self.prim.stage(), self.prim.path(), A_SHADOW_COLOR, color)?;
        Ok(self)
    }

    /// Set `inputs:shadow:distance` (spec default -1.0, meaning no limit).
    pub fn set_distance(self, distance: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_SHADOW_DISTANCE, distance)?;
        Ok(self)
    }

    /// Set `inputs:shadow:falloff` (spec default -1.0, meaning no falloff).
    pub fn set_falloff(self, falloff: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_SHADOW_FALLOFF, falloff)?;
        Ok(self)
    }

    /// Set `inputs:shadow:falloffGamma` (spec default 1.0).
    pub fn set_falloff_gamma(self, gamma: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_SHADOW_FALLOFF_GAMMA, gamma)?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn shaping_api_roundtrip_full_surface() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Spot")?.set_type_name("RectLight")?;
        apply_shaping(&stage, sdf::path("/Spot")?)?
            .set_focus(4.0)?
            .set_focus_tint([0.1, 0.2, 0.3])?
            .set_cone_angle_deg(45.0)?
            .set_cone_softness(0.2)?
            .set_ies_file("./profile.ies")?
            .set_ies_angle_scale(1.0)?
            .set_ies_normalize(true)?;

        let shaping = crate::schemas::lux::read_shaping(&stage, &sdf::path("/Spot")?)?.expect("ShapingAPI");
        assert!((shaping.focus - 4.0).abs() < 1e-3);
        assert_eq!(shaping.focus_tint, [0.1, 0.2, 0.3]);
        assert!((shaping.cone_angle_deg - 45.0).abs() < 1e-3);
        assert!((shaping.cone_softness - 0.2).abs() < 1e-3);
        assert_eq!(shaping.ies_file.as_deref(), Some("./profile.ies"));
        assert!((shaping.ies_angle_scale - 1.0).abs() < 1e-3);
        assert!(shaping.ies_normalize);
        Ok(())
    }

    #[test]
    fn shadow_api_roundtrip_full_surface() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Spot")?.set_type_name("RectLight")?;
        apply_shadow(&stage, sdf::path("/Spot")?)?
            .set_enable(false)?
            .set_color([0.1, 0.1, 0.1])?
            .set_distance(10.0)?
            .set_falloff(2.0)?
            .set_falloff_gamma(1.5)?;

        let shadow = crate::schemas::lux::read_shadow(&stage, &sdf::path("/Spot")?)?.expect("ShadowAPI");
        assert!(!shadow.enable);
        assert_eq!(shadow.color, [0.1, 0.1, 0.1]);
        assert!((shadow.distance - 10.0).abs() < 1e-3);
        assert!((shadow.falloff - 2.0).abs() < 1e-3);
        assert!((shadow.falloff_gamma - 1.5).abs() < 1e-3);
        Ok(())
    }
}
