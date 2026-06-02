//! `DomeLight` + `DomeLight_1` authoring.
//!
//! Both prim types inherit `NonboundableLightBase` per
//! `usdLux/schema.usda`. They share the same set of attributes
//! (`inputs:texture:file`, `inputs:texture:format`, `portals` rel,
//! `guideRadius`); `DomeLight_1` adds the `poleAxis` token to control
//! the dome's starting orientation.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Prim, Stage};

use crate::schemas::lux::tokens::{
    A_GUIDE_RADIUS, A_POLE_AXIS, A_TEXTURE_FILE, A_TEXTURE_FORMAT, REL_PORTALS, T_DOME_LIGHT, T_DOME_LIGHT_1,
};
use crate::schemas::lux::types::{PoleAxis, TextureFormat};

use super::common::{author_input_asset, author_rel_targets};
use super::light_api::LightApiSetters;

/// Author a `def DomeLight` prim at `path`. Returns a chainable
/// [`DomeLightAuthor`] for the dome-specific attributes plus the
/// shared LightAPI setters via [`LightApiSetters`].
pub fn define_dome_light(stage: &Stage, path: impl Into<Path>) -> Result<DomeLightAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_DOME_LIGHT)?;
    Ok(DomeLightAuthor { prim })
}

pub struct DomeLightAuthor {
    prim: Prim,
}

impl DomeLightAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `inputs:texture:file` — IBL/HDR texture file path.
    pub fn set_texture_file(self, path: impl Into<String>) -> Result<Self> {
        author_input_asset(self.prim.stage(), self.prim.path(), A_TEXTURE_FILE, path)?;
        Ok(self)
    }

    /// Set `inputs:texture:format` — texture parameterisation. The
    /// [`TextureFormat`] enum enforces the spec's allowedTokens set
    /// (`automatic` / `latlong` / `mirroredBall` / `angular` /
    /// `cubeMapVerticalCross`).
    pub fn set_texture_format(self, format: TextureFormat) -> Result<Self> {
        author_token_input(
            self.prim.stage(),
            self.prim.path(),
            A_TEXTURE_FORMAT,
            format.as_token().to_string(),
        )?;
        Ok(self)
    }

    /// Set the `portals` rel targets — paths to PortalLight prims
    /// that focus the dome's sampling for indoor scenes.
    pub fn set_portals<I, P>(self, targets: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        author_rel_targets(self.prim.stage(), self.prim.path(), REL_PORTALS, targets)?;
        Ok(self)
    }

    /// Set `guideRadius` — radius of the guide geometry used to
    /// visualise the dome (spec default 1.0e5).
    pub fn set_guide_radius(self, radius: f32) -> Result<Self> {
        author_scalar_float(self.prim.stage(), self.prim.path(), A_GUIDE_RADIUS, radius)?;
        Ok(self)
    }
}

impl LightApiSetters for DomeLightAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── DomeLight_1 ─────────────────────────────────────────────────────

/// Author a `def DomeLight_1` prim at `path`. Same attribute set as
/// [`DomeLightAuthor`] plus the `poleAxis` token introduced in the
/// versioned `DomeLight_1` schema.
pub fn define_dome_light_1(stage: &Stage, path: impl Into<Path>) -> Result<DomeLight1Author> {
    let prim = stage.define_prim(path)?.set_type_name(T_DOME_LIGHT_1)?;
    Ok(DomeLight1Author { prim })
}

pub struct DomeLight1Author {
    prim: Prim,
}

impl DomeLight1Author {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `inputs:texture:file`.
    pub fn set_texture_file(self, path: impl Into<String>) -> Result<Self> {
        author_input_asset(self.prim.stage(), self.prim.path(), A_TEXTURE_FILE, path)?;
        Ok(self)
    }

    /// Set `inputs:texture:format`.
    pub fn set_texture_format(self, format: TextureFormat) -> Result<Self> {
        author_token_input(
            self.prim.stage(),
            self.prim.path(),
            A_TEXTURE_FORMAT,
            format.as_token().to_string(),
        )?;
        Ok(self)
    }

    /// Set the `portals` rel targets.
    pub fn set_portals<I, P>(self, targets: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        author_rel_targets(self.prim.stage(), self.prim.path(), REL_PORTALS, targets)?;
        Ok(self)
    }

    /// Set `guideRadius`.
    pub fn set_guide_radius(self, radius: f32) -> Result<Self> {
        author_scalar_float(self.prim.stage(), self.prim.path(), A_GUIDE_RADIUS, radius)?;
        Ok(self)
    }

    /// Set `poleAxis` — controls the dome's top-pole alignment. The
    /// [`PoleAxis`] enum enforces the spec's allowedTokens
    /// (`scene` / `Y` / `Z`).
    pub fn set_pole_axis(self, axis: PoleAxis) -> Result<Self> {
        author_uniform_token(
            self.prim.stage(),
            self.prim.path(),
            A_POLE_AXIS,
            axis.as_token().to_string(),
        )?;
        Ok(self)
    }
}

impl LightApiSetters for DomeLight1Author {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── private helpers ────────────────────────────────────────────────

/// Author a `varying token` input — for `inputs:texture:format`
/// which the schema declares without the `uniform` keyword.
fn author_token_input(stage: &Stage, prim: &Path, name: &str, value: String) -> Result<()> {
    // Body unchanged — name now matches the varying behaviour.
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "token")?
        .set_custom(false)?
        .set(Value::Token(value))?;
    Ok(())
}

/// Author a `uniform token` attribute — for `poleAxis` which the
/// schema declares as `uniform`.
fn author_uniform_token(stage: &Stage, prim: &Path, name: &str, value: String) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "token")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Token(value))?;
    Ok(())
}

/// Author a bare `float` (no `inputs:` prefix) — for DomeLight's
/// `guideRadius`.
fn author_scalar_float(stage: &Stage, prim: &Path, name: &str, value: f32) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "float")?
        .set_custom(false)?
        .set(Value::Float(value))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn dome_light_roundtrip_with_texture_and_portals() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_dome_light(&stage, sdf::path("/Dome")?)?
            .set_texture_file("./studio.hdr")?
            .set_texture_format(TextureFormat::Latlong)?
            .set_portals([sdf::path("/Dome/Portal")?])?
            .set_guide_radius(50.0)?
            .set_intensity(1.0)?;

        let dome = crate::schemas::lux::read_dome_light(&stage, &sdf::path("/Dome")?)?.expect("DomeLight");
        assert_eq!(dome.texture_file.as_deref(), Some("./studio.hdr"));
        assert_eq!(dome.texture_format, TextureFormat::Latlong);
        assert!((dome.guide_radius - 50.0).abs() < 1e-3);
        assert_eq!(dome.portals, vec!["/Dome/Portal".to_string()]);
        Ok(())
    }

    #[test]
    fn dome_light_1_authors_pole_axis() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_dome_light_1(&stage, sdf::path("/Dome")?)?
            .set_texture_file("./studio.hdr")?
            .set_pole_axis(PoleAxis::Z)?;

        // The lux reader's `read_dome_light` accepts both `DomeLight`
        // and `DomeLight_1` per the existing reader contract.
        let dome = crate::schemas::lux::read_dome_light(&stage, &sdf::path("/Dome")?)?.expect("DomeLight_1");
        assert_eq!(dome.texture_file.as_deref(), Some("./studio.hdr"));

        // poleAxis lands on the prim as a uniform token.
        match stage.field::<sdf::Value>("/Dome.poleAxis", sdf::FieldKey::Default)? {
            Some(sdf::Value::Token(t)) => assert_eq!(t, "Z"),
            other => panic!("expected token 'Z' for poleAxis, got {other:?}"),
        }
        Ok(())
    }
}
