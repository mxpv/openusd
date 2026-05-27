//! `LightAPI` applied schema authoring.
//!
//! The concrete light prim types (`RectLight`, `DistantLight`, etc.)
//! all `prepend apiSchemas = ["LightAPI"]` per Pixar's
//! `usdLux/schema.usda`, so they pick up these attributes implicitly via
//! the schema registry. For lights *not* covered by a built-in concrete
//! type — applying LightAPI to a Mesh, Volume, or other Gprim —
//! [`apply_light_api`] handles the explicit `apiSchemas += ["LightAPI"]`
//! step.
//!
//! The free functions below are shared by the concrete light authors:
//! each `*LightAuthor::set_intensity` etc. simply delegates here so the
//! attribute-name + type-name + default-value choices live in one place.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::lux::tokens::{
    API_LIGHT, A_COLOR, A_COLOR_TEMPERATURE, A_DIFFUSE, A_ENABLE_COLOR_TEMPERATURE, A_EXPOSURE, A_INTENSITY,
    A_NORMALIZE, A_SPECULAR, REL_FILTERS,
};

use super::common::{author_input_bool, author_input_color3f, author_input_float, author_rel_targets};

/// Apply `LightAPI` to the prim at `path` and return a chainable
/// [`LightAuthor`] for setting the 8 schema-defined input attributes
/// (intensity / exposure / diffuse / specular / normalize / color /
/// enableColorTemperature / colorTemperature) and the `light:filters`
/// relationship.
///
/// `apiSchemas += ["LightAPI"]` lands via
/// [`Prim::add_applied_schema`]. The prim spec must already exist on the
/// active edit target — use [`Stage::define_prim`] (or one of the
/// `define_*_light` helpers in sibling modules) first.
pub fn apply_light_api<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<LightAuthor<'s>> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_LIGHT)?;
    Ok(LightAuthor { prim })
}

/// Chainable LightAPI authoring handle.
///
/// LightAPI setters live on the [`LightApiSetters`] trait so concrete
/// light authors (e.g. `RectLightAuthor`) share the same fluent surface
/// without duplicated methods. Bring the trait into scope to use the
/// setters: `use openusd::schemas::lux::LightApiSetters;`.
pub struct LightAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> LightAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }
}

// ── Free functions ──────────────────────────────────────────────────
//
// These are crate-internal so concrete light authors (RectLightAuthor,
// SphereLightAuthor, …) can share the same attribute-write logic
// without re-deriving the type-name and attribute-name choices.

pub(crate) fn set_intensity(stage: &Stage, prim: &Path, value: f32) -> Result<()> {
    author_input_float(stage, prim, A_INTENSITY, value)
}

pub(crate) fn set_exposure(stage: &Stage, prim: &Path, value: f32) -> Result<()> {
    author_input_float(stage, prim, A_EXPOSURE, value)
}

pub(crate) fn set_diffuse(stage: &Stage, prim: &Path, value: f32) -> Result<()> {
    author_input_float(stage, prim, A_DIFFUSE, value)
}

pub(crate) fn set_specular(stage: &Stage, prim: &Path, value: f32) -> Result<()> {
    author_input_float(stage, prim, A_SPECULAR, value)
}

pub(crate) fn set_normalize(stage: &Stage, prim: &Path, value: bool) -> Result<()> {
    author_input_bool(stage, prim, A_NORMALIZE, value)
}

pub(crate) fn set_color(stage: &Stage, prim: &Path, value: [f32; 3]) -> Result<()> {
    author_input_color3f(stage, prim, A_COLOR, value)
}

pub(crate) fn set_enable_color_temperature(stage: &Stage, prim: &Path, value: bool) -> Result<()> {
    author_input_bool(stage, prim, A_ENABLE_COLOR_TEMPERATURE, value)
}

pub(crate) fn set_color_temperature(stage: &Stage, prim: &Path, value: f32) -> Result<()> {
    author_input_float(stage, prim, A_COLOR_TEMPERATURE, value)
}

pub(crate) fn set_filters<I, P>(stage: &Stage, prim: &Path, targets: I) -> Result<()>
where
    I: IntoIterator<Item = P>,
    P: Into<Path>,
{
    author_rel_targets(stage, prim, REL_FILTERS, targets)
}

/// Concrete light authors implement this trait to inherit the 9
/// LightAPI chainable setters. Each implementor exposes a `prim()`
/// accessor; the trait's default methods route every setter through the
/// shared free functions above so attribute-name + type-name choices
/// live in one place.
pub trait LightApiSetters<'s>: Sized {
    /// Borrow the underlying prim handle. Implementations typically just
    /// return `&self.prim`.
    fn prim(&self) -> &Prim<'s>;

    /// Set `inputs:intensity`. See [`LightAuthor::set_intensity`].
    fn set_intensity(self, value: f32) -> Result<Self> {
        set_intensity(self.prim().stage(), self.prim().path(), value)?;
        Ok(self)
    }

    /// Set `inputs:exposure`.
    fn set_exposure(self, value: f32) -> Result<Self> {
        set_exposure(self.prim().stage(), self.prim().path(), value)?;
        Ok(self)
    }

    /// Set `inputs:diffuse`.
    fn set_diffuse(self, value: f32) -> Result<Self> {
        set_diffuse(self.prim().stage(), self.prim().path(), value)?;
        Ok(self)
    }

    /// Set `inputs:specular`.
    fn set_specular(self, value: f32) -> Result<Self> {
        set_specular(self.prim().stage(), self.prim().path(), value)?;
        Ok(self)
    }

    /// Set `inputs:normalize`.
    fn set_normalize(self, value: bool) -> Result<Self> {
        set_normalize(self.prim().stage(), self.prim().path(), value)?;
        Ok(self)
    }

    /// Set `inputs:color`.
    fn set_color(self, value: [f32; 3]) -> Result<Self> {
        set_color(self.prim().stage(), self.prim().path(), value)?;
        Ok(self)
    }

    /// Set `inputs:enableColorTemperature`.
    fn set_enable_color_temperature(self, value: bool) -> Result<Self> {
        set_enable_color_temperature(self.prim().stage(), self.prim().path(), value)?;
        Ok(self)
    }

    /// Set `inputs:colorTemperature` in degrees Kelvin.
    fn set_color_temperature(self, value: f32) -> Result<Self> {
        set_color_temperature(self.prim().stage(), self.prim().path(), value)?;
        Ok(self)
    }

    /// Set the `light:filters` rel targets.
    fn set_filters<I, P>(self, targets: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        set_filters(self.prim().stage(), self.prim().path(), targets)?;
        Ok(self)
    }
}

impl<'s> LightApiSetters<'s> for LightAuthor<'s> {
    fn prim(&self) -> &Prim<'s> {
        &self.prim
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn apply_light_api_adds_api_and_writes_inputs() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Emitter")?.set_type_name("Mesh")?;
        apply_light_api(&stage, sdf::path("/Emitter")?)?
            .set_intensity(1500.0)?
            .set_exposure(1.5)?
            .set_diffuse(0.8)?
            .set_specular(1.2)?
            .set_normalize(true)?
            .set_color([1.0, 0.9, 0.8])?
            .set_enable_color_temperature(true)?
            .set_color_temperature(5500.0)?;

        // LightAPI ended up in apiSchemas.
        let api = stage.api_schemas(&sdf::path("/Emitter")?)?;
        assert!(api.iter().any(|s| s == "LightAPI"));

        match stage.field::<sdf::Value>("/Emitter.inputs:intensity", sdf::FieldKey::Default)? {
            Some(sdf::Value::Float(f)) => assert!((f - 1500.0).abs() < 1e-3),
            other => panic!("expected Float(1500.0) for intensity, got {other:?}"),
        }
        match stage.field::<sdf::Value>("/Emitter.inputs:color", sdf::FieldKey::Default)? {
            Some(sdf::Value::Vec3f(v)) => assert_eq!(v, [1.0, 0.9, 0.8]),
            other => panic!("expected Vec3f for color, got {other:?}"),
        }
        match stage.field::<sdf::Value>("/Emitter.inputs:enableColorTemperature", sdf::FieldKey::Default)? {
            Some(sdf::Value::Bool(b)) => assert!(b),
            other => panic!("expected Bool(true) for enableColorTemperature, got {other:?}"),
        }
        Ok(())
    }

    #[test]
    fn set_filters_writes_relationship_targets() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Emitter")?.set_type_name("Mesh")?;
        stage.define_prim("/Filter1")?.set_type_name("LightFilter")?;
        stage.define_prim("/Filter2")?.set_type_name("LightFilter")?;
        apply_light_api(&stage, sdf::path("/Emitter")?)?
            .set_filters([sdf::path("/Filter1")?, sdf::path("/Filter2")?])?;

        // Read back via the existing LightAPI reader.
        let light = crate::schemas::lux::read_light_api(&stage, &sdf::path("/Emitter")?)?.expect("LightAPI applied");
        assert_eq!(light.filters, vec!["/Filter1".to_string(), "/Filter2".to_string()],);
        Ok(())
    }

    #[test]
    fn round_trips_through_lightapi_reader() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Sun")?.set_type_name("Mesh")?;
        apply_light_api(&stage, sdf::path("/Sun")?)?
            .set_intensity(2000.0)?
            .set_color([1.0, 0.95, 0.85])?
            .set_normalize(true)?;

        let light = crate::schemas::lux::read_light_api(&stage, &sdf::path("/Sun")?)?.expect("LightAPI applied");
        assert!((light.intensity - 2000.0).abs() < 1e-3);
        assert!((light.color[1] - 0.95).abs() < 1e-3);
        assert!(light.normalize);
        // Unauthored attrs fall back to Pixar's defaults.
        assert!((light.exposure - 0.0).abs() < 1e-6);
        assert!((light.diffuse - 1.0).abs() < 1e-6);
        Ok(())
    }
}
