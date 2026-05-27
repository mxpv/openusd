//! `LightListAPI` applied schema authoring.
//!
//! Per `usdLux/schema.usda`, the cached light-list on a parent prim
//! has two fields: a `lightList` rel targeting the lights in the
//! subtree and a `lightList:cacheBehavior` token controlling how
//! consumers consult the cache.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Prim, Stage};

use crate::schemas::lux::tokens::{API_LIGHT_LIST, A_LIGHT_LIST_CACHE_BEHAVIOR, REL_LIGHT_LIST};
use crate::schemas::lux::types::LightListCacheBehavior;

use super::common::author_rel_targets;

/// Apply `LightListAPI` to the prim at `path` and return a chainable
/// [`LightListAuthor`] for the cached light-list contents.
///
/// Typically applied to a model-hierarchy prim above a payload so
/// consumers can discover lights without loading the heavy
/// payload — see the spec's "Publishing a Cached Light List" section.
pub fn apply_light_list<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<LightListAuthor<'s>> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_LIGHT_LIST)?;
    Ok(LightListAuthor { prim })
}

pub struct LightListAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> LightListAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set the `lightList` rel — paths to the cached set of lights.
    pub fn set_lights<I, P>(self, targets: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        author_rel_targets(self.prim.stage(), self.prim.path(), REL_LIGHT_LIST, targets)?;
        Ok(self)
    }

    /// Set `lightList:cacheBehavior` — controls how the cached list is
    /// consulted (`ignore` / `consumeAndContinue` / `consumeAndHalt`).
    /// The [`LightListCacheBehavior`] enum enforces the spec's
    /// allowedTokens at the type level.
    pub fn set_cache_behavior(self, behavior: LightListCacheBehavior) -> Result<Self> {
        let attr_path = self.prim.path().append_property(A_LIGHT_LIST_CACHE_BEHAVIOR)?;
        self.prim
            .stage()
            .create_attribute(attr_path, "token")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::Token(behavior.as_token().to_string()))?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn light_list_api_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/World")?.set_type_name("Xform")?;
        stage.define_prim("/World/Sun")?.set_type_name("DistantLight")?;
        stage.define_prim("/World/Lamp")?.set_type_name("SphereLight")?;
        apply_light_list(&stage, sdf::path("/World")?)?
            .set_lights([sdf::path("/World/Sun")?, sdf::path("/World/Lamp")?])?
            .set_cache_behavior(LightListCacheBehavior::ConsumeAndContinue)?;

        let list = crate::schemas::lux::read_light_list(&stage, &sdf::path("/World")?)?.expect("LightListAPI");
        assert_eq!(list.cache_behavior, LightListCacheBehavior::ConsumeAndContinue);
        assert_eq!(list.lights, vec!["/World/Sun".to_string(), "/World/Lamp".to_string()],);
        Ok(())
    }

    /// End-to-end check: author a complete lit scene with every concrete
    /// light type + ShapingAPI + ShadowAPI + LightListAPI, then read it
    /// back through the existing lux reader and assert every field
    /// matches.
    #[test]
    fn full_scene_roundtrip_authoring_to_reader() -> Result<()> {
        use crate::schemas::lux::{
            apply_shadow, apply_shaping, define_cylinder_light, define_disk_light, define_distant_light,
            define_dome_light, define_geometry_light, define_portal_light, define_rect_light, define_sphere_light,
            LightApiSetters, TextureFormat,
        };

        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/World")?.set_type_name("Xform")?;
        stage.define_prim("/World/Emitter")?.set_type_name("Mesh")?;

        // Every concrete light type the reader covers.
        define_distant_light(&stage, sdf::path("/World/Sun")?)?
            .set_angle_deg(0.53)?
            .set_color([1.0, 0.95, 0.85])?;
        define_sphere_light(&stage, sdf::path("/World/Bulb")?)?
            .set_radius(0.1)?
            .set_intensity(800.0)?;
        define_rect_light(&stage, sdf::path("/World/Panel")?)?
            .set_width(2.0)?
            .set_height(1.0)?;
        define_disk_light(&stage, sdf::path("/World/Disk")?)?.set_radius(0.5)?;
        define_cylinder_light(&stage, sdf::path("/World/Tube")?)?
            .set_length(2.0)?
            .set_treat_as_line(true)?;
        define_dome_light(&stage, sdf::path("/World/Dome")?)?.set_texture_format(TextureFormat::Latlong)?;
        define_geometry_light(&stage, sdf::path("/World/MeshLight")?)?.set_geometry(sdf::path("/World/Emitter")?)?;
        define_portal_light(&stage, sdf::path("/World/Portal")?)?.set_width(1.2)?;

        // Applied APIs on a shaped, shadowed light.
        apply_shaping(&stage, sdf::path("/World/Panel")?)?.set_cone_angle_deg(45.0)?;
        apply_shadow(&stage, sdf::path("/World/Panel")?)?.set_distance(10.0)?;

        // LightListAPI on the parent.
        apply_light_list(&stage, sdf::path("/World")?)?
            .set_lights([
                sdf::path("/World/Sun")?,
                sdf::path("/World/Bulb")?,
                sdf::path("/World/Panel")?,
                sdf::path("/World/Disk")?,
                sdf::path("/World/Tube")?,
                sdf::path("/World/Dome")?,
                sdf::path("/World/MeshLight")?,
                sdf::path("/World/Portal")?,
            ])?
            .set_cache_behavior(LightListCacheBehavior::ConsumeAndContinue)?;

        // Round-trip every prim through the reader.
        assert!(crate::schemas::lux::read_distant_light(&stage, &sdf::path("/World/Sun")?)?.is_some());
        assert!(crate::schemas::lux::read_sphere_light(&stage, &sdf::path("/World/Bulb")?)?.is_some());
        assert!(crate::schemas::lux::read_rect_light(&stage, &sdf::path("/World/Panel")?)?.is_some());
        assert!(crate::schemas::lux::read_disk_light(&stage, &sdf::path("/World/Disk")?)?.is_some());
        assert!(crate::schemas::lux::read_cylinder_light(&stage, &sdf::path("/World/Tube")?)?.is_some());
        assert!(crate::schemas::lux::read_dome_light(&stage, &sdf::path("/World/Dome")?)?.is_some());
        assert!(crate::schemas::lux::read_geometry_light(&stage, &sdf::path("/World/MeshLight")?)?.is_some());
        assert!(crate::schemas::lux::read_portal_light(&stage, &sdf::path("/World/Portal")?)?.is_some());

        let shaping =
            crate::schemas::lux::read_shaping(&stage, &sdf::path("/World/Panel")?)?.expect("ShapingAPI applied");
        assert!((shaping.cone_angle_deg - 45.0).abs() < 1e-3);

        let shadow = crate::schemas::lux::read_shadow(&stage, &sdf::path("/World/Panel")?)?.expect("ShadowAPI applied");
        assert!((shadow.distance - 10.0).abs() < 1e-3);

        let list = crate::schemas::lux::read_light_list(&stage, &sdf::path("/World")?)?.expect("LightListAPI applied");
        assert_eq!(list.lights.len(), 8);
        Ok(())
    }
}
