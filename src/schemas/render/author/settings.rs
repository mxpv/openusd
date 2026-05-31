//! `RenderSettings` authoring — the top-level render configuration.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::common::{author_rel_targets, author_uniform_token, author_uniform_token_vec};
use crate::schemas::render::tokens::*;

use super::base::SettingsBaseSetters;

/// Author a `def RenderSettings` prim at `path`. Returns a chainable
/// [`RenderSettingsAuthor`] for the settings-specific attributes plus the
/// shared base attributes via [`SettingsBaseSetters`].
pub fn define_render_settings<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<RenderSettingsAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_RENDER_SETTINGS)?;
    Ok(RenderSettingsAuthor { prim })
}

pub struct RenderSettingsAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> RenderSettingsAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set the `products` relationship — the `RenderProduct` prims to produce.
    pub fn set_products<I, P>(self, targets: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        author_rel_targets(self.prim.stage(), self.prim.path(), REL_PRODUCTS, targets)?;
        Ok(self)
    }

    /// Set `includedPurposes` (`uniform token[]`) — the `UsdGeomImageable`
    /// purposes included in the render.
    pub fn set_included_purposes<I, S>(self, purposes: I) -> Result<Self>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let purposes = purposes.into_iter().map(Into::into).collect();
        author_uniform_token_vec(self.prim.stage(), self.prim.path(), A_INCLUDED_PURPOSES, purposes)?;
        Ok(self)
    }

    /// Set `materialBindingPurposes` (`uniform token[]`) — the ordered
    /// material-binding resolution priority.
    pub fn set_material_binding_purposes<I, S>(self, purposes: I) -> Result<Self>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let purposes = purposes.into_iter().map(Into::into).collect();
        author_uniform_token_vec(
            self.prim.stage(),
            self.prim.path(),
            A_MATERIAL_BINDING_PURPOSES,
            purposes,
        )?;
        Ok(self)
    }

    /// Set `renderingColorSpace` (`uniform token`) — the renderer's linear
    /// working color space.
    pub fn set_rendering_color_space(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_RENDERING_COLOR_SPACE, value)?;
        Ok(self)
    }
}

impl<'s> SettingsBaseSetters<'s> for RenderSettingsAuthor<'s> {
    fn prim(&self) -> &Prim<'s> {
        &self.prim
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::render::{read_render_settings, AspectRatioConformPolicy};
    use crate::sdf;

    #[test]
    fn render_settings_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_render_settings(&stage, sdf::path("/Render/Settings")?)?
            .set_resolution([1280, 720])?
            .set_aspect_ratio_conform_policy(AspectRatioConformPolicy::AdjustApertureWidth)?
            .set_products([sdf::path("/Render/Products/beauty")?])?
            .set_included_purposes(["default", "render", "proxy"])?
            .set_material_binding_purposes(["full", ""])?
            .set_rendering_color_space("lin_rec709")?;

        let s = read_render_settings(&stage, &sdf::path("/Render/Settings")?)?.expect("RenderSettings");
        assert_eq!(s.base.resolution, [1280, 720]);
        assert_eq!(
            s.base.aspect_ratio_conform_policy,
            AspectRatioConformPolicy::AdjustApertureWidth
        );
        assert_eq!(s.products, vec!["/Render/Products/beauty".to_string()]);
        assert_eq!(s.included_purposes, vec!["default", "render", "proxy"]);
        assert_eq!(s.material_binding_purposes, vec!["full".to_string(), String::new()]);
        assert_eq!(s.rendering_color_space.as_deref(), Some("lin_rec709"));
        Ok(())
    }

    #[test]
    fn render_settings_defaults_and_type_gate() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_render_settings(&stage, sdf::path("/Render/Settings")?)?;

        let s = read_render_settings(&stage, &sdf::path("/Render/Settings")?)?.expect("RenderSettings");
        assert_eq!(s.included_purposes, vec!["default", "render"]);
        assert_eq!(s.material_binding_purposes, vec!["full".to_string(), String::new()]);
        assert_eq!(s.rendering_color_space, None);
        assert!(s.products.is_empty());

        // A non-RenderSettings prim reads back as None.
        stage.define_prim(sdf::path("/NotSettings")?)?.set_type_name("Scope")?;
        assert!(read_render_settings(&stage, &sdf::path("/NotSettings")?)?.is_none());
        Ok(())
    }
}
