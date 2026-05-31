//! `RenderProduct` authoring — one output artifact of a render.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::usd::{Prim, Stage};

use crate::schemas::common::{author_rel_targets, author_uniform_token, varying_attribute};
use crate::schemas::render::tokens::*;
use crate::schemas::render::types::ProductType;

use super::base::SettingsBaseSetters;

/// Author a `def RenderProduct` prim at `path`. Returns a chainable
/// [`RenderProductAuthor`] for the product-specific attributes plus the
/// shared base attributes via [`SettingsBaseSetters`] (which the product
/// may author to override the settings it is produced from).
pub fn define_render_product<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<RenderProductAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_RENDER_PRODUCT)?;
    Ok(RenderProductAuthor { prim })
}

pub struct RenderProductAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> RenderProductAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `productType` (`uniform token`).
    pub fn set_product_type(self, value: ProductType) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_PRODUCT_TYPE, value.as_token())?;
        Ok(self)
    }

    /// Set `productName` (`token`) — the output / display-driver name.
    /// Authored as a varying `token` (not `uniform`), per the schema.
    pub fn set_product_name(self, value: impl Into<String>) -> Result<Self> {
        varying_attribute(self.prim.stage(), self.prim.path(), A_PRODUCT_NAME, "token")?
            .set(Value::Token(value.into()))?;
        Ok(self)
    }

    /// Set the `orderedVars` relationship — the `RenderVar` prims composited
    /// into this product, in order.
    pub fn set_ordered_vars<I, P>(self, targets: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        author_rel_targets(self.prim.stage(), self.prim.path(), REL_ORDERED_VARS, targets)?;
        Ok(self)
    }
}

impl<'s> SettingsBaseSetters<'s> for RenderProductAuthor<'s> {
    fn prim(&self) -> &Prim<'s> {
        &self.prim
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::render::{read_render_product, ReadRenderProduct};
    use crate::sdf;

    #[test]
    fn render_product_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_render_product(&stage, sdf::path("/Render/Products/beauty")?)?
            .set_product_type(ProductType::Raster)?
            .set_product_name("beauty.exr")?
            // A product-level override of an inherited base attribute.
            .set_resolution([512, 512])?
            .set_ordered_vars([sdf::path("/Render/Vars/color")?, sdf::path("/Render/Vars/alpha")?])?;

        let p = read_render_product(&stage, &sdf::path("/Render/Products/beauty")?)?.expect("RenderProduct");
        assert_eq!(p.product_type, ProductType::Raster);
        assert_eq!(p.product_name, "beauty.exr");
        assert_eq!(p.base.resolution, [512, 512]);
        assert_eq!(
            p.ordered_vars,
            vec!["/Render/Vars/color".to_string(), "/Render/Vars/alpha".to_string()]
        );
        Ok(())
    }

    #[test]
    fn render_product_defaults_and_type_gate() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_render_product(&stage, sdf::path("/Render/Products/p")?)?;

        let p = read_render_product(&stage, &sdf::path("/Render/Products/p")?)?.expect("RenderProduct");
        assert_eq!(p, ReadRenderProduct::default());
        assert!(read_render_product(&stage, &sdf::path("/Missing")?)?.is_none());
        Ok(())
    }
}
