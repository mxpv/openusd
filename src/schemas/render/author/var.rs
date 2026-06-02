//! `RenderVar` authoring — one output channel (AOV).

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Prim, Stage};

use crate::schemas::common::author_uniform_token;
use crate::schemas::render::tokens::*;
use crate::schemas::render::types::SourceType;

/// Author a `def RenderVar` prim at `path`. Returns a chainable
/// [`RenderVarAuthor`].
pub fn define_render_var(stage: &Stage, path: impl Into<Path>) -> Result<RenderVarAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_RENDER_VAR)?;
    Ok(RenderVarAuthor { prim })
}

pub struct RenderVarAuthor {
    prim: Prim,
}

impl RenderVarAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `dataType` (`uniform token`) — the channel's USD attribute type.
    pub fn set_data_type(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_DATA_TYPE, value)?;
        Ok(self)
    }

    /// Set `sourceName` (`uniform string`) — the name the renderer looks up.
    pub fn set_source_name(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_string(self.prim.stage(), self.prim.path(), A_SOURCE_NAME, value.into())?;
        Ok(self)
    }

    /// Set `sourceType` (`uniform token`).
    pub fn set_source_type(self, value: SourceType) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_SOURCE_TYPE, value.as_token())?;
        Ok(self)
    }
}

/// Author a `uniform string` attribute — for `sourceName`.
fn author_uniform_string(stage: &Stage, prim: &Path, name: &str, value: String) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "string")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::String(value))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::render::{read_render_var, ReadRenderVar};
    use crate::sdf;

    #[test]
    fn render_var_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_render_var(&stage, sdf::path("/Render/Vars/N")?)?
            .set_data_type("normal3f")?
            .set_source_name("Nworld")?
            .set_source_type(SourceType::Primvar)?;

        let v = read_render_var(&stage, &sdf::path("/Render/Vars/N")?)?.expect("RenderVar");
        assert_eq!(v.data_type, "normal3f");
        assert_eq!(v.source_name, "Nworld");
        assert_eq!(v.source_type, SourceType::Primvar);
        Ok(())
    }

    #[test]
    fn render_var_defaults_and_type_gate() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_render_var(&stage, sdf::path("/Render/Vars/V")?)?;

        let v = read_render_var(&stage, &sdf::path("/Render/Vars/V")?)?.expect("RenderVar");
        assert_eq!(v, ReadRenderVar::default());
        assert_eq!(v.data_type, "color3f");
        assert_eq!(v.source_type, SourceType::Raw);
        assert!(read_render_var(&stage, &sdf::path("/Missing")?)?.is_none());
        Ok(())
    }
}
