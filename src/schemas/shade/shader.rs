//! `UsdShadeShader` + `NodeDefAPI` authoring.
//!
//! A Shader is a `def Shader` prim carrying NodeDefAPI's `info:*`
//! attributes that identify the shading node (by registry id, source
//! asset, or inline source) plus typed `inputs:` / `outputs:`.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Attribute, Prim, Stage};

use crate::schemas::common::author_uniform_token;

use super::connectable::{create_input, create_output};
use super::tokens::{
    A_INFO_ID, A_INFO_IMPLEMENTATION_SOURCE, A_INFO_SOURCE_ASSET, A_INFO_SOURCE_ASSET_SUBIDENTIFIER,
    A_INFO_SOURCE_CODE, T_SHADER,
};
use super::types::ImplementationSource;

/// Author a `def Shader` prim at `path` and return a chainable
/// [`ShaderAuthor`].
pub fn define_shader<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<ShaderAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_SHADER)?;
    Ok(ShaderAuthor { prim })
}

/// Chainable Shader authoring handle. Mirrors C++ `UsdShadeShader`
/// (which is `UsdShadeNodeDefAPI` applied to a `Shader` prim).
pub struct ShaderAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> ShaderAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Borrow the underlying prim handle.
    pub fn prim(&self) -> &Prim<'s> {
        &self.prim
    }

    /// Set `info:id` (uniform token) — the Sdr registry identifier,
    /// e.g. `UsdPreviewSurface` or `UsdUVTexture`. Authoring an id
    /// implies `info:implementationSource = "id"` (the schema default),
    /// so the latter is left unauthored unless set explicitly.
    pub fn set_id(self, id: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_INFO_ID, id)?;
        Ok(self)
    }

    /// Set `info:implementationSource` (uniform token, `id` /
    /// `sourceAsset` / `sourceCode`). Defaults to `id` per the schema
    /// when unauthored.
    pub fn set_implementation_source(self, source: ImplementationSource) -> Result<Self> {
        author_uniform_token(
            self.prim.stage(),
            self.prim.path(),
            A_INFO_IMPLEMENTATION_SOURCE,
            source.as_token(),
        )?;
        Ok(self)
    }

    /// Set `info:sourceAsset` (asset) — path to a shader source asset
    /// parsed by an Sdr plugin (e.g. an `.mdl` / `.osl` file). Pairs
    /// with `info:implementationSource = "sourceAsset"`.
    pub fn set_source_asset(self, asset: impl Into<String>) -> Result<Self> {
        author_asset(self.prim.stage(), self.prim.path(), A_INFO_SOURCE_ASSET, asset)?;
        Ok(self)
    }

    /// Set `info:sourceAsset:subIdentifier` (token) — selects one
    /// definition inside a multi-shader source asset.
    pub fn set_source_asset_subidentifier(self, sub: impl Into<String>) -> Result<Self> {
        author_uniform_token(
            self.prim.stage(),
            self.prim.path(),
            A_INFO_SOURCE_ASSET_SUBIDENTIFIER,
            sub,
        )?;
        Ok(self)
    }

    /// Set `info:sourceCode` (uniform string) — inline shader source.
    /// Pairs with `info:implementationSource = "sourceCode"`.
    pub fn set_source_code(self, code: impl Into<String>) -> Result<Self> {
        let attr = self.prim.path().append_property(A_INFO_SOURCE_CODE)?;
        self.prim
            .stage()
            .create_attribute(attr, "string")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::String(code.into()))?;
        Ok(self)
    }

    /// Create a `inputs:<base>` attribute of `type_name`. Returns the
    /// [`Attribute`] handle — chain `.set(value)` for a default or
    /// `.set_connections([..])` to wire it to another property.
    pub fn create_input(&self, base: &str, type_name: &str) -> Result<Attribute<'s>> {
        create_input(&self.prim, base, type_name)
    }

    /// Create an `outputs:<base>` attribute of `type_name`.
    pub fn create_output(&self, base: &str, type_name: &str) -> Result<Attribute<'s>> {
        create_output(&self.prim, base, type_name)
    }
}

/// Author a `uniform asset` attribute. NodeDefAPI `info:*` asset fields
/// (`info:sourceAsset`) are uniform per the UsdShade schema.
fn author_asset(stage: &Stage, prim: &Path, name: &str, value: impl Into<String>) -> Result<()> {
    let attr = prim.append_property(name)?;
    stage
        .create_attribute(attr, "asset")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::AssetPath(value.into()))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn shader_id_and_inputs() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let shader = define_shader(&stage, sdf::path("/Mat/Surface")?)?.set_id("UsdPreviewSurface")?;
        shader
            .create_input("diffuseColor", "color3f")?
            .set(Value::Vec3f([0.8, 0.2, 0.2]))?;
        shader.create_output("surface", "token")?;

        assert_eq!(stage.type_name(&sdf::path("/Mat/Surface")?)?.as_deref(), Some("Shader"));
        assert_eq!(
            stage.field::<sdf::Value>("/Mat/Surface.info:id", sdf::FieldKey::Default)?,
            Some(sdf::Value::Token("UsdPreviewSurface".into())),
        );
        assert_eq!(
            stage.field::<sdf::Value>("/Mat/Surface.inputs:diffuseColor", sdf::FieldKey::Default)?,
            Some(sdf::Value::Vec3f([0.8, 0.2, 0.2])),
        );
        assert_eq!(
            stage.spec_type("/Mat/Surface.outputs:surface")?,
            Some(sdf::SpecType::Attribute),
        );
        Ok(())
    }

    #[test]
    fn shader_source_asset() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_shader(&stage, sdf::path("/Mat/MdlShader")?)?
            .set_implementation_source(ImplementationSource::SourceAsset)?
            .set_source_asset("./OmniPBR.mdl")?
            .set_source_asset_subidentifier("OmniPBR")?;

        assert_eq!(
            stage.field::<sdf::Value>("/Mat/MdlShader.info:implementationSource", sdf::FieldKey::Default)?,
            Some(sdf::Value::Token("sourceAsset".into())),
        );
        assert_eq!(
            stage.field::<sdf::Value>("/Mat/MdlShader.info:sourceAsset", sdf::FieldKey::Default)?,
            Some(sdf::Value::AssetPath("./OmniPBR.mdl".into())),
        );
        Ok(())
    }
}
