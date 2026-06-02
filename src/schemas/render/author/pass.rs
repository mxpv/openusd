//! `RenderPass` authoring — a node in a multi-pass render graph.
//!
//! Covers the scalar attributes, the `renderSource` / `inputPasses`
//! relationships, and the two collection `includeRoot` flags. The
//! `renderVisibility` / `cameraVisibility` / `prune` / `matte`
//! collection-membership relationships (a multi-apply `CollectionAPI`) are
//! deferred until collection-membership evaluation lands.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Prim, Stage};

use crate::schemas::common::{author_rel_targets, author_uniform_asset, author_uniform_token};
use crate::schemas::render::tokens::*;

/// Author a `def RenderPass` prim at `path`. Returns a chainable
/// [`RenderPassAuthor`].
pub fn define_render_pass(stage: &Stage, path: impl Into<Path>) -> Result<RenderPassAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_RENDER_PASS)?;
    Ok(RenderPassAuthor { prim })
}

pub struct RenderPassAuthor {
    prim: Prim,
}

impl RenderPassAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `passType` (`uniform token`).
    pub fn set_pass_type(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_PASS_TYPE, value)?;
        Ok(self)
    }

    /// Set `command` (`uniform string[]`) — command + args generating the pass.
    pub fn set_command<I, S>(self, command: I) -> Result<Self>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let command = command.into_iter().map(Into::into).collect();
        author_uniform_string_vec(self.prim.stage(), self.prim.path(), A_COMMAND, command)?;
        Ok(self)
    }

    /// Set `fileName` (`uniform asset`).
    pub fn set_file_name(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_asset(self.prim.stage(), self.prim.path(), A_FILE_NAME, value)?;
        Ok(self)
    }

    /// Set the `renderSource` relationship — the object to render.
    pub fn set_render_source(self, target: impl Into<Path>) -> Result<Self> {
        author_rel_targets(self.prim.stage(), self.prim.path(), REL_RENDER_SOURCE, [target.into()])?;
        Ok(self)
    }

    /// Set the `inputPasses` relationship — passes this one depends on.
    pub fn set_input_passes<I, P>(self, targets: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        author_rel_targets(self.prim.stage(), self.prim.path(), REL_INPUT_PASSES, targets)?;
        Ok(self)
    }

    /// Set `collection:renderVisibility:includeRoot` (`uniform bool`).
    pub fn set_render_visibility_include_root(self, value: bool) -> Result<Self> {
        author_uniform_bool(
            self.prim.stage(),
            self.prim.path(),
            A_RENDER_VISIBILITY_INCLUDE_ROOT,
            value,
        )?;
        Ok(self)
    }

    /// Set `collection:cameraVisibility:includeRoot` (`uniform bool`).
    pub fn set_camera_visibility_include_root(self, value: bool) -> Result<Self> {
        author_uniform_bool(
            self.prim.stage(),
            self.prim.path(),
            A_CAMERA_VISIBILITY_INCLUDE_ROOT,
            value,
        )?;
        Ok(self)
    }
}

fn author_uniform_bool(stage: &Stage, prim: &Path, name: &str, value: bool) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "bool")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Bool(value))?;
    Ok(())
}

fn author_uniform_string_vec(stage: &Stage, prim: &Path, name: &str, value: Vec<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "string[]")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::StringVec(value))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::render::{read_render_pass, ReadRenderPass};
    use crate::sdf;

    #[test]
    fn render_pass_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_render_pass(&stage, sdf::path("/Render/Passes/beauty")?)?
            .set_pass_type("prman")?
            .set_command(["prman", "-t:0", "{fileName}"])?
            .set_file_name("./beauty.rib")?
            .set_render_source(sdf::path("/Render/Settings")?)?
            .set_input_passes([sdf::path("/Render/Passes/shadow")?])?
            .set_camera_visibility_include_root(false)?;

        let p = read_render_pass(&stage, &sdf::path("/Render/Passes/beauty")?)?.expect("RenderPass");
        assert_eq!(p.pass_type.as_deref(), Some("prman"));
        assert_eq!(p.command, vec!["prman", "-t:0", "{fileName}"]);
        assert_eq!(p.file_name.as_deref(), Some("./beauty.rib"));
        assert_eq!(p.render_source.as_deref(), Some("/Render/Settings"));
        assert_eq!(p.input_passes, vec!["/Render/Passes/shadow".to_string()]);
        // Authored false; the unauthored renderVisibility flag keeps its default.
        assert!(!p.camera_visibility_include_root);
        assert!(p.render_visibility_include_root);
        Ok(())
    }

    #[test]
    fn render_pass_defaults_and_type_gate() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_render_pass(&stage, sdf::path("/Render/Passes/p")?)?;

        let p = read_render_pass(&stage, &sdf::path("/Render/Passes/p")?)?.expect("RenderPass");
        assert_eq!(p, ReadRenderPass::default());
        assert!(p.render_visibility_include_root); // includeRoot defaults to true
        assert!(read_render_pass(&stage, &sdf::path("/Missing")?)?.is_none());
        Ok(())
    }
}
