//! Authoring for the [UsdUI](super) schema family.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Prim, Stage};

use crate::schemas::common::author_uniform_token;
use crate::schemas::ui::tokens::*;
use crate::schemas::ui::types::ExpansionState;

/// Apply `SceneGraphPrimAPI` to `prim` and return a chainable author for
/// `ui:displayName` / `ui:displayGroup`.
pub fn apply_scene_graph_prim<'s>(stage: &'s Stage, prim: impl Into<Path>) -> Result<SceneGraphPrimAuthor<'s>> {
    Ok(SceneGraphPrimAuthor {
        prim: apply_api(stage, prim.into(), API_SCENE_GRAPH_PRIM)?,
    })
}

pub struct SceneGraphPrimAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> SceneGraphPrimAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `ui:displayName` (`uniform token`).
    pub fn set_display_name(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_DISPLAY_NAME, value)?;
        Ok(self)
    }

    /// Set `ui:displayGroup` (`uniform token`).
    pub fn set_display_group(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_DISPLAY_GROUP, value)?;
        Ok(self)
    }
}

/// Apply `NodeGraphNodeAPI` to `prim` and return a chainable author for the
/// node-editor layout attributes.
pub fn apply_nodegraph_node<'s>(stage: &'s Stage, prim: impl Into<Path>) -> Result<NodeGraphNodeAuthor<'s>> {
    Ok(NodeGraphNodeAuthor {
        prim: apply_api(stage, prim.into(), API_NODEGRAPH_NODE)?,
    })
}

pub struct NodeGraphNodeAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> NodeGraphNodeAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `ui:nodegraph:node:pos` (`uniform float2`).
    pub fn set_pos(self, value: [f32; 2]) -> Result<Self> {
        author_uniform_float2(self.prim.stage(), self.prim.path(), A_NODE_POS, value)?;
        Ok(self)
    }

    /// Set `ui:nodegraph:node:size` (`uniform float2`).
    pub fn set_size(self, value: [f32; 2]) -> Result<Self> {
        author_uniform_float2(self.prim.stage(), self.prim.path(), A_NODE_SIZE, value)?;
        Ok(self)
    }

    /// Set `ui:nodegraph:node:stackingOrder` (`uniform int`).
    pub fn set_stacking_order(self, value: i32) -> Result<Self> {
        author_uniform_int(self.prim.stage(), self.prim.path(), A_NODE_STACKING_ORDER, value)?;
        Ok(self)
    }

    /// Set `ui:nodegraph:node:displayColor` (`uniform color3f`).
    pub fn set_display_color(self, value: [f32; 3]) -> Result<Self> {
        author_uniform_color3f(self.prim.stage(), self.prim.path(), A_NODE_DISPLAY_COLOR, value)?;
        Ok(self)
    }

    /// Set `ui:nodegraph:node:icon` (`uniform asset`).
    pub fn set_icon(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_asset(self.prim.stage(), self.prim.path(), A_NODE_ICON, value.into())?;
        Ok(self)
    }

    /// Set `ui:nodegraph:node:expansionState` (`uniform token`).
    pub fn set_expansion_state(self, value: ExpansionState) -> Result<Self> {
        author_uniform_token(
            self.prim.stage(),
            self.prim.path(),
            A_NODE_EXPANSION_STATE,
            value.as_token(),
        )?;
        Ok(self)
    }

    /// Set `ui:nodegraph:node:docURI` (`uniform string`).
    pub fn set_doc_uri(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_string(self.prim.stage(), self.prim.path(), A_NODE_DOC_URI, value.into())?;
        Ok(self)
    }
}

/// Author a `def Backdrop` prim at `path`. Returns a chainable
/// [`BackdropAuthor`].
pub fn define_backdrop<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<BackdropAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_BACKDROP)?;
    Ok(BackdropAuthor { prim })
}

pub struct BackdropAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> BackdropAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `ui:description` (`uniform token`).
    pub fn set_description(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_DESCRIPTION, value)?;
        Ok(self)
    }
}

/// Ensure `prim` exists on the edit target and carries `api` in its
/// `apiSchemas`, returning a handle to it.
fn apply_api<'s>(stage: &'s Stage, prim: Path, api: &str) -> Result<Prim<'s>> {
    stage.override_prim(prim.clone())?;
    Ok(Prim::new(stage, prim).add_applied_schema(api)?)
}

fn author_uniform_float2(stage: &Stage, prim: &Path, name: &str, value: [f32; 2]) -> Result<()> {
    uniform(stage, prim, name, "float2")?.set(Value::Vec2f(value))?;
    Ok(())
}

fn author_uniform_color3f(stage: &Stage, prim: &Path, name: &str, value: [f32; 3]) -> Result<()> {
    uniform(stage, prim, name, "color3f")?.set(Value::Vec3f(value))?;
    Ok(())
}

fn author_uniform_int(stage: &Stage, prim: &Path, name: &str, value: i32) -> Result<()> {
    uniform(stage, prim, name, "int")?.set(Value::Int(value))?;
    Ok(())
}

fn author_uniform_asset(stage: &Stage, prim: &Path, name: &str, value: String) -> Result<()> {
    uniform(stage, prim, name, "asset")?.set(Value::AssetPath(value))?;
    Ok(())
}

fn author_uniform_string(stage: &Stage, prim: &Path, name: &str, value: String) -> Result<()> {
    uniform(stage, prim, name, "string")?.set(Value::String(value))?;
    Ok(())
}

/// Create a `uniform`, `custom = false` attribute of `type_name` on `prim`,
/// returning the handle for the caller to set its value.
fn uniform<'s>(stage: &'s Stage, prim: &Path, name: &str, type_name: &str) -> Result<crate::usd::Attribute<'s>> {
    Ok(stage
        .create_attribute(prim.append_property(name)?, type_name)?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?)
}
