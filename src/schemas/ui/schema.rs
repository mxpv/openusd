//! The UsdUI prim and applied-API views: [`Backdrop`], [`SceneGraphPrimAPI`],
//! and [`NodeGraphNodeAPI`].

use anyhow::Result;

use crate::sdf::{self, Variability};
use crate::usd::{Attribute, Prim, Stage};

use super::impl_ui_schema;
use super::tokens as tok;
use crate::schemas::common::{get_typed, get_with_api};

/// A labelled box drawn behind a group of nodes in a node-graph editor (C++
/// `UsdUIBackdrop`). It carries only `ui:description`; an editor that also lays
/// it out applies [`NodeGraphNodeAPI`] alongside.
#[derive(Clone, derive_more::Deref)]
pub struct Backdrop(Prim);

impl Backdrop {
    /// Author a `def Backdrop` prim at `path` (C++ `UsdUIBackdrop::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_BACKDROP)?))
    }

    /// Wrap `path` as a `Backdrop` if it is typed `Backdrop`
    /// (C++ `UsdUIBackdrop::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_BACKDROP).map(|o| o.map(Self))
    }

    /// The descriptive text shown inside the backdrop box.
    /// C++ `UsdUIBackdrop::GetDescriptionAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<String>()?`.
    pub fn description_attr(&self) -> Attribute {
        self.attribute(tok::A_DESCRIPTION)
    }

    /// Author `ui:description` (`uniform token`) (C++ `CreateDescriptionAttr`).
    pub fn create_description_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_DESCRIPTION, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }
}

impl_ui_schema!(typed Backdrop);

/// Outliner label and grouping for a prim (C++ `UsdUISceneGraphPrimAPI`,
/// single-apply). Adds the `ui:displayName` / `ui:displayGroup` hints.
#[derive(Clone, derive_more::Deref)]
pub struct SceneGraphPrimAPI(Prim);

impl SceneGraphPrimAPI {
    /// Apply `SceneGraphPrimAPI` to the prim at `path`
    /// (C++ `UsdUISceneGraphPrimAPI::Apply`). The prim is opened as `over`.
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage
                .override_prim(path)?
                .add_applied_schema(tok::API_SCENE_GRAPH_PRIM)?,
        ))
    }

    /// Wrap `path` as a `SceneGraphPrimAPI` if it carries `SceneGraphPrimAPI` in
    /// its `apiSchemas` (C++ `UsdUISceneGraphPrimAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_SCENE_GRAPH_PRIM]).map(|o| o.map(Self))
    }

    /// The human-readable name an outliner shows instead of the prim name.
    /// C++ `UsdUISceneGraphPrimAPI::GetDisplayNameAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<String>()?`.
    pub fn display_name_attr(&self) -> Attribute {
        self.attribute(tok::A_DISPLAY_NAME)
    }

    /// Author `ui:displayName` (`uniform token`) (C++ `CreateDisplayNameAttr`).
    pub fn create_display_name_attr(&self) -> Result<Attribute> {
        self.uniform_token(tok::A_DISPLAY_NAME)
    }

    /// The outliner group this prim sorts under.
    /// C++ `UsdUISceneGraphPrimAPI::GetDisplayGroupAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<String>()?`.
    pub fn display_group_attr(&self) -> Attribute {
        self.attribute(tok::A_DISPLAY_GROUP)
    }

    /// Author `ui:displayGroup` (`uniform token`) (C++ `CreateDisplayGroupAttr`).
    pub fn create_display_group_attr(&self) -> Result<Attribute> {
        self.uniform_token(tok::A_DISPLAY_GROUP)
    }

    fn uniform_token(&self, name: &str) -> Result<Attribute> {
        Ok(self
            .create_attribute(name, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }
}

impl_ui_schema!(single_api SceneGraphPrimAPI);

/// Layout of a shading node in a node-graph editor (C++ `UsdUINodeGraphNodeAPI`,
/// single-apply): the node's position, size, stacking order, display color,
/// icon, expansion state, and documentation URI.
#[derive(Clone, derive_more::Deref)]
pub struct NodeGraphNodeAPI(Prim);

impl NodeGraphNodeAPI {
    /// Apply `NodeGraphNodeAPI` to the prim at `path`
    /// (C++ `UsdUINodeGraphNodeAPI::Apply`). The prim is opened as `over`.
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.override_prim(path)?.add_applied_schema(tok::API_NODEGRAPH_NODE)?,
        ))
    }

    /// Wrap `path` as a `NodeGraphNodeAPI` if it carries `NodeGraphNodeAPI` in
    /// its `apiSchemas` (C++ `UsdUINodeGraphNodeAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_NODEGRAPH_NODE]).map(|o| o.map(Self))
    }

    /// The node's position in the editor canvas, in editor units.
    /// C++ `UsdUINodeGraphNodeAPI::GetPosAttr`.
    ///
    /// Type `uniform float2`. Fetch with `get::<gf::Vec2f>()?`.
    pub fn pos_attr(&self) -> Attribute {
        self.attribute(tok::A_NODE_POS)
    }

    /// Author `ui:nodegraph:node:pos` (`uniform float2`) (C++ `CreatePosAttr`).
    pub fn create_pos_attr(&self) -> Result<Attribute> {
        self.uniform(tok::A_NODE_POS, "float2")
    }

    /// The node's size in the editor canvas, in editor units.
    /// C++ `UsdUINodeGraphNodeAPI::GetSizeAttr`.
    ///
    /// Type `uniform float2`. Fetch with `get::<gf::Vec2f>()?`.
    pub fn size_attr(&self) -> Attribute {
        self.attribute(tok::A_NODE_SIZE)
    }

    /// Author `ui:nodegraph:node:size` (`uniform float2`) (C++ `CreateSizeAttr`).
    pub fn create_size_attr(&self) -> Result<Attribute> {
        self.uniform(tok::A_NODE_SIZE, "float2")
    }

    /// The node's draw order among overlapping nodes; higher draws on top.
    /// C++ `UsdUINodeGraphNodeAPI::GetStackingOrderAttr`.
    ///
    /// Type `uniform int`. Fetch with `get::<i32>()?`.
    pub fn stacking_order_attr(&self) -> Attribute {
        self.attribute(tok::A_NODE_STACKING_ORDER)
    }

    /// Author `ui:nodegraph:node:stackingOrder` (`uniform int`)
    /// (C++ `CreateStackingOrderAttr`).
    pub fn create_stacking_order_attr(&self) -> Result<Attribute> {
        self.uniform(tok::A_NODE_STACKING_ORDER, "int")
    }

    /// The node's background tint in the editor.
    /// C++ `UsdUINodeGraphNodeAPI::GetDisplayColorAttr`.
    ///
    /// Type `uniform color3f`. Fetch with `get::<gf::Vec3f>()?`.
    pub fn display_color_attr(&self) -> Attribute {
        self.attribute(tok::A_NODE_DISPLAY_COLOR)
    }

    /// Author `ui:nodegraph:node:displayColor` (`uniform color3f`)
    /// (C++ `CreateDisplayColorAttr`).
    pub fn create_display_color_attr(&self) -> Result<Attribute> {
        self.uniform(tok::A_NODE_DISPLAY_COLOR, "color3f")
    }

    /// An icon image shown on the collapsed node.
    /// C++ `UsdUINodeGraphNodeAPI::GetIconAttr`.
    ///
    /// Type `uniform asset`. Fetch with `get::<sdf::Value>()?` (an
    /// [`sdf::Value::AssetPath`]).
    pub fn icon_attr(&self) -> Attribute {
        self.attribute(tok::A_NODE_ICON)
    }

    /// Author `ui:nodegraph:node:icon` (`uniform asset`) (C++ `CreateIconAttr`).
    pub fn create_icon_attr(&self) -> Result<Attribute> {
        self.uniform(tok::A_NODE_ICON, "asset")
    }

    /// How the node renders (open / closed / minimized).
    /// C++ `UsdUINodeGraphNodeAPI::GetExpansionStateAttr`.
    ///
    /// Type `uniform token`. Fetch with
    /// `get::<`[`ExpansionState`](super::ExpansionState)`>()?`.
    pub fn expansion_state_attr(&self) -> Attribute {
        self.attribute(tok::A_NODE_EXPANSION_STATE)
    }

    /// Author `ui:nodegraph:node:expansionState` (`uniform token`)
    /// (C++ `CreateExpansionStateAttr`). Pass an
    /// [`ExpansionState`](super::ExpansionState) to `set`.
    pub fn create_expansion_state_attr(&self) -> Result<Attribute> {
        self.uniform(tok::A_NODE_EXPANSION_STATE, "token")
    }

    /// A documentation URI for the node.
    /// C++ `UsdUINodeGraphNodeAPI::GetDocURIAttr`.
    ///
    /// Type `uniform string`. Fetch with `get::<String>()?`.
    pub fn doc_uri_attr(&self) -> Attribute {
        self.attribute(tok::A_NODE_DOC_URI)
    }

    /// Author `ui:nodegraph:node:docURI` (`uniform string`)
    /// (C++ `CreateDocURIAttr`).
    pub fn create_doc_uri_attr(&self) -> Result<Attribute> {
        self.uniform(tok::A_NODE_DOC_URI, "string")
    }

    fn uniform(&self, name: &str, type_name: &str) -> Result<Attribute> {
        Ok(self
            .create_attribute(name, type_name)?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }
}

impl_ui_schema!(single_api NodeGraphNodeAPI);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf;
    use crate::schemas::ui::ExpansionState;
    use crate::usd::SchemaBase;

    #[test]
    fn scene_graph_prim_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim(sdf::path("/World/Mesh")?)?.set_type_name("Mesh")?;
        let sg = SceneGraphPrimAPI::apply(&stage, "/World/Mesh")?;
        sg.create_display_name_attr()?.set("Hero Mesh".to_string())?;
        sg.create_display_group_attr()?.set("Characters".to_string())?;

        let p = SceneGraphPrimAPI::get(&stage, "/World/Mesh")?.expect("SceneGraphPrimAPI");
        assert_eq!(p.display_name_attr().get::<String>()?.as_deref(), Some("Hero Mesh"));
        assert_eq!(p.display_group_attr().get::<String>()?.as_deref(), Some("Characters"));

        // Unapplied prim → None.
        stage.define_prim(sdf::path("/Bare")?)?.set_type_name("Scope")?;
        assert!(SceneGraphPrimAPI::get(&stage, "/Bare")?.is_none());
        Ok(())
    }

    #[test]
    fn nodegraph_node_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim(sdf::path("/Mat/Shader")?)?.set_type_name("Shader")?;
        let n = NodeGraphNodeAPI::apply(&stage, "/Mat/Shader")?;
        n.create_pos_attr()?.set(gf::vec2f(12.0, 34.0))?;
        n.create_size_attr()?.set(gf::vec2f(180.0, 90.0))?;
        n.create_stacking_order_attr()?.set(3)?;
        n.create_display_color_attr()?.set(gf::vec3f(0.2, 0.4, 0.8))?;
        n.create_icon_attr()?.set(sdf::Value::AssetPath("./node.png".into()))?;
        n.create_expansion_state_attr()?.set(ExpansionState::Minimized)?;
        n.create_doc_uri_attr()?.set("https://example.com/node".to_string())?;

        let n = NodeGraphNodeAPI::get(&stage, "/Mat/Shader")?.expect("NodeGraphNodeAPI");
        assert_eq!(n.pos_attr().get::<gf::Vec2f>()?, Some(gf::vec2f(12.0, 34.0)));
        assert_eq!(n.size_attr().get::<gf::Vec2f>()?, Some(gf::vec2f(180.0, 90.0)));
        assert_eq!(n.stacking_order_attr().get::<i32>()?, Some(3));
        assert_eq!(
            n.display_color_attr().get::<gf::Vec3f>()?,
            Some(gf::vec3f(0.2, 0.4, 0.8))
        );
        assert_eq!(
            n.expansion_state_attr().get::<ExpansionState>()?,
            Some(ExpansionState::Minimized)
        );
        assert_eq!(
            n.doc_uri_attr().get::<String>()?.as_deref(),
            Some("https://example.com/node")
        );
        Ok(())
    }

    #[test]
    fn backdrop_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        Backdrop::define(&stage, "/Mat/Note")?
            .create_description_attr()?
            .set("lighting nodes".to_string())?;

        let b = Backdrop::get(&stage, "/Mat/Note")?.expect("Backdrop");
        assert_eq!(b.description_attr().get::<String>()?.as_deref(), Some("lighting nodes"));
        assert!(b.is_concrete());
        Ok(())
    }
}
