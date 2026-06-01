//! UsdUI schema reader + authoring.
//!
//! Decodes and authors Pixar's `UsdUI` family - cosmetic metadata that
//! authoring tools use to label outliners and lay out node-graph editors.
//! All properties live under the `ui:` namespace.
//!
//! - [`tokens::API_SCENE_GRAPH_PRIM`] (applied) - `ui:displayName` /
//!   `ui:displayGroup` for the outliner.
//! - [`tokens::API_NODEGRAPH_NODE`] (applied) - a shading node's editor
//!   layout (position, size, color, icon, expansion state, doc URI).
//! - [`tokens::T_BACKDROP`] (concrete prim) - a labelled box behind a group
//!   of nodes; also carries the NodeGraphNode layout attributes.
//!
//! UsdUI attributes have no spec defaults, so unauthored fields read as
//! `None`.

pub mod tokens;

mod author;
mod read;
mod types;

pub use author::{
    apply_nodegraph_node, apply_scene_graph_prim, define_backdrop, BackdropAuthor, NodeGraphNodeAuthor,
    SceneGraphPrimAuthor,
};
pub use read::{read_backdrop, read_nodegraph_node, read_scene_graph_prim};
pub use types::{ExpansionState, ReadBackdrop, ReadNodeGraphNode, ReadSceneGraphPrim};

#[cfg(test)]
mod tests {
    use super::tokens::API_SCENE_GRAPH_PRIM;
    use super::*;
    use crate::sdf;
    use crate::usd::Stage;
    use anyhow::Result;

    #[test]
    fn scene_graph_prim_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim(sdf::path("/World/Mesh")?)?.set_type_name("Mesh")?;
        apply_scene_graph_prim(&stage, sdf::path("/World/Mesh")?)?
            .set_display_name("Hero Mesh")?
            .set_display_group("Characters")?;

        assert!(stage.has_api_schema(&sdf::path("/World/Mesh")?, API_SCENE_GRAPH_PRIM)?);
        let p = read_scene_graph_prim(&stage, &sdf::path("/World/Mesh")?)?.expect("SceneGraphPrimAPI");
        assert_eq!(p.display_name.as_deref(), Some("Hero Mesh"));
        assert_eq!(p.display_group.as_deref(), Some("Characters"));

        // Unapplied prim → None.
        stage.define_prim(sdf::path("/Bare")?)?.set_type_name("Scope")?;
        assert!(read_scene_graph_prim(&stage, &sdf::path("/Bare")?)?.is_none());
        Ok(())
    }

    #[test]
    fn nodegraph_node_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim(sdf::path("/Mat/Shader")?)?.set_type_name("Shader")?;
        apply_nodegraph_node(&stage, sdf::path("/Mat/Shader")?)?
            .set_pos([12.0, 34.0])?
            .set_size([180.0, 90.0])?
            .set_stacking_order(3)?
            .set_display_color([0.2, 0.4, 0.8])?
            .set_icon("./node.png")?
            .set_expansion_state(ExpansionState::Minimized)?
            .set_doc_uri("https://example.com/node")?;

        let n = read_nodegraph_node(&stage, &sdf::path("/Mat/Shader")?)?.expect("NodeGraphNodeAPI");
        assert_eq!(n.pos, Some([12.0, 34.0]));
        assert_eq!(n.size, Some([180.0, 90.0]));
        assert_eq!(n.stacking_order, Some(3));
        assert_eq!(n.display_color, Some([0.2, 0.4, 0.8]));
        assert_eq!(n.icon.as_deref(), Some("./node.png"));
        assert_eq!(n.expansion_state, Some(ExpansionState::Minimized));
        assert_eq!(n.doc_uri.as_deref(), Some("https://example.com/node"));
        Ok(())
    }

    #[test]
    fn backdrop_roundtrip_and_defaults() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_backdrop(&stage, sdf::path("/Mat/Note")?)?.set_description("lighting nodes")?;

        let b = read_backdrop(&stage, &sdf::path("/Mat/Note")?)?.expect("Backdrop");
        assert_eq!(b.description.as_deref(), Some("lighting nodes"));

        // A backdrop with no layout authored reads default NodeGraphNode fields.
        let n = read_nodegraph_node(&stage, &sdf::path("/Mat/Note")?)?.expect("Backdrop carries node layout");
        assert_eq!(n, ReadNodeGraphNode::default());
        Ok(())
    }
}
