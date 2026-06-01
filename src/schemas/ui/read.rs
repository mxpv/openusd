//! Readers for the [UsdUI](super) schema family.

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::Stage;

use super::tokens::*;
use super::types::*;

/// Read `SceneGraphPrimAPI` (displayName / displayGroup). Returns `None`
/// unless the API is applied on `prim`.
pub fn read_scene_graph_prim(stage: &Stage, prim: &Path) -> Result<Option<ReadSceneGraphPrim>> {
    if !stage.has_api_schema(prim, API_SCENE_GRAPH_PRIM)? {
        return Ok(None);
    }
    Ok(Some(ReadSceneGraphPrim {
        display_name: read_token(stage, prim, A_DISPLAY_NAME)?,
        display_group: read_token(stage, prim, A_DISPLAY_GROUP)?,
    }))
}

/// Read `NodeGraphNodeAPI` layout. Returns `None` unless the API is applied
/// (or the prim is a `Backdrop`, which carries the same layout attributes).
pub fn read_nodegraph_node(stage: &Stage, prim: &Path) -> Result<Option<ReadNodeGraphNode>> {
    let is_backdrop = stage.type_name(prim)?.as_deref() == Some(T_BACKDROP);
    if !is_backdrop && !stage.has_api_schema(prim, API_NODEGRAPH_NODE)? {
        return Ok(None);
    }
    Ok(Some(ReadNodeGraphNode {
        pos: read_float2(stage, prim, A_NODE_POS)?,
        size: read_float2(stage, prim, A_NODE_SIZE)?,
        stacking_order: read_int(stage, prim, A_NODE_STACKING_ORDER)?,
        display_color: read_color3f(stage, prim, A_NODE_DISPLAY_COLOR)?,
        icon: read_asset(stage, prim, A_NODE_ICON)?,
        expansion_state: read_token(stage, prim, A_NODE_EXPANSION_STATE)?.and_then(|t| ExpansionState::from_token(&t)),
        doc_uri: read_string(stage, prim, A_NODE_DOC_URI)?,
    }))
}

/// Read a `Backdrop` prim. Returns `None` when the prim is not typed
/// `Backdrop`.
pub fn read_backdrop(stage: &Stage, prim: &Path) -> Result<Option<ReadBackdrop>> {
    if stage.type_name(prim)?.as_deref() != Some(T_BACKDROP) {
        return Ok(None);
    }
    Ok(Some(ReadBackdrop {
        description: read_token(stage, prim, A_DESCRIPTION)?,
    }))
}

fn attr_value(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    stage.field::<Value>(prim.append_property(name)?, FieldKey::Default)
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Token(s) | Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_string(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::String(s) | Value::Token(s)) => Some(s),
        _ => None,
    })
}

fn read_asset(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::AssetPath(s) | Value::String(s) | Value::Token(s)) => Some(s),
        _ => None,
    })
}

fn read_int(stage: &Stage, prim: &Path, name: &str) -> Result<Option<i32>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Int(i)) => Some(i),
        Some(Value::Int64(i)) => Some(i as i32),
        _ => None,
    })
}

fn read_float2(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[f32; 2]>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Vec2f(v)) => Some(v),
        Some(Value::Vec2d(v)) => Some([v[0] as f32, v[1] as f32]),
        _ => None,
    })
}

fn read_color3f(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[f32; 3]>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Vec3f(v)) => Some(v),
        Some(Value::Vec3d(v)) => Some([v[0] as f32, v[1] as f32, v[2] as f32]),
        _ => None,
    })
}
