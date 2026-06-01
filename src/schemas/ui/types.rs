//! Decoded enum + read structs for the [UsdUI](super) schema family.

use super::tokens::*;

/// `ui:nodegraph:node:expansionState` - how a node renders in a node-graph
/// editor. No spec default (read as `Option`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpansionState {
    /// Fully expanded, showing all parameters.
    Open,
    /// Collapsed to the title bar.
    Closed,
    /// Reduced to a minimal icon.
    Minimized,
}

impl ExpansionState {
    pub fn as_token(self) -> &'static str {
        match self {
            ExpansionState::Open => EXPANSION_OPEN,
            ExpansionState::Closed => EXPANSION_CLOSED,
            ExpansionState::Minimized => EXPANSION_MINIMIZED,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            EXPANSION_OPEN => ExpansionState::Open,
            EXPANSION_CLOSED => ExpansionState::Closed,
            EXPANSION_MINIMIZED => ExpansionState::Minimized,
            _ => return None,
        })
    }
}

/// `SceneGraphPrimAPI` - outliner label + grouping for a prim. UsdUI
/// attributes have no spec defaults, so unauthored fields read as `None`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReadSceneGraphPrim {
    /// `ui:displayName`.
    pub display_name: Option<String>,
    /// `ui:displayGroup`.
    pub display_group: Option<String>,
}

/// `NodeGraphNodeAPI` - layout of a shading node in a node-graph editor.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ReadNodeGraphNode {
    /// `ui:nodegraph:node:pos`.
    pub pos: Option<[f32; 2]>,
    /// `ui:nodegraph:node:size`.
    pub size: Option<[f32; 2]>,
    /// `ui:nodegraph:node:stackingOrder`.
    pub stacking_order: Option<i32>,
    /// `ui:nodegraph:node:displayColor`.
    pub display_color: Option<[f32; 3]>,
    /// `ui:nodegraph:node:icon`.
    pub icon: Option<String>,
    /// `ui:nodegraph:node:expansionState`.
    pub expansion_state: Option<ExpansionState>,
    /// `ui:nodegraph:node:docURI`.
    pub doc_uri: Option<String>,
}

/// A `Backdrop` prim - a labelled box behind a group of nodes in an editor.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReadBackdrop {
    /// `ui:description`.
    pub description: Option<String>,
}
