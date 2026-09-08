//! UsdUI schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdUI` family — cosmetic metadata that authoring tools use to label
//! outliners and lay out node-graph editors. All properties live under the
//! `ui:` namespace, and none have spec defaults, so unauthored fields read as
//! `None`.
//!
//! ```text
//! SchemaBase
//!  ├ Backdrop                           (typed; a labelled box behind nodes)
//!  ├ SceneGraphPrimAPI   (single-apply; outliner label + grouping)
//!  └ NodeGraphNodeAPI    (single-apply; node-editor layout)
//! ```
//!
//! [`SceneGraphPrimAPI`] adds `ui:displayName` / `ui:displayGroup` for an
//! outliner. [`NodeGraphNodeAPI`] adds a shading node's editor layout
//! (position, size, color, icon, expansion state, doc URI). [`Backdrop`] is a
//! concrete prim carrying only `ui:description`.
//!
//! # Example
//!
//! ```
//! use openusd::gf;
//! use openusd_schemas::ui::{self, ExpansionState};
//! use openusd::usd::Stage;
//!
//! let stage = Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("scene.usda")
//!     .unwrap();
//! let prim = stage.define_prim("/Mat/Surface").unwrap();
//! prim.clone().set_type_name("Shader").unwrap();
//!
//! // An API schema is applied to the prim it is carried by.
//! let node = ui::NodeGraphNodeAPI::apply(&prim).unwrap();
//! node.create_pos_attr().unwrap().set(gf::vec2f(12.0, 34.0)).unwrap();
//! node.create_expansion_state_attr().unwrap().set(ExpansionState::Minimized).unwrap();
//!
//! assert_eq!(node.pos_attr().get::<gf::Vec2f>().unwrap(), Some(gf::vec2f(12.0, 34.0)));
//! assert_eq!(
//!     node.expansion_state_attr().get::<ExpansionState>().unwrap(),
//!     Some(ExpansionState::Minimized),
//! );
//! ```

openusd::include_schema!("usdUI");

use openusd::tf;
use tokens::*;

/// `ui:nodegraph:node:expansionState` — how a node renders in a node-graph
/// editor. There is no spec default, so an unauthored value reads as `None`.
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
            ExpansionState::Open => OPEN,
            ExpansionState::Closed => CLOSED,
            ExpansionState::Minimized => MINIMIZED,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            OPEN => ExpansionState::Open,
            CLOSED => ExpansionState::Closed,
            MINIMIZED => ExpansionState::Minimized,
            _ => return None,
        })
    }
}

// `From`/`TryFrom<Value>` so the state passes straight to `Attribute::set` and
// `get::<ExpansionState>()`.
crate::token_value::impl_token_value!(ExpansionState);
