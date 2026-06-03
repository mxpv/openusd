//! UsdUI schema views.
//!
//! Typed value-views over a composed [`crate::usd::Stage`], mirroring Pixar's
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
//! use openusd::schemas::ui::{self, ExpansionState};
//! use openusd::usd::Stage;
//!
//! let stage = Stage::builder().in_memory("scene.usda")?;
//! stage.define_prim("/Mat/Surface")?.set_type_name("Shader")?;
//!
//! let node = ui::NodeGraphNodeAPI::apply(&stage, "/Mat/Surface")?;
//! node.create_pos_attr()?.set([12.0_f32, 34.0])?;
//! node.create_expansion_state_attr()?.set(ExpansionState::Minimized)?;
//!
//! assert_eq!(node.pos_attr().get::<[f32; 2]>()?, Some([12.0, 34.0]));
//! assert_eq!(
//!     node.expansion_state_attr().get::<ExpansionState>()?,
//!     Some(ExpansionState::Minimized),
//! );
//! # Ok::<(), Box<dyn std::error::Error + Send + Sync>>(())
//! ```

pub mod tokens;

mod schema;

pub use schema::{Backdrop, NodeGraphNodeAPI, SceneGraphPrimAPI};

use tokens::*;

/// Implement the `SchemaBase` membership for a concrete UsdUI view. All trait
/// paths are fully qualified, so the call site only needs the macro in scope.
///
/// - `typed` is a concrete typed prim ([`Backdrop`]).
/// - `single_api` is a single-apply API schema ([`SceneGraphPrimAPI`],
///   [`NodeGraphNodeAPI`]).
macro_rules! impl_ui_schema {
    (typed $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::ConcreteTyped;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
    };
    (single_api $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::SingleApplyApi;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
    };
}

pub(crate) use impl_ui_schema;

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

// `From`/`TryFrom<Value>` so the state passes straight to `Attribute::set` and
// `get::<ExpansionState>()`.
crate::schemas::common::impl_token_value!(ExpansionState);
