//! Token constants for the [UsdUI](super) schema family.
//!
//! Mirrors Pixar's `pxr/usd/usdUI/tokens.h`. All UsdUI properties live
//! under the `ui:` namespace.

// Concrete prim type names.
pub const T_BACKDROP: &str = "Backdrop";

// Applied API schema names.
pub const API_SCENE_GRAPH_PRIM: &str = "SceneGraphPrimAPI";
pub const API_NODEGRAPH_NODE: &str = "NodeGraphNodeAPI";

// SceneGraphPrimAPI attributes.
pub const A_DISPLAY_NAME: &str = "ui:displayName";
pub const A_DISPLAY_GROUP: &str = "ui:displayGroup";

// Backdrop attributes.
pub const A_DESCRIPTION: &str = "ui:description";

// NodeGraphNodeAPI attributes.
pub const A_NODE_POS: &str = "ui:nodegraph:node:pos";
pub const A_NODE_SIZE: &str = "ui:nodegraph:node:size";
pub const A_NODE_STACKING_ORDER: &str = "ui:nodegraph:node:stackingOrder";
pub const A_NODE_DISPLAY_COLOR: &str = "ui:nodegraph:node:displayColor";
pub const A_NODE_ICON: &str = "ui:nodegraph:node:icon";
pub const A_NODE_EXPANSION_STATE: &str = "ui:nodegraph:node:expansionState";
pub const A_NODE_DOC_URI: &str = "ui:nodegraph:node:docURI";

// `ui:nodegraph:node:expansionState` token values.
pub const EXPANSION_OPEN: &str = "open";
pub const EXPANSION_CLOSED: &str = "closed";
pub const EXPANSION_MINIMIZED: &str = "minimized";
