//! UsdShade schema reader + authoring.
//!
//! UsdShade is the material / shading-network schema family. Unlike the
//! geometry / lighting families, its substance is **connection
//! topology** rather than a flat set of typed attributes: a
//! [`Material`](tokens::T_MATERIAL) contains [`Shader`](tokens::T_SHADER)
//! prims whose `inputs:` / `outputs:` attributes are wired together by
//! `.connect` ([`connectionPaths`](crate::sdf::FieldKey::ConnectionPaths)).
//!
//! # Surface
//!
//! - [`shader`] — `define_shader`: `Shader` + `NodeDefAPI` (`info:id` /
//!   implementation source) plus typed `inputs:` / `outputs:`.
//! - [`material`] — `define_material` / `define_node_graph`: containers
//!   with `surface` / `displacement` / `volume` terminal outputs,
//!   connected to a shader's output.
//! - [`connectable`] — the `inputs:` / `outputs:` namespacing + path
//!   helpers shared across the above.
//! - [`binding`] — `MaterialBindingAPI`: direct + collection bindings,
//!   purpose-namespaced, with `bindMaterialAs` strength.
//! - [`preview`] — readers for the canonical `UsdPreviewSurface` +
//!   `UsdUVTexture` shader graph.
//! - [`read`] — stage walk + `read_material` (resolve a Material's
//!   surface terminal back through the shader graph).
//!
//! Connections are authored / read through
//! [`crate::usd::Attribute::set_connections`] /
//! [`get_connections`](crate::usd::Attribute::get_connections).

pub mod tokens;

mod connectable;
mod material;
mod shader;
mod types;

pub use connectable::{create_input, create_output, input_name, input_path, output_name, output_path};
pub use material::{define_material, define_node_graph, MaterialAuthor, NodeGraphAuthor};
pub use shader::{define_shader, ShaderAuthor};
pub use types::{BindingStrength, Connectability, ImplementationSource};
