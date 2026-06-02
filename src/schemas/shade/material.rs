//! `UsdShadeMaterial` + `UsdShadeNodeGraph` authoring.
//!
//! A NodeGraph is a container for a shading network with a public
//! `inputs:` interface and `outputs:` results. A Material is a
//! NodeGraph with three well-known terminal outputs — `surface`,
//! `displacement`, `volume` — each optionally namespaced by a render
//! context (`outputs:<ctx>:surface`; the universal context is the bare
//! `outputs:surface`).
//!
//! Terminals carry no value; they connect to a shader output, e.g.
//! `Material.outputs:surface.connect = </Material/Surface.outputs:surface>`.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Attribute, Prim, Stage};

use super::connectable::{create_input, create_output};
use super::tokens::{
    TERMINAL_DISPLACEMENT, TERMINAL_SURFACE, TERMINAL_VOLUME, T_MATERIAL, T_NODE_GRAPH, UNIVERSAL_RENDER_CONTEXT,
};

/// Author a `def Material` prim and return a chainable [`MaterialAuthor`].
pub fn define_material(stage: &Stage, path: impl Into<Path>) -> Result<MaterialAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_MATERIAL)?;
    Ok(MaterialAuthor { prim })
}

/// Author a `def NodeGraph` prim and return a chainable
/// [`NodeGraphAuthor`].
pub fn define_node_graph(stage: &Stage, path: impl Into<Path>) -> Result<NodeGraphAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_NODE_GRAPH)?;
    Ok(NodeGraphAuthor { prim })
}

/// The terminal output name for `terminal` in `render_context`.
/// Universal context (empty) yields the bare `outputs:<terminal>`;
/// a non-empty context yields `outputs:<ctx>:<terminal>`.
fn terminal_output_name(render_context: &str, terminal: &str) -> String {
    if render_context == UNIVERSAL_RENDER_CONTEXT {
        format!("outputs:{terminal}")
    } else {
        format!("outputs:{render_context}:{terminal}")
    }
}

/// Chainable Material authoring handle. Mirrors C++ `UsdShadeMaterial`.
pub struct MaterialAuthor {
    prim: Prim,
}

impl MaterialAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    pub fn prim(&self) -> &Prim {
        &self.prim
    }

    /// Create a public interface `inputs:<base>` of `type_name` on the
    /// Material. Downstream shaders connect their inputs to this so the
    /// material's look is tweakable from one place (the
    /// "PreviewMaterial interface" pattern).
    pub fn create_input(&self, base: &str, type_name: &str) -> Result<Attribute> {
        create_input(&self.prim, base, type_name)
    }

    /// Connect the universal `outputs:surface` terminal to `source`
    /// (typically a shader's `outputs:surface`).
    pub fn connect_surface(self, source: Path) -> Result<Self> {
        self.connect_terminal(UNIVERSAL_RENDER_CONTEXT, TERMINAL_SURFACE, source)
    }

    /// Connect the universal `outputs:displacement` terminal to `source`.
    pub fn connect_displacement(self, source: Path) -> Result<Self> {
        self.connect_terminal(UNIVERSAL_RENDER_CONTEXT, TERMINAL_DISPLACEMENT, source)
    }

    /// Connect the universal `outputs:volume` terminal to `source`.
    pub fn connect_volume(self, source: Path) -> Result<Self> {
        self.connect_terminal(UNIVERSAL_RENDER_CONTEXT, TERMINAL_VOLUME, source)
    }

    /// Connect the `surface` terminal for an explicit render context
    /// (e.g. `"ri"` → `outputs:ri:surface`). Pass
    /// [`UNIVERSAL_RENDER_CONTEXT`](super::tokens::UNIVERSAL_RENDER_CONTEXT)
    /// for the universal terminal.
    pub fn connect_surface_for(self, render_context: &str, source: Path) -> Result<Self> {
        self.connect_terminal(render_context, TERMINAL_SURFACE, source)
    }

    fn connect_terminal(self, render_context: &str, terminal: &str, source: Path) -> Result<Self> {
        let name = terminal_output_name(render_context, terminal);
        self.prim
            .create_attribute(&name, "token")?
            .set_custom(false)?
            .set_connections([source])?;
        Ok(self)
    }
}

/// Chainable NodeGraph authoring handle. Mirrors C++ `UsdShadeNodeGraph`.
pub struct NodeGraphAuthor {
    prim: Prim,
}

impl NodeGraphAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    pub fn prim(&self) -> &Prim {
        &self.prim
    }

    /// Create a public interface `inputs:<base>` of `type_name`.
    pub fn create_input(&self, base: &str, type_name: &str) -> Result<Attribute> {
        create_input(&self.prim, base, type_name)
    }

    /// Create a public `outputs:<base>` of `type_name`, typically
    /// connected to a shader output inside the graph.
    pub fn create_output(&self, base: &str, type_name: &str) -> Result<Attribute> {
        create_output(&self.prim, base, type_name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    fn connections(stage: &Stage, attr: &str) -> Result<Vec<sdf::Path>> {
        match stage.field::<sdf::Value>(sdf::path(attr)?, sdf::FieldKey::ConnectionPaths)? {
            Some(sdf::Value::PathListOp(op)) => Ok(op.flatten()),
            Some(sdf::Value::PathVec(v)) => Ok(v),
            _ => Ok(Vec::new()),
        }
    }

    #[test]
    fn material_surface_terminal_connects_to_shader() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        super::super::define_shader(&stage, sdf::path("/Mat/Surface")?)?.set_id("UsdPreviewSurface")?;
        let shader_out = sdf::path("/Mat/Surface.outputs:surface")?;
        define_material(&stage, sdf::path("/Mat")?)?.connect_surface(shader_out.clone())?;

        assert_eq!(stage.type_name(&sdf::path("/Mat")?)?.as_deref(), Some("Material"));
        assert_eq!(connections(&stage, "/Mat.outputs:surface")?, vec![shader_out]);
        Ok(())
    }

    #[test]
    fn material_render_context_terminal() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let src = sdf::path("/Mat/RiSurface.outputs:surface")?;
        define_material(&stage, sdf::path("/Mat")?)?.connect_surface_for("ri", src.clone())?;
        assert_eq!(
            stage.spec_type("/Mat.outputs:ri:surface")?,
            Some(sdf::SpecType::Attribute),
        );
        Ok(())
    }

    #[test]
    fn node_graph_interface() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let ng = define_node_graph(&stage, sdf::path("/NG")?)?;
        ng.create_input("gain", "float")?.set(sdf::Value::Float(2.0))?;
        ng.create_output("out", "color3f")?;
        assert_eq!(stage.type_name(&sdf::path("/NG")?)?.as_deref(), Some("NodeGraph"));
        assert_eq!(
            stage.field::<sdf::Value>("/NG.inputs:gain", sdf::FieldKey::Default)?,
            Some(sdf::Value::Float(2.0)),
        );
        Ok(())
    }
}
