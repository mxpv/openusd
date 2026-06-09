//! The UsdShade prim views: [`Shader`], [`NodeGraph`], and [`Material`].

use anyhow::Result;

use crate::sdf::{self, Variability};
use crate::usd::{Attribute, Prim, Stage};

use super::impl_shade_schema;
use super::tokens as tok;
use crate::schemas::common::get_typed;

/// A shading node (C++ `UsdShadeShader`) — a `def Shader` prim that identifies
/// a shading implementation through the NodeDefAPI `info:*` attributes (a
/// registry id, a source asset, or inline source) and carries typed
/// [`Connectable`](super::Connectable) `inputs:` / `outputs:`.
#[derive(Clone, derive_more::Deref)]
pub struct Shader(Prim);

impl Shader {
    /// Author a `def Shader` prim at `path` (C++ `UsdShadeShader::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_SHADER)?))
    }

    /// Wrap `path` as a `Shader` if it is typed `Shader`
    /// (C++ `UsdShadeShader::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_SHADER).map(|o| o.map(Self))
    }

    /// The Sdr registry identifier, e.g. `UsdPreviewSurface` or `UsdUVTexture`.
    /// C++ `UsdShadeShader::GetIdAttr` (via `UsdShadeNodeDefAPI`).
    ///
    /// Type `uniform token`. Fetch with `get::<String>()?`.
    pub fn id_attr(&self) -> Attribute {
        self.attribute(tok::A_INFO_ID)
    }

    /// Author `info:id` (`uniform token`) (C++ `CreateIdAttr`). Authoring an id
    /// implies `info:implementationSource = "id"` (the schema default), so the
    /// latter is left unauthored unless set explicitly.
    pub fn create_id_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_INFO_ID, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// The composed `info:id` as a string, if authored — the convenience
    /// behind dispatching on shader type (C++ `UsdShadeShader::GetShaderId`).
    pub fn id(&self) -> Result<Option<String>> {
        self.id_attr().get::<String>()
    }

    /// Which `info:*` attribute carries the implementation
    /// (`id` / `sourceAsset` / `sourceCode`).
    /// C++ `UsdShadeShader::GetImplementationSourceAttr`.
    ///
    /// Type `uniform token`. Fetch with
    /// `get::<`[`ImplementationSource`](super::ImplementationSource)`>()?`
    /// (defaults to [`ImplementationSource::Id`](super::ImplementationSource::Id)).
    pub fn implementation_source_attr(&self) -> Attribute {
        self.attribute(tok::A_INFO_IMPLEMENTATION_SOURCE)
    }

    /// Author `info:implementationSource` (`uniform token`)
    /// (C++ `CreateImplementationSourceAttr`). Pass an
    /// [`ImplementationSource`](super::ImplementationSource) to `set`.
    pub fn create_implementation_source_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_INFO_IMPLEMENTATION_SOURCE, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Path to a shader source asset parsed by an Sdr plugin (e.g. an `.mdl` /
    /// `.osl` file); pairs with `info:implementationSource = "sourceAsset"`.
    /// C++ `UsdShadeShader::GetSourceAssetAttr`.
    ///
    /// Type `uniform asset`. Fetch with `get::<sdf::AssetPath>()?`.
    pub fn source_asset_attr(&self) -> Attribute {
        self.attribute(tok::A_INFO_SOURCE_ASSET)
    }

    /// Author `info:sourceAsset` (`uniform asset`) (C++ `SetSourceAsset`).
    pub fn create_source_asset_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_INFO_SOURCE_ASSET, "asset")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Selects one definition inside a multi-shader source asset.
    /// C++ `UsdShadeShader::GetSourceAssetSubIdentifierAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<String>()?`.
    pub fn source_asset_subidentifier_attr(&self) -> Attribute {
        self.attribute(tok::A_INFO_SOURCE_ASSET_SUBIDENTIFIER)
    }

    /// Author `info:sourceAsset:subIdentifier` (`uniform token`).
    pub fn create_source_asset_subidentifier_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_INFO_SOURCE_ASSET_SUBIDENTIFIER, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Inline shader source; pairs with
    /// `info:implementationSource = "sourceCode"`.
    /// C++ `UsdShadeShader::GetSourceCodeAttr`.
    ///
    /// Type `uniform string`. Fetch with `get::<String>()?`.
    pub fn source_code_attr(&self) -> Attribute {
        self.attribute(tok::A_INFO_SOURCE_CODE)
    }

    /// Author `info:sourceCode` (`uniform string`) (C++ `SetSourceCode`).
    pub fn create_source_code_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_INFO_SOURCE_CODE, "string")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }
}

impl_shade_schema!(connectable Shader);

/// A container for a shading network (C++ `UsdShadeNodeGraph`) with a public
/// [`Connectable`](super::Connectable) `inputs:` interface and `outputs:`
/// results connected to shaders inside it.
#[derive(Clone, derive_more::Deref)]
pub struct NodeGraph(Prim);

impl NodeGraph {
    /// Author a `def NodeGraph` prim at `path`
    /// (C++ `UsdShadeNodeGraph::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_NODE_GRAPH)?))
    }

    /// Wrap `path` as a `NodeGraph` if it is typed `NodeGraph`
    /// (C++ `UsdShadeNodeGraph::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_NODE_GRAPH).map(|o| o.map(Self))
    }
}

impl_shade_schema!(connectable NodeGraph);

/// A network of shading prims with well-known terminal outputs (C++
/// `UsdShadeMaterial`) — a [`NodeGraph`]-like [`Connectable`](super::Connectable)
/// container exposing `surface` / `displacement` / `volume` terminals, each
/// optionally namespaced by a render context (the universal context is the bare
/// `outputs:surface`). A terminal carries no value; it connects to a shader
/// output.
#[derive(Clone, derive_more::Deref)]
pub struct Material(Prim);

impl Material {
    /// Author a `def Material` prim at `path` (C++ `UsdShadeMaterial::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_MATERIAL)?))
    }

    /// Wrap `path` as a `Material` if it is typed `Material`
    /// (C++ `UsdShadeMaterial::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_MATERIAL).map(|o| o.map(Self))
    }

    /// Handle to the universal `outputs:surface` terminal
    /// (C++ `UsdShadeMaterial::GetSurfaceOutput`).
    pub fn surface_output(&self) -> Attribute {
        self.attribute(tok::A_OUTPUTS_SURFACE)
    }

    /// Author the universal `outputs:surface` terminal
    /// (C++ `CreateSurfaceOutput`). Wire it with `.set_connections([source])`.
    pub fn create_surface_output(&self) -> Result<Attribute> {
        self.create_terminal_output(tok::UNIVERSAL_RENDER_CONTEXT, tok::TERMINAL_SURFACE)
    }

    /// Handle to the universal `outputs:displacement` terminal
    /// (C++ `UsdShadeMaterial::GetDisplacementOutput`).
    pub fn displacement_output(&self) -> Attribute {
        self.attribute(tok::A_OUTPUTS_DISPLACEMENT)
    }

    /// Author the universal `outputs:displacement` terminal
    /// (C++ `CreateDisplacementOutput`).
    pub fn create_displacement_output(&self) -> Result<Attribute> {
        self.create_terminal_output(tok::UNIVERSAL_RENDER_CONTEXT, tok::TERMINAL_DISPLACEMENT)
    }

    /// Handle to the universal `outputs:volume` terminal
    /// (C++ `UsdShadeMaterial::GetVolumeOutput`).
    pub fn volume_output(&self) -> Attribute {
        self.attribute(tok::A_OUTPUTS_VOLUME)
    }

    /// Author the universal `outputs:volume` terminal
    /// (C++ `CreateVolumeOutput`).
    pub fn create_volume_output(&self) -> Result<Attribute> {
        self.create_terminal_output(tok::UNIVERSAL_RENDER_CONTEXT, tok::TERMINAL_VOLUME)
    }

    /// Author the `surface` terminal for an explicit render context (e.g.
    /// `"ri"` → `outputs:ri:surface`). Pass
    /// [`UNIVERSAL_RENDER_CONTEXT`](super::tokens::UNIVERSAL_RENDER_CONTEXT) for
    /// the universal terminal. C++ `CreateSurfaceOutput(renderContext)`.
    pub fn create_surface_output_for(&self, render_context: &str) -> Result<Attribute> {
        self.create_terminal_output(render_context, tok::TERMINAL_SURFACE)
    }

    /// Resolve this material's surface terminal to the [`Shader`] that drives
    /// it (C++ `UsdShadeMaterial::ComputeSurfaceSource`). Follows
    /// `outputs:surface.connect` to the connected shader output, trying the
    /// universal render context first and falling back to any authored
    /// context-specific `surface` terminal (candidates sorted for a stable
    /// choice). Returns `None` when no surface terminal is connected, or its
    /// source prim is not a `Shader`.
    pub fn compute_surface_source(&self) -> Result<Option<Shader>> {
        let mut conns = self.surface_output().connections()?;
        if conns.is_empty() {
            let suffix = format!(":{}", tok::TERMINAL_SURFACE);
            let mut contexts: Vec<String> = self
                .stage()
                .prim_at(self.path().clone())
                .property_names()?
                .into_iter()
                .filter(|prop| {
                    prop.strip_prefix(tok::NS_OUTPUTS)
                        .and_then(|rest| rest.strip_suffix(&suffix))
                        .is_some_and(|ctx| !ctx.is_empty() && !ctx.contains(':'))
                })
                .map(String::from)
                .collect();
            contexts.sort();
            for prop in contexts {
                conns = self.attribute(&prop).connections()?;
                if !conns.is_empty() {
                    break;
                }
            }
        }
        let Some(source) = conns.into_iter().next() else {
            return Ok(None);
        };
        // The connection target is a property path (`/Mat/Surface.outputs:surface`);
        // the shader prim is its owning prim.
        Shader::get(self.stage(), source.prim_path())
    }

    /// The terminal output name for `terminal` in `render_context`. Universal
    /// context (empty) yields the bare `outputs:<terminal>`; a non-empty
    /// context yields `outputs:<ctx>:<terminal>`.
    fn create_terminal_output(&self, render_context: &str, terminal: &str) -> Result<Attribute> {
        let name = if render_context == tok::UNIVERSAL_RENDER_CONTEXT {
            format!("outputs:{terminal}")
        } else {
            format!("outputs:{render_context}:{terminal}")
        };
        Ok(self.create_attribute(&name, "token")?.set_custom(false)?)
    }
}

impl_shade_schema!(connectable Material);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::shade::{Connectable, ImplementationSource};
    use crate::sdf::Value;

    #[test]
    fn shader_id_and_inputs() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let shader = Shader::define(&stage, "/Mat/Surface")?;
        shader.create_id_attr()?.set("UsdPreviewSurface".to_string())?;
        shader
            .create_input("diffuseColor", "color3f")?
            .set(Value::vec3f(0.8_f32, 0.2, 0.2))?;
        shader.create_output("surface", "token")?;

        let shader = Shader::get(&stage, "/Mat/Surface")?.expect("Shader");
        assert_eq!(shader.id()?.as_deref(), Some("UsdPreviewSurface"));
        assert_eq!(
            shader.input("diffuseColor").get::<Value>()?,
            Some(Value::vec3f(0.8_f32, 0.2, 0.2))
        );
        assert!(shader
            .input_names()
            .iter()
            .any(|v| v.contains(&"diffuseColor".to_string())));
        assert_eq!(
            stage.spec_type("/Mat/Surface.outputs:surface")?,
            Some(sdf::SpecType::Attribute)
        );
        Ok(())
    }

    #[test]
    fn shader_source_asset() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let shader = Shader::define(&stage, "/Mat/MdlShader")?;
        shader
            .create_implementation_source_attr()?
            .set(ImplementationSource::SourceAsset)?;
        shader
            .create_source_asset_attr()?
            .set(Value::AssetPath("./OmniPBR.mdl".into()))?;
        shader
            .create_source_asset_subidentifier_attr()?
            .set("OmniPBR".to_string())?;

        let shader = Shader::get(&stage, "/Mat/MdlShader")?.expect("Shader");
        assert_eq!(
            shader.implementation_source_attr().get::<ImplementationSource>()?,
            Some(ImplementationSource::SourceAsset)
        );
        Ok(())
    }

    #[test]
    fn material_surface_terminal() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        Shader::define(&stage, "/Mat/Surface")?
            .create_id_attr()?
            .set("UsdPreviewSurface".to_string())?;
        Shader::get(&stage, "/Mat/Surface")?
            .expect("Shader")
            .create_output("surface", "token")?;
        let shader_out = sdf::path("/Mat/Surface.outputs:surface")?;
        let mat = Material::define(&stage, "/Mat")?;
        mat.create_surface_output()?.set_connections([shader_out.clone()])?;

        let mat = Material::get(&stage, "/Mat")?.expect("Material");
        assert_eq!(mat.surface_output().connections()?, vec![shader_out]);
        let surface = mat.compute_surface_source()?.expect("surface shader");
        assert_eq!(surface.path().as_str(), "/Mat/Surface");
        Ok(())
    }

    #[test]
    fn material_render_context_terminal() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let src = sdf::path("/Mat/RiSurface.outputs:surface")?;
        Material::define(&stage, "/Mat")?
            .create_surface_output_for("ri")?
            .set_connections([src])?;
        assert_eq!(
            stage.spec_type("/Mat.outputs:ri:surface")?,
            Some(sdf::SpecType::Attribute)
        );
        Ok(())
    }

    #[test]
    fn node_graph_interface() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let ng = NodeGraph::define(&stage, "/NG")?;
        ng.create_input("gain", "float")?.set(Value::Float(2.0))?;
        ng.create_output("out", "color3f")?;
        let ng = NodeGraph::get(&stage, "/NG")?.expect("NodeGraph");
        assert_eq!(ng.input("gain").get::<f32>()?, Some(2.0));
        assert!(ng.output_names().iter().any(|v| v.contains(&"out".to_string())));
        Ok(())
    }

    #[test]
    fn connect_connectability_render_type() -> Result<()> {
        use crate::schemas::shade::{base_name, Connectability};

        let stage = Stage::builder().in_memory("anon.usda")?;
        let tex = NodeGraph::define(&stage, "/Mat/Tex")?;
        tex.create_output("rgb", "float3")?;

        let surf = Shader::define(&stage, "/Mat/Surface")?;
        // `connect_to` chains off `create_input`, wiring it to the texture output.
        surf.create_input("diffuseColor", "color3f")?
            .connect_to(&tex.output("rgb"))?;
        assert_eq!(
            surf.input("diffuseColor").connections()?,
            vec![sdf::path("/Mat/Tex.outputs:rgb")?]
        );

        // Connectability defaults to Full, and round-trips once authored.
        assert_eq!(surf.input_connectability("diffuseColor")?, Connectability::Full);
        surf.set_input_connectability("diffuseColor", Connectability::InterfaceOnly)?;
        assert_eq!(
            surf.input_connectability("diffuseColor")?,
            Connectability::InterfaceOnly
        );

        // Render type round-trips on both an input and an output.
        surf.set_input_render_type("diffuseColor", "color")?;
        assert_eq!(surf.input_render_type("diffuseColor")?.as_deref(), Some("color"));
        tex.set_output_render_type("rgb", "color")?;
        assert_eq!(tex.output_render_type("rgb")?.as_deref(), Some("color"));

        // `base_name` strips the namespace prefix.
        assert_eq!(base_name("inputs:diffuseColor"), "diffuseColor");
        assert_eq!(base_name("outputs:rgb"), "rgb");
        Ok(())
    }
}
