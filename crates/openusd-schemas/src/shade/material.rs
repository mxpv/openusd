//! What a shading prim does, over the properties its schema declares.
//!
//! A `Shader` names the implementation it stands for, and a `Material` carries
//! the terminal outputs a renderer asks it for, each resolving to the shader
//! that drives it.

use openusd::Result;
use openusd::sdf;
use openusd::tf;
use openusd::usd;

use std::borrow::Cow;
use std::collections::HashSet;

use super::node_def;
use super::tokens;
use super::utils::ProducerFilter;
use super::{AttributeType, Connectable, Material, NodeDefAPI, Output, Shader, ShadingAttribute};
use crate::SchemaError;

impl Shader {
    /// The `UsdShadeNodeDefAPI` view of this shader, which is where upstream
    /// declares what implementation a shader stands for.
    pub fn node_def(&self) -> NodeDefAPI {
        NodeDefAPI::new((**self).clone())
    }

    /// The Sdr registry identifier, e.g. `UsdPreviewSurface` or `UsdUVTexture`.
    /// C++ `UsdShadeShader::GetIdAttr` (via `UsdShadeNodeDefAPI`).
    ///
    /// Type `uniform token`. Fetch with `get::<tf::Token>()?`.
    pub fn id_attr(&self) -> usd::Attribute {
        self.node_def().id_attr()
    }

    /// Author `info:id` (`uniform token`) (C++ `CreateIdAttr`). Authoring an id
    /// implies `info:implementationSource = "id"` (the schema default), so the
    /// latter is left unauthored unless set explicitly.
    pub fn create_id_attr(&self) -> Result<usd::Attribute> {
        self.node_def().create_id_attr()
    }

    /// The composed `info:id` as a string when identifier mode is active — the
    /// convenience behind dispatching on shader type (C++
    /// `UsdShadeShader::GetShaderId`).
    pub fn id(&self) -> Result<Option<String>> {
        if self.implementation_source()? != super::ImplementationSource::Id {
            return Ok(None);
        }
        Ok(self.id_attr().get::<tf::Token>()?.map(Into::into))
    }

    /// Which `info:*` attribute carries the implementation
    /// (`id` / `sourceAsset` / `sourceCode`).
    /// C++ `UsdShadeShader::GetImplementationSourceAttr`.
    ///
    /// Type `uniform token`. Fetch with
    /// `get::<`[`ImplementationSource`](super::ImplementationSource)`>()?`
    /// (defaults to [`ImplementationSource::Id`](super::ImplementationSource::Id)).
    pub fn implementation_source_attr(&self) -> usd::Attribute {
        self.node_def().implementation_source_attr()
    }

    /// Author `info:implementationSource` (`uniform token`)
    /// (C++ `CreateImplementationSourceAttr`). Pass an
    /// [`ImplementationSource`](super::ImplementationSource) to `set`.
    pub fn create_implementation_source_attr(&self) -> Result<usd::Attribute> {
        self.node_def().create_implementation_source_attr()
    }

    /// Path to a shader source asset parsed by an Sdr plugin (e.g. an `.mdl` /
    /// `.osl` file); pairs with `info:implementationSource = "sourceAsset"`.
    /// C++ `UsdShadeShader::GetSourceAssetAttr`.
    ///
    /// Type `uniform asset`. Fetch with `get::<sdf::AssetPath>()?`.
    pub fn source_asset_attr(&self) -> usd::Attribute {
        self.attribute(node_def::INFO_SOURCE_ASSET)
    }

    /// Author `info:sourceAsset` (`uniform asset`) (C++ `SetSourceAsset`).
    pub fn create_source_asset_attr(&self) -> Result<usd::Attribute> {
        Ok(self
            .create_attribute(node_def::INFO_SOURCE_ASSET, sdf::ValueTypeName::ASSET)?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// Selects one definition inside a multi-shader source asset.
    /// C++ `UsdShadeShader::GetSourceAssetSubIdentifierAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<tf::Token>()?`.
    pub fn source_asset_subidentifier_attr(&self) -> usd::Attribute {
        self.attribute(node_def::INFO_SOURCE_ASSET_SUBIDENTIFIER)
    }

    /// Author `info:sourceAsset:subIdentifier` (`uniform token`).
    pub fn create_source_asset_subidentifier_attr(&self) -> Result<usd::Attribute> {
        Ok(self
            .create_attribute(node_def::INFO_SOURCE_ASSET_SUBIDENTIFIER, sdf::ValueTypeName::TOKEN)?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// Inline shader source; pairs with
    /// `info:implementationSource = "sourceCode"`.
    /// C++ `UsdShadeShader::GetSourceCodeAttr`.
    ///
    /// Type `uniform string`. Fetch with `get::<String>()?`.
    pub fn source_code_attr(&self) -> usd::Attribute {
        self.attribute(node_def::INFO_SOURCE_CODE)
    }

    /// Author `info:sourceCode` (`uniform string`) (C++ `SetSourceCode`).
    pub fn create_source_code_attr(&self) -> Result<usd::Attribute> {
        Ok(self
            .create_attribute(node_def::INFO_SOURCE_CODE, sdf::ValueTypeName::STRING)?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

/// One of the three standard output terminals on a [`Material`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TerminalKind {
    /// Surface scattering and emission.
    Surface,
    /// Geometric displacement.
    Displacement,
    /// Volumetric scattering, absorption, and emission.
    Volume,
}

impl TerminalKind {
    /// The terminal's base output name.
    pub const fn as_str(self) -> &'static str {
        match self {
            TerminalKind::Surface => tokens::SURFACE,
            TerminalKind::Displacement => tokens::DISPLACEMENT,
            TerminalKind::Volume => tokens::VOLUME,
        }
    }

    /// The universal terminal's full property name (e.g. `outputs:surface`).
    pub const fn universal_attribute(self) -> &'static str {
        match self {
            TerminalKind::Surface => tokens::OUTPUTS_SURFACE,
            TerminalKind::Displacement => tokens::OUTPUTS_DISPLACEMENT,
            TerminalKind::Volume => tokens::OUTPUTS_VOLUME,
        }
    }
}

/// One value-producing attribute that contributes to a resolved material
/// terminal.
///
/// Multiple instances are retained when the selected terminal branches through
/// a multi-connection. The attribute records the exact endpoint, including its
/// base name, Input/Output role, path, and composed USD value type.
#[derive(Clone)]
pub struct TerminalSource {
    shader: Option<Shader>,
    attribute: ShadingAttribute,
}

impl TerminalSource {
    /// The `Shader`-typed prim that owns the source attribute, or `None` when
    /// the endpoint's prim carries another (or no) type — the analog of C++'s
    /// invalid `UsdShadeShader` result for such endpoints.
    pub fn shader(&self) -> Option<&Shader> {
        self.shader.as_ref()
    }

    /// The exact value-producing shader attribute.
    pub fn attribute(&self) -> &ShadingAttribute {
        &self.attribute
    }

    /// The source attribute's base name without `inputs:` or `outputs:`.
    pub fn source_name(&self) -> &str {
        match &self.attribute {
            ShadingAttribute::Input(input) => input.base_name(),
            ShadingAttribute::Output(output) => output.base_name(),
        }
    }

    /// Whether the source attribute is an input or output.
    pub const fn source_type(&self) -> AttributeType {
        self.attribute.attribute_type()
    }
}

/// The selected render-context terminal and every shader source that drives it.
#[derive(Clone)]
pub struct ResolvedTerminal {
    kind: TerminalKind,
    render_context: tf::Token,
    sources: Vec<TerminalSource>,
}

impl ResolvedTerminal {
    /// Which standard material terminal was resolved.
    pub const fn kind(&self) -> TerminalKind {
        self.kind
    }

    /// The selected render context. An empty token is the universal context.
    pub fn render_context(&self) -> &tf::Token {
        &self.render_context
    }

    /// All valid value-producing shader sources in connection order.
    pub fn sources(&self) -> &[TerminalSource] {
        &self.sources
    }
}

impl Material {
    /// Handle to the universal `outputs:surface` terminal
    /// (C++ `UsdShadeMaterial::GetSurfaceOutput`).
    pub fn surface_output(&self) -> Output {
        self.terminal_output(tokens::UNIVERSAL_RENDER_CONTEXT, TerminalKind::Surface)
    }

    /// Handle to the `surface` terminal for `render_context`.
    ///
    /// An empty context addresses the universal `outputs:surface` terminal;
    /// a context that is not a namespaced identifier errors, as the create
    /// counterpart does.
    pub fn surface_output_for(&self, render_context: &str) -> Result<Output, SchemaError> {
        checked_context(render_context)?;
        Ok(self.terminal_output(render_context, TerminalKind::Surface))
    }

    /// Every authored surface terminal, with the universal terminal first.
    pub fn surface_outputs(&self) -> Result<Vec<Output>> {
        self.terminal_outputs(TerminalKind::Surface)
    }

    /// Author the universal `outputs:surface` terminal
    /// (C++ `CreateSurfaceOutput`). Wire it with `.set_connections([source])`.
    pub fn create_surface_output(&self) -> Result<Output> {
        self.create_terminal_output(tokens::UNIVERSAL_RENDER_CONTEXT, TerminalKind::Surface)
    }

    /// Author the `surface` terminal for `render_context`.
    ///
    /// An empty context authors the universal `outputs:surface` terminal.
    pub fn create_surface_output_for(&self, render_context: &str) -> Result<Output> {
        self.create_terminal_output(render_context, TerminalKind::Surface)
    }

    /// Handle to the universal `outputs:displacement` terminal
    /// (C++ `UsdShadeMaterial::GetDisplacementOutput`).
    pub fn displacement_output(&self) -> Output {
        self.terminal_output(tokens::UNIVERSAL_RENDER_CONTEXT, TerminalKind::Displacement)
    }

    /// Handle to the `displacement` terminal for `render_context`.
    ///
    /// An empty context addresses the universal `outputs:displacement`
    /// terminal; a context that is not a namespaced identifier errors, as the
    /// create counterpart does.
    pub fn displacement_output_for(&self, render_context: &str) -> Result<Output, SchemaError> {
        checked_context(render_context)?;
        Ok(self.terminal_output(render_context, TerminalKind::Displacement))
    }

    /// Every authored displacement terminal, with the universal terminal
    /// first.
    pub fn displacement_outputs(&self) -> Result<Vec<Output>> {
        self.terminal_outputs(TerminalKind::Displacement)
    }

    /// Author the universal `outputs:displacement` terminal
    /// (C++ `CreateDisplacementOutput`).
    pub fn create_displacement_output(&self) -> Result<Output> {
        self.create_terminal_output(tokens::UNIVERSAL_RENDER_CONTEXT, TerminalKind::Displacement)
    }

    /// Author the `displacement` terminal for `render_context`.
    ///
    /// An empty context authors the universal `outputs:displacement` terminal.
    pub fn create_displacement_output_for(&self, render_context: &str) -> Result<Output> {
        self.create_terminal_output(render_context, TerminalKind::Displacement)
    }

    /// Handle to the universal `outputs:volume` terminal
    /// (C++ `UsdShadeMaterial::GetVolumeOutput`).
    pub fn volume_output(&self) -> Output {
        self.terminal_output(tokens::UNIVERSAL_RENDER_CONTEXT, TerminalKind::Volume)
    }

    /// Handle to the `volume` terminal for `render_context`.
    ///
    /// An empty context addresses the universal `outputs:volume` terminal; a
    /// context that is not a namespaced identifier errors, as the create
    /// counterpart does.
    pub fn volume_output_for(&self, render_context: &str) -> Result<Output, SchemaError> {
        checked_context(render_context)?;
        Ok(self.terminal_output(render_context, TerminalKind::Volume))
    }

    /// Every authored volume terminal, with the universal terminal first.
    pub fn volume_outputs(&self) -> Result<Vec<Output>> {
        self.terminal_outputs(TerminalKind::Volume)
    }

    /// Author the universal `outputs:volume` terminal
    /// (C++ `CreateVolumeOutput`).
    pub fn create_volume_output(&self) -> Result<Output> {
        self.create_terminal_output(tokens::UNIVERSAL_RENDER_CONTEXT, TerminalKind::Volume)
    }

    /// Author the `volume` terminal for `render_context`.
    ///
    /// An empty context authors the universal `outputs:volume` terminal.
    pub fn create_volume_output_for(&self, render_context: &str) -> Result<Output> {
        self.create_terminal_output(render_context, TerminalKind::Volume)
    }

    /// Resolve the surface terminal for the ordered render-context preferences.
    ///
    /// The earliest context with valid shader sources wins. The universal
    /// context is tried last unless it already appears in `render_contexts`.
    pub fn compute_surface_source(&self, render_contexts: &[&str]) -> Result<Option<ResolvedTerminal>, SchemaError> {
        self.compute_terminal_source(TerminalKind::Surface, render_contexts)
    }

    /// Resolve the displacement terminal for the ordered render-context
    /// preferences, with universal fallback.
    pub fn compute_displacement_source(
        &self,
        render_contexts: &[&str],
    ) -> Result<Option<ResolvedTerminal>, SchemaError> {
        self.compute_terminal_source(TerminalKind::Displacement, render_contexts)
    }

    /// Resolve the volume terminal for the ordered render-context preferences,
    /// with universal fallback.
    pub fn compute_volume_source(&self, render_contexts: &[&str]) -> Result<Option<ResolvedTerminal>, SchemaError> {
        self.compute_terminal_source(TerminalKind::Volume, render_contexts)
    }

    fn compute_terminal_source(
        &self,
        kind: TerminalKind,
        render_contexts: &[&str],
    ) -> Result<Option<ResolvedTerminal>, SchemaError> {
        for &render_context in render_contexts {
            checked_context(render_context)?;
        }
        let mut universal_visited = false;
        for &render_context in render_contexts {
            universal_visited |= render_context == tokens::UNIVERSAL_RENDER_CONTEXT;
            if let Some(resolved) = self.resolve_terminal(kind, render_context)? {
                return Ok(Some(resolved));
            }
        }
        if !universal_visited {
            return self.resolve_terminal(kind, tokens::UNIVERSAL_RENDER_CONTEXT);
        }
        Ok(None)
    }

    fn resolve_terminal(
        &self,
        kind: TerminalKind,
        render_context: &str,
    ) -> Result<Option<ResolvedTerminal>, SchemaError> {
        let output = self.terminal_output(render_context, kind);
        let mut sources = Vec::new();
        let mut seen = HashSet::new();
        for attribute in output.value_producing_attributes(ProducerFilter::ShaderOutputsOnly)? {
            // Sibling branches can converge on one endpoint; report it once.
            if !seen.insert(attribute.path().clone()) {
                continue;
            }
            // Any value-producing endpoint commits this terminal, whether or
            // not its prim is typed Shader — C++ hands back an invalid
            // UsdShadeShader rather than falling through to a weaker render
            // context.
            let prim = attribute.attribute().prim();
            let shader = prim.is_a(tokens::SHADER)?.then(|| Shader::new(prim));
            sources.push(TerminalSource { shader, attribute });
        }
        if sources.is_empty() {
            return Ok(None);
        }
        Ok(Some(ResolvedTerminal {
            kind,
            render_context: tf::Token::from(render_context),
            sources,
        }))
    }

    fn terminal_output(&self, render_context: &str, kind: TerminalKind) -> Output {
        Output::new(self.attribute(terminal_output_name(render_context, kind).as_ref()))
    }

    fn terminal_outputs(&self, kind: TerminalKind) -> Result<Vec<Output>> {
        let mut universal = None;
        let mut contextual = Vec::new();
        for output in self.outputs()? {
            let base_name = output.base_name();
            if base_name == kind.as_str() {
                universal = Some(output);
            } else if base_name
                .strip_suffix(kind.as_str())
                .is_some_and(|context| context.ends_with(':') && context.len() > 1)
            {
                contextual.push(output);
            }
        }
        Ok(universal.into_iter().chain(contextual).collect())
    }

    fn create_terminal_output(&self, render_context: &str, kind: TerminalKind) -> Result<Output> {
        let name = terminal_output_name(render_context, kind);
        Ok(Output::new(
            self.create_attribute(name.as_ref(), "token")?.set_custom(false)?,
        ))
    }
}

/// The terminal's full property name for `render_context`: the universal
/// constant, or `outputs:<context>:<terminal>`.
fn terminal_output_name(render_context: &str, kind: TerminalKind) -> Cow<'static, str> {
    if render_context == tokens::UNIVERSAL_RENDER_CONTEXT {
        Cow::Borrowed(kind.universal_attribute())
    } else {
        Cow::Owned(format!("{}{render_context}:{}", tokens::OUTPUTS, kind.as_str()))
    }
}

/// Validates a caller-supplied render context: the universal context, or a
/// namespaced identifier (`ri`, `mtlx:standard`).
fn checked_context(render_context: &str) -> Result<(), SchemaError> {
    if render_context != tokens::UNIVERSAL_RENDER_CONTEXT && !sdf::Path::is_valid_namespace_identifier(render_context) {
        return Err(SchemaError::InvalidRenderContext {
            context: render_context.to_owned(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use openusd::Result;
    use openusd::sdf;

    use crate::shade::{Connectable, NodeGraph};

    #[test]
    fn material_terminal_kinds() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let surface = Shader::define(&stage, "/Mat/Surface")?.create_output("surface", "token")?;
        let displacement = Shader::define(&stage, "/Mat/Displace")?.create_output("displacement", "token")?;
        let volume = Shader::define(&stage, "/Mat/Volume")?.create_output("volume", "token")?;
        let material = Material::define(&stage, "/Mat")?;
        material.create_surface_output()?.connect_to(&surface)?;
        material.create_displacement_output()?.connect_to(&displacement)?;
        material.create_volume_output()?.connect_to(&volume)?;

        let displacement = material
            .compute_displacement_source(&[])?
            .expect("displacement terminal");
        assert_eq!(displacement.kind(), TerminalKind::Displacement);
        assert_eq!(
            displacement.sources()[0]
                .shader()
                .expect("shader source")
                .path()
                .as_str(),
            "/Mat/Displace"
        );

        let volume = material.compute_volume_source(&[])?.expect("volume terminal");
        assert_eq!(volume.kind(), TerminalKind::Volume);
        assert_eq!(
            volume.sources()[0].shader().expect("shader source").path().as_str(),
            "/Mat/Volume"
        );
        Ok(())
    }

    #[test]
    fn context_selection_fallback() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let universal = Shader::define(&stage, "/Mat/Universal")?.create_output("result", "token")?;
        let renderman = Shader::define(&stage, "/Mat/Renderman")?.create_output("result", "token")?;
        let material = Material::define(&stage, "/Mat")?;
        material.create_surface_output()?.connect_to(&universal)?;
        material
            .create_surface_output_for("mtlx")?
            .set_connections([sdf::path("/Missing.outputs:result")?])?;
        material.create_surface_output_for("ri")?.connect_to(&renderman)?;

        let selected = material.compute_surface_source(&["mtlx", "ri"])?.expect("ri terminal");
        assert_eq!(selected.render_context().as_str(), "ri");
        assert_eq!(
            selected.sources()[0].shader().expect("shader source").path().as_str(),
            "/Mat/Renderman"
        );

        let fallback = material
            .compute_surface_source(&["unknown"])?
            .expect("universal terminal");
        assert!(fallback.render_context().is_empty());
        assert_eq!(
            fallback.sources()[0].shader().expect("shader source").path().as_str(),
            "/Mat/Universal"
        );
        Ok(())
    }

    #[test]
    fn terminal_source_order() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let first = Shader::define(&stage, "/Mat/First")?.create_output("density", "token")?;
        let second = Shader::define(&stage, "/Mat/Second")?.create_output("fog", "token")?;
        let graph = NodeGraph::define(&stage, "/Mat/Graph")?;
        graph
            .create_output("volume", "token")?
            .set_connections([second.path().clone(), first.path().clone()])?;
        let material = Material::define(&stage, "/Mat")?;
        material
            .create_volume_output_for("ri")?
            .connect_to(&graph.output("volume"))?;

        let terminal = material.compute_volume_source(&["ri"])?.expect("volume terminal");
        let paths: Vec<&str> = terminal
            .sources()
            .iter()
            .map(|source| source.shader().expect("shader source").path().as_str())
            .collect();
        let names: Vec<&str> = terminal.sources().iter().map(TerminalSource::source_name).collect();
        assert_eq!(paths, ["/Mat/Second", "/Mat/First"]);
        assert_eq!(names, ["fog", "density"]);
        assert!(
            terminal
                .sources()
                .iter()
                .all(|source| source.source_type() == AttributeType::Output)
        );
        Ok(())
    }

    #[test]
    fn terminal_commits_untyped_endpoint() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let material = Material::define(&stage, "/Mat")?;
        // The ri terminal ends on a custom-typed node; the universal terminal
        // ends on a Shader.
        let custom = stage.define_prim("/Mat/Custom")?.set_type_name("MyNode")?;
        let custom_out = Output::new(custom.create_attribute("outputs:out", "token")?);
        material.create_surface_output_for("ri")?.connect_to(&custom_out)?;
        let universal = Shader::define(&stage, "/Mat/Universal")?;
        let universal_out = universal.create_output("surface", "token")?;
        material.create_surface_output()?.connect_to(&universal_out)?;

        // The requested context commits to its own endpoint (with no shader
        // view) rather than falling through to the universal shader.
        let terminal = material.compute_surface_source(&["ri"])?.expect("ri terminal");
        assert_eq!(terminal.render_context().as_str(), "ri");
        let source = &terminal.sources()[0];
        assert!(source.shader().is_none());
        assert_eq!(source.attribute().path().as_str(), "/Mat/Custom.outputs:out");
        Ok(())
    }

    #[test]
    fn converging_sources_dedup() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let material = Material::define(&stage, "/Mat")?;
        let shader = Shader::define(&stage, "/Mat/S")?;
        let shader_out = shader.create_output("surface", "token")?;
        let graph = NodeGraph::define(&stage, "/Mat/NG")?;
        let graph_out = graph.create_output("out", "token")?.connect_to(&shader_out)?;
        // Two branches of the terminal converge on one shader endpoint.
        material
            .create_surface_output()?
            .set_connections([shader_out.path().clone(), graph_out.path().clone()])?;

        let terminal = material.compute_surface_source(&[])?.expect("terminal");
        assert_eq!(terminal.sources().len(), 1);
        Ok(())
    }

    #[test]
    fn invalid_context_rejected() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let material = Material::define(&stage, "/Mat")?;
        assert!(material.surface_output_for("ri ").is_err());
        assert!(material.displacement_output_for("ri:").is_err());
        assert!(material.volume_output_for("a b").is_err());
        assert!(material.compute_surface_source(&["ri "]).is_err());
        // The universal context stays addressable through the empty string.
        assert!(material.surface_output_for("").is_ok());
        Ok(())
    }

    #[test]
    fn render_context_terminal_source() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let ri = Shader::define(&stage, "/Mat/RiSurface")?;
        let ri_output = ri.create_output("surface", "token")?;
        Material::define(&stage, "/Mat")?
            .create_surface_output_for("ri")?
            .connect_to(&ri_output)?;

        // With no universal terminal authored, the render-context terminal
        // answers.
        let mat = Material::get(&stage, "/Mat")?.expect("Material");
        let terminal = mat.compute_surface_source(&["ri"])?.expect("surface terminal");
        let source = terminal.sources().first().expect("surface source");
        assert_eq!(
            source.shader().expect("shader source").path().as_str(),
            "/Mat/RiSurface"
        );
        Ok(())
    }

    #[test]
    fn universal_terminal_decides() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let ri = Shader::define(&stage, "/Mat/RiSurface")?;
        let ri_output = ri.create_output("surface", "token")?;
        let mat = Material::define(&stage, "/Mat")?;
        mat.create_surface_output_for("ri")?.connect_to(&ri_output)?;

        // A connected universal terminal states where the surface comes from,
        // so a render-context terminal never stands in for it â€” not even when
        // the source it names produces nothing.
        let empty = NodeGraph::define(&stage, "/Mat/Empty")?;
        mat.create_surface_output()?
            .connect_to(&empty.create_output("surface", "token")?)?;

        let mat = Material::get(&stage, "/Mat")?.expect("Material");
        assert!(mat.compute_surface_source(&[])?.is_none());
        Ok(())
    }
}
