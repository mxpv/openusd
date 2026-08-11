//! UsdShade connection source queries and attribute namespacing.

use anyhow::Result;

use crate::schemas::common::is_any_typed;
use crate::{sdf, tf, usd};

use super::tokens::{NS_INPUTS, NS_OUTPUTS, T_MATERIAL, T_NODE_GRAPH};
use super::{Input, Output};

/// Whether a shading attribute is an `inputs:` or `outputs:` property.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AttributeType {
    /// An `inputs:` attribute.
    Input,
    /// An `outputs:` attribute.
    Output,
}

impl AttributeType {
    /// The namespace prefix for this attribute type.
    pub const fn prefix(self) -> &'static str {
        match self {
            AttributeType::Input => NS_INPUTS,
            AttributeType::Output => NS_OUTPUTS,
        }
    }
}

/// A UsdShade attribute a connection may name as its source.
///
/// Only an `inputs:` or `outputs:` attribute is a legal connection source, so
/// the typed views implement this and a bare
/// [`usd::Attribute`](crate::usd::Attribute) does not.
pub trait ConnectionTarget {
    /// The full property path a connection should record.
    fn target_path(&self) -> &sdf::Path;
}

/// A typed UsdShade input or output attribute.
#[derive(Clone)]
pub enum ShadingAttribute {
    /// An `inputs:` attribute.
    Input(Input),
    /// An `outputs:` attribute.
    Output(Output),
}

impl ShadingAttribute {
    /// The underlying composed USD attribute.
    pub fn attribute(&self) -> &usd::Attribute {
        match self {
            ShadingAttribute::Input(input) => input.attribute(),
            ShadingAttribute::Output(output) => output.attribute(),
        }
    }

    /// Consume this view and return its underlying USD attribute.
    pub fn into_attribute(self) -> usd::Attribute {
        match self {
            ShadingAttribute::Input(input) => input.into_attribute(),
            ShadingAttribute::Output(output) => output.into_attribute(),
        }
    }

    /// Whether this is an input or output.
    pub const fn attribute_type(&self) -> AttributeType {
        match self {
            ShadingAttribute::Input(_) => AttributeType::Input,
            ShadingAttribute::Output(_) => AttributeType::Output,
        }
    }

    /// The full property path of this attribute.
    pub fn path(&self) -> &sdf::Path {
        self.attribute().path()
    }

    /// Valid and invalid upstream connection sources, in composed order.
    pub fn connected_sources(&self) -> Result<ConnectedSources> {
        connected_sources(self.attribute())
    }
}

impl ConnectionTarget for ShadingAttribute {
    fn target_path(&self) -> &sdf::Path {
        self.path()
    }
}

/// Information about one valid upstream UsdShade connection source.
///
/// This is the Rust counterpart of `UsdShadeConnectionSourceInfo`. A source
/// path is valid when a namespaced attribute is defined there. Nothing is
/// asked of the owning prim's type: it may be an untyped `over`, as OpenUSD
/// permits for connection targets.
#[derive(Clone)]
pub struct ConnectionSource {
    source_prim: usd::Prim,
    source_path: sdf::Path,
    source_name: tf::Token,
    source_type: AttributeType,
    type_name: Option<tf::Token>,
    source_is_container: bool,
}

impl ConnectionSource {
    /// The connectable prim that owns the source attribute.
    pub fn source_prim(&self) -> &usd::Prim {
        &self.source_prim
    }

    /// The complete property path targeted by the connection.
    pub fn source_path(&self) -> &sdf::Path {
        &self.source_path
    }

    /// The source attribute's base name without its namespace prefix.
    pub fn source_name(&self) -> &tf::Token {
        &self.source_name
    }

    /// The source attribute's full name, including its namespace prefix.
    pub fn full_name(&self) -> &str {
        self.source_path
            .split_property()
            .expect("a ConnectionSource always holds a property path")
            .1
    }

    /// Whether the source attribute is an input or output.
    pub const fn source_type(&self) -> AttributeType {
        self.source_type
    }

    /// The source attribute's composed USD value type, absent when the
    /// attribute is defined without one.
    pub fn type_name(&self) -> Option<&tf::Token> {
        self.type_name.as_ref()
    }

    /// The typed source attribute.
    pub fn attribute(&self) -> ShadingAttribute {
        let attribute = self.source_prim.stage().attribute(self.source_path.clone());
        match self.source_type {
            AttributeType::Input => ShadingAttribute::Input(Input::new(attribute)),
            AttributeType::Output => ShadingAttribute::Output(Output::new(attribute)),
        }
    }

    pub(super) const fn source_is_container(&self) -> bool {
        self.source_is_container
    }
}

/// Valid and invalid sources found on one UsdShade attribute.
///
/// Both collections preserve the order of the composed connection paths. A
/// path is invalid when it does not identify an existing input or output on a
/// defined prim.
#[derive(Clone, Default)]
pub struct ConnectedSources {
    sources: Vec<ConnectionSource>,
    invalid_source_paths: Vec<sdf::Path>,
}

impl ConnectedSources {
    /// Valid upstream connection sources.
    pub fn sources(&self) -> &[ConnectionSource] {
        &self.sources
    }

    /// Connection paths that do not identify valid UsdShade sources.
    pub fn invalid_source_paths(&self) -> &[sdf::Path] {
        &self.invalid_source_paths
    }

    /// Consume the result and return its valid sources.
    pub fn into_sources(self) -> Vec<ConnectionSource> {
        self.sources
    }
}

pub(super) fn connected_sources(attribute: &usd::Attribute) -> Result<ConnectedSources> {
    let mut result = ConnectedSources::default();
    for source_path in attribute.connections()? {
        let Some((source_prim_path, full_name)) = source_path.split_property() else {
            result.invalid_source_paths.push(source_path);
            continue;
        };
        let Some((source_name, source_type)) = base_name_and_type(full_name) else {
            result.invalid_source_paths.push(source_path);
            continue;
        };
        let Some((source_prim, source_is_container)) = source_prim(attribute.stage(), &source_prim_path)? else {
            result.invalid_source_paths.push(source_path);
            continue;
        };

        let source_attribute = attribute.stage().attribute(source_path.clone());
        if !source_attribute.is_defined()? {
            result.invalid_source_paths.push(source_path);
            continue;
        }
        let source_name = tf::Token::from(source_name);

        result.sources.push(ConnectionSource {
            source_prim,
            source_path,
            source_name,
            source_type,
            type_name: source_attribute.type_name()?,
            source_is_container,
        });
    }
    Ok(result)
}

/// The full property name for an input: `inputs:<base>`.
pub(super) fn input_name(base: &str) -> String {
    format!("{NS_INPUTS}{base}")
}

/// The full property name for an output: `outputs:<base>`.
pub(super) fn output_name(base: &str) -> String {
    format!("{NS_OUTPUTS}{base}")
}

/// The base name of a connectable property.
///
/// Names outside the `inputs:` and `outputs:` namespaces are returned
/// unchanged.
pub fn base_name(full_name: &str) -> &str {
    base_name_and_type(full_name).map_or(full_name, |(name, _)| name)
}

/// Split a full shading attribute name into its base name and attribute type.
pub fn base_name_and_type(full_name: &str) -> Option<(&str, AttributeType)> {
    full_name
        .strip_prefix(NS_INPUTS)
        .map(|name| (name, AttributeType::Input))
        .or_else(|| {
            full_name
                .strip_prefix(NS_OUTPUTS)
                .map(|name| (name, AttributeType::Output))
        })
}

/// The connectable prim owning a source attribute, paired with whether it is a
/// container.
fn source_prim(stage: &usd::Stage, path: &sdf::Path) -> Result<Option<(usd::Prim, bool)>> {
    let prim = stage.prim(path.clone());
    if !prim.is_valid()? {
        return Ok(None);
    }
    let source_is_container = is_container(&prim)?;
    Ok(Some((prim, source_is_container)))
}

/// Whether `prim` is a NodeGraph or Material container.
///
/// A container holds other connectable prims and reaches them through its own
/// interface. A prim of any other type produces its outputs directly.
///
/// TODO: C++ reads containment off a plugin-registered connectable behavior,
/// so a site can teach it about its own container types. Naming the two
/// built-in ones stands in for that registry.
pub(super) fn is_container(prim: &usd::Prim) -> Result<bool> {
    is_any_typed(prim, &[T_NODE_GRAPH, T_MATERIAL])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::shade::{Connectable, Shader};

    #[test]
    fn structured_sources() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let source = Shader::define(&stage, "/Mat/Source")?;
        let output = source.create_output("rgb", "float3")?;
        let sink = Shader::define(&stage, "/Mat/Sink")?;
        sink.create_input("color", "color3f")?.connect_to(&output)?;

        let connected = sink.input("color").connected_sources()?;
        assert!(connected.invalid_source_paths().is_empty());
        let source = connected.sources().first().expect("connected source");
        assert_eq!(source.source_prim().path().as_str(), "/Mat/Source");
        assert_eq!(source.source_path().as_str(), "/Mat/Source.outputs:rgb");
        assert_eq!(source.source_name().as_str(), "rgb");
        assert_eq!(source.full_name(), "outputs:rgb");
        assert_eq!(source.source_type(), AttributeType::Output);
        assert_eq!(source.type_name().map(tf::Token::as_str), Some("float3"));
        Ok(())
    }

    #[test]
    fn untyped_source_valid() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let source = stage.override_prim("/Mat/Source")?;
        let source_output = source.create_attribute("outputs:result", "float")?;
        let sink = Shader::define(&stage, "/Mat/Sink")?;
        // An attribute authored through the generic API becomes a connection
        // target by way of the namespace-checked wrapper.
        let source_output = Output::from_attribute(source_output).expect("an outputs: attribute");
        sink.create_input("value", "float")?.connect_to(&source_output)?;

        // Nothing is asked of the source prim's type, so an `over` carrying a
        // namespaced attribute is a source like any other.
        let connected = sink.input("value").connected_sources()?;
        assert!(connected.invalid_source_paths().is_empty());
        assert_eq!(connected.sources().len(), 1);
        assert_eq!(connected.sources()[0].source_prim().path(), source.path());
        Ok(())
    }

    #[test]
    fn invalid_sources_reported() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let valid = Shader::define(&stage, "/Mat/Valid")?;
        let valid_output = valid.create_output("result", "float")?;
        let missing_output = Shader::define(&stage, "/Mat/MissingOutput")?;
        let plain = stage.define_prim("/Mat/Plain")?.set_type_name("Scope")?;
        plain.create_attribute("result", "float")?;
        let sink = Shader::define(&stage, "/Mat/Sink")?;
        sink.create_input("value", "float")?.set_connections([
            sdf::path("/Missing.outputs:result")?,
            sdf::path("/Mat/Plain.result")?,
            missing_output.path().append_property("outputs:result")?,
            valid_output.path().clone(),
        ])?;

        let connected = sink.input("value").connected_sources()?;
        assert_eq!(connected.sources().len(), 1);
        assert_eq!(connected.sources()[0].source_path(), valid_output.path());

        // A missing prim, a name outside the shading namespaces, and a
        // namespaced name nothing defines each fail for their own reason.
        let invalid: Vec<&str> = connected.invalid_source_paths().iter().map(sdf::Path::as_str).collect();
        assert_eq!(
            invalid,
            vec![
                "/Missing.outputs:result",
                "/Mat/Plain.result",
                "/Mat/MissingOutput.outputs:result"
            ]
        );
        Ok(())
    }

    #[test]
    fn material_is_container() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let material = crate::schemas::shade::Material::define(&stage, "/Mat")?;
        material.create_input("gain", "float")?;
        let shader = Shader::define(&stage, "/Mat/Shader")?;
        shader
            .create_input("value", "float")?
            .connect_to(&material.input("gain"))?;

        let connected = shader.input("value").connected_sources()?;
        let source = connected.sources().first().expect("connected source");
        assert_eq!(source.source_type(), AttributeType::Input);
        assert!(source.source_is_container(), "a Material is a NodeGraph container");
        Ok(())
    }
}
