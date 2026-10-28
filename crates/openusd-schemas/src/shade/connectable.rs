//! UsdShade connection source queries and attribute namespacing.

use std::iter;

use openusd::Result;

use openusd::{pcp, sdf, tf, usd};

use super::tokens::{INPUTS, OUTPUTS};
use super::{Input, Output};
use crate::SchemaError;

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
            AttributeType::Input => INPUTS,
            AttributeType::Output => OUTPUTS,
        }
    }
}

/// Where a new connection goes among the ones an attribute has (C++
/// `UsdShadeConnectionModification`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum ConnectionModification {
    /// The new connection is the only one.
    #[default]
    Replace,
    /// The new connection is the strongest the edit target prepends.
    Prepend,
    /// The new connection is the weakest the edit target appends.
    Append,
}

/// A UsdShade attribute a connection may name as its source.
///
/// Only an `inputs:` or `outputs:` attribute is a legal connection source, so
/// the typed views implement this and a bare
/// [`usd::Attribute`](openusd::usd::Attribute) does not.
pub trait ConnectionTarget {
    /// The source attribute.
    fn attribute(&self) -> &usd::Attribute;
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
    fn attribute(&self) -> &usd::Attribute {
        ShadingAttribute::attribute(self)
    }
}

/// Information about one upstream UsdShade connection source.
///
/// This is the Rust counterpart of `UsdShadeConnectionSourceInfo`: an
/// `inputs:` or `outputs:` property on a prim the stage holds. One that
/// [`connected_sources`](ShadingAttribute::connected_sources) reads names a
/// defined attribute, and one [`new`](Self::new) builds may name an
/// attribute not yet authored. Nothing is asked of the owning prim's type:
/// it may be an untyped `over`, as OpenUSD permits for connection targets.
#[derive(Clone)]
pub struct ConnectionSource {
    source_prim: usd::Prim,
    source_path: sdf::Path,
    source_name: tf::Token,
    source_type: AttributeType,
    type_name: Option<sdf::ValueTypeName>,
}

impl ConnectionSource {
    /// The source a connection to `path` names (C++
    /// `UsdShadeConnectionSourceInfo(stage, sourcePath)`): `path` is a
    /// property path in the `inputs:` or `outputs:` namespace, on a prim the
    /// stage holds. `None` otherwise, where C++ builds an info that is not
    /// `IsValid`. Nothing is asked of the prim's type.
    ///
    /// The attribute need not exist yet, and its type name is read where it
    /// does. Connecting to the source's [`attribute`](Self::attribute) then
    /// creates a missing one (C++ `ConnectToSource(sourcePath)`).
    pub fn new(stage: &usd::Stage, path: impl sdf::IntoPath) -> Result<Option<Self>> {
        Ok(Self::resolve(stage, sdf::try_into_path(path)?)?.map(|(source, _)| source))
    }

    /// The source a connection to `path` names, and whether its attribute is
    /// defined. The type name is read only from a defined attribute.
    fn resolve(stage: &usd::Stage, path: sdf::Path) -> Result<Option<(Self, bool)>> {
        let Some((prim_path, full_name)) = path.split_property() else {
            return Ok(None);
        };
        let Some((name, source_type)) = base_name_and_type(full_name) else {
            return Ok(None);
        };
        let source_prim = stage.prim(prim_path)?;
        if !source_prim.is_valid()? {
            return Ok(None);
        }
        let source_name = tf::Token::from(name);
        let attribute = stage.attribute(path.clone())?;
        let defined = attribute.is_defined()?;
        let source = Self {
            source_prim,
            source_path: path,
            source_name,
            source_type,
            type_name: if defined { attribute.type_name()? } else { None },
        };
        Ok(Some((source, defined)))
    }

    /// The connectable prim that owns the source attribute.
    pub fn prim(&self) -> &usd::Prim {
        &self.source_prim
    }

    /// The complete property path targeted by the connection.
    pub fn path(&self) -> &sdf::Path {
        &self.source_path
    }

    /// The source attribute's base name without its namespace prefix.
    pub fn name(&self) -> &tf::Token {
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

    /// The source attribute's composed value type (C++
    /// `UsdShadeConnectionSourceInfo::typeName`), absent when the attribute
    /// is defined without a registered one.
    pub fn type_name(&self) -> Option<&sdf::ValueTypeName> {
        self.type_name.as_ref()
    }

    /// The typed source attribute.
    pub fn attribute(&self) -> ShadingAttribute {
        let attribute = self.source_prim.attribute(self.full_name());
        match self.source_type {
            AttributeType::Input => ShadingAttribute::Input(Input::new(attribute)),
            AttributeType::Output => ShadingAttribute::Output(Output::new(attribute)),
        }
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
    invalid_paths: Vec<sdf::Path>,
}

impl ConnectedSources {
    /// Valid upstream connection sources.
    pub fn sources(&self) -> &[ConnectionSource] {
        &self.sources
    }

    /// Connection paths that do not identify valid UsdShade sources.
    pub fn invalid_paths(&self) -> &[sdf::Path] {
        &self.invalid_paths
    }

    /// Consume the result and return its valid sources.
    pub fn into_sources(self) -> Vec<ConnectionSource> {
        self.sources
    }
}

/// The valid and invalid sources `attribute` connects to, in composed order
/// (C++ `UsdShadeConnectableAPI::GetConnectedSources`).
pub(super) fn connected_sources(attribute: &usd::Attribute) -> Result<ConnectedSources> {
    let mut result = ConnectedSources::default();
    for source_path in attribute.connections()? {
        match ConnectionSource::resolve(attribute.stage(), source_path.clone())? {
            // A connected source also needs its attribute to exist.
            Some((source, true)) => result.sources.push(source),
            _ => result.invalid_paths.push(source_path),
        }
    }
    Ok(result)
}

/// The full property name for an input: `inputs:<base>`.
pub(super) fn input_name(base: &str) -> String {
    format!("{INPUTS}{base}")
}

/// The full property name for an output: `outputs:<base>`.
pub(super) fn output_name(base: &str) -> String {
    format!("{OUTPUTS}{base}")
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
        .strip_prefix(INPUTS)
        .map(|name| (name, AttributeType::Input))
        .or_else(|| {
            full_name
                .strip_prefix(OUTPUTS)
                .map(|name| (name, AttributeType::Output))
        })
}

/// The authored `inputs:` attributes of `prim` in composed property order —
/// the collection behind
/// [`Connectable::authored_inputs`](super::Connectable::authored_inputs) and
/// the interface-consumer walk.
pub(super) fn authored_inputs(prim: &usd::Prim) -> Result<Vec<Input>> {
    Ok(prim
        .authored_attributes_in_namespace(INPUTS)?
        .into_iter()
        .map(Input::new)
        .collect())
}

/// The path of `source`, which `consumer` is to connect to, defined first
/// where it is not, with `consumer`'s type and `custom = false` (C++
/// `_GetOrCreateSourceAttr`). A source no layer or schema defines declares
/// no type of its own.
pub(super) fn define_source(source: &usd::Attribute, consumer: &usd::Attribute) -> Result<sdf::Path, SchemaError> {
    if !source.is_defined()? {
        let type_name = consumer
            .type_name()?
            .ok_or_else(|| SchemaError::UntypedConnectionSource {
                attribute: source.path().clone(),
                consumer: consumer.path().clone(),
            })?;
        source
            .prim()
            .attribute_builder(source.name(), type_name)
            .custom(false)
            .build()?;
    }
    Ok(source.path().clone())
}

/// Whether the strongest connection opinion on `attribute` is authored across
/// a specializes arc, as a base material's is (C++
/// `IsSourceConnectionFromBaseMaterial`): the node that introduced the spec
/// holding it came through one, or was implied from one.
pub(super) fn source_from_base_material(attribute: &usd::Attribute) -> Result<bool> {
    let stage = attribute.stage();
    let Some(site) = attribute.property_stack()?.into_iter().find(|site| {
        stage.layer(&site.layer).is_some_and(|layer| {
            layer
                .attribute(&site.path)
                .ok()
                .flatten()
                .is_some_and(|spec| spec.has_connection_paths())
        })
    }) else {
        return Ok(false);
    };
    attribute.prim().prim_index().with(|index| {
        index
            .node_providing_spec(&site.layer, &site.path.prim_path())
            .is_some_and(|node| within_base_material(index, node.id()))
    })
}

/// Whether `node` lies within a base material: it, or a node it was
/// introduced from, came through a specializes arc (C++
/// `_NodeRepresentsLiveBaseMaterial`).
fn within_base_material(index: &pcp::PrimIndex, node: pcp::NodeId) -> bool {
    iter::successors(Some(node), |id| index.node(*id).origin())
        .any(|id| index.node(id).arc() == pcp::ArcType::Specialize)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::shade::{Connectable, Shader};
    use openusd::Result;

    #[test]
    fn structured_sources() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let source = Shader::define(&stage, "/Mat/Source")?;
        let output = source.create_output("rgb", "float3")?;
        let sink = Shader::define(&stage, "/Mat/Sink")?;
        sink.create_input("color", "color3f")?.connect_to(&output)?;

        let connected = sink.input("color").connected_sources()?;
        assert!(connected.invalid_paths().is_empty());
        let source = connected.sources().first().expect("connected source");
        assert_eq!(source.prim().path().as_str(), "/Mat/Source");
        assert_eq!(source.path().as_str(), "/Mat/Source.outputs:rgb");
        assert_eq!(source.name().as_str(), "rgb");
        assert_eq!(source.full_name(), "outputs:rgb");
        assert_eq!(source.source_type(), AttributeType::Output);
        assert_eq!(source.type_name(), Some(&sdf::ValueTypeName::FLOAT3));
        Ok(())
    }

    /// A source built from a path needs a namespaced property on a prim the
    /// stage holds, and not the attribute itself, which connecting creates
    /// with the consumer's type (C++ `ConnectToSource(sourcePath)`).
    #[test]
    fn source_from_path() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        Shader::define(&stage, "/Mat/Source")?;
        let sink = Shader::define(&stage, "/Mat/Sink")?;

        let source = ConnectionSource::new(&stage, "/Mat/Source.outputs:out")?.expect("a valid source");
        assert_eq!(source.name().as_str(), "out");
        assert_eq!(source.source_type(), AttributeType::Output);
        assert_eq!(source.type_name(), None, "the attribute does not exist yet");

        let input = sink.create_input("in", "color3f")?.connect_to(&source.attribute())?;
        let connected = input.connected_sources()?;
        let created = connected.sources().first().expect("the created source");
        assert_eq!(created.path().as_str(), "/Mat/Source.outputs:out");
        assert_eq!(created.type_name(), Some(&sdf::ValueTypeName::COLOR3F));

        for invalid in ["/Mat/Source.out", "/Mat/Missing.outputs:out", "/Mat/Source"] {
            assert!(ConnectionSource::new(&stage, invalid)?.is_none(), "{invalid}");
        }
        Ok(())
    }

    #[test]
    fn untyped_source_valid() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
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
        assert!(connected.invalid_paths().is_empty());
        assert_eq!(connected.sources().len(), 1);
        assert_eq!(connected.sources()[0].prim().path(), source.path());
        Ok(())
    }

    #[test]
    fn invalid_sources_reported() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
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
        assert_eq!(connected.sources()[0].path(), valid_output.path());

        // A missing prim, a name outside the shading namespaces, and a
        // namespaced name nothing defines each fail for their own reason.
        let invalid: Vec<&str> = connected.invalid_paths().iter().map(sdf::Path::as_str).collect();
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
    fn material_is_container() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let material = crate::shade::Material::define(&stage, "/Mat")?;
        material.create_input("gain", "float")?;
        let shader = Shader::define(&stage, "/Mat/Shader")?;
        shader
            .create_input("value", "float")?
            .connect_to(&material.input("gain"))?;

        let connected = shader.input("value").connected_sources()?;
        let source = connected.sources().first().expect("connected source");
        assert_eq!(source.source_type(), AttributeType::Input);
        let context = crate::shade::ConnectableContext::default();
        assert!(context.is_container(source.prim())?, "a Material is a container");
        Ok(())
    }
}
