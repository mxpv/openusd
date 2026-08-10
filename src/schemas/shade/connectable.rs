//! UsdShade connection source queries and attribute namespacing.

use anyhow::Result;

use crate::{sdf, tf, usd};

use super::tokens::{NS_INPUTS, NS_OUTPUTS};
use super::{Input, Material, NodeGraph, Output};

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
}

/// Information about one valid upstream UsdShade connection source.
///
/// This is the Rust counterpart of `UsdShadeConnectionSourceInfo`. The source
/// path is valid when its owning prim and namespaced source attribute exist.
/// The prim may be an untyped `over`, as OpenUSD permits for connection
/// targets.
#[derive(Clone)]
pub struct ConnectionSource {
    source_prim: usd::Prim,
    source_path: sdf::Path,
    source_name: tf::Token,
    source_type: AttributeType,
    type_name: tf::Token,
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

    /// The source attribute's composed USD value type.
    pub fn type_name(&self) -> &tf::Token {
        &self.type_name
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

    /// Whether no valid connection source was found.
    pub fn is_empty(&self) -> bool {
        self.sources.is_empty()
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
        let Some(type_name) = source_attribute.type_name()? else {
            result.invalid_source_paths.push(source_path);
            continue;
        };
        let source_name = tf::Token::from(source_name);

        result.sources.push(ConnectionSource {
            source_prim,
            source_path,
            source_name,
            source_type,
            type_name,
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

/// Full property path of an input on `prim`.
pub(super) fn input_path(prim: &sdf::Path, base: &str) -> Result<sdf::Path> {
    prim.append_property(input_name(base))
}

fn source_prim(stage: &usd::Stage, path: &sdf::Path) -> Result<Option<(usd::Prim, bool)>> {
    let prim = stage.prim(path.clone());
    if !prim.is_valid()? {
        return Ok(None);
    }
    let is_container = NodeGraph::get(stage, path.clone())?.is_some() || Material::get(stage, path.clone())?.is_some();
    Ok(Some((prim, is_container)))
}
