//! Typed view over a UsdShade `outputs:` attribute.

use std::ops::Deref;

use anyhow::Result;

use crate::{sdf, tf, usd};

use super::Input;
use super::connectable::{ConnectedSources, ShadingAttribute, connected_sources};
use super::tokens::{META_RENDER_TYPE, NS_OUTPUTS};
use super::utils::value_producing_attributes;

/// A UsdShade output backed by an `outputs:<base>` USD attribute.
///
/// Outputs on shaders are terminal producers. Outputs on NodeGraphs and
/// Materials may connect through container interfaces to other inputs or
/// outputs.
#[derive(Clone)]
pub struct Output {
    attribute: usd::Attribute,
}

impl Output {
    /// Wrap an attribute when it belongs to the `outputs:` namespace.
    pub fn from_attribute(attribute: usd::Attribute) -> Option<Self> {
        let is_output = attribute.path().split_property()?.1.strip_prefix(NS_OUTPUTS).is_some();
        is_output.then_some(Self { attribute })
    }

    /// The underlying composed USD attribute.
    pub fn attribute(&self) -> &usd::Attribute {
        &self.attribute
    }

    /// Consume this view and return its underlying USD attribute.
    pub fn into_attribute(self) -> usd::Attribute {
        self.attribute
    }

    /// The full attribute name, including the `outputs:` prefix.
    pub fn full_name(&self) -> &str {
        self.attribute
            .path()
            .split_property()
            .expect("an Output always holds a property path")
            .1
    }

    /// The output's base name without the `outputs:` prefix.
    pub fn base_name(&self) -> &str {
        self.full_name()
            .strip_prefix(NS_OUTPUTS)
            .expect("an Output always holds an outputs: attribute")
    }

    /// Author this output's default value.
    pub fn set(self, value: impl Into<sdf::Value>) -> Result<Self, usd::StageAuthoringError> {
        Ok(Self {
            attribute: self.attribute.set(value)?,
        })
    }

    /// Author this output's value at a numeric time code.
    pub fn set_at(
        self,
        value: impl Into<sdf::Value>,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<Self, usd::StageAuthoringError> {
        Ok(Self {
            attribute: self.attribute.set_at(value, time)?,
        })
    }

    /// Replace this output's composed connection source paths.
    pub fn set_connections<I>(self, targets: I) -> Result<Self, usd::StageAuthoringError>
    where
        I: IntoIterator<Item = sdf::Path>,
    {
        Ok(Self {
            attribute: self.attribute.set_connections(targets)?,
        })
    }

    /// Connect this output to an input, replacing existing connections.
    pub fn connect_to_input(self, source: &Input) -> Result<Self, usd::StageAuthoringError> {
        self.set_connections([source.path().clone()])
    }

    /// Connect this output to another output, replacing existing connections.
    pub fn connect_to_output(self, source: &Output) -> Result<Self, usd::StageAuthoringError> {
        self.set_connections([source.path().clone()])
    }

    /// The renderer-specific `renderType` hint, when authored.
    pub fn render_type(&self) -> Result<Option<tf::Token>> {
        self.attribute.get_metadata(META_RENDER_TYPE)
    }

    /// Author this output's renderer-specific `renderType` hint.
    pub fn set_render_type(self, render_type: impl Into<tf::Token>) -> Result<Self, usd::StageAuthoringError> {
        Ok(Self {
            attribute: self
                .attribute
                .set_metadata(META_RENDER_TYPE, sdf::Value::Token(render_type.into()))?,
        })
    }

    /// Valid and invalid upstream connection sources in composed order.
    pub fn connected_sources(&self) -> Result<ConnectedSources> {
        connected_sources(&self.attribute)
    }

    /// Resolve the logical attributes that produce this output's value.
    ///
    /// When `shader_outputs_only` is true, container values are omitted and
    /// only outputs on shader nodes are returned.
    pub fn value_producing_attributes(&self, shader_outputs_only: bool) -> Result<Vec<ShadingAttribute>> {
        value_producing_attributes(ShadingAttribute::Output(self.clone()), shader_outputs_only)
    }

    pub(super) fn new(attribute: usd::Attribute) -> Self {
        debug_assert!(Self::from_attribute(attribute.clone()).is_some());
        Self { attribute }
    }
}

impl Deref for Output {
    type Target = usd::Attribute;

    fn deref(&self) -> &Self::Target {
        &self.attribute
    }
}
