//! Typed view over a UsdShade `outputs:` attribute.

use openusd::Result;
use openusd::{sdf, usd};

use super::impl_shading_attribute;
use super::tokens::OUTPUTS;
use super::{ConnectableContext, ConnectionTarget, ShadingAttribute};

/// A UsdShade output backed by an `outputs:<base>` USD attribute
/// (C++ `UsdShadeOutput`).
///
/// An output on a shader is a terminal producer — the endpoint a downstream
/// input connects to. An output on a NodeGraph or Material is an interface
/// that carries the connection further, into the container's own inputs or
/// down to the nodes it holds.
#[derive(Clone, derive_more::Deref)]
pub struct Output {
    attribute: usd::Attribute,
}

impl_shading_attribute!(Output, OUTPUTS);

impl Output {
    /// Whether this output may connect to `source` under the behavior of
    /// its prim (C++ `UsdShadeConnectableAPI::CanConnect`). An
    /// [`Input`](super::Input) or an [`Output`] passes as its attribute.
    pub fn can_connect(&self, source: &usd::Attribute) -> Result<bool> {
        ConnectableContext::default().can_connect_output(self, source)
    }
}

impl From<Output> for ShadingAttribute {
    fn from(output: Output) -> Self {
        ShadingAttribute::Output(output)
    }
}

impl ConnectionTarget for Output {
    fn target_path(&self) -> &sdf::Path {
        self.attribute().path()
    }
}
