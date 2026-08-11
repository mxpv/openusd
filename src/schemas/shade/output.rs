//! Typed view over a UsdShade `outputs:` attribute.

use crate::{sdf, usd};

use super::impl_shading_attribute;
use super::tokens::NS_OUTPUTS;
use super::{ConnectionTarget, ShadingAttribute};

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

impl_shading_attribute!(Output, NS_OUTPUTS);

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
