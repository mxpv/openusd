//! What a plugin light and a plugin light filter add to their generated
//! views: the `NodeDefAPI` that names the shader a renderer plugin draws
//! them with.

use openusd::usd::SchemaBase;

use super::{PluginLight, PluginLightFilter};
use crate::shade::NodeDefAPI;

impl PluginLight {
    /// The light's `NodeDefAPI`, which identifies its shader (C++
    /// `UsdLuxPluginLight::GetNodeDefAPI`).
    pub fn node_def(&self) -> NodeDefAPI {
        NodeDefAPI::from_prim_unchecked(self.prim().clone())
    }
}

impl PluginLightFilter {
    /// The filter's `NodeDefAPI`, which identifies its shader (C++
    /// `UsdLuxPluginLightFilter::GetNodeDefAPI`).
    pub fn node_def(&self) -> NodeDefAPI {
        NodeDefAPI::from_prim_unchecked(self.prim().clone())
    }
}
