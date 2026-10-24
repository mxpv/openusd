//! Lights and light filters as shading nodes: the connectable interface their
//! views share with the shade views, and the behaviors their inputs and
//! outputs connect by.

use super::{LightAPI, LightFilter, PluginLightFilter, ShadowAPI, ShapingAPI, tokens};
use crate::shade::behavior::BuiltIn;
use crate::shade::{BehaviorRegistry, Connectable, NodeKind};

// The views C++ gives the connectable interface. A concrete light reaches it
// through its `light_api()`, as C++ `LightAPI()` does.
impl Connectable for LightAPI {}
impl Connectable for ShapingAPI {}
impl Connectable for ShadowAPI {}
impl Connectable for LightFilter {}
impl Connectable for PluginLightFilter {}

/// Add the behavior of each `UsdLux` schema that has one: `LightAPI`
/// (`lightAPI.cpp:325-360`), which every light builds in, and `LightFilter`
/// (`lightFilter.cpp:152-193`).
///
/// Both are containers that connect across scopes without encapsulation,
/// under the rules of a container node. A filter's outputs connect to
/// nothing.
pub(crate) fn register_behaviors(registry: &mut BehaviorRegistry) {
    let light = BuiltIn {
        container: true,
        encapsulation: false,
        kind: NodeKind::Container,
        outputs: true,
    };
    let filter = BuiltIn {
        outputs: false,
        ..light
    };
    registry
        .register(tokens::LIGHT_API, light)
        .register(tokens::LIGHT_FILTER, filter);
}
