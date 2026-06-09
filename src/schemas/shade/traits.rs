//! The UsdShade connectable interface shared across the shading prims.
//!
//! [`Connectable`] (C++ `UsdShadeConnectableAPI`) is the surface every shading
//! prim shares — [`Shader`](super::Shader), [`NodeGraph`](super::NodeGraph),
//! and [`Material`](super::Material) all carry `inputs:` / `outputs:`
//! attributes that are wired together by connections. A UsdShadeInput is an
//! `inputs:<base>` attribute and a UsdShadeOutput is an `outputs:<base>`
//! attribute; both are plain attributes, so the accessors return
//! [`Attribute`] handles and connections are authored / read through
//! [`Attribute::set_connections`](crate::usd::Attribute::set_connections) /
//! [`connections`](crate::usd::Attribute::connections).

use anyhow::Result;

use crate::sdf::Value;
use crate::usd::{Attribute, SchemaBase};

use super::connectable::{input_name, output_name};
use super::tokens::{META_CONNECTABILITY, META_RENDER_TYPE, NS_INPUTS, NS_OUTPUTS};
use super::Connectability;

/// The connectable surface shared by shading prims (C++
/// `UsdShadeConnectableAPI`): typed `inputs:` / `outputs:` attributes addressed
/// by their base name (the `inputs:` / `outputs:` namespace prefix is added for
/// you).
pub trait Connectable: SchemaBase {
    /// Handle to the `inputs:<base>` attribute (C++ `GetInput`). Read its value
    /// with `get::<T>()` or its connection sources with `connections()`.
    fn input(&self, base: &str) -> Attribute {
        self.prim().attribute(input_name(base))
    }

    /// Author `inputs:<base>` of `type_name` (`custom = false`)
    /// (C++ `CreateInput`). Chain `.set(value)` for a default or
    /// `.set_connections([..])` to wire it to another property.
    fn create_input(&self, base: &str, type_name: &str) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(input_name(base), type_name)?
            .set_custom(false)?)
    }

    /// Handle to the `outputs:<base>` attribute (C++ `GetOutput`). An output
    /// usually carries no value — it is the source endpoint a downstream input
    /// connects to.
    fn output(&self, base: &str) -> Attribute {
        self.prim().attribute(output_name(base))
    }

    /// Author `outputs:<base>` of `type_name` (`custom = false`)
    /// (C++ `CreateOutput`).
    fn create_output(&self, base: &str, type_name: &str) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(output_name(base), type_name)?
            .set_custom(false)?)
    }

    /// The authored input base names (without the `inputs:` prefix)
    /// (C++ `GetInputs`).
    fn input_names(&self) -> Result<Vec<String>> {
        Ok(self
            .prim()
            .property_names()?
            .into_iter()
            .filter_map(|p| p.strip_prefix(NS_INPUTS).map(str::to_string))
            .collect())
    }

    /// The authored output base names (without the `outputs:` prefix)
    /// (C++ `GetOutputs`).
    fn output_names(&self) -> Result<Vec<String>> {
        Ok(self
            .prim()
            .property_names()?
            .into_iter()
            .filter_map(|p| p.strip_prefix(NS_OUTPUTS).map(str::to_string))
            .collect())
    }

    /// The `connectability` of `inputs:<base>` (C++
    /// `UsdShadeInput::GetConnectability`), defaulting to
    /// [`Connectability::Full`](super::Connectability::Full) when unauthored.
    fn input_connectability(&self, base: &str) -> Result<Connectability> {
        Ok(self
            .input(base)
            .get_metadata::<Connectability>(META_CONNECTABILITY)?
            .unwrap_or_default())
    }

    /// Author the `connectability` of `inputs:<base>` (C++
    /// `UsdShadeInput::SetConnectability`). The input must already exist
    /// (`create_input`).
    fn set_input_connectability(&self, base: &str, connectability: Connectability) -> Result<()> {
        self.input(base).set_metadata(META_CONNECTABILITY, connectability)?;
        Ok(())
    }

    /// The renderer-specific `renderType` hint on `inputs:<base>`
    /// (C++ `UsdShadeInput::GetRenderType`).
    fn input_render_type(&self, base: &str) -> Result<Option<String>> {
        self.input(base).get_metadata::<String>(META_RENDER_TYPE)
    }

    /// Author the `renderType` hint on `inputs:<base>` (C++
    /// `UsdShadeInput::SetRenderType`). The input must already exist.
    fn set_input_render_type(&self, base: &str, render_type: &str) -> Result<()> {
        self.input(base)
            .set_metadata(META_RENDER_TYPE, Value::token(render_type))?;
        Ok(())
    }

    /// The renderer-specific `renderType` hint on `outputs:<base>`
    /// (C++ `UsdShadeOutput::GetRenderType`).
    fn output_render_type(&self, base: &str) -> Result<Option<String>> {
        self.output(base).get_metadata::<String>(META_RENDER_TYPE)
    }

    /// Author the `renderType` hint on `outputs:<base>` (C++
    /// `UsdShadeOutput::SetRenderType`). The output must already exist.
    fn set_output_render_type(&self, base: &str, render_type: &str) -> Result<()> {
        self.output(base)
            .set_metadata(META_RENDER_TYPE, Value::token(render_type))?;
        Ok(())
    }
}
