//! The UsdShade connectable interface shared across shading prims.

use anyhow::Result;

use crate::usd::SchemaBase;

use super::connectable::{authored_inputs, input_name, output_name};
use super::{Input, Output};

/// The `inputs:` and `outputs:` surface shared by Shader, NodeGraph, and
/// Material prims (C++ `UsdShadeConnectableAPI`).
pub trait Connectable: SchemaBase {
    /// The `inputs:<base>` attribute view (C++ `GetInput`).
    ///
    /// The handle comes back whether or not anything is authored there, as
    /// [`Prim::attribute`](crate::usd::Prim::attribute) does; an input nothing
    /// defines reads back empty.
    fn input(&self, base: &str) -> Input {
        Input::new(self.prim().attribute(input_name(base)))
    }

    /// Author `inputs:<base>` with `type_name` and `custom = false`.
    fn create_input(&self, base: &str, type_name: &str) -> Result<Input> {
        Ok(Input::new(
            self.prim()
                .create_attribute(input_name(base), type_name)?
                .set_custom(false)?,
        ))
    }

    /// The authored inputs in composed property order (C++ `GetInputs`).
    fn inputs(&self) -> Result<Vec<Input>> {
        authored_inputs(self.prim())
    }

    /// The `outputs:<base>` attribute view (C++ `GetOutput`), returned whether
    /// or not anything is authored there.
    fn output(&self, base: &str) -> Output {
        Output::new(self.prim().attribute(output_name(base)))
    }

    /// Author `outputs:<base>` with `type_name` and `custom = false`.
    fn create_output(&self, base: &str, type_name: &str) -> Result<Output> {
        Ok(Output::new(
            self.prim()
                .create_attribute(output_name(base), type_name)?
                .set_custom(false)?,
        ))
    }

    /// The authored outputs in composed property order (C++ `GetOutputs`).
    fn outputs(&self) -> Result<Vec<Output>> {
        Ok(self
            .prim()
            .authored_attributes()?
            .into_iter()
            .filter_map(Output::from_attribute)
            .collect())
    }
}
