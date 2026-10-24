//! The UsdShade connectable interface shared across shading prims.

use openusd::Result;
use openusd::sdf;

use openusd::usd::SchemaBase;

use super::connectable::{authored_inputs, input_name, output_name};
use super::tokens::{INPUTS, OUTPUTS};
use super::{Input, Output};

/// The `inputs:` and `outputs:` surface shared by Shader, NodeGraph, and
/// Material prims, and by any prim a [`ConnectableAPI`](super::ConnectableAPI)
/// views (C++ `UsdShadeConnectableAPI`).
pub trait Connectable: SchemaBase {
    /// The `inputs:<base>` attribute view (C++ `GetInput`).
    ///
    /// The handle comes back whether or not anything is authored there, as
    /// [`Prim::attribute`](openusd::usd::Prim::attribute) does; an input nothing
    /// defines reads back empty.
    fn input(&self, base: &str) -> Input {
        Input::new(self.prim().attribute(input_name(base)))
    }

    /// Author `inputs:<base>` with `type_name` and `custom = false`.
    fn create_input(&self, base: &str, type_name: impl Into<sdf::ValueTypeName>) -> Result<Input> {
        Ok(Input::new(
            self.prim()
                .attribute_builder(input_name(base), type_name)
                .custom(false)
                .build()?,
        ))
    }

    /// The inputs this prim composes, authored or declared by its schema, in
    /// the order
    /// [`Prim::attributes_in_namespace`](openusd::usd::Prim::attributes_in_namespace)
    /// lists them (C++ `GetInputs` with `onlyAuthored` off).
    fn inputs(&self) -> Result<Vec<Input>> {
        Ok(self
            .prim()
            .attributes_in_namespace(INPUTS)?
            .into_iter()
            .map(Input::new)
            .collect())
    }

    /// The inputs layers author on this prim, in the order
    /// [`Prim::authored_attributes_in_namespace`](openusd::usd::Prim::authored_attributes_in_namespace)
    /// lists them (C++ `GetInputs`).
    fn authored_inputs(&self) -> Result<Vec<Input>> {
        authored_inputs(self.prim())
    }

    /// The `outputs:<base>` attribute view (C++ `GetOutput`), returned whether
    /// or not anything is authored there.
    fn output(&self, base: &str) -> Output {
        Output::new(self.prim().attribute(output_name(base)))
    }

    /// Author `outputs:<base>` with `type_name` and `custom = false`.
    fn create_output(&self, base: &str, type_name: impl Into<sdf::ValueTypeName>) -> Result<Output> {
        Ok(Output::new(
            self.prim()
                .attribute_builder(output_name(base), type_name)
                .custom(false)
                .build()?,
        ))
    }

    /// The outputs this prim composes, authored or declared by its schema, in
    /// the order
    /// [`Prim::attributes_in_namespace`](openusd::usd::Prim::attributes_in_namespace)
    /// lists them (C++ `GetOutputs` with `onlyAuthored` off).
    fn outputs(&self) -> Result<Vec<Output>> {
        Ok(self
            .prim()
            .attributes_in_namespace(OUTPUTS)?
            .into_iter()
            .map(Output::new)
            .collect())
    }

    /// The outputs layers author on this prim, in the order
    /// [`Prim::authored_attributes_in_namespace`](openusd::usd::Prim::authored_attributes_in_namespace)
    /// lists them (C++ `GetOutputs`).
    fn authored_outputs(&self) -> Result<Vec<Output>> {
        Ok(self
            .prim()
            .authored_attributes_in_namespace(OUTPUTS)?
            .into_iter()
            .map(Output::new)
            .collect())
    }
}

// The views a shading network connects through, which is what the trait is
// about; a generated view carries no membership of a hand-written trait.
impl Connectable for super::Shader {}
impl Connectable for super::NodeGraph {}
impl Connectable for super::Material {}
impl Connectable for super::ConnectableAPI {}

#[cfg(test)]
mod tests {
    use openusd::Result;

    use super::Connectable;
    use crate::shade::{Input, Material, Output, Shader};

    /// The base names of `views`, sorted: the listings interleave authored and
    /// declared properties in an order of their own.
    fn names<T>(views: &[T], base_name: impl Fn(&T) -> &str) -> Vec<&str> {
        let mut names: Vec<&str> = views.iter().map(base_name).collect();
        names.sort_unstable();
        names
    }

    /// A Material's schema declares its three terminals, which the composed
    /// listing carries and the authored one does not until written.
    #[test]
    fn declared_outputs() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let material = Material::define(&stage, "/Mat")?;
        assert_eq!(
            names(&material.outputs()?, Output::base_name),
            ["displacement", "surface", "volume"]
        );
        assert!(material.authored_outputs()?.is_empty());

        material.create_surface_output()?;
        assert_eq!(names(&material.authored_outputs()?, Output::base_name), ["surface"]);
        assert_eq!(material.outputs()?.len(), 3, "an authored terminal is listed once");
        Ok(())
    }

    /// A Shader's two listings agree: it declares no inputs.
    #[test]
    fn shader_inputs() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Surface")?;
        assert!(shader.inputs()?.is_empty());
        shader.create_input("roughness", "float")?;
        shader.create_input("metallic", "float")?;
        assert_eq!(names(&shader.inputs()?, Input::base_name), ["metallic", "roughness"]);
        assert_eq!(
            names(&shader.authored_inputs()?, Input::base_name),
            ["metallic", "roughness"]
        );
        Ok(())
    }
}
