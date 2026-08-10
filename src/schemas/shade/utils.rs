//! Logical UsdShade value-producing attribute resolution.

use anyhow::Result;

use crate::{sdf, usd};

use super::connectable::{AttributeType, ConnectionSource, ShadingAttribute};

pub(super) fn value_producing_attributes(
    attribute: ShadingAttribute,
    shader_outputs_only: bool,
) -> Result<Vec<ShadingAttribute>> {
    let mut producing = Vec::new();
    resolve_recursive(attribute, &mut Vec::new(), &mut producing, shader_outputs_only)?;
    Ok(producing)
}

fn resolve_recursive(
    attribute: ShadingAttribute,
    visited: &mut Vec<sdf::Path>,
    producing: &mut Vec<ShadingAttribute>,
    shader_outputs_only: bool,
) -> Result<bool> {
    if attribute.attribute().type_name()?.is_none() || visited.contains(attribute.path()) {
        return Ok(false);
    }

    let sources = match &attribute {
        ShadingAttribute::Input(input) => input.connected_sources()?,
        ShadingAttribute::Output(output) => output.connected_sources()?,
    };
    if !sources.is_empty() {
        visited.push(attribute.path().clone());
    }

    let mut found = false;
    if sources.sources().len() > 1 {
        for source in sources.sources() {
            let mut branch_visited = visited.clone();
            found |= follow_source(source, &mut branch_visited, producing, shader_outputs_only)?;
        }
    } else if let Some(source) = sources.sources().first() {
        found = follow_source(source, visited, producing, shader_outputs_only)?;
    }

    if !shader_outputs_only && !found && attribute.attribute().value_source()? == usd::ValueSource::Authored {
        producing.push(attribute);
        found = true;
    }
    Ok(found)
}

fn follow_source(
    source: &ConnectionSource,
    visited: &mut Vec<sdf::Path>,
    producing: &mut Vec<ShadingAttribute>,
    shader_outputs_only: bool,
) -> Result<bool> {
    let attribute = source.attribute();
    match source.source_type() {
        AttributeType::Output if !source.source_is_container() => {
            producing.push(attribute);
            Ok(true)
        }
        AttributeType::Input if !source.source_is_container() => Ok(false),
        AttributeType::Input | AttributeType::Output => {
            resolve_recursive(attribute, visited, producing, shader_outputs_only)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::shade::{AttributeType, Connectable, Material, NodeGraph, Shader};
    use crate::{sdf, usd};

    #[test]
    fn structured_sources() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let source = Shader::define(&stage, "/Mat/Source")?;
        let output = source.create_output("rgb", "float3")?;
        let sink = Shader::define(&stage, "/Mat/Sink")?;
        sink.create_input("color", "color3f")?.connect_to_output(&output)?;

        let connected = sink.input("color").connected_sources()?;
        assert!(connected.invalid_source_paths().is_empty());
        let source = connected.sources().first().expect("connected source");
        assert_eq!(source.source_prim().path().as_str(), "/Mat/Source");
        assert_eq!(source.source_path().as_str(), "/Mat/Source.outputs:rgb");
        assert_eq!(source.source_name().as_str(), "rgb");
        assert_eq!(source.full_name(), "outputs:rgb");
        assert_eq!(source.source_type(), AttributeType::Output);
        assert_eq!(source.type_name().as_str(), "float3");
        Ok(())
    }

    #[test]
    fn untyped_source_valid() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let source = stage.override_prim("/Mat/Source")?;
        let source_output = source.create_attribute("outputs:result", "float")?;
        let sink = Shader::define(&stage, "/Mat/Sink")?;
        sink.create_input("value", "float")?
            .set_connections([source_output.path().clone()])?;

        let connected = sink.input("value").connected_sources()?;
        assert!(connected.invalid_source_paths().is_empty());
        assert_eq!(connected.sources().len(), 1);
        assert_eq!(connected.sources()[0].source_prim().path(), source.path());

        let producing = sink.input("value").value_producing_attributes(false)?;
        assert_eq!(producing.len(), 1);
        assert_eq!(producing[0].path(), source_output.path());
        assert_eq!(producing[0].attribute_type(), AttributeType::Output);
        Ok(())
    }

    #[test]
    fn nested_graph_resolution() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let source = Shader::define(&stage, "/Mat/Source")?;
        let source_output = source.create_output("result", "float")?;

        let inner = NodeGraph::define(&stage, "/Mat/Inner")?;
        inner
            .create_output("result", "float")?
            .connect_to_output(&source_output)?;
        let outer = NodeGraph::define(&stage, "/Mat/Outer")?;
        outer
            .create_output("result", "float")?
            .connect_to_output(&inner.output("result"))?;
        let sink = Shader::define(&stage, "/Mat/Sink")?;
        sink.create_input("value", "float")?
            .connect_to_output(&outer.output("result"))?;

        let producing = sink.input("value").value_producing_attributes(false)?;
        assert_eq!(producing.len(), 1);
        assert_eq!(producing[0].path().as_str(), "/Mat/Source.outputs:result");
        assert_eq!(producing[0].attribute_type(), AttributeType::Output);
        Ok(())
    }

    #[test]
    fn interface_value_resolution() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let material = Material::define(&stage, "/Mat")?;
        material.create_input("gain", "float")?.set(2.0_f32)?;
        let graph = NodeGraph::define(&stage, "/Mat/Graph")?;
        graph
            .create_output("result", "float")?
            .connect_to_input(&material.input("gain"))?;

        let producing = graph.output("result").value_producing_attributes(false)?;
        assert_eq!(producing.len(), 1);
        assert_eq!(producing[0].path().as_str(), "/Mat.inputs:gain");
        assert_eq!(producing[0].attribute_type(), AttributeType::Input);
        assert!(graph.output("result").value_producing_attributes(true)?.is_empty());
        Ok(())
    }

    #[test]
    fn multiple_source_order() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let first = Shader::define(&stage, "/Mat/First")?;
        let first_output = first.create_output("result", "float")?;
        let second = Shader::define(&stage, "/Mat/Second")?;
        let second_output = second.create_output("result", "float")?;

        let first_graph = NodeGraph::define(&stage, "/Mat/FirstGraph")?;
        first_graph
            .create_output("result", "float")?
            .connect_to_output(&first_output)?;
        let second_graph = NodeGraph::define(&stage, "/Mat/SecondGraph")?;
        second_graph
            .create_output("result", "float")?
            .connect_to_output(&second_output)?;
        let root = NodeGraph::define(&stage, "/Mat/Root")?;
        root.create_output("result", "float")?.set_connections([
            second_graph.output("result").path().clone(),
            first_graph.output("result").path().clone(),
        ])?;

        let producing = root.output("result").value_producing_attributes(false)?;
        let paths: Vec<&str> = producing.iter().map(|attribute| attribute.path().as_str()).collect();
        assert_eq!(paths, vec!["/Mat/Second.outputs:result", "/Mat/First.outputs:result"]);
        Ok(())
    }

    #[test]
    fn invalid_sources_reported() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
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
        assert_eq!(connected.sources()[0].source_path(), valid_output.path());
        let invalid: Vec<&str> = connected.invalid_source_paths().iter().map(sdf::Path::as_str).collect();
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
    fn cycle_stops() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let first = NodeGraph::define(&stage, "/Mat/First")?;
        let second = NodeGraph::define(&stage, "/Mat/Second")?;
        first.create_output("result", "float")?;
        second.create_output("result", "float")?;
        first.output("result").connect_to_output(&second.output("result"))?;
        second.output("result").connect_to_output(&first.output("result"))?;

        assert!(first.output("result").value_producing_attributes(false)?.is_empty());
        Ok(())
    }
}
