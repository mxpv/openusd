//! Logical UsdShade value-producing attribute resolution.

use openusd::Result;

use crate::SchemaError;

use openusd::sdf;

use super::ConnectableContext;
use super::connectable::{AttributeType, ConnectionSource, ShadingAttribute};

/// Which upstream attributes count as producing a value, the choice C++
/// `UsdShadeUtils::GetValueProducingAttributes` spells `shaderOutputsOnly`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ProducerFilter {
    /// Any producer: an output on a shader node, or an input or output
    /// carrying an authored value, which is how a NodeGraph or Material
    /// interface supplies a constant.
    #[default]
    Any,
    /// Only outputs on shader nodes — the terminals a renderer can evaluate.
    /// Authored interface values are skipped, which also makes the walk
    /// cheaper by never asking whether a value is authored.
    ShaderOutputsOnly,
}

/// The longest connection chain the walk descends before giving up.
///
/// Following a chain costs a stack frame per hop, so scene description alone
/// would decide how deep the recursion goes. Shading networks nest a handful
/// of levels; this leaves several orders of magnitude of room before a chain
/// is treated as scene description the walk refuses to trust.
const MAX_CONNECTION_DEPTH: usize = 256;

impl ConnectableContext {
    /// The logical attributes that produce `attribute`'s value, following
    /// connections through the containers this context knows (C++
    /// `UsdShadeUtils::GetValueProducingAttributes`).
    pub fn value_producing_attributes(
        &self,
        attribute: impl Into<ShadingAttribute>,
        filter: ProducerFilter,
    ) -> Result<Vec<ShadingAttribute>, SchemaError> {
        let mut walk = Walk {
            context: self,
            chain: Vec::new(),
            producing: Vec::new(),
            filter,
        };
        walk.resolve(attribute.into())?;
        Ok(walk.producing)
    }
}

/// The state one producer walk carries from hop to hop.
struct Walk<'a> {
    context: &'a ConnectableContext,
    /// The connected attributes between the walk's origin and the attribute
    /// being resolved, both the cycle guard and the depth counter: an
    /// attribute already on the chain is a back edge, while one a sibling
    /// branch reached and left is not.
    chain: Vec<sdf::Path>,
    /// Every attribute found to produce a value, in walk order.
    producing: Vec<ShadingAttribute>,
    filter: ProducerFilter,
}

impl Walk<'_> {
    /// Walk `attribute`'s connections, appending every attribute that
    /// produces a value to `producing`, and report whether any was found.
    fn resolve(&mut self, attribute: ShadingAttribute) -> Result<bool, SchemaError> {
        if !attribute.attribute().is_defined()? || self.chain.contains(attribute.path()) {
            return Ok(false);
        }

        let sources = attribute.connected_sources()?;
        let sources = distinct_sources(&sources);
        let connected = !sources.is_empty();
        if connected {
            if self.chain.len() >= MAX_CONNECTION_DEPTH {
                return Err(SchemaError::ConnectionDepthExceeded {
                    attribute: attribute.path().clone(),
                    max: MAX_CONNECTION_DEPTH,
                });
            }
            self.chain.push(attribute.path().clone());
        }

        let mut found = false;
        for source in sources {
            found |= self.follow(source)?;
        }

        if connected {
            self.chain.pop();
        }

        // Nothing upstream produced a value, so an authored value here is
        // what a consumer resolves to — a NodeGraph or Material interface
        // value.
        if self.filter == ProducerFilter::Any && !found && attribute.attribute().has_authored_value()? {
            self.producing.push(attribute);
            found = true;
        }
        Ok(found)
    }

    /// Follow one connection to `source`, reporting whether a value was found
    /// behind it.
    fn follow(&mut self, source: &ConnectionSource) -> Result<bool, SchemaError> {
        let attribute = source.attribute();
        let container = self.context.is_container(source.prim())?;
        match source.source_type() {
            // An output on a node that holds no others is a terminal
            // producer; nothing upstream of it takes part in the value.
            AttributeType::Output if !container => {
                self.producing.push(attribute);
                Ok(true)
            }
            // Reaching an input on a node that holds no others ends the
            // chain: an input can only legally consume, so there is nothing
            // further to follow and no value to take.
            AttributeType::Input if !container => Ok(false),
            // A container was reached through its interface, so the value
            // comes from whatever that interface resolves to inside.
            AttributeType::Input | AttributeType::Output => self.resolve(attribute),
        }
    }
}

/// The sources of `connected` with repeats dropped, keeping composed order.
///
/// One source drives one value however many times a connection list names it,
/// and following it once per mention would multiply the walk at every hop.
fn distinct_sources(connected: &super::ConnectedSources) -> Vec<&ConnectionSource> {
    let mut distinct: Vec<&ConnectionSource> = Vec::new();
    for source in connected.sources() {
        if !distinct.iter().any(|seen| seen.path() == source.path()) {
            distinct.push(source);
        }
    }
    distinct
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::shade::{AttributeType, Connectable, Material, NodeGraph, Shader};
    use openusd::Result;

    #[test]
    fn untyped_source_terminal() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let source = stage.override_prim("/Mat/Source")?;
        let source_output = source.create_attribute("outputs:result", "float")?;
        let sink = Shader::define(&stage, "/Mat/Sink")?;
        sink.create_input("value", "float")?
            .set_connections([source_output.path().clone()])?;

        // A prim of no shading type holds no others, so its output is a
        // terminal producer rather than an interface to follow.
        let producing = sink.input("value").value_producing_attributes(ProducerFilter::Any)?;
        assert_eq!(producing.len(), 1);
        assert_eq!(producing[0].path(), source_output.path());
        assert_eq!(producing[0].attribute_type(), AttributeType::Output);
        Ok(())
    }

    #[test]
    fn nested_graph_resolution() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let source = Shader::define(&stage, "/Mat/Source")?;
        let source_output = source.create_output("result", "float")?;

        let inner = NodeGraph::define(&stage, "/Mat/Inner")?;
        inner.create_output("result", "float")?.connect_to(&source_output)?;
        let outer = NodeGraph::define(&stage, "/Mat/Outer")?;
        outer
            .create_output("result", "float")?
            .connect_to(&inner.output("result"))?;
        let sink = Shader::define(&stage, "/Mat/Sink")?;
        sink.create_input("value", "float")?
            .connect_to(&outer.output("result"))?;

        let producing = sink.input("value").value_producing_attributes(ProducerFilter::Any)?;
        assert_eq!(producing.len(), 1);
        assert_eq!(producing[0].path().as_str(), "/Mat/Source.outputs:result");
        assert_eq!(producing[0].attribute_type(), AttributeType::Output);
        Ok(())
    }

    #[test]
    fn interface_value_resolution() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let material = Material::define(&stage, "/Mat")?;
        material.create_input("gain", "float")?.set(2.0_f32)?;
        let graph = NodeGraph::define(&stage, "/Mat/Graph")?;
        graph
            .create_output("result", "float")?
            .connect_to(&material.input("gain"))?;

        let producing = graph.output("result").value_producing_attributes(ProducerFilter::Any)?;
        assert_eq!(producing.len(), 1);
        assert_eq!(producing[0].path().as_str(), "/Mat.inputs:gain");
        assert_eq!(producing[0].attribute_type(), AttributeType::Input);

        // A renderer terminal takes shader outputs only, so an interface value
        // is no answer at all.
        assert!(
            graph
                .output("result")
                .value_producing_attributes(ProducerFilter::ShaderOutputsOnly)?
                .is_empty()
        );
        Ok(())
    }

    #[test]
    fn multiple_source_order() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let first = Shader::define(&stage, "/Mat/First")?;
        let first_output = first.create_output("result", "float")?;
        let second = Shader::define(&stage, "/Mat/Second")?;
        let second_output = second.create_output("result", "float")?;

        let first_graph = NodeGraph::define(&stage, "/Mat/FirstGraph")?;
        first_graph
            .create_output("result", "float")?
            .connect_to(&first_output)?;
        let second_graph = NodeGraph::define(&stage, "/Mat/SecondGraph")?;
        second_graph
            .create_output("result", "float")?
            .connect_to(&second_output)?;
        let root = NodeGraph::define(&stage, "/Mat/Root")?;
        root.create_output("result", "float")?.set_connections([
            second_graph.output("result").path().clone(),
            first_graph.output("result").path().clone(),
        ])?;

        let producing = root.output("result").value_producing_attributes(ProducerFilter::Any)?;
        let paths: Vec<&str> = producing.iter().map(|attribute| attribute.path().as_str()).collect();
        assert_eq!(paths, vec!["/Mat/Second.outputs:result", "/Mat/First.outputs:result"]);
        Ok(())
    }

    #[test]
    fn diamond_resolves_both() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Mat/Source")?;
        let shader_output = shader.create_output("result", "float")?;
        let shared = NodeGraph::define(&stage, "/Mat/Shared")?;
        shared.create_output("result", "float")?.connect_to(&shader_output)?;

        // Two distinct branches converging on one attribute is a diamond, not
        // a cycle: the second reaches an attribute the first has already left,
        // so both resolve.
        let left = NodeGraph::define(&stage, "/Mat/Left")?;
        left.create_output("result", "float")?
            .connect_to(&shared.output("result"))?;
        let right = NodeGraph::define(&stage, "/Mat/Right")?;
        right
            .create_output("result", "float")?
            .connect_to(&shared.output("result"))?;
        let root = NodeGraph::define(&stage, "/Mat/Root")?;
        root.create_output("result", "float")?.set_connections([
            left.output("result").path().clone(),
            right.output("result").path().clone(),
        ])?;

        let producing = root.output("result").value_producing_attributes(ProducerFilter::Any)?;
        let paths: Vec<&str> = producing.iter().map(|attribute| attribute.path().as_str()).collect();
        assert_eq!(paths, vec!["/Mat/Source.outputs:result", "/Mat/Source.outputs:result"]);
        Ok(())
    }

    #[test]
    fn repeated_source_followed_once() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Mat/Source")?;
        let shader_output = shader.create_output("result", "float")?;
        let root = NodeGraph::define(&stage, "/Mat/Root")?;

        // One source drives one value however often a connection list names
        // it, so repeats never multiply the walk.
        root.create_output("result", "float")?
            .set_connections([shader_output.path().clone(), shader_output.path().clone()])?;

        let producing = root.output("result").value_producing_attributes(ProducerFilter::Any)?;
        assert_eq!(producing.len(), 1);
        assert_eq!(producing[0].path().as_str(), "/Mat/Source.outputs:result");
        Ok(())
    }

    #[test]
    fn deep_chain_errors() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let depth = MAX_CONNECTION_DEPTH + 2;
        for hop in 0..depth {
            NodeGraph::define(&stage, format!("/Mat/N{hop}"))?.create_output("result", "float")?;
        }
        for hop in 0..depth - 1 {
            let next = stage.attribute(format!("/Mat/N{}.outputs:result", hop + 1));
            stage
                .attribute(format!("/Mat/N{hop}.outputs:result"))?
                .set_connections([next?.path().clone()])?;
        }

        // A chain past the depth budget is refused rather than walked until
        // the stack runs out.
        let head = NodeGraph::get(&stage, "/Mat/N0")?.expect("NodeGraph");
        let Err(error) = head.output("result").value_producing_attributes(ProducerFilter::Any) else {
            panic!("a chain past the depth budget should be refused");
        };
        assert!(error.to_string().contains("deeper than"), "{error}");
        Ok(())
    }

    #[test]
    fn cycle_stops() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let first = NodeGraph::define(&stage, "/Mat/First")?;
        let second = NodeGraph::define(&stage, "/Mat/Second")?;
        first.create_output("result", "float")?;
        second.create_output("result", "float")?;
        first.output("result").connect_to(&second.output("result"))?;
        second.output("result").connect_to(&first.output("result"))?;

        assert!(
            first
                .output("result")
                .value_producing_attributes(ProducerFilter::Any)?
                .is_empty()
        );
        Ok(())
    }
}
