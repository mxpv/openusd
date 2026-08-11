//! Reverse queries for NodeGraph interface-input connections.

use std::collections::{HashMap, HashSet};
use std::ptr;

use anyhow::Result;

use crate::{sdf, usd};

use super::connectable::is_container;

use super::{Connectable, Input, Material, NodeGraph, Shader};

/// A NodeGraph's interface inputs and the inputs that consume their values.
///
/// Entries follow the container's composed input order. Every authored
/// interface input has an entry, including inputs with no consumers.
#[derive(Clone, Default)]
pub struct InterfaceInputConsumersMap {
    entries: Vec<InterfaceInputConsumers>,
}

impl InterfaceInputConsumersMap {
    /// The number of interface inputs represented by the map.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the container has no authored interface inputs.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The consumers for `interface_input`, or `None` when the map has no entry
    /// with the same stage identity and path.
    pub fn consumers(&self, interface_input: &Input) -> Option<&[Input]> {
        self.entry(interface_input).map(|entry| entry.consumers.as_slice())
    }

    /// Iterate over interface inputs and their consumers in composed order.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (&Input, &[Input])> {
        self.entries
            .iter()
            .map(|entry| (&entry.interface_input, entry.consumers.as_slice()))
    }

    fn entry(&self, interface_input: &Input) -> Option<&InterfaceInputConsumers> {
        self.entries
            .iter()
            .find(|entry| same_input(&entry.interface_input, interface_input))
    }

    fn entry_mut(&mut self, stage: &usd::Stage, path: &sdf::Path) -> Option<&mut InterfaceInputConsumers> {
        self.entries
            .iter_mut()
            .find(|entry| input_matches(&entry.interface_input, stage, path))
    }
}

#[derive(Clone)]
struct InterfaceInputConsumers {
    interface_input: Input,
    consumers: Vec<Input>,
}

impl InterfaceInputConsumers {
    fn push_consumer(&mut self, consumer: Input) {
        if !self.consumers.iter().any(|existing| same_input(existing, &consumer)) {
            self.consumers.push(consumer);
        }
    }
}

/// The interface-input queries shared by [`NodeGraph`] and [`Material`].
///
/// A non-transitive map reports shader inputs and nested NodeGraph or Material
/// inputs that connect directly to this container's interface. A transitive
/// map follows nested container inputs to their leaf shader inputs. A nested
/// interface input with no consumers remains in the transitive result.
pub trait NodeGraphInterface: Connectable {
    /// Compute the reverse map from interface inputs to their consumers.
    ///
    /// This walks the active, loaded, defined, non-abstract descendants rooted
    /// at this container and stops at instances. It is the Rust counterpart of
    /// `UsdShadeNodeGraph::ComputeInterfaceInputConsumersMap`.
    fn compute_interface_input_consumers_map(&self, transitive: bool) -> Result<InterfaceInputConsumersMap> {
        let direct = compute_direct_map(self.prim())?;
        if !transitive {
            return Ok(direct);
        }

        let mut nested_maps = HashMap::new();
        collect_nested_maps(&direct, self.stage(), &mut nested_maps)?;
        if nested_maps.is_empty() {
            return Ok(direct);
        }

        let mut resolved = InterfaceInputConsumersMap::default();
        for (interface_input, consumers) in direct.iter() {
            resolved.entries.push(InterfaceInputConsumers {
                interface_input: interface_input.clone(),
                consumers: resolve_consumers(consumers, &nested_maps),
            });
        }
        Ok(resolved)
    }
}

impl NodeGraphInterface for NodeGraph {}
impl NodeGraphInterface for Material {}

fn compute_direct_map(root: &usd::Prim) -> Result<InterfaceInputConsumersMap> {
    let mut result = InterfaceInputConsumersMap {
        entries: connectable_inputs(root)?
            .unwrap_or_default()
            .into_iter()
            .map(|interface_input| InterfaceInputConsumers {
                interface_input,
                consumers: Vec::new(),
            })
            .collect(),
    };

    let mut stack = if root.is_instance()? {
        Vec::new()
    } else {
        root.children()?
    };
    stack.reverse();
    while let Some(prim) = stack.pop() {
        if !root.stage().prim_matches(prim.path(), usd::PrimPredicate::DEFAULT)? {
            continue;
        }
        if !prim.is_instance()? {
            let mut children = prim.children()?;
            children.reverse();
            stack.extend(children);
        }

        let Some(inputs) = connectable_inputs(&prim)? else {
            continue;
        };
        for input in inputs {
            for source in input.connected_sources()?.sources() {
                if source.source_type() != super::AttributeType::Input || source.source_prim().path() != root.path() {
                    continue;
                }
                if let Some(entry) = result.entry_mut(source.source_prim().stage(), source.source_path()) {
                    entry.push_consumer(input.clone());
                }
            }
        }
    }
    Ok(result)
}

fn connectable_inputs(prim: &usd::Prim) -> Result<Option<Vec<Input>>> {
    let stage = prim.stage();
    let path = prim.path();
    if Shader::get(stage, path.clone())?.is_none() && !is_container(prim)? {
        return Ok(None);
    }
    Ok(Some(
        prim.authored_attributes()?
            .into_iter()
            .filter_map(Input::from_attribute)
            .collect(),
    ))
}

fn collect_nested_maps(
    consumers: &InterfaceInputConsumersMap,
    stage: &usd::Stage,
    maps: &mut HashMap<sdf::Path, InterfaceInputConsumersMap>,
) -> Result<()> {
    let mut pending = nested_container_paths(consumers);
    pending.reverse();
    while let Some(path) = pending.pop() {
        if maps.contains_key(&path) {
            continue;
        }
        let prim = stage.prim(path.clone());
        if !is_container(&prim)? {
            continue;
        }
        let nested = compute_direct_map(&prim)?;
        let mut nested_paths = nested_container_paths(&nested);
        nested_paths.reverse();
        maps.insert(path, nested);
        pending.extend(nested_paths);
    }
    Ok(())
}

fn nested_container_paths(consumers: &InterfaceInputConsumersMap) -> Vec<sdf::Path> {
    consumers
        .iter()
        .flat_map(|(_, consumers)| consumers)
        .map(|consumer| consumer.prim().path().clone())
        .collect()
}

fn resolve_consumers(consumers: &[Input], nested_maps: &HashMap<sdf::Path, InterfaceInputConsumersMap>) -> Vec<Input> {
    let mut pending: Vec<Input> = consumers.iter().rev().cloned().collect();
    let mut visited = HashSet::new();
    let mut resolved = Vec::new();
    while let Some(consumer) = pending.pop() {
        if !visited.insert(consumer.path().clone()) {
            continue;
        }
        let Some(map) = nested_maps.get(consumer.prim().path()) else {
            resolved.push(consumer);
            continue;
        };
        let Some(nested) = map.consumers(&consumer) else {
            continue;
        };
        if nested.is_empty() {
            resolved.push(consumer);
        } else {
            pending.extend(nested.iter().rev().cloned());
        }
    }
    resolved
}

fn same_input(left: &Input, right: &Input) -> bool {
    input_matches(left, right.attribute().stage(), right.path())
}

fn input_matches(input: &Input, stage: &usd::Stage, path: &sdf::Path) -> bool {
    ptr::eq(&**input.attribute().stage(), &**stage) && input.path() == path
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::shade::Shader;
    use crate::usd::SchemaBase;

    fn paths(inputs: &[Input]) -> Vec<&str> {
        inputs.iter().map(|input| input.path().as_str()).collect()
    }

    #[test]
    fn direct_consumers() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let graph = NodeGraph::define(&stage, "/Graph")?;
        let gain = graph.create_input("gain", "float")?;
        let unused = graph.create_input("unused", "float")?;
        let shader = Shader::define(&stage, "/Graph/Shader")?;
        shader.create_input("gain", "float")?.connect_to(&gain)?;
        let nested = NodeGraph::define(&stage, "/Graph/Nested")?;
        nested.create_input("gain", "float")?.connect_to(&gain)?;

        let map = graph.compute_interface_input_consumers_map(false)?;
        assert_eq!(map.len(), 2);
        assert_eq!(
            paths(map.consumers(&gain).expect("gain entry")),
            ["/Graph/Shader.inputs:gain", "/Graph/Nested.inputs:gain"]
        );
        assert!(map.consumers(&unused).expect("unused entry").is_empty());
        Ok(())
    }

    #[test]
    fn consumer_deduplication() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let graph = NodeGraph::define(&stage, "/Graph")?;
        let gain = graph.create_input("gain", "float")?;
        let nested = NodeGraph::define(&stage, "/Graph/Nested")?;
        let first = nested
            .create_input("first", "float")?
            .set_connections([gain.path().clone(), gain.path().clone()])?;
        let second = nested.create_input("second", "float")?.connect_to(&gain)?;
        let shader = Shader::define(&stage, "/Graph/Nested/Shader")?;
        let shader_gain = shader
            .create_input("gain", "float")?
            .set_connections([first.path().clone(), second.path().clone()])?;

        let direct = graph.compute_interface_input_consumers_map(false)?;
        assert_eq!(
            paths(direct.consumers(&gain).expect("gain entry")),
            [first.path().as_str(), second.path().as_str()]
        );

        let transitive = graph.compute_interface_input_consumers_map(true)?;
        assert_eq!(
            paths(transitive.consumers(&gain).expect("gain entry")),
            [shader_gain.path().as_str()]
        );
        Ok(())
    }

    #[test]
    fn stage_bound_lookup() -> Result<()> {
        let first_stage = usd::Stage::builder().in_memory("same.usda")?;
        let first_graph = NodeGraph::define(&first_stage, "/Graph")?;
        let first_gain = first_graph.create_input("gain", "float")?;
        let shader = Shader::define(&first_stage, "/Graph/Shader")?;
        shader.create_input("gain", "float")?.connect_to(&first_gain)?;
        let map = first_graph.compute_interface_input_consumers_map(false)?;

        let second_stage = usd::Stage::builder().in_memory("same.usda")?;
        let second_graph = NodeGraph::define(&second_stage, "/Graph")?;
        let second_gain = second_graph.create_input("gain", "float")?;

        assert_eq!(map.consumers(&first_gain).expect("first-stage entry").len(), 1);
        assert!(map.consumers(&second_gain).is_none());
        Ok(())
    }

    #[test]
    fn transitive_consumers() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let graph = NodeGraph::define(&stage, "/Graph")?;
        let gain = graph.create_input("gain", "float")?;
        let spare = graph.create_input("spare", "float")?;
        let nested = NodeGraph::define(&stage, "/Graph/Nested")?;
        let nested_gain = nested.create_input("gain", "float")?.connect_to(&gain)?;
        let nested_spare = nested.create_input("spare", "float")?.connect_to(&spare)?;
        let shader = Shader::define(&stage, "/Graph/Nested/Shader")?;
        shader.create_input("gain", "float")?.connect_to(&nested_gain)?;

        let map = graph.compute_interface_input_consumers_map(true)?;
        assert_eq!(
            paths(map.consumers(&gain).expect("gain entry")),
            ["/Graph/Nested/Shader.inputs:gain"]
        );
        assert_eq!(
            paths(map.consumers(&spare).expect("spare entry")),
            [nested_spare.path().as_str()]
        );
        Ok(())
    }

    #[test]
    fn material_transitive() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let graph = NodeGraph::define(&stage, "/Graph")?;
        let gain = graph.create_input("gain", "float")?;
        let material = Material::define(&stage, "/Graph/Mat")?;
        let material_gain = material.create_input("gain", "float")?.connect_to(&gain)?;
        let shader = Shader::define(&stage, "/Graph/Mat/Shader")?;
        let shader_gain = shader.create_input("gain", "float")?.connect_to(&material_gain)?;

        let direct = graph.compute_interface_input_consumers_map(false)?;
        assert_eq!(
            paths(direct.consumers(&gain).expect("gain entry")),
            [material_gain.path().as_str()]
        );

        let transitive = graph.compute_interface_input_consumers_map(true)?;
        assert_eq!(
            paths(transitive.consumers(&gain).expect("gain entry")),
            [shader_gain.path().as_str()]
        );
        Ok(())
    }

    #[test]
    fn material_consumers() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let material = Material::define(&stage, "/Mat")?;
        let roughness = material.create_input("roughness", "float")?;
        let shader = Shader::define(&stage, "/Mat/Surface")?;
        shader.create_input("roughness", "float")?.connect_to(&roughness)?;

        let map = material.compute_interface_input_consumers_map(false)?;
        assert_eq!(
            paths(map.consumers(&roughness).expect("roughness entry")),
            ["/Mat/Surface.inputs:roughness"]
        );
        Ok(())
    }

    #[test]
    fn filtered_consumers() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let graph = NodeGraph::define(&stage, "/Graph")?;
        let gain = graph.create_input("gain", "float")?;
        let active = Shader::define(&stage, "/Graph/Active")?;
        active.create_input("gain", "float")?.connect_to(&gain)?;

        let inactive = NodeGraph::define(&stage, "/Graph/Inactive")?;
        let inactive_shader = Shader::define(&stage, "/Graph/Inactive/Shader")?;
        inactive_shader.create_input("gain", "float")?.connect_to(&gain)?;
        inactive.prim().clone().set_active(false)?;

        stage.override_prim("/Graph/Undefined")?;
        let undefined_shader = Shader::define(&stage, "/Graph/Undefined/Shader")?;
        undefined_shader.create_input("gain", "float")?.connect_to(&gain)?;

        stage.define_prim("/Graph/Abstract")?;
        let abstract_shader = Shader::define(&stage, "/Graph/Abstract/Shader")?;
        abstract_shader.create_input("gain", "float")?.connect_to(&gain)?;
        let root_id = stage.root_layer().identifier().to_owned();
        stage.layer_mut(&root_id).expect("root layer").edit(|edit| {
            edit.prim_mut("/Graph/Abstract")
                .expect("abstract prim")
                .set_specifier(sdf::Specifier::Class);
            Ok(())
        })?;

        let map = graph.compute_interface_input_consumers_map(false)?;
        assert_eq!(
            paths(map.consumers(&gain).expect("gain entry")),
            ["/Graph/Active.inputs:gain"]
        );
        Ok(())
    }

    #[test]
    fn instance_consumers() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let source = NodeGraph::define(&stage, "/Source")?;
        let gain = source.create_input("gain", "float")?;
        let shader = Shader::define(&stage, "/Source/Shader")?;
        shader.create_input("gain", "float")?.connect_to(&gain)?;

        stage
            .define_prim("/Instance")?
            .set_metadata(
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    prim_path: sdf::path("/Source")?,
                    ..Default::default()
                }])),
            )?
            .set_instanceable(true)?;
        let instance = NodeGraph::get(&stage, "/Instance")?.expect("node graph instance");
        let instance_gain = instance.input("gain");

        let map = instance.compute_interface_input_consumers_map(false)?;
        assert!(map.consumers(&instance_gain).expect("gain entry").is_empty());
        Ok(())
    }

    #[test]
    fn deep_consumer_chain() -> Result<()> {
        const DEPTH: usize = 10_000;

        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let mut chain = Vec::with_capacity(DEPTH);
        for index in 0..DEPTH {
            let name = sdf::path(format!("N{index}"))?;
            let prim_path = sdf::Path::abs_root().append_path(name)?;
            let input_path = prim_path.append_property("inputs:value")?;
            chain.push(Input::new(stage.attribute(input_path)));
        }

        let mut maps = HashMap::with_capacity(DEPTH - 1);
        for pair in chain.windows(2) {
            maps.insert(
                pair[0].prim().path().clone(),
                InterfaceInputConsumersMap {
                    entries: vec![InterfaceInputConsumers {
                        interface_input: pair[0].clone(),
                        consumers: vec![pair[1].clone()],
                    }],
                },
            );
        }

        let resolved = resolve_consumers(&chain[..1], &maps);
        assert_eq!(paths(&resolved), [chain.last().expect("last input").path().as_str()]);
        Ok(())
    }
}
