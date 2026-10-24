//! What makes a prim connectable, and the registry that says which schema
//! types and API schemas do (C++ `UsdShadeConnectableAPIBehavior`).

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use openusd::Result;
use openusd::usd::{SchemaBase, SchemaKind};
use openusd::{tf, usd};

use super::ConnectableAPI;
use super::tokens;

/// How the prims of one schema take part in a shading network (C++
/// `UsdShadeConnectableAPIBehavior`). A prim has the behavior a
/// [`BehaviorRegistry`] finds for its type and API schemas, or none, and only
/// a prim with one is connectable.
pub trait Behavior: Send + Sync + fmt::Debug {
    /// Whether the prim holds other connectable prims and passes values to
    /// and from them through its own inputs and outputs, as a NodeGraph does.
    fn is_container(&self) -> bool;

    /// Whether the prim's connections stay within the container that holds
    /// it.
    fn requires_encapsulation(&self) -> bool;
}

/// The behavior of each schema that has one, by the identifier of the schema
/// (the registry behind C++ `UsdShadeRegisterConnectableAPIBehavior`).
///
/// [`connectable_registry`](crate::connectable_registry) holds the behaviors
/// of this crate's schemas. A clone of it takes the behaviors of schemas
/// declared elsewhere, and a [`ConnectableContext`] over it answers the
/// connection queries with them.
///
/// TODO: C++ also gives a behavior to a schema that registers no code but
/// declares `providesUsdShadeConnectableAPIBehavior`, `isUsdShadeContainer`
/// and `requiresUsdShadeEncapsulation` in its plug metadata
/// (`connectableAPIBehavior.cpp:480-502`). That needs the class's
/// `extraPlugInfo` read into `usd::SchemaInfo`; until then such a schema has
/// a behavior only where a crate registers one for it.
#[derive(Debug, Clone, Default)]
pub struct BehaviorRegistry {
    /// Shared between the clones of a registry until one of them registers
    /// a behavior, so that a clone costs no copy of the table.
    behaviors: Arc<HashMap<tf::Token, Arc<dyn Behavior>>>,
}

impl BehaviorRegistry {
    /// A registry with no behaviors.
    pub fn new() -> Self {
        Self::default()
    }

    /// Give the prims of the type or single-apply API schema `schema` the
    /// behavior `behavior`, which replaces one already registered for it.
    pub fn register(&mut self, schema: impl Into<tf::Token>, behavior: impl Behavior + 'static) -> &mut Self {
        Arc::make_mut(&mut self.behaviors).insert(schema.into(), Arc::new(behavior));
        self
    }

    /// The behavior of `prim`, or `None` where it is not connectable.
    ///
    /// This is the order of C++ `_GetBehaviorForPrimTypeId`
    /// (`connectableAPIBehavior.cpp:547-704`), which differs from the
    /// precedence its comment lists (`:536-545`):
    /// 1. The prim's type, then each of its ancestors in the order of
    ///    [`usd::SchemaRegistry::ancestors`]: the first with a behavior
    ///    answers.
    /// 2. Where one did, the first API schema the prim's own `apiSchemas`
    ///    authors that has a behavior overrides it.
    /// 3. Where none did, the first API schema of the prim's definition, the
    ///    built-in and auto-applied ones included, that has a behavior
    ///    answers.
    ///
    /// The walk starts from the prim's concrete schema type. A prim whose
    /// `typeName` is abstract or unknown has only its API schemas.
    ///
    /// Only a single-apply API schema has a behavior.
    pub fn behavior(&self, prim: &usd::Prim) -> Result<Option<Arc<dyn Behavior>>> {
        // TODO(perf): C++ caches the answer by prim type identity. The lookup
        // depends on the identity and this registry alone, and one answer per
        // identity would serve every prim sharing it. The interface-consumer
        // walk asks it of the same container once per consumer input.
        // C++ starts from `GetPrimTypeInfo().GetSchemaType()`, which is
        // concrete-only.
        let info = prim.prim_type_info()?;
        Ok(self.resolve(
            prim.stage().schema_registry(),
            info.schema_type_name(),
            info.id().applied_api_schemas(),
            info.prim_definition().applied_api_schemas(),
        ))
    }

    /// The behavior a prim of the type `schema` has, with no API schema
    /// applied beyond the type's built-in ones, or `None` where it is not
    /// connectable. `schema` is a type or an API schema, as `schemas` knows
    /// it; an abstract type has no built-in ones to consult
    /// (`connectableAPIBehavior.cpp:660-662`).
    pub fn type_behavior(&self, schemas: &usd::SchemaRegistry, schema: &tf::Token) -> Option<Arc<dyn Behavior>> {
        let definition = match schemas.is_concrete_type(schema) {
            true => schemas.concrete_prim_definition(schema),
            false => schemas.api_prim_definition(schema),
        };
        let is_abstract = schemas
            .schema_info(schema)
            .is_some_and(|info| info.kind().is_abstract());
        let built_in = definition
            .filter(|_| !is_abstract)
            .map_or(&[][..], |definition| definition.applied_api_schemas());
        self.resolve(schemas, schema, &[], built_in)
    }

    /// The behavior of a prim of the type `schema` whose own `apiSchemas`
    /// author `authored` and whose definition applies `applied`.
    fn resolve(
        &self,
        schemas: &usd::SchemaRegistry,
        schema: &tf::Token,
        authored: &[tf::Token],
        applied: &[tf::Token],
    ) -> Option<Arc<dyn Behavior>> {
        if let Some(typed) = schemas
            .ancestors(schema)
            .into_iter()
            .find_map(|ty| self.behaviors.get(ty))
        {
            let api = authored.iter().find_map(|api| self.api_behavior(schemas, api));
            return Some(api.unwrap_or_else(|| typed.clone()));
        }
        applied.iter().find_map(|api| self.api_behavior(schemas, api))
    }

    /// The behavior of the applied API schema named `api`, which only a
    /// single-apply schema has (C++ `_FindBehaviorForApiSchema`). A name
    /// carrying an instance names a multiple-apply schema, and is no key of
    /// the table.
    fn api_behavior(&self, schemas: &usd::SchemaRegistry, api: &tf::Token) -> Option<Arc<dyn Behavior>> {
        let behavior = self.behaviors.get(api)?;
        let single = schemas.schema_info(api)?.kind() == SchemaKind::SingleApplyApi;
        single.then(|| behavior.clone())
    }
}

/// The behaviors a connection query asks of the prims it meets, which
/// decide what is a container and what is connectable.
///
/// Every query that asks whether a prim is a container or connectable is a
/// method of a context, run under its [`BehaviorRegistry`], so that every
/// prim it reaches is asked of one registry:
/// [`value_producing_attributes`](Self::value_producing_attributes),
/// [`interface_input_consumers`](Self::interface_input_consumers),
/// [`terminal_source`](Self::terminal_source) and
/// [`read_preview_surface`](Self::read_preview_surface). The same query on a
/// shading view runs under [`ConnectableContext::default`].
#[derive(Debug, Clone)]
pub struct ConnectableContext {
    behaviors: BehaviorRegistry,
}

impl ConnectableContext {
    /// A context whose prims have the behaviors of `behaviors`.
    pub fn new(behaviors: BehaviorRegistry) -> Self {
        Self { behaviors }
    }

    /// The registry the prims' behaviors come from.
    pub fn behaviors(&self) -> &BehaviorRegistry {
        &self.behaviors
    }

    /// Whether `prim` is a container (C++
    /// `UsdShadeConnectableAPI::IsContainer`), `false` where it has no
    /// behavior.
    pub fn is_container(&self, prim: &usd::Prim) -> Result<bool> {
        Ok(self
            .behaviors
            .behavior(prim)?
            .is_some_and(|behavior| behavior.is_container()))
    }

    /// Whether `prim`'s connections stay within its container (C++
    /// `UsdShadeConnectableAPI::RequiresEncapsulation`), `false` where it
    /// has no behavior.
    pub fn requires_encapsulation(&self, prim: &usd::Prim) -> Result<bool> {
        Ok(self
            .behaviors
            .behavior(prim)?
            .is_some_and(|behavior| behavior.requires_encapsulation()))
    }
}

impl Default for ConnectableContext {
    /// A context over [`connectable_registry`](crate::connectable_registry).
    fn default() -> Self {
        Self::new(crate::connectable_registry().clone())
    }
}

impl ConnectableAPI {
    /// View `prim` as connectable where the stage holds it and it has a
    /// behavior (C++ `UsdShadeConnectableAPI::_IsCompatible`), and `None`
    /// otherwise.
    pub fn from_prim(prim: usd::Prim) -> Result<Option<Self>> {
        if !prim.is_valid()? {
            return Ok(None);
        }
        let connectable = ConnectableContext::default().behaviors().behavior(&prim)?.is_some();
        Ok(connectable.then(|| Self::from_prim_unchecked(prim)))
    }

    /// Whether the prim is a container (C++
    /// `UsdShadeConnectableAPI::IsContainer`).
    pub fn is_container(&self) -> Result<bool> {
        ConnectableContext::default().is_container(self.prim())
    }

    /// Whether the prim's connections stay within its container (C++
    /// `UsdShadeConnectableAPI::RequiresEncapsulation`).
    pub fn requires_encapsulation(&self) -> Result<bool> {
        ConnectableContext::default().requires_encapsulation(self.prim())
    }

    /// Whether a prim of the type `schema` is connectable with no API schema
    /// applied beyond the type's built-in ones (C++
    /// `UsdShadeConnectableAPI::HasConnectableAPI`).
    pub fn has_connectable_api(schemas: &usd::SchemaRegistry, schema: &tf::Token) -> bool {
        ConnectableContext::default()
            .behaviors()
            .type_behavior(schemas, schema)
            .is_some()
    }
}

/// The behavior of a built-in schema of this family: what is fixed for every
/// prim of the schema.
#[derive(Debug)]
struct BuiltIn {
    container: bool,
    encapsulation: bool,
}

impl Behavior for BuiltIn {
    fn is_container(&self) -> bool {
        self.container
    }

    fn requires_encapsulation(&self) -> bool {
        self.encapsulation
    }
}

/// Add the behavior of each `UsdShade` schema that has one: NodeGraph
/// (`nodeGraph.cpp:360-385`), Material (`material.cpp:725-756`) and Shader
/// (`shader.cpp:120-138`).
pub(crate) fn register_behaviors(registry: &mut BehaviorRegistry) {
    let container = || BuiltIn {
        container: true,
        encapsulation: true,
    };
    let shader = BuiltIn {
        container: false,
        encapsulation: true,
    };
    registry
        .register(tokens::NODE_GRAPH, container())
        .register(tokens::MATERIAL, container())
        .register(tokens::SHADER, shader);
}

#[cfg(test)]
mod tests {
    use super::*;

    use openusd::sdf;
    use openusd::usd::SchemaDecl;

    use crate::SchemaError;
    use crate::geom::boundable::tests::stage_with;
    use crate::shade::{Connectable, Input, NodeGraph, Output, ProducerFilter, Shader};

    /// A family of a typed schema with a typed child, an abstract type, a
    /// type with a built-in API schema, a type an API schema auto-applies
    /// to, and three single-apply API schemas.
    const FAMILY: &[SchemaDecl<'static>] = &[
        SchemaDecl::new("TestTyped", SchemaKind::ConcreteTyped).bases(&["Typed"]),
        SchemaDecl::new("TestChild", SchemaKind::ConcreteTyped).bases(&["TestTyped"]),
        SchemaDecl::new("TestAbstract", SchemaKind::AbstractTyped).bases(&["Typed"]),
        SchemaDecl::new("TestBuiltIn", SchemaKind::ConcreteTyped)
            .bases(&["Typed"])
            .applied_api_schemas(&["TestApiA"]),
        SchemaDecl::new("TestPlain", SchemaKind::ConcreteTyped).bases(&["Typed"]),
        SchemaDecl::new("TestApiA", SchemaKind::SingleApplyApi).bases(&["APISchemaBase"]),
        SchemaDecl::new("TestApiB", SchemaKind::SingleApplyApi).bases(&["APISchemaBase"]),
        SchemaDecl::new("TestAuto", SchemaKind::SingleApplyApi)
            .bases(&["APISchemaBase"])
            .auto_apply_to(&["TestPlain"]),
    ];

    /// A behavior known by its name.
    #[derive(Debug)]
    // The name is read through `Debug`, which the tests compare.
    #[allow(dead_code)]
    struct Named(&'static str);

    impl Behavior for Named {
        fn is_container(&self) -> bool {
            false
        }

        fn requires_encapsulation(&self) -> bool {
            false
        }
    }

    /// This crate's behaviors, with each of `named` registered under its
    /// schema.
    fn registry(named: &[(&str, &'static str)]) -> BehaviorRegistry {
        let mut registry = crate::connectable_registry().clone();
        for &(schema, name) in named {
            registry.register(schema, Named(name));
        }
        registry
    }

    /// The `Debug` form of `behavior`, which names a [`Named`] one.
    fn debug(behavior: Option<Arc<dyn Behavior>>) -> Option<String> {
        behavior.map(|behavior| format!("{behavior:?}"))
    }

    /// The `Debug` form of the behavior named `name`.
    fn name(name: &'static str) -> Option<String> {
        Some(format!("{:?}", Named(name)))
    }

    /// The behavior `registry` finds for the prim at `path`.
    fn named(registry: &BehaviorRegistry, stage: &usd::Stage, path: &str) -> Result<Option<String>> {
        Ok(debug(registry.behavior(&stage.prim(path)?)?))
    }

    /// A typed behavior wins over a built-in API schema's.
    #[test]
    fn typed_beats_builtin() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        stage.define_prim("/P")?.set_type_name("TestBuiltIn")?;
        let registry = registry(&[("TestBuiltIn", "typed"), ("TestApiA", "api")]);
        assert_eq!(named(&registry, &stage, "/P")?, name("typed"));
        Ok(())
    }

    /// An authored API schema's behavior overrides the typed one.
    #[test]
    fn authored_api_overrides() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        stage
            .define_prim("/P")?
            .set_type_name("TestTyped")?
            .apply_api("TestApiA")?;
        let registry = registry(&[("TestTyped", "typed"), ("TestApiA", "api")]);
        assert_eq!(named(&registry, &stage, "/P")?, name("api"));
        Ok(())
    }

    /// Of two authored API schemas with behaviors, the first wins.
    #[test]
    fn authored_api_order() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        let prim = stage
            .define_prim("/P")?
            .set_type_name("TestTyped")?
            .apply_api("TestApiB")?
            .apply_api("TestApiA")?;
        let authored = prim.prim_type_info()?.id().applied_api_schemas().to_vec();
        assert_eq!(authored, ["TestApiB", "TestApiA"]);
        let registry = registry(&[("TestTyped", "typed"), ("TestApiA", "a"), ("TestApiB", "b")]);
        assert_eq!(named(&registry, &stage, "/P")?, name("b"));
        Ok(())
    }

    /// A type with no behavior of its own takes its parent type's.
    #[test]
    fn ancestor_type_behavior() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        stage.define_prim("/P")?.set_type_name("TestChild")?;
        let registry = registry(&[("TestTyped", "typed")]);
        assert_eq!(named(&registry, &stage, "/P")?, name("typed"));
        Ok(())
    }

    /// With no typed behavior, a built-in or an auto-applied API schema's
    /// answers.
    #[test]
    fn builtin_api_fallback() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        stage.define_prim("/BuiltIn")?.set_type_name("TestBuiltIn")?;
        stage.define_prim("/Auto")?.set_type_name("TestPlain")?;
        let registry = registry(&[("TestApiA", "built-in"), ("TestAuto", "auto")]);
        assert_eq!(named(&registry, &stage, "/BuiltIn")?, name("built-in"));
        assert_eq!(named(&registry, &stage, "/Auto")?, name("auto"));

        let built_in = registry.type_behavior(stage.schema_registry(), &tf::Token::from("TestBuiltIn"));
        assert_eq!(debug(built_in), name("built-in"));
        Ok(())
    }

    /// An abstract type consults no built-in API schemas and has no behavior
    /// of its own, while a prim authored with that type has no schema type
    /// to walk and falls through to the API schemas it authors.
    #[test]
    fn abstract_type_skipped() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        stage
            .define_prim("/P")?
            .set_type_name("TestAbstract")?
            .apply_api("TestApiA")?;
        let registry = registry(&[("TestAbstract", "abstract"), ("TestApiA", "api")]);
        assert_eq!(named(&registry, &stage, "/P")?, name("api"));
        let registry = BehaviorRegistry::new();
        let abstract_type = registry.type_behavior(stage.schema_registry(), &tf::Token::from("TestAbstract"));
        assert!(abstract_type.is_none());
        Ok(())
    }

    /// A context where `TestTyped` is a container that keeps no
    /// encapsulation.
    fn custom_context() -> ConnectableContext {
        let mut behaviors = crate::connectable_registry().clone();
        behaviors.register(
            "TestTyped",
            BuiltIn {
                container: true,
                encapsulation: false,
            },
        );
        ConnectableContext::new(behaviors)
    }

    /// The paths of the consumers `context` maps `input` of `graph` to.
    fn consumer_paths(
        context: &ConnectableContext,
        graph: &NodeGraph,
        input: &Input,
        transitive: bool,
    ) -> Result<Vec<sdf::Path>> {
        let map = context.interface_input_consumers(graph, transitive)?;
        let consumers = map.consumers(input).expect("an interface input entry");
        Ok(consumers.iter().map(|consumer| consumer.path().clone()).collect())
    }

    /// A custom container answers as one through every query asked under the
    /// context that knows it, and as no container under the default one.
    #[test]
    fn custom_container_context() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        let custom = custom_context();
        let default = ConnectableContext::default();

        // A shader output routed out through the custom container's output.
        stage.define_prim("/Box")?.set_type_name("TestTyped")?;
        let inner = Shader::define(&stage, "/Box/Inner")?.create_output("out", "float")?;
        let routed = Output::new(stage.prim("/Box")?.create_attribute("outputs:out", "float")?).connect_to(&inner)?;
        let consumer = Shader::define(&stage, "/Consumer")?
            .create_input("in", "float")?
            .connect_to(&routed)?;

        let source = consumer.connected_sources()?.sources()[0].prim().clone();
        assert!(custom.is_container(&source)?);
        assert!(!default.is_container(&source)?);

        let producer = |context: &ConnectableContext| -> Result<Vec<sdf::Path>, SchemaError> {
            let producing = context.value_producing_attributes(consumer.clone(), ProducerFilter::Any)?;
            Ok(producing.iter().map(|attribute| attribute.path().clone()).collect())
        };
        assert_eq!(producer(&custom)?, [inner.path().clone()]);
        assert_eq!(producer(&default)?, [routed.path().clone()]);

        // The custom prim consumes a NodeGraph's interface input.
        let graph = NodeGraph::define(&stage, "/Graph")?;
        let gain = graph.create_input("gain", "float")?;
        stage.define_prim("/Graph/Box")?.set_type_name("TestTyped")?;
        let box_gain =
            Input::new(stage.prim("/Graph/Box")?.create_attribute("inputs:gain", "float")?).connect_to(&gain)?;
        assert_eq!(
            consumer_paths(&custom, &graph, &gain, false)?,
            [box_gain.path().clone()]
        );
        assert!(consumer_paths(&default, &graph, &gain, false)?.is_empty());
        Ok(())
    }

    /// The context a transitive query starts under answers at every nested
    /// level: an input on a custom prim inside a nested NodeGraph resolves as
    /// a consumer only where the context gives that prim a behavior.
    #[test]
    fn custom_nested_consumers() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        let outer = NodeGraph::define(&stage, "/Outer")?;
        let x = outer.create_input("x", "float")?;
        let nested = NodeGraph::define(&stage, "/Outer/Nested")?;
        let nested_x = nested.create_input("x", "float")?.connect_to(&x)?;
        stage.define_prim("/Outer/Nested/Box")?.set_type_name("TestTyped")?;
        let box_x = Input::new(stage.prim("/Outer/Nested/Box")?.create_attribute("inputs:x", "float")?)
            .connect_to(&nested_x)?;

        assert_eq!(
            consumer_paths(&custom_context(), &outer, &x, true)?,
            [box_x.path().clone()]
        );
        // With no consumer of its own, the nested input is kept as resolved.
        let default = ConnectableContext::default();
        assert_eq!(consumer_paths(&default, &outer, &x, true)?, [nested_x.path().clone()]);
        Ok(())
    }

    /// A prim the stage does not hold is not connectable.
    #[test]
    fn missing_not_connectable() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        assert!(ConnectableAPI::from_prim(stage.prim("/Missing")?)?.is_none());
        Ok(())
    }
}
