//! What makes a prim connectable, and the registry that says which schema
//! types and API schemas do (C++ `UsdShadeConnectableAPIBehavior`).

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use openusd::Result;
use openusd::usd::{SchemaBase, SchemaKind};
use openusd::{tf, usd, vt};

use super::tokens;
use super::{ConnectableAPI, Input, Output};

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

    /// Whether `input`, an input on a prim of this behavior, may connect to
    /// `source`, or the rule that refuses it (C++
    /// `CanConnectInputToSource`). By default, the rules of a
    /// [`NodeKind::Basic`] node.
    fn can_connect_input(
        &self,
        context: &ConnectableContext,
        input: &Input,
        source: &usd::Attribute,
    ) -> Result<Result<(), Refusal>> {
        rules::input(context, input, source, NodeKind::Basic, self.requires_encapsulation())
    }

    /// Whether `output`, an output on a prim of this behavior, may connect to
    /// `source`, or the rule that refuses it (C++
    /// `CanConnectOutputToSource`). By default, the rules of a
    /// [`NodeKind::Basic`] node.
    fn can_connect_output(
        &self,
        _context: &ConnectableContext,
        output: &Output,
        source: &usd::Attribute,
    ) -> Result<Result<(), Refusal>> {
        rules::output(output, source, NodeKind::Basic, self.requires_encapsulation())
    }
}

/// Which connection rules a node follows (C++ `ConnectableNodeTypes`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeKind {
    /// A node connected within the container that holds it (C++
    /// `BasicNodes`): a NodeGraph, a Shader.
    Basic,
    /// A container whose inputs are fed from the nodes it holds, and whose
    /// outputs pass nothing through (C++ `DerivedContainerNodes`): a
    /// Material, and a light or light filter of `lux`.
    Container,
}

/// The rule that refuses a connection: the reasons C++ gives in
/// `connectableAPIBehavior.cpp:52-293`, and the refusal of every output
/// connection a Shader and a light filter make (`shader.cpp:123-128`,
/// `lightFilter.cpp:176-182`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refusal {
    /// The input being connected is not defined.
    InvalidInput,
    /// The output being connected is not defined.
    InvalidOutput,
    /// The source's prim is not on the stage.
    InvalidSource,
    /// The source is on another stage than the attribute it would feed. A
    /// connection names a path on its own stage and cannot reach a source
    /// elsewhere. C++ compares the paths alone.
    ForeignSource,
    /// An input source's prim is not a container.
    SourceNotContainer,
    /// An input source's prim is not the parent of the input's prim.
    SourceNotParent,
    /// An output source feeds an input of a container node whose prim is not
    /// a container.
    InputNotContainer,
    /// An output source's prim is not a child of the container node whose
    /// input it feeds.
    SourceNotChild,
    /// An output source feeds an input of a basic node whose parent is not a
    /// container.
    ParentNotContainer,
    /// An output source's prim and a basic node's prim have different
    /// parents.
    NotSiblings,
    /// An `interfaceOnly` input's source is an input that is not
    /// `interfaceOnly`.
    SourceNotInterfaceOnly,
    /// An `interfaceOnly` input's source is not an input.
    SourceNotInput,
    /// The input's `connectability` is neither `full` nor `interfaceOnly`.
    UnspecifiedConnectability,
    /// A container node's output is fed from an input, which would pass a
    /// value through.
    Passthrough,
    /// An output is fed from an input on another prim.
    PassthroughElsewhere,
    /// An output source's prim is not a child of the output's prim.
    OutputSourceNotChild,
    /// The prim's outputs connect to nothing, as a Shader's and a light
    /// filter's do.
    OutputsNotConnectable,
}

/// The behavior of each schema that has one, by the identifier of the schema
/// (the registry behind C++ `UsdShadeRegisterConnectableAPIBehavior`).
///
/// [`connectable_registry`](crate::connectable_registry) holds the behaviors
/// of this crate's schemas. A clone of it takes the behaviors of schemas
/// declared elsewhere, and a [`ConnectableContext`] over it answers the
/// connection queries with them.
///
/// A schema that registers no behavior still has one when its
/// [`plug_info`](usd::SchemaInfo::plug_info) sets
/// `providesUsdShadeConnectableAPIBehavior` to `true`. That behavior follows
/// the [`NodeKind::Basic`] rules, and its flags come from
/// `isUsdShadeContainer` (`false` when absent or not a bool) and
/// `requiresUsdShadeEncapsulation` (`true` when absent or not a bool), as
/// C++ `RegisterPlugConfiguredBehaviorForType` builds it
/// (`connectableAPIBehavior.cpp:480-502`). A registered behavior wins over
/// it.
///
/// A prim's type and its ancestors take a registered behavior whatever their
/// plug info says. An applied API schema takes one only where its plug info
/// sets `providesUsdShadeConnectableAPIBehavior` to `true`, as C++
/// `_FindBehaviorForApiSchema` asks (`connectableAPIBehavior.cpp:777-802`).
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
    ///
    /// A prim takes the behavior of an applied API schema only where the
    /// schema's [`plug_info`](usd::SchemaInfo::plug_info) sets
    /// `providesUsdShadeConnectableAPIBehavior` to `true`. Registering one
    /// for an API schema without that entry gives its prims nothing.
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
    ///    [`usd::SchemaRegistry::ancestors`]: the first with a behavior,
    ///    registered or configured by its plug info, answers.
    /// 2. Where one did, the first API schema the prim's own `apiSchemas`
    ///    authors that has a behavior overrides it.
    /// 3. Where none did, the first API schema of the prim's definition, the
    ///    built-in and auto-applied ones included, that has a behavior
    ///    answers.
    ///
    /// The walk starts from the prim's concrete schema type. A prim whose
    /// `typeName` is abstract or unknown has only its API schemas.
    ///
    /// Of the API schemas, only a single-apply one whose plug info provides a
    /// behavior has one.
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
            .find_map(|ty| self.own_behavior(schemas, ty))
        {
            let api = authored.iter().find_map(|api| self.api_behavior(schemas, api));
            return Some(api.unwrap_or(typed));
        }
        applied.iter().find_map(|api| self.api_behavior(schemas, api))
    }

    /// The behavior of the applied API schema named `api` (C++
    /// `_FindBehaviorForApiSchema`). Only a single-apply schema whose plug
    /// info provides a behavior has one: the behavior registered for it, or
    /// else the one its plug info configures. A name carrying an instance
    /// names a multiple-apply schema, which the registry does not know by
    /// that name.
    fn api_behavior(&self, schemas: &usd::SchemaRegistry, api: &tf::Token) -> Option<Arc<dyn Behavior>> {
        let info = schemas.schema_info(api)?;
        if info.kind() != SchemaKind::SingleApplyApi || !provides_behavior(info) {
            return None;
        }
        Some(self.behaviors.get(api).cloned().unwrap_or_else(|| configured(info)))
    }

    /// The behavior a type in a prim's lineage has of its own (C++
    /// `_GetBehaviorForPrimTypeId`'s ancestor walk): the one registered for
    /// it, or else the one its plug info configures where it provides one.
    fn own_behavior(&self, schemas: &usd::SchemaRegistry, schema: &tf::Token) -> Option<Arc<dyn Behavior>> {
        if let Some(behavior) = self.behaviors.get(schema) {
            return Some(behavior.clone());
        }
        let info = schemas.schema_info(schema)?;
        provides_behavior(info).then(|| configured(info))
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
/// [`terminal_source`](Self::terminal_source),
/// [`read_preview_surface`](Self::read_preview_surface),
/// [`can_connect_input`](Self::can_connect_input) and
/// [`can_connect_output`](Self::can_connect_output). The same query on a
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

    /// Whether `input` may connect to `source` under the behavior of its
    /// prim, `false` where the prim has none (C++
    /// `UsdShadeConnectableAPI::CanConnect`).
    pub fn can_connect_input(&self, input: &Input, source: &usd::Attribute) -> Result<bool> {
        let Some(behavior) = self.behaviors.behavior(&input.attribute().prim())? else {
            return Ok(false);
        };
        Ok(behavior.can_connect_input(self, input, source)?.is_ok())
    }

    /// Whether `output` may connect to `source` under the behavior of its
    /// prim, `false` where the prim has none (C++
    /// `UsdShadeConnectableAPI::CanConnect`).
    pub fn can_connect_output(&self, output: &Output, source: &usd::Attribute) -> Result<bool> {
        let Some(behavior) = self.behaviors.behavior(&output.attribute().prim())? else {
            return Ok(false);
        };
        Ok(behavior.can_connect_output(self, output, source)?.is_ok())
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

/// The behavior a schema's plug info configures (C++
/// `UsdShadeConnectableAPIBehavior(isContainer, requiresEncapsulation)`): its
/// two flags, and the default [`NodeKind::Basic`] rules.
#[derive(Debug)]
struct Configured {
    container: bool,
    encapsulation: bool,
}

impl Behavior for Configured {
    fn is_container(&self) -> bool {
        self.container
    }

    fn requires_encapsulation(&self) -> bool {
        self.encapsulation
    }
}

/// The behavior of a built-in schema of this crate: what is fixed for every
/// prim of the schema, and the rules its inputs and outputs connect by.
#[derive(Debug)]
pub(crate) struct BuiltIn {
    pub(crate) container: bool,
    pub(crate) encapsulation: bool,
    /// The rules the prim's inputs and outputs follow.
    pub(crate) kind: NodeKind,
    /// Whether outputs connect at all.
    pub(crate) outputs: bool,
}

impl Behavior for BuiltIn {
    fn is_container(&self) -> bool {
        self.container
    }

    fn requires_encapsulation(&self) -> bool {
        self.encapsulation
    }

    fn can_connect_input(
        &self,
        context: &ConnectableContext,
        input: &Input,
        source: &usd::Attribute,
    ) -> Result<Result<(), Refusal>> {
        rules::input(context, input, source, self.kind, self.encapsulation)
    }

    fn can_connect_output(
        &self,
        _context: &ConnectableContext,
        output: &Output,
        source: &usd::Attribute,
    ) -> Result<Result<(), Refusal>> {
        match self.outputs {
            true => rules::output(output, source, self.kind, self.encapsulation),
            false => Ok(Err(Refusal::OutputsNotConnectable)),
        }
    }
}

/// The plug info entry that gives a schema a behavior with no code behind it.
const PROVIDES_BEHAVIOR: &str = "providesUsdShadeConnectableAPIBehavior";

/// The plug info entry that makes a configured behavior a container.
const IS_CONTAINER: &str = "isUsdShadeContainer";

/// The plug info entry that a configured behavior's encapsulation reads.
const REQUIRES_ENCAPSULATION: &str = "requiresUsdShadeEncapsulation";

/// Whether `info`'s plug info provides a behavior (C++
/// `_LoadPluginDefiningBehaviorForType`): it holds a bool `true` under
/// `providesUsdShadeConnectableAPIBehavior`, on a typed or API schema. The
/// schema's kind answers which it is, as C++ asks `IsA<UsdTyped>` and
/// `IsA<UsdAPISchemaBase>`.
fn provides_behavior(info: &usd::SchemaInfo) -> bool {
    let kind = info.kind();
    plug_flag(info, PROVIDES_BEHAVIOR) == Some(true) && (kind.is_typed() || kind.is_api())
}

/// The behavior `info`'s plug info configures (C++
/// `RegisterPlugConfiguredBehaviorForType`), each flag taking its default
/// where the entry is absent or not a bool.
// TODO(perf): C++ registers a configured behavior once, against its type.
// This builds one per lookup; the per-identity cache noted on
// `BehaviorRegistry::behavior` would hold it too.
fn configured(info: &usd::SchemaInfo) -> Arc<dyn Behavior> {
    Arc::new(Configured {
        container: plug_flag(info, IS_CONTAINER).unwrap_or(false),
        encapsulation: plug_flag(info, REQUIRES_ENCAPSULATION).unwrap_or(true),
    })
}

/// The bool `info`'s plug info holds under `key`, if it holds one.
fn plug_flag(info: &usd::SchemaInfo, key: &str) -> Option<bool> {
    info.plug_info().get(key).and_then(vt::Value::try_as_bool_ref).copied()
}

/// Add the behavior of each `UsdShade` schema that has one: NodeGraph
/// (`nodeGraph.cpp:360-385`), Material (`material.cpp:725-756`) and Shader
/// (`shader.cpp:120-138`).
pub(crate) fn register_behaviors(registry: &mut BehaviorRegistry) {
    let node_graph = BuiltIn {
        container: true,
        encapsulation: true,
        kind: NodeKind::Basic,
        outputs: true,
    };
    let material = BuiltIn {
        container: true,
        encapsulation: true,
        kind: NodeKind::Container,
        outputs: true,
    };
    let shader = BuiltIn {
        container: false,
        encapsulation: true,
        kind: NodeKind::Basic,
        outputs: false,
    };
    registry
        .register(tokens::NODE_GRAPH, node_graph)
        .register(tokens::MATERIAL, material)
        .register(tokens::SHADER, shader);
}

/// The connection rules a [`Behavior`] answers by (C++
/// `_CanConnectInputToSource` and `_CanConnectOutputToSource`), for a
/// behavior of a site's own to reuse with its [`NodeKind`].
pub mod rules {
    use openusd::Result;
    use openusd::{tf, usd, vt};

    use super::super::tokens::{CONNECTABILITY, FULL, INPUTS, INTERFACE_ONLY};
    use super::super::{Input, Output};
    use super::{ConnectableContext, NodeKind, Refusal};

    /// Whether `input` may connect to `source` under the rules of a `kind`
    /// node, its containers asked of `context`, encapsulated where
    /// `encapsulation` holds (`connectableAPIBehavior.cpp:52-221`).
    ///
    /// The input's `connectability` is read as authored: empty or
    /// unauthored is `full`, and any token other than `full` or
    /// `interfaceOnly` refuses every source.
    pub fn input(
        context: &ConnectableContext,
        input: &Input,
        source: &usd::Attribute,
        kind: NodeKind,
        encapsulation: bool,
    ) -> Result<Result<(), Refusal>> {
        if !input.attribute().is_defined()? {
            return Ok(Err(Refusal::InvalidInput));
        }
        let source_prim = source.prim();
        if !source_prim.is_valid()? {
            return Ok(Err(Refusal::InvalidSource));
        }
        if source.stage() != input.attribute().stage() {
            return Ok(Err(Refusal::ForeignSource));
        }
        let interface_only = match connectability(input.attribute())?.as_deref().unwrap_or_default() {
            "" | FULL => false,
            INTERFACE_ONLY => true,
            _ => return Ok(Err(Refusal::UnspecifiedConnectability)),
        };
        let source_is_input = is_input(source)?;
        if interface_only {
            if !source_is_input {
                return Ok(Err(Refusal::SourceNotInput));
            }
            if connectability(source)?.as_deref() != Some(INTERFACE_ONLY) {
                return Ok(Err(Refusal::SourceNotInterfaceOnly));
            }
        }
        if !encapsulation {
            return Ok(Ok(()));
        }

        let input_prim = input.attribute().prim();
        if source_is_input {
            // An input source is an interface input of the container just
            // above the input's prim.
            if !context.is_container(&source_prim)? {
                return Ok(Err(Refusal::SourceNotContainer));
            }
            if input_prim.path().parent().as_ref() != Some(source_prim.path()) {
                return Ok(Err(Refusal::SourceNotParent));
            }
            return Ok(Ok(()));
        }
        // An output source is a sibling's within the container holding a
        // basic node, or a child's of a container node.
        match kind {
            NodeKind::Container => {
                if !context.is_container(&input_prim)? {
                    return Ok(Err(Refusal::InputNotContainer));
                }
                if source_prim.path().parent().as_ref() != Some(input_prim.path()) {
                    return Ok(Err(Refusal::SourceNotChild));
                }
            }
            NodeKind::Basic => {
                let Some(parent) = input_prim.parent() else {
                    return Ok(Err(Refusal::ParentNotContainer));
                };
                if !context.is_container(&parent)? {
                    return Ok(Err(Refusal::ParentNotContainer));
                }
                if input_prim.path().parent() != source_prim.path().parent() {
                    return Ok(Err(Refusal::NotSiblings));
                }
            }
        }
        Ok(Ok(()))
    }

    /// Whether `output` may connect to `source` under the rules of a `kind`
    /// node, encapsulated where `encapsulation` holds
    /// (`connectableAPIBehavior.cpp:225-293`).
    pub fn output(
        output: &Output,
        source: &usd::Attribute,
        kind: NodeKind,
        encapsulation: bool,
    ) -> Result<Result<(), Refusal>> {
        if !output.attribute().is_defined()? {
            return Ok(Err(Refusal::InvalidOutput));
        }
        let source_prim = source.prim();
        if !source_prim.is_valid()? {
            return Ok(Err(Refusal::InvalidSource));
        }
        if source.stage() != output.attribute().stage() {
            return Ok(Err(Refusal::ForeignSource));
        }
        let output_prim = output.attribute().prim();
        if is_input(source)? {
            // An input feeds an output only as a passthrough on one prim.
            if kind == NodeKind::Container {
                return Ok(Err(Refusal::Passthrough));
            }
            if source_prim.path() != output_prim.path() {
                return Ok(Err(Refusal::PassthroughElsewhere));
            }
            return Ok(Ok(()));
        }
        if encapsulation && source_prim.path().parent().as_ref() != Some(output_prim.path()) {
            return Ok(Err(Refusal::OutputSourceNotChild));
        }
        Ok(Ok(()))
    }

    /// Whether `attribute` is a defined input (C++ `UsdShadeInput::IsInput`).
    fn is_input(attribute: &usd::Attribute) -> Result<bool> {
        Ok(attribute.name().starts_with(INPUTS) && attribute.is_defined()?)
    }

    /// The `connectability` token `attribute` composes, as authored: the
    /// rules refuse a token that names neither rule, which the typed
    /// [`Input::connectability`] has no value for. A value of another type
    /// is no token, and reads as `full` (C++ `GetMetadata` failing on it).
    fn connectability(attribute: &usd::Attribute) -> Result<Option<tf::Token>> {
        Ok(attribute
            .metadata::<vt::Value>(CONNECTABILITY)?
            .and_then(vt::Value::try_as_token))
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    use openusd::sdf;
    use openusd::usd::{Field, SchemaDecl};

    use crate::SchemaError;
    use crate::geom::boundable::tests::stage_with;
    use crate::shade::{Connectability, Connectable, Input, Material, NodeGraph, Output, ProducerFilter, Shader};

    /// A family of a typed schema with a typed child, an abstract type, a
    /// type with a built-in API schema, a type an API schema auto-applies
    /// to, and three single-apply API schemas. Each API schema's plug info
    /// provides a behavior, as an API schema's must for a registered one to
    /// count.
    pub(crate) const FAMILY: &[SchemaDecl<'static>] = &[
        SchemaDecl::new("TestTyped", SchemaKind::ConcreteTyped).bases(&["Typed"]),
        SchemaDecl::new("TestChild", SchemaKind::ConcreteTyped).bases(&["TestTyped"]),
        SchemaDecl::new("TestAbstract", SchemaKind::AbstractTyped).bases(&["Typed"]),
        SchemaDecl::new("TestBuiltIn", SchemaKind::ConcreteTyped)
            .bases(&["Typed"])
            .applied_api_schemas(&["TestApiA"]),
        SchemaDecl::new("TestPlain", SchemaKind::ConcreteTyped).bases(&["Typed"]),
        SchemaDecl::new("TestApiA", SchemaKind::SingleApplyApi)
            .bases(&["APISchemaBase"])
            .plug_info(&[PROVIDES]),
        SchemaDecl::new("TestApiB", SchemaKind::SingleApplyApi)
            .bases(&["APISchemaBase"])
            .plug_info(&[PROVIDES]),
        SchemaDecl::new("TestAuto", SchemaKind::SingleApplyApi)
            .bases(&["APISchemaBase"])
            .auto_apply_to(&["TestPlain"])
            .plug_info(&[PROVIDES]),
        SchemaDecl::new("TestUnflaggedApi", SchemaKind::SingleApplyApi).bases(&["APISchemaBase"]),
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

    /// A context where `TestTyped` is a basic container, encapsulated where
    /// `encapsulation` holds.
    pub(crate) fn custom_context(encapsulation: bool) -> ConnectableContext {
        let mut behaviors = crate::connectable_registry().clone();
        behaviors.register(
            "TestTyped",
            BuiltIn {
                container: true,
                encapsulation,
                kind: NodeKind::Basic,
                outputs: true,
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
        let custom = custom_context(false);
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

        // The custom prim's input connects from anywhere, as no encapsulation
        // asks; under the default context it is not connectable at all.
        let far = Shader::define(&stage, "/Far/Away")?.create_output("out", "float")?;
        let box_in = Input::new(stage.prim("/Box")?.create_attribute("inputs:in", "float")?);
        assert!(custom.can_connect_input(&box_in, far.attribute())?);
        assert!(!default.can_connect_input(&box_in, far.attribute())?);
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
            consumer_paths(&custom_context(false), &outer, &x, true)?,
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

    /// The rule `context` refuses `input` connecting to `source` by.
    fn input_refusal(context: &ConnectableContext, input: &Input, source: &usd::Attribute) -> Result<Option<Refusal>> {
        let behavior = context.behaviors().behavior(&input.attribute().prim())?;
        let behavior = behavior.expect("the input's prim has a behavior");
        Ok(behavior.can_connect_input(context, input, source)?.err())
    }

    /// The rule `context` refuses `output` connecting to `source` by.
    fn output_refusal(
        context: &ConnectableContext,
        output: &Output,
        source: &usd::Attribute,
    ) -> Result<Option<Refusal>> {
        let behavior = context.behaviors().behavior(&output.attribute().prim())?;
        let behavior = behavior.expect("the output's prim has a behavior");
        Ok(behavior.can_connect_output(context, output, source)?.err())
    }

    /// A source on another stage is refused, whatever its path: a NodeGraph
    /// output does not pass through an input at its own path elsewhere, nor
    /// a shader input take a sibling's output there.
    #[test]
    fn foreign_source_refused() -> Result<(), SchemaError> {
        let context = ConnectableContext::default();
        let stages = [crate::tests::stage("one.usda")?, crate::tests::stage("two.usda")?];
        let [here, there] = stages.each_ref().map(|stage| -> Result<_, SchemaError> {
            let graph = NodeGraph::define(stage, "/G")?;
            let input = graph.create_input("in", "float")?;
            let output = graph.create_output("out", "float")?;
            let shader_in = Shader::define(stage, "/G/S")?.create_input("in", "float")?;
            let sibling_out = Shader::define(stage, "/G/T")?.create_output("out", "float")?;
            Ok((input, output, shader_in, sibling_out))
        });
        let (here, there) = (here?, there?);

        assert_eq!(output_refusal(&context, &here.1, here.0.attribute())?, None);
        assert_eq!(
            output_refusal(&context, &here.1, there.0.attribute())?,
            Some(Refusal::ForeignSource)
        );
        assert_eq!(input_refusal(&context, &here.2, here.3.attribute())?, None);
        assert_eq!(
            input_refusal(&context, &here.2, there.3.attribute())?,
            Some(Refusal::ForeignSource)
        );
        Ok(())
    }

    /// An input whose name the stage refuses is connectable to nothing, as
    /// an invalid C++ input is.
    #[test]
    fn invalid_input_refused() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/S")?;
        let source = shader.create_output("out", "float")?;
        assert!(!shader.input("not a name").can_connect(&source)?);
        Ok(())
    }

    /// Each rule of `connectableAPIBehavior.cpp` refuses a connection that
    /// breaks it alone.
    #[test]
    fn refusal_per_rule() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let context = ConnectableContext::default();
        let material = Material::define(&stage, "/M")?;
        let m_in = material.create_input("in", "float")?;
        let m_out = material.create_output("out", "float")?;
        let graph = NodeGraph::define(&stage, "/M/G")?;
        let g_in = graph.create_input("in", "float")?;
        let g_out = graph.create_output("out", "float")?;
        let nested = Shader::define(&stage, "/M/G/S")?;
        let nested_in = nested.create_input("in", "float")?;
        let nested_out = nested.create_output("out", "float")?;
        let sibling = Shader::define(&stage, "/M/S2")?;
        let sibling_in = sibling.create_input("in", "float")?;
        let sibling_out = sibling.create_output("out", "float")?;
        let root = Shader::define(&stage, "/Root")?.create_input("in", "float")?;
        let missing_source = stage.attribute("/Nowhere.outputs:out")?;

        let refused = |input: &Input, source: &usd::Attribute| input_refusal(&context, input, source);
        assert_eq!(
            refused(&sibling.input("missing"), sibling_out.attribute())?,
            Some(Refusal::InvalidInput)
        );
        assert_eq!(refused(&sibling_in, &missing_source)?, Some(Refusal::InvalidSource));
        assert_eq!(
            refused(&sibling_in, nested_in.attribute())?,
            Some(Refusal::SourceNotContainer)
        );
        assert_eq!(refused(&nested_in, m_in.attribute())?, Some(Refusal::SourceNotParent));
        assert_eq!(refused(&m_in, nested_out.attribute())?, Some(Refusal::SourceNotChild));
        assert_eq!(
            refused(&root, sibling_out.attribute())?,
            Some(Refusal::ParentNotContainer)
        );
        assert_eq!(
            refused(&sibling_in, nested_out.attribute())?,
            Some(Refusal::NotSiblings)
        );
        let container_rules = rules::input(&context, &sibling_in, nested_out.attribute(), NodeKind::Container, true)?;
        assert_eq!(container_rules, Err(Refusal::InputNotContainer));

        let g_in = g_in.set_connectability(Connectability::InterfaceOnly)?;
        assert_eq!(refused(&g_in, m_in.attribute())?, Some(Refusal::SourceNotInterfaceOnly));
        assert_eq!(refused(&g_in, sibling_out.attribute())?, Some(Refusal::SourceNotInput));
        let bogus = Input::new(
            sibling_in
                .attribute()
                .clone()
                .set_metadata(tokens::CONNECTABILITY, tf::Token::from("bogus"))?,
        );
        assert_eq!(
            refused(&bogus, sibling_out.attribute())?,
            Some(Refusal::UnspecifiedConnectability)
        );

        assert_eq!(
            output_refusal(&context, &graph.output("missing"), nested_out.attribute())?,
            Some(Refusal::InvalidOutput)
        );
        assert_eq!(
            output_refusal(&context, &g_out, &missing_source)?,
            Some(Refusal::InvalidSource)
        );
        assert_eq!(
            output_refusal(&context, &m_out, m_in.attribute())?,
            Some(Refusal::Passthrough)
        );
        assert_eq!(
            output_refusal(&context, &g_out, m_in.attribute())?,
            Some(Refusal::PassthroughElsewhere)
        );
        assert_eq!(
            output_refusal(&context, &g_out, sibling_out.attribute())?,
            Some(Refusal::OutputSourceNotChild)
        );
        assert_eq!(
            output_refusal(&context, &nested_out, sibling_out.attribute())?,
            Some(Refusal::OutputsNotConnectable)
        );
        Ok(())
    }

    /// An `interfaceOnly` input on a prim whose behavior keeps no
    /// encapsulation connects to an `interfaceOnly` input in another
    /// container; with encapsulation the same pair is refused, as a `full`
    /// source is.
    #[test]
    fn interface_only_unencapsulated() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        let interface_only = Connectability::InterfaceOnly;
        let source = NodeGraph::define(&stage, "/A")?
            .create_input("x", "float")?
            .set_connectability(interface_only)?;
        NodeGraph::define(&stage, "/B")?;
        stage.define_prim("/B/Box")?.set_type_name("TestTyped")?;
        let input = Input::new(stage.prim("/B/Box")?.create_attribute("inputs:x", "float")?)
            .set_connectability(interface_only)?;

        assert_eq!(input_refusal(&custom_context(false), &input, source.attribute())?, None);
        assert_eq!(
            input_refusal(&custom_context(true), &input, source.attribute())?,
            Some(Refusal::SourceNotParent)
        );
        let full = source.clear_connectability()?;
        assert_eq!(
            input_refusal(&custom_context(false), &input, full.attribute())?,
            Some(Refusal::SourceNotInterfaceOnly)
        );
        Ok(())
    }

    /// An input whose `connectability` names neither rule connects to
    /// nothing.
    #[test]
    fn unspecified_connectability() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let material = Material::define(&stage, "/M")?;
        let gain = material.create_input("gain", "float")?;
        let input = Shader::define(&stage, "/M/S")?.create_input("gain", "float")?;
        assert!(input.can_connect(gain.attribute())?);
        let input = Input::new(
            input
                .into_attribute()
                .set_metadata(tokens::CONNECTABILITY, tf::Token::from("sometimes"))?,
        );
        assert!(!input.can_connect(gain.attribute())?);
        Ok(())
    }

    /// `connect_to` authors a connection `can_connect` refuses, as C++
    /// `ConnectToSource` does.
    #[test]
    fn connect_to_unchecked() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let output = Shader::define(&stage, "/A")?.create_output("out", "float")?;
        let input = Shader::define(&stage, "/B")?.create_input("in", "float")?;
        assert!(!input.can_connect(output.attribute())?);
        let input = input.connect_to(&output)?;
        assert_eq!(input.attribute().connections()?, [output.path().clone()]);
        Ok(())
    }

    /// The `testUsdShadeConnectableAPIBehavior` plugin
    /// (`testenv/testUsdShadeConnectableAPIBehavior/resources/plugins1`):
    /// schemas whose behaviors come from plug info alone, with no code
    /// registered for them.
    const PLUG_FAMILY: &[SchemaDecl<'static>] = &[
        SchemaDecl::new("AutoApplyDefaultConnectableBehaviorAPI", SchemaKind::SingleApplyApi)
            .bases(&["APISchemaBase"])
            .auto_apply_to(&["Material", "UsdShadeTestTypedHasAutoApplyDefault"])
            .plug_info(&[PROVIDES]),
        SchemaDecl::new(
            "AutoApplyConnectableBehaviorContainerSetAPI",
            SchemaKind::SingleApplyApi,
        )
        .bases(&["APISchemaBase"])
        .auto_apply_to(&["Shader", "UsdShadeTestTypedHasAutoApplyContainer"])
        .plug_info(&[PROVIDES, CONTAINER]),
        SchemaDecl::new(
            "AutoApplyConnectableBehaviorNoRequiresEncapsulationAPI",
            SchemaKind::SingleApplyApi,
        )
        .bases(&["APISchemaBase"])
        .auto_apply_to(&["Material", "UsdShadeTestTypedHasAutoApplyRequiresEncapsulation"])
        .plug_info(&[PROVIDES, NO_ENCAPSULATION]),
        SchemaDecl::new("DefaultConnectableBehaviorAPI", SchemaKind::SingleApplyApi)
            .bases(&["APISchemaBase"])
            .plug_info(&[PROVIDES]),
        SchemaDecl::new("ModifiedDefaultConnectableBehaviorAPI", SchemaKind::SingleApplyApi)
            .bases(&["APISchemaBase"])
            .plug_info(&[PROVIDES, CONTAINER, NO_ENCAPSULATION]),
        SchemaDecl::new("UsdShadeTestTypedHasAutoApplyDefault", SchemaKind::ConcreteTyped).bases(&["Typed"]),
        SchemaDecl::new("UsdShadeTestTypedHasAutoApplyContainer", SchemaKind::ConcreteTyped).bases(&["Typed"]),
        SchemaDecl::new(
            "UsdShadeTestTypedHasAutoApplyRequiresEncapsulation",
            SchemaKind::ConcreteTyped,
        )
        .bases(&["Typed"]),
        SchemaDecl::new("UsdShadeTestTyped", SchemaKind::ConcreteTyped).bases(&["Typed"]),
        SchemaDecl::new("UsdShadeTestPlugConfiguredType", SchemaKind::ConcreteTyped)
            .bases(&["NodeGraph"])
            .plug_info(&[PROVIDES, NOT_CONTAINER, NO_ENCAPSULATION]),
        SchemaDecl::new("UsdShadeTestAncestorConfiguredType", SchemaKind::ConcreteTyped).bases(&["NodeGraph"]),
        // Beyond the C++ plugin: flags that are not bools, and a schema that
        // both registers a behavior and configures one.
        SchemaDecl::new("StringFlagAPI", SchemaKind::SingleApplyApi)
            .bases(&["APISchemaBase"])
            .plug_info(&[Field::string(PROVIDES_BEHAVIOR, "true")]),
        SchemaDecl::new("FalseFlagAPI", SchemaKind::SingleApplyApi)
            .bases(&["APISchemaBase"])
            .plug_info(&[Field::new(PROVIDES_BEHAVIOR, || vt::Value::Bool(false))]),
        SchemaDecl::new("IntContainerAPI", SchemaKind::SingleApplyApi)
            .bases(&["APISchemaBase"])
            .plug_info(&[PROVIDES, Field::new(IS_CONTAINER, || vt::Value::Int(1))]),
        SchemaDecl::new("RegisteredAndConfigured", SchemaKind::ConcreteTyped)
            .bases(&["Typed"])
            .plug_info(&[PROVIDES, NO_ENCAPSULATION]),
        SchemaDecl::new("UntypedConfigured", SchemaKind::AbstractBase)
            .bases(&["SchemaBase"])
            .plug_info(&[PROVIDES, CONTAINER]),
        SchemaDecl::new("UnderUntyped", SchemaKind::ConcreteTyped).bases(&["UntypedConfigured"]),
    ];

    const PROVIDES: Field<'static> = Field::new(PROVIDES_BEHAVIOR, || vt::Value::Bool(true));
    const CONTAINER: Field<'static> = Field::new(IS_CONTAINER, || vt::Value::Bool(true));
    const NOT_CONTAINER: Field<'static> = Field::new(IS_CONTAINER, || vt::Value::Bool(false));
    const NO_ENCAPSULATION: Field<'static> = Field::new(REQUIRES_ENCAPSULATION, || vt::Value::Bool(false));

    /// The flags of the behavior the default registry finds for the prim at
    /// `path`, `(container, encapsulation)`, or `None` where it has none.
    fn flags(stage: &usd::Stage, path: &str) -> Result<Option<(bool, bool)>> {
        let behavior = crate::connectable_registry().behavior(&stage.prim(path)?)?;
        Ok(behavior.map(|behavior| (behavior.is_container(), behavior.requires_encapsulation())))
    }

    /// Whether `schema` has a behavior with no API schema applied (C++
    /// `HasConnectableAPI`).
    fn has_api(stage: &usd::Stage, schema: &str) -> bool {
        ConnectableAPI::has_connectable_api(stage.schema_registry(), &tf::Token::from(schema))
    }

    /// A type's own plug info configures its behavior ahead of the ancestor's
    /// registered one, and a type with none takes the ancestor's (C++
    /// `test_AncestorAndPlugConfiguredTypedSchema`).
    #[test]
    fn plug_configured_type() -> Result<(), SchemaError> {
        let stage = stage_with(PLUG_FAMILY)?;
        assert!(has_api(&stage, "UsdShadeTestPlugConfiguredType"));
        stage
            .define_prim("/Configured")?
            .set_type_name("UsdShadeTestPlugConfiguredType")?;
        assert_eq!(flags(&stage, "/Configured")?, Some((false, false)));

        assert!(has_api(&stage, "UsdShadeTestAncestorConfiguredType"));
        stage
            .define_prim("/Ancestor")?
            .set_type_name("UsdShadeTestAncestorConfiguredType")?;
        assert_eq!(flags(&stage, "/Ancestor")?, Some((true, true)), "NodeGraph's behavior");
        Ok(())
    }

    /// An applied API schema configured by plug info makes a prim
    /// connectable, and overrides the behavior of its type (C++
    /// `test_AppliedSchemaWithDefaultBehavior` and
    /// `test_AppliedSchemaWithOverridingPlugMetadata`).
    #[test]
    fn applied_plug_behavior() -> Result<(), SchemaError> {
        let stage = stage_with(PLUG_FAMILY)?;

        let typeless = stage.define_prim("/Prim")?;
        assert_eq!(flags(&stage, "/Prim")?, None);
        typeless.apply_api("ModifiedDefaultConnectableBehaviorAPI")?;
        assert_eq!(flags(&stage, "/Prim")?, Some((true, false)));
        assert!(ConnectableAPI::from_prim(stage.prim("/Prim")?)?.is_some());

        // The type has no behavior; the applied schema gives one, with the
        // default flags.
        assert!(!has_api(&stage, "UsdShadeTestTyped"));
        let typed = stage.define_prim("/Typed")?.set_type_name("UsdShadeTestTyped")?;
        assert_eq!(flags(&stage, "/Typed")?, None);
        typed.apply_api("DefaultConnectableBehaviorAPI")?;
        assert_eq!(flags(&stage, "/Typed")?, Some((false, true)));
        assert!(!has_api(&stage, "UsdShadeTestTyped"));

        // Of two applied schemas, the first authored decides.
        stage
            .define_prim("/Both")?
            .set_type_name("UsdShadeTestTyped")?
            .apply_api("ModifiedDefaultConnectableBehaviorAPI")?
            .apply_api("DefaultConnectableBehaviorAPI")?;
        assert_eq!(flags(&stage, "/Both")?, Some((true, false)));

        // An authored schema overrides a registered type's behavior.
        Material::define(&stage, "/Mat")?;
        assert_eq!(flags(&stage, "/Mat")?, Some((true, true)));
        stage.prim("/Mat")?.apply_api("DefaultConnectableBehaviorAPI")?;
        assert_eq!(flags(&stage, "/Mat")?, Some((false, true)));

        Material::define(&stage, "/Mat2")?;
        stage
            .prim("/Mat2")?
            .apply_api("ModifiedDefaultConnectableBehaviorAPI")?;
        assert_eq!(flags(&stage, "/Mat2")?, Some((true, false)));

        Shader::define(&stage, "/Shader")?;
        assert_eq!(flags(&stage, "/Shader")?, Some((false, true)));
        stage
            .prim("/Shader")?
            .apply_api("ModifiedDefaultConnectableBehaviorAPI")?;
        assert_eq!(flags(&stage, "/Shader")?, Some((true, false)));
        Ok(())
    }

    /// An auto-applied API schema configured by plug info gives a type with
    /// no behavior one, and leaves a registered type's behavior alone (C++
    /// `test_AutoAppliedSchemaWithDefaultBehavior` and
    /// `test_AutoAppliedSchemaWithOverridingPlugMetadata`).
    #[test]
    fn auto_applied_plug_behavior() -> Result<(), SchemaError> {
        let stage = stage_with(PLUG_FAMILY)?;
        for (path, type_name, expected) in [
            ("/Default", "UsdShadeTestTypedHasAutoApplyDefault", (false, true)),
            ("/Container", "UsdShadeTestTypedHasAutoApplyContainer", (true, true)),
            (
                "/Loose",
                "UsdShadeTestTypedHasAutoApplyRequiresEncapsulation",
                (false, false),
            ),
        ] {
            stage.define_prim(path)?.set_type_name(type_name)?;
            assert_eq!(flags(&stage, path)?, Some(expected), "{type_name}");
        }

        // Auto-applied to Material and Shader, which keep their own.
        Material::define(&stage, "/Mat")?;
        assert_eq!(flags(&stage, "/Mat")?, Some((true, true)));
        Shader::define(&stage, "/Shader")?;
        assert_eq!(flags(&stage, "/Shader")?, Some((false, true)));
        Ok(())
    }

    /// No behavior comes from a multiple-apply schema, a schema the registry
    /// does not know, or a typed schema written as an API schema (C++
    /// `test_InvalidAppliedSchemaWithDefaultBehavior`).
    #[test]
    fn invalid_applied_schemas() -> Result<(), SchemaError> {
        let stage = stage_with(PLUG_FAMILY)?;
        // Authored unchecked, as C++ `AddAppliedSchema` does.
        stage
            .define_prim("/Multi")?
            .add_applied_schema("CollectionAPI:fanciness")?;
        stage
            .define_prim("/Unknown")?
            .add_applied_schema("NoSuchLuckInvalidAPISchemaAPI")?;
        stage.define_prim("/Typed")?.add_applied_schema("Material")?;
        for path in ["/Multi", "/Unknown", "/Typed"] {
            assert_eq!(flags(&stage, path)?, None, "{path}");
            assert!(!ConnectableContext::default().is_container(&stage.prim(path)?)?);
        }
        Ok(())
    }

    /// Only a bool `true` provides a behavior, and a flag that is not a bool
    /// takes its default, as C++ asks of a `JsValue`.
    #[test]
    fn plug_flag_types() -> Result<(), SchemaError> {
        let stage = stage_with(PLUG_FAMILY)?;
        stage.define_prim("/String")?.apply_api("StringFlagAPI")?;
        stage.define_prim("/False")?.apply_api("FalseFlagAPI")?;
        stage.define_prim("/Int")?.apply_api("IntContainerAPI")?;
        assert_eq!(flags(&stage, "/String")?, None);
        assert_eq!(flags(&stage, "/False")?, None);
        assert_eq!(flags(&stage, "/Int")?, Some((false, true)));
        Ok(())
    }

    /// The vendored families carry the flag on the schemas C++ marks, which
    /// each also register a behavior of their own.
    #[test]
    fn vendored_plug_info() {
        let schemas = crate::schema_registry();
        let lux: &[&str] = if cfg!(feature = "lux") {
            &["LightAPI", "LightFilter"]
        } else {
            &[]
        };
        for &schema in ["NodeGraph", "Material", "Shader"].iter().chain(lux) {
            let info = schemas.schema_info(&tf::Token::from(schema)).expect(schema);
            assert_eq!(
                info.plug_info().get(PROVIDES_BEHAVIOR),
                Some(&vt::Value::Bool(true)),
                "{schema}"
            );
            assert!(crate::connectable_registry().behaviors.contains_key(schema), "{schema}");
        }
        let scope = schemas.schema_info(&tf::Token::from("Scope")).expect("Scope");
        assert!(scope.plug_info().get(PROVIDES_BEHAVIOR).is_none());
    }

    /// Plug info configures a behavior only on a typed or API schema, as
    /// C++ `_LoadPluginDefiningBehaviorForType` requires
    /// (`connectableAPIBehavior.cpp:713-716`).
    #[test]
    fn untyped_plug_ignored() -> Result<(), SchemaError> {
        let stage = stage_with(PLUG_FAMILY)?;
        stage.define_prim("/P")?.set_type_name("UnderUntyped")?;
        assert_eq!(flags(&stage, "/P")?, None);
        assert!(!has_api(&stage, "UntypedConfigured"));
        Ok(())
    }

    /// An applied API schema whose plug info does not provide a behavior
    /// adds none, even with one registered; a type takes its registered one
    /// regardless (C++ `_FindBehaviorForApiSchema`).
    #[test]
    fn api_needs_plug_flag() -> Result<(), SchemaError> {
        let stage = stage_with(FAMILY)?;
        stage
            .define_prim("/Typed")?
            .set_type_name("TestTyped")?
            .apply_api("TestUnflaggedApi")?;
        stage.define_prim("/Typeless")?.apply_api("TestUnflaggedApi")?;
        let registry = registry(&[("TestTyped", "typed"), ("TestUnflaggedApi", "api")]);
        assert_eq!(named(&registry, &stage, "/Typed")?, name("typed"));
        assert_eq!(named(&registry, &stage, "/Typeless")?, None);
        Ok(())
    }

    /// A registered behavior wins over the one a schema's plug info
    /// configures.
    #[test]
    fn registered_beats_configured() -> Result<(), SchemaError> {
        let stage = stage_with(PLUG_FAMILY)?;
        stage.define_prim("/P")?.set_type_name("RegisteredAndConfigured")?;
        assert_eq!(flags(&stage, "/P")?, Some((false, false)), "the plug info's");

        let registry = registry(&[("RegisteredAndConfigured", "registered")]);
        assert_eq!(named(&registry, &stage, "/P")?, name("registered"));
        Ok(())
    }
}
