//! The composed schema view of one prim type.

use std::sync::Arc;

use crate::tf;

use super::PrimDefinition;

/// Everything the registry knows about a prim whose type and applied API
/// schemas are exactly these (C++ `UsdPrimTypeInfo`).
///
/// Prims that agree on [`PrimTypeId`] share one of these, so composing their
/// definition happens once no matter how many prims have that type. They are
/// handed out by
/// [`SchemaRegistry::prim_type_info`](super::SchemaRegistry::prim_type_info).
#[derive(Debug)]
pub struct PrimTypeInfo {
    id: PrimTypeId,
    /// The registered type the definition came from, empty when no registered
    /// type backs it.
    schema_type_name: tf::Token,
    definition: Arc<PrimDefinition>,
}

/// What makes one prim type distinct from another (C++
/// `UsdPrimTypeInfo::_TypeId`).
///
/// Two prims with the same identity have the same schema properties and
/// fallbacks, whatever else differs about them, which is what lets the registry
/// key its cache on this.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct PrimTypeId {
    type_name: tf::Token,
    /// The type actually used to find a definition, set when the stage's
    /// `fallbackPrimTypes` maps an authored type the registry does not know
    /// onto one it does.
    mapped_type_name: Option<tf::Token>,
    applied: Vec<tf::Token>,
}

impl PrimTypeInfo {
    /// What this type is.
    pub fn id(&self) -> &PrimTypeId {
        &self.id
    }

    /// The properties and fallbacks a prim of this type has.
    pub fn prim_definition(&self) -> &Arc<PrimDefinition> {
        &self.definition
    }

    /// The registered type whose definition backs this one (C++
    /// `UsdPrimTypeInfo::GetSchemaTypeName`).
    ///
    /// This is the authored `typeName`, or the `fallbackPrimTypes` substitute
    /// when one applied, and it is what an `IsA` query walks from. It is empty
    /// unless the registry knows that name as an instantiable type, so a
    /// typeless prim, one whose type the registry does not know, and one
    /// authored as a registered *abstract* type all report nothing — matching
    /// C++, whose `GetConcreteTypeFromSchemaTypeName` is concrete-only.
    pub fn schema_type_name(&self) -> &tf::Token {
        &self.schema_type_name
    }

    /// Builds the information for one type identity.
    pub(super) fn new(id: PrimTypeId, schema_type_name: tf::Token, definition: Arc<PrimDefinition>) -> PrimTypeInfo {
        PrimTypeInfo {
            id,
            schema_type_name,
            definition,
        }
    }
}

impl PrimTypeId {
    /// The identity of a prim with this `typeName` and these composed
    /// `apiSchemas`. An empty type name and no applied schemas is the identity
    /// of a prim that has no schema at all.
    pub fn new(type_name: Option<tf::Token>, applied: Vec<tf::Token>) -> PrimTypeId {
        PrimTypeId {
            type_name: type_name.unwrap_or_default(),
            mapped_type_name: None,
            applied,
        }
    }

    /// Redirects the definition lookup to `mapped`, the type the stage's
    /// `fallbackPrimTypes` names for a `typeName` the registry does not know
    /// (C++ `UsdPrimTypeInfo::_TypeId::mappedTypeName`).
    ///
    /// The authored name stays in the identity, so two prims differing only in
    /// their authored type remain distinct even when both map to the same
    /// fallback.
    pub fn with_mapped_type_name(mut self, mapped: tf::Token) -> PrimTypeId {
        self.mapped_type_name = Some(mapped);
        self
    }

    /// The prim's authored `typeName`, empty when it has none.
    pub fn type_name(&self) -> &tf::Token {
        &self.type_name
    }

    /// The prim's composed `apiSchemas`, strongest first.
    pub fn applied_api_schemas(&self) -> &[tf::Token] {
        &self.applied
    }

    /// Whether this identity carries no schema information, and so has nothing
    /// worth caching or composing.
    pub fn is_empty(&self) -> bool {
        self.type_name.as_str().is_empty() && self.applied.is_empty()
    }

    /// The type name a definition is looked up under: the mapped fallback when
    /// the stage supplied one, otherwise the authored name.
    pub(super) fn lookup_name(&self) -> &tf::Token {
        self.mapped_type_name.as_ref().unwrap_or(&self.type_name)
    }
}
