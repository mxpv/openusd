//! The schema registry (C++ `UsdSchemaRegistry`) — the type table and prim
//! definitions behind spec §13.3.
//!
//! A schema describes what properties a prim of a given `typeName` has, what
//! their fallback values are, and which API schemas that type includes. A
//! [`SchemaRegistry`] is the index of that information: it answers "what does a
//! `Cube` look like?" without any stage or composition involved.
//!
//! Two ingredients define a schema family, both plain `.usda` text. The
//! schematics are a fully flattened layer holding one class prim per schema,
//! named after the schema identifier — the shape OpenUSD's
//! `generatedSchema.usda` already has; every property a schema defines, with
//! its fallback value, lives on that class prim. The manifest supplies what a
//! flattened layer cannot: each schema's [`SchemaKind`](super::SchemaKind) and
//! its base schemas. C++ keeps that in `plugInfo.json`; see
//! [`SchemaRegistryBuilder::family`] for the format.
//!
//! A family may also say where its schematics was resolved from
//! ([`FamilySource::resolved_location`]), which is what lets
//! [`Attribute::get`](super::Attribute::get) hand back a resolved path for an
//! `asset` fallback.
//!
//! [`SchemaRegistry::global`] is the lazily built process registry every
//! [`Stage`](super::Stage) uses by default. It currently registers no families
//! — the machinery is here, the OpenUSD schema data is not vendored yet — so
//! fallback lookups uniformly find nothing. Registering families through
//! [`SchemaRegistry::builder`] and handing the result to
//! [`StageBuilder::schema_registry`](super::StageBuilder::schema_registry)
//! works today.

use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};
use std::mem;
use std::sync::{Arc, OnceLock, PoisonError, RwLock};

use anyhow::{Context, Result, bail};

use crate::{ar, sdf, tf, usda};

use super::prim_definition::{self, FamilyVersions};
use super::{PrimDefinition, PrimTypeId, PrimTypeInfo, SchemaKind};

/// The registered schemas of a process or a stage (C++ `UsdSchemaRegistry`).
///
/// A registry is built once from a set of schema families and is immutable
/// afterwards, so it is cheap to share: stages hold an `Arc` of one, and
/// [`global`](Self::global) hands out the process-wide default.
///
/// Lookups are by schema identifier — the name a `typeName` or an `apiSchemas`
/// entry uses (`"Sphere"`, `"CollectionAPI"`). An unregistered identifier is
/// never an error; it simply has no information, so a stage carrying types
/// this registry has never heard of still composes.
#[derive(Debug)]
pub struct SchemaRegistry {
    infos: HashMap<tf::Token, SchemaInfo>,
    /// Reverse index over [`SchemaInfo::family`], so a versioned family can be
    /// queried without scanning `infos`. Ordered as
    /// [`schema_infos_in_family`](Self::schema_infos_in_family) answers.
    families: HashMap<tf::Token, Vec<tf::Token>>,
    /// Definitions of the instantiable types, keyed by `typeName`.
    concrete_defs: HashMap<tf::Token, Arc<PrimDefinition>>,
    /// Definitions of the applied API schemas. A multiple-apply schema is
    /// stored under its bare identifier, its property names still carrying the
    /// instance-name placeholder.
    api_defs: HashMap<tf::Token, Arc<PrimDefinition>>,
    /// The answer for a prim whose type declares nothing, so callers never
    /// have to special-case an unknown type.
    empty_def: Arc<PrimDefinition>,
    empty_type_info: Arc<PrimTypeInfo>,
    /// Composed definitions, keyed by the type identity that produced them, so
    /// every prim sharing a type shares one. Pure memoization: it changes what
    /// the registry has already computed, never what it answers. Entries are
    /// kept for the registry's lifetime, which is what lets a
    /// [`PrimTypeInfo`] handle outlive the stage that asked for it.
    // TODO(perf): shard this if the single lock ever shows up under contention,
    // and reclaim entries — today they live as long as the registry does.
    type_infos: RwLock<HashMap<PrimTypeId, Arc<PrimTypeInfo>>>,
}

/// What is known about one registered schema, independent of its properties
/// (C++ `UsdSchemaRegistry::SchemaInfo`).
///
/// This is the cheap tier: identity, kind, and inheritance, all of it read
/// from the family manifest. The properties and fallback values a schema
/// defines live in its [`PrimDefinition`](super::PrimDefinition).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemaInfo {
    identifier: tf::Token,
    family: tf::Token,
    version: u32,
    kind: SchemaKind,
    bases: Vec<tf::Token>,
    property_namespace_prefix: Option<tf::Token>,
    auto_apply_to: Vec<tf::Token>,
    can_only_apply_to: Vec<tf::Token>,
    allowed_instance_names: Vec<tf::Token>,
}

/// One family's parsed schematics — the class prims that define what each
/// schema's properties are.
///
/// The registry keeps the parsed [`sdf::Data`] rather than an
/// [`sdf::Layer`](crate::sdf::Layer) because a layer carries change-notification
/// state that is neither `Send` nor `Sync`, while a registry is shared across
/// stages and threads. Reading a fallback is a field read on this store, so
/// nothing is copied until a caller asks for an owned value.
#[derive(Debug)]
pub struct Schematics {
    family: tf::Token,
    /// Taken verbatim from [`FamilySource::resolved_location`].
    resolved_location: Option<ar::ResolvedPath>,
    data: sdf::Data,
}

/// One schema family's source text, as handed to
/// [`SchemaRegistryBuilder::family`].
///
/// Both halves are `.usda`: `schematics` is a flattened layer of class prims,
/// `manifest` is the per-schema metadata that flattening cannot preserve.
#[derive(Debug, Clone, Copy)]
pub struct FamilySource<'a> {
    /// Family name, used to attribute parse failures and to identify the
    /// parsed [`Schematics`].
    pub name: &'a str,
    /// Manifest text — see [`SchemaRegistryBuilder::family`] for the format.
    pub manifest: &'a str,
    /// Schematics text, in `generatedSchema.usda` form.
    pub schematics: &'a str,
    /// Where that text was resolved from — the anchor for the relative asset
    /// paths its fallback values author, and the one thing that lets
    /// [`Attribute::get`](super::Attribute::get) resolve such a fallback.
    ///
    /// It must be non-empty, and it must be what the resolver applicable to
    /// stages using this registry returns for the schematics; the registry
    /// stores it verbatim and never canonicalizes or re-resolves it. A
    /// [`ResolvedPath`](crate::ar::ResolvedPath) is an opaque resolver result,
    /// so filesystem absoluteness is neither required nor checked.
    ///
    /// `None` for a family with no location, such as one compiled into a
    /// binary; its fallbacks then read back exactly as authored, with no
    /// resolved path, which is what C++ produces for every family (see the
    /// module documentation).
    pub resolved_location: Option<&'a ar::ResolvedPath>,
}

/// Accumulates schema families into a [`SchemaRegistry`].
///
/// Each [`family`](Self::family) call parses one family's manifest and
/// schematics; [`build`](Self::build) then composes the prim definitions that
/// need every family present, such as a typed schema whose built-in API schema
/// comes from another family, or one an API schema auto-applies to.
#[derive(Debug, Default)]
pub struct SchemaRegistryBuilder {
    infos: HashMap<tf::Token, SchemaInfo>,
    /// Which family's schematics holds each identifier's class prim.
    source_of: HashMap<tf::Token, Arc<Schematics>>,
    /// The auto-apply declarations registered through
    /// [`auto_apply`](Self::auto_apply), keyed by the API schema they apply.
    /// [`build`](Self::build) merges each into its API schema's
    /// [`SchemaInfo`].
    extra_auto_apply: HashMap<tf::Token, Vec<tf::Token>>,
}

/// Which versions of a schema family a query accepts (C++
/// `UsdSchemaRegistry::VersionPolicy`).
///
/// C++ passes the policy and the version it compares against separately; here
/// the version rides on the variant that uses it, so [`All`](Self::All) cannot
/// be paired with a version that means nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VersionFilter {
    /// Every version in the family.
    All,
    /// Versions strictly newer than this one.
    GreaterThan(u32),
    /// This version and anything newer.
    GreaterThanOrEqual(u32),
    /// Versions strictly older than this one.
    LessThan(u32),
    /// This version and anything older.
    LessThanOrEqual(u32),
}

/// Why an API schema cannot be applied to a prim — the reason C++
/// `UsdPrim::CanApplyAPI` reports through its `whyNot`.
///
/// Apart from [`PrimNotValid`](Self::PrimNotValid), every variant names a
/// registered schema: a name no registry knows carries no rules to break, so
/// applying it is accepted (see [`Prim::apply_api`](super::Prim::apply_api)).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ApplyApiError {
    /// No prim is composed at the path, so there is nothing to apply to.
    #[error("no prim at {path} to apply an API schema to")]
    PrimNotValid {
        /// The path that composed no prim.
        path: sdf::Path,
    },

    /// Deciding the question needed the prim's composed type, and composing it
    /// failed.
    #[error(transparent)]
    Composition(#[from] anyhow::Error),

    /// The schema is registered, but is not one that applies to a prim through
    /// `apiSchemas` — a typed schema, or a non-applied API schema.
    #[error("{schema} is not an applied API schema")]
    NotAppliedApi {
        /// The offending schema identifier.
        schema: tf::Token,
    },

    /// A multiple-apply schema applies per instance, so it needs an instance
    /// name (`CollectionAPI:render`).
    #[error("multiple-apply schema {schema} needs an instance name")]
    MissingInstanceName {
        /// The offending schema identifier.
        schema: tf::Token,
    },

    /// A single-apply schema applies whole, so it has no instance to name.
    #[error("single-apply schema {schema} takes no instance name, got {instance}")]
    UnexpectedInstanceName {
        /// The offending schema identifier.
        schema: tf::Token,
        /// The instance name that was supplied anyway.
        instance: tf::Token,
    },

    /// The schema restricts its instance names, or the name collides with one
    /// of the schema's own property base names.
    #[error("{instance} is not an allowed instance name for {schema}")]
    InstanceNameNotAllowed {
        /// The offending schema identifier.
        schema: tf::Token,
        /// The rejected instance name.
        instance: tf::Token,
    },

    /// The schema's `apiSchemaCanOnlyApplyTo` does not cover this prim's type.
    #[error("{schema} can only be applied to {allowed:?}")]
    PrimTypeNotAllowed {
        /// The offending schema identifier.
        schema: tf::Token,
        /// The prim types the schema restricts itself to.
        allowed: Vec<tf::Token>,
    },
}

impl SchemaRegistry {
    /// The process-wide registry, built on first use.
    ///
    /// Every stage opened without an explicit
    /// [`StageBuilder::schema_registry`](crate::usd::StageBuilder::schema_registry)
    /// shares this one. It registers the families compiled into the crate,
    /// which today is none — see the module documentation.
    pub fn global() -> &'static Arc<SchemaRegistry> {
        static GLOBAL: OnceLock<Arc<SchemaRegistry>> = OnceLock::new();
        GLOBAL.get_or_init(|| {
            SchemaRegistryBuilder::compiled_in()
                .build()
                .expect("compiled-in schema data must parse")
        })
    }

    /// Starts a registry with no families registered.
    pub fn builder() -> SchemaRegistryBuilder {
        SchemaRegistryBuilder::default()
    }

    /// Looks up a schema by identifier (C++ `FindSchemaInfo`).
    pub fn schema_info(&self, identifier: &tf::Token) -> Option<&SchemaInfo> {
        self.infos.get(identifier)
    }

    /// Looks up a specific version within a schema family
    /// (C++ `FindSchemaInfo(family, version)`).
    ///
    /// A family may not itself carry a version suffix, so `("Foo_1", 0)` names
    /// no schema even though `Foo_1` may well be registered.
    pub fn schema_info_in_family(&self, family: &tf::Token, version: u32) -> Option<&SchemaInfo> {
        Self::is_allowed_family(family)
            .then(|| self.infos.get(&Self::make_identifier(family, version)))
            .flatten()
    }

    /// Every registered schema in `family` that `filter` accepts, newest
    /// version first (C++ `FindSchemaInfosInFamily`).
    ///
    /// The order is what makes a family query answer with the newest version a
    /// prim satisfies, so a caller that wants the best match takes the first
    /// item.
    pub fn schema_infos_in_family<'a>(
        &'a self,
        family: &tf::Token,
        filter: VersionFilter,
    ) -> impl Iterator<Item = &'a SchemaInfo> + use<'a> {
        self.families
            .get(family)
            .into_iter()
            .flatten()
            .filter_map(|identifier| self.infos.get(identifier))
            .filter(move |info| filter.accepts(info.version))
    }

    /// The version of `family` that `schema_type` is, or `None` when it is none
    /// of them (C++ `UsdPrim::GetVersionIfIsInFamily`'s registry half).
    ///
    /// A type qualifies by deriving from a schema in the family, not by name,
    /// so this runs through [`is_a`](Self::is_a).
    pub fn version_in_family(&self, schema_type: &tf::Token, family: &tf::Token, filter: VersionFilter) -> Option<u32> {
        self.schema_infos_in_family(family, filter)
            .find(|info| self.is_a(schema_type, info.identifier()))
            .map(SchemaInfo::version)
    }

    /// The family and version `identifier` names, or `None` when it does not
    /// name one canonically.
    ///
    /// Registration is not consulted: an identifier carries its own family and
    /// version, which is what lets an authored `typeName` be placed in a family
    /// while no schema data is registered. Only a spelling
    /// [`is_allowed_identifier`](Self::is_allowed_identifier) accepts is placed,
    /// so `Foo_01` — which could never name a registered schema — belongs to no
    /// family rather than to `Foo`. C++ `ParseSchemaFamilyAndVersionFromIdentifier`
    /// parses the same suffix but places every spelling, because it reaches
    /// this question only for names that already resolved through `TfType`.
    pub fn parse_allowed_identifier(identifier: &tf::Token) -> Option<(tf::Token, u32)> {
        Self::is_allowed_identifier(identifier).then(|| Self::parse_identifier(identifier))
    }

    /// Every registered schema, in unspecified order.
    pub fn schema_infos(&self) -> impl Iterator<Item = &SchemaInfo> {
        self.infos.values()
    }

    /// The definition of an instantiable prim type
    /// (C++ `FindConcretePrimDefinition`).
    ///
    /// Abstract types and unregistered names have none; callers that want a
    /// definition regardless fall back to
    /// [`empty_prim_definition`](Self::empty_prim_definition).
    pub fn concrete_prim_definition(&self, type_name: &tf::Token) -> Option<&Arc<PrimDefinition>> {
        self.concrete_defs.get(type_name)
    }

    /// The definition of an applied API schema
    /// (C++ `FindAppliedAPIPrimDefinition`).
    ///
    /// A multiple-apply schema is keyed by its bare identifier; its properties
    /// still carry the instance-name placeholder and are instantiated when the
    /// schema is applied under a name.
    pub fn api_prim_definition(&self, identifier: &tf::Token) -> Option<&Arc<PrimDefinition>> {
        self.api_defs.get(identifier)
    }

    /// The definition that declares nothing.
    pub fn empty_prim_definition(&self) -> &Arc<PrimDefinition> {
        &self.empty_def
    }

    /// Whether no schemas are registered, so every prim resolves the empty
    /// definition and deriving its type identity would be wasted work.
    pub fn is_empty(&self) -> bool {
        self.infos.is_empty()
    }

    /// Whether `type_name` names an instantiable type this registry knows.
    pub fn is_concrete_type(&self, type_name: &tf::Token) -> bool {
        self.concrete_defs.contains_key(type_name)
    }

    /// Whether `schema` is `base`, or derives from it through the base chain
    /// the family manifests declare (C++ `UsdPrim::IsA`, which walks the
    /// `TfType` hierarchy the same information builds).
    ///
    /// The walk covers every base transitively, so a query against an abstract
    /// ancestor (`Boundable`, `Imageable`) answers for the concrete types under
    /// it.
    ///
    /// Both sides have to name a registered schema, as they do in C++, where an
    /// identifier with no `TfType` resolves to nothing. An unregistered name is
    /// therefore not a schema: nothing derives from it, and it derives from
    /// nothing — not even itself. Registering a family whose bases live in a
    /// family that was left out gets the same answer as registering nothing,
    /// which is the only answer that does not vary with how far up the chain
    /// the loaded set happens to reach.
    // TODO(perf): the base graph is fixed once `build` returns, so this could
    // resolve against a transitive closure computed there instead of walking
    // per query. Worth doing when the schema data lands and chains get deep.
    pub fn is_a(&self, schema: &tf::Token, base: &tf::Token) -> bool {
        if !self.infos.contains_key(base) {
            return false;
        }

        // Manifests are data, so a malformed one can name a base cycle; the
        // visited set makes the walk terminate on it rather than the caller.
        let mut visited = HashSet::new();
        let mut pending = vec![schema];
        while let Some(next) = pending.pop() {
            if next == base {
                return true;
            }
            if !visited.insert(next) {
                continue;
            }
            let Some(info) = self.infos.get(next) else {
                continue;
            };
            pending.extend(&info.bases);
        }
        false
    }

    /// Resolves an applied-schema name to the schema it names and its instance,
    /// rejecting a name whose shape its kind does not permit.
    ///
    /// An applied name carries an instance exactly when the schema is
    /// multiple-apply (`CollectionAPI:render`), and only an applied API schema
    /// can appear in `apiSchemas` at all. This is the rule composition applies
    /// when it walks a prim's list, so authoring answers for a name exactly as
    /// composition will treat it.
    ///
    /// `Ok(None)` for a name this registry has no schema for: it carries no
    /// rules to break, and composition passes over it.
    pub fn check_applied_name(
        &self,
        name: &tf::Token,
    ) -> Result<Option<(&SchemaInfo, Option<tf::Token>)>, ApplyApiError> {
        check_applied_shape(&self.infos, name)
    }

    /// Whether `instance` may name an instance of the multiple-apply schema
    /// `identifier` (C++ `IsAllowedAPISchemaInstanceName`).
    ///
    /// A schema may restrict its instance names through
    /// [`SchemaInfo::allowed_instance_names`]; an empty list allows any. On top
    /// of that, no schema accepts an instance name whose base collides with one
    /// of its own property base names, since the instantiated property would
    /// then be indistinguishable from the schema's own.
    ///
    /// `false` for anything that is not a registered multiple-apply schema, and
    /// for an instance name that is not a valid namespaced identifier — the
    /// name becomes a namespace component of every property the schema
    /// instantiates, so anything unspellable there is rejected here.
    pub fn is_allowed_instance_name(&self, identifier: &tf::Token, instance: &tf::Token) -> bool {
        let (Some(info), Some(definition)) = (self.infos.get(identifier), self.api_defs.get(identifier)) else {
            return false;
        };
        // Every component has to be an identifier in its own right, which is
        // what C++ `TokenizeIdentifierAsTokens` returns nothing for. The
        // namespace delimiter is the only one an instance name may carry, so a
        // `.` is rejected here where a property path would accept it.
        if !instance.split(':').all(sdf::Path::is_valid_identifier) || info.kind != SchemaKind::MultipleApplyApi {
            return false;
        }
        if !info.allowed_instance_names.is_empty() && !info.allowed_instance_names.contains(instance) {
            return false;
        }

        // A property carries the instance-name placeholder, so the comparison
        // is against each property's base name rather than the whole name: a
        // built-in from another multiple-apply schema need not share a prefix.
        let base = instance.rsplit_once(':').map_or(instance.as_str(), |(_, base)| base);
        !definition
            .property_names()
            .iter()
            .any(|property| name_template_base(property) == base)
    }

    /// Whether a field is meaningless as a schema fallback
    /// (C++ `UsdSchemaRegistry::IsDisallowedField`).
    ///
    /// A schema's class prim is a prim spec like any other, so it carries
    /// fields that describe *it* rather than the prims that use it — its
    /// `specifier`, its children, the `customData` the schema generator wrote.
    /// Composition and value resolution never consult a fallback for these, so
    /// a prim definition refuses to report them however the schematics were
    /// authored. This is what lets a fallback lookup be unconditional: the
    /// unsafe fields are excluded once, here, rather than at each reader.
    pub fn is_disallowed_field(field: &str) -> bool {
        // Composition arcs: a fallback arc would never be composed.
        const ARCS: [sdf::FieldKey; 6] = [
            sdf::FieldKey::InheritPaths,
            sdf::FieldKey::Payload,
            sdf::FieldKey::References,
            sdf::FieldKey::Specializes,
            sdf::FieldKey::VariantSelection,
            sdf::FieldKey::VariantSetNames,
        ];
        // Fields consulted during scenegraph population or value resolution
        // rather than read as metadata, plus `customData`, which carries the
        // schema generator's own bookkeeping, and `kind`, whose fallback prim
        // composition deliberately ignores.
        const RESOLVED: [sdf::FieldKey; 10] = [
            sdf::FieldKey::Active,
            sdf::FieldKey::ConnectionPaths,
            sdf::FieldKey::CustomData,
            sdf::FieldKey::Instanceable,
            sdf::FieldKey::Kind,
            sdf::FieldKey::Specifier,
            sdf::FieldKey::TargetPaths,
            sdf::FieldKey::TimeSamples,
            sdf::FieldKey::Clips,
            sdf::FieldKey::ClipSets,
        ];

        ARCS.iter().chain(RESOLVED.iter()).any(|key| key.as_str() == field) || sdf::is_children_field(field)
    }

    /// The definition of a prim with this type and these applied API schemas
    /// (C++ `BuildComposedPrimDefinition`).
    ///
    /// The type's own definition is strongest, then each applied schema in the
    /// order given. `applied` is a prim's composed `apiSchemas`, so it may name
    /// schemas the type already builds in — those contribute once — and schemas
    /// this registry does not know, which are skipped. A typeless prim still
    /// gets whatever its applied schemas declare.
    ///
    /// With nothing applied this is the type's own definition, shared rather
    /// than rebuilt.
    pub fn build_composed_prim_definition(&self, type_name: &tf::Token, applied: &[tf::Token]) -> Arc<PrimDefinition> {
        let typed = self.concrete_defs.get(type_name).unwrap_or(&self.empty_def);
        if applied.is_empty() {
            return typed.clone();
        }

        // An applied schema may not introduce a second version of a family the
        // type already builds in, so those versions are claimed up front.
        let mut seen = FamilyVersions::new();
        for name in typed.applied_api_schemas() {
            let (identifier, instance) = split_instance_name(name);
            if let Some(info) = self.infos.get(&identifier) {
                seen.insert((info.family().clone(), instance), info.version());
            }
        }

        let mut definition = PrimDefinition::clone(typed);
        for name in applied {
            // A name whose shape its schema does not permit contributes
            // nothing, as does one no schema backs.
            // TODO: report the rejected name. C++ `_ComposeAPISchemasIntoPrim-
            // Definition` warns through `TF_WARN`; this crate has no diagnostic
            // channel for a composed definition to carry one out through, so
            // the typed error is discarded here.
            let Ok(Some((info, instance))) = self.check_applied_name(name) else {
                continue;
            };
            let Some(weaker) = self.api_defs.get(info.identifier()) else {
                continue;
            };
            definition.compose_weaker_api(weaker, instance.as_ref(), &self.infos, &mut seen);
        }
        definition.finish_composition();
        Arc::new(definition)
    }

    /// The shared information for a prim type identity, composing it on first
    /// request (C++ `Usd_PrimTypeInfoCache::FindOrCreatePrimTypeInfo`).
    ///
    /// Every prim with the same identity gets the same handle, so a stage that
    /// asks per prim composes each distinct type once. The handle stays valid
    /// for as long as the registry does.
    pub fn prim_type_info(&self, id: PrimTypeId) -> Arc<PrimTypeInfo> {
        if id.is_empty() {
            return self.empty_type_info.clone();
        }
        // A panic while another thread held this lock cannot have left a
        // half-written entry, so the poison is ignored on both sides.
        let cached = self.type_infos.read().unwrap_or_else(PoisonError::into_inner);
        if let Some(info) = cached.get(&id) {
            return info.clone();
        }
        drop(cached);

        // Composed outside the lock, so a slow composition never blocks
        // lookups. A concurrent caller may finish first, in which case its
        // entry is the one everyone uses and this one is dropped.
        // Resolve the type first, then compose from it, so the definition is by
        // construction the one belonging to the reported schema type. An
        // unregistered name resolves to the empty token, whose definition is
        // the empty one.
        let schema_type_name = match self.is_concrete_type(id.lookup_name()) {
            true => id.lookup_name().clone(),
            false => tf::Token::default(),
        };
        let definition = self.build_composed_prim_definition(&schema_type_name, id.applied_api_schemas());
        let info = Arc::new(PrimTypeInfo::new(id.clone(), schema_type_name, definition));
        self.type_infos
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .entry(id)
            .or_insert(info)
            .clone()
    }

    /// The information for a prim with no type and no applied schemas.
    pub fn empty_prim_type_info(&self) -> &Arc<PrimTypeInfo> {
        &self.empty_type_info
    }

    /// Splits a schema identifier into its family and version
    /// (C++ `ParseSchemaFamilyAndVersionFromIdentifier`).
    ///
    /// A version suffix is a trailing underscore followed by one or more
    /// digits; an identifier without one is version 0.
    ///
    /// ```
    /// use openusd::{tf, usd::SchemaRegistry};
    ///
    /// let (family, version) = SchemaRegistry::parse_identifier(&tf::Token::new("DomeLight_1"));
    /// assert_eq!((family.as_str(), version), ("DomeLight", 1));
    ///
    /// let (family, version) = SchemaRegistry::parse_identifier(&tf::Token::new("DomeLight"));
    /// assert_eq!((family.as_str(), version), ("DomeLight", 0));
    /// ```
    pub fn parse_identifier(identifier: &tf::Token) -> (tf::Token, u32) {
        match version_delimiter(identifier.as_str()) {
            // A version that does not fit a `u32` is treated as absent, which
            // keeps the identifier addressable under its own full name.
            Some(delim) => match identifier[delim + 1..].parse() {
                Ok(version) => (tf::Token::from(&identifier[..delim]), version),
                Err(_) => (identifier.clone(), 0),
            },
            None => (identifier.clone(), 0),
        }
    }

    /// Builds the identifier for a family and version
    /// (C++ `MakeSchemaIdentifierForFamilyAndVersion`). Version 0 is the bare
    /// family name.
    pub fn make_identifier(family: &tf::Token, version: u32) -> tf::Token {
        match version {
            0 => family.clone(),
            _ => tf::Token::from(format!("{family}_{version}")),
        }
    }

    /// Whether `family` may name a schema family (C++ `IsAllowedSchemaFamily`):
    /// a valid identifier that does not itself end in a version suffix.
    pub fn is_allowed_family(family: &tf::Token) -> bool {
        sdf::Path::is_valid_identifier(family.as_str()) && version_delimiter(family.as_str()).is_none()
    }

    /// Whether `identifier` may name a schema (C++ `IsAllowedSchemaIdentifier`):
    /// an allowed family plus a canonical version suffix, so `Foo_01` and
    /// `Foo_1_2` are rejected.
    pub fn is_allowed_identifier(identifier: &tf::Token) -> bool {
        let (family, version) = Self::parse_identifier(identifier);
        Self::is_allowed_family(&family) && &Self::make_identifier(&family, version) == identifier
    }
}

impl VersionFilter {
    /// Whether `version` passes this filter.
    pub fn accepts(self, version: u32) -> bool {
        match self {
            Self::All => true,
            Self::GreaterThan(other) => version > other,
            Self::GreaterThanOrEqual(other) => version >= other,
            Self::LessThan(other) => version < other,
            Self::LessThanOrEqual(other) => version <= other,
        }
    }
}

impl SchemaInfo {
    /// The name this schema is registered and referenced under.
    pub fn identifier(&self) -> &tf::Token {
        &self.identifier
    }

    /// The identifier with any version suffix removed.
    pub fn family(&self) -> &tf::Token {
        &self.family
    }

    /// The version parsed from the identifier's suffix; 0 when it has none.
    pub fn version(&self) -> u32 {
        self.version
    }

    /// How this schema applies to a prim.
    pub fn kind(&self) -> SchemaKind {
        self.kind
    }

    /// The schemas this one directly derives from, nearest first, as the
    /// family manifest declares them. [`SchemaRegistry::is_a`] walks them
    /// transitively.
    pub fn bases(&self) -> &[tf::Token] {
        &self.bases
    }

    /// The namespace every property of a multiple-apply schema sits under, when
    /// the family declares one.
    pub fn property_namespace_prefix(&self) -> Option<&tf::Token> {
        self.property_namespace_prefix.as_ref()
    }

    /// Schema identifiers this API schema is automatically applied to
    /// (C++ `apiSchemaAutoApplyTo`), from the family manifest and any
    /// [`SchemaRegistryBuilder::auto_apply`] declaration.
    pub fn auto_apply_to(&self) -> &[tf::Token] {
        &self.auto_apply_to
    }

    /// Schema identifiers this API schema may be applied to
    /// (C++ `apiSchemaCanOnlyApplyTo`); empty means unrestricted.
    pub fn can_only_apply_to(&self) -> &[tf::Token] {
        &self.can_only_apply_to
    }

    /// Instance names a multiple-apply schema accepts; empty means any.
    pub fn allowed_instance_names(&self) -> &[tf::Token] {
        &self.allowed_instance_names
    }

    /// Whether this schema is applied through a prim's `apiSchemas` list.
    pub fn is_applied_api(&self) -> bool {
        matches!(self.kind, SchemaKind::SingleApplyApi | SchemaKind::MultipleApplyApi)
    }
}

impl Schematics {
    /// The family these class prims came from.
    pub fn family(&self) -> &tf::Token {
        &self.family
    }

    /// Where these class prims were resolved from, as
    /// [`FamilySource::resolved_location`] gave it.
    pub fn resolved_location(&self) -> Option<&ar::ResolvedPath> {
        self.resolved_location.as_ref()
    }

    /// The parsed class prims, keyed by `/<SchemaIdentifier>`.
    pub fn data(&self) -> &sdf::Data {
        &self.data
    }
}

impl SchemaRegistryBuilder {
    /// The families compiled into this crate.
    ///
    /// Registers nothing today: the registry machinery ships ahead of the
    /// OpenUSD schema data, so importing `generatedSchema.usda` for the core
    /// and domain families is still outstanding.
    // TODO: register the vendored core and per-feature family schematics here
    // once the OpenUSD schema data is imported.
    pub fn compiled_in() -> Self {
        Self::default()
    }

    /// Registers one schema family.
    ///
    /// `schematics` is a flattened layer of class prims, one per schema, named
    /// after the schema identifier — either `class "CollectionAPI"` or, for a
    /// concrete type, `class Sphere "Sphere"`. Every property a schema defines
    /// sits on its class prim, with its fallback as the property's default
    /// value.
    ///
    /// `manifest` supplies what flattening drops: one `def` prim per schema
    /// identifier carrying uniform attributes.
    ///
    /// ```usda
    /// #usda 1.0
    ///
    /// def "CollectionAPI"
    /// {
    ///     uniform token schemaKind = "multipleApplyAPI"
    ///     uniform token[] bases = ["APISchemaBase"]
    /// }
    /// ```
    ///
    /// `schemaKind` is required and must be one of the spellings
    /// [`SchemaKind::as_str`] produces. `bases` lists the schema's *direct*
    /// bases, nearest first, by schema identifier rather than by the C++ type
    /// name `plugInfo.json` records, and may name a schema registered by
    /// another family; [`SchemaRegistry::is_a`] walks them transitively.
    ///
    /// The optional `propertyNamespacePrefix`, `apiSchemaAutoApplyTo`,
    /// `apiSchemaCanOnlyApplyTo` and `allowedInstanceNames` attributes map onto
    /// the matching [`SchemaInfo`] accessors.
    ///
    /// `apiSchemaAutoApplyTo` auto-applies the declaring API schema to the
    /// named target schemas, under the same rules as a declaration registered
    /// through [`auto_apply`](Self::auto_apply).
    ///
    /// Errors when [`resolved_location`](FamilySource::resolved_location) is
    /// present but empty, which is a resolver's way of saying it found nothing.
    // TODO: take the schematics through `sdf::FileFormat` so a family can ship
    // a binary `generatedSchema.usdc`, as C++ does by opening it as a layer.
    // Opening it as a layer also subsumes `FamilySource::resolved_location`:
    // the layer carries its own `anchor_location`, so no caller has to supply
    // one and none can supply a wrong one.
    pub fn family(mut self, source: FamilySource<'_>) -> Result<Self> {
        let family = tf::Token::from(source.name);

        if source.resolved_location.is_some_and(|location| location.is_empty()) {
            bail!("Schema family {family} was registered with an empty resolved location");
        }

        let schematics = Arc::new(Schematics {
            family: family.clone(),
            resolved_location: source.resolved_location.cloned(),
            data: usda::parse(source.schematics)
                .with_context(|| format!("Unable to parse schematics for schema family {family}"))?,
        });

        let manifest = usda::parse(source.manifest)
            .with_context(|| format!("Unable to parse manifest for schema family {family}"))?;

        for identifier in root_prims(&manifest) {
            let info = read_schema_info(&manifest, &identifier)
                .with_context(|| format!("Unable to read schema {identifier} of family {family}"))?;

            if !SchemaRegistry::is_allowed_identifier(&identifier) {
                bail!("Schema identifier {identifier} of family {family} is not a valid identifier");
            }
            // An allowed identifier is exactly its family plus its version, so
            // rejecting a repeat identifier also rejects a repeated
            // (family, version).
            if self.infos.contains_key(&identifier) {
                bail!("Duplicate schema identifier {identifier} registering family {family}");
            }
            self.source_of.insert(identifier.clone(), schematics.clone());
            self.infos.insert(identifier, info);
        }

        Ok(self)
    }

    /// Auto-applies an API schema to schemas whose families do not declare it
    /// (C++ `CollectAddtlAutoApplyAPISchemasFromPlugins`).
    ///
    /// A family declares its own auto-applies through the manifest's
    /// `apiSchemaAutoApplyTo`; this registers one that no manifest carries,
    /// which is what lets an API schema reach a type owned by a family it
    /// cannot edit. Both sources follow the same rules: `targets` name
    /// schemas by identifier, each carrying everything derived from it, and
    /// only a single-apply API schema is applied — applying a multiple-apply
    /// one takes an instance name, which no declaration supplies.
    ///
    /// Neither side has to be registered yet: [`build`](Self::build) resolves
    /// the declaration, and one that names no registered schema resolves to
    /// nothing. A merged declaration reads back through
    /// [`SchemaInfo::auto_apply_to`] beside what the manifest declares.
    pub fn auto_apply(
        mut self,
        api: impl Into<tf::Token>,
        targets: impl IntoIterator<Item = impl Into<tf::Token>>,
    ) -> Self {
        self.extra_auto_apply
            .entry(api.into())
            .or_default()
            .extend(targets.into_iter().map(Into::into));
        self
    }

    /// Composes the registered families into a registry.
    ///
    /// Auto-apply declarations resolve first, since they decide which API
    /// schemas a definition builds in. Applied API schemas are defined next
    /// and fully expanded, so a typed schema that includes one picks up
    /// everything that schema itself includes.
    pub fn build(mut self) -> Result<Arc<SchemaRegistry>> {
        // TODO: report an auto-apply declaration that resolves to nothing —
        // an API schema name no family registered (dropped here) or one that
        // is not single-apply (ignored by `compute_auto_applied`). C++ lets
        // such a name flow into definition composition, which warns through
        // `TF_WARN`; this crate has no diagnostic channel for a registry
        // build to carry the report out through.
        for (api, targets) in mem::take(&mut self.extra_auto_apply) {
            if let Some(info) = self.infos.get_mut(&api) {
                info.auto_apply_to.extend(targets);
            }
        }
        let auto_applied = self.compute_auto_applied();

        let mut api_defs = HashMap::new();
        for identifier in self.sorted_identifiers(SchemaInfo::is_applied_api) {
            if api_defs.contains_key(&identifier) {
                continue;
            }
            let mut expansion = Expansion::default();
            self.expand_api_definition(&identifier, &auto_applied, &mut api_defs, &mut expansion)?;
            // Whatever this root reached while a cycle was open saw only part of
            // its own built-ins. Drop those so each is rebuilt from its own
            // root, where the cycle truncates at the schema that closes it. The
            // root itself was expanded from the top, so it stands.
            expansion.provisional.remove(&identifier);
            for identifier in expansion.provisional {
                api_defs.remove(&identifier);
            }
        }

        let mut concrete_defs = HashMap::new();
        for identifier in self.sorted_identifiers(|info| info.kind == SchemaKind::ConcreteTyped) {
            let definition = self.typed_definition(&identifier, &auto_applied, &api_defs)?;
            concrete_defs.insert(identifier, Arc::new(definition));
        }

        // A family answers newest version first, so the index is ordered here,
        // keyed on the version each identifier carries.
        let mut grouped: HashMap<tf::Token, Vec<(u32, tf::Token)>> = HashMap::new();
        for (identifier, info) in &self.infos {
            grouped
                .entry(info.family.clone())
                .or_default()
                .push((info.version, identifier.clone()));
        }
        let families = grouped
            .into_iter()
            .map(|(family, mut versions)| {
                versions.sort_unstable_by_key(|(version, _)| Reverse(*version));
                (family, versions.into_iter().map(|(_, identifier)| identifier).collect())
            })
            .collect();

        let empty_def = Arc::new(PrimDefinition::default());
        Ok(Arc::new(SchemaRegistry {
            infos: self.infos,
            families,
            concrete_defs,
            api_defs,
            empty_def: empty_def.clone(),
            empty_type_info: Arc::new(PrimTypeInfo::new(
                PrimTypeId::default(),
                tf::Token::default(),
                empty_def,
            )),
            type_infos: RwLock::default(),
        }))
    }

    /// Inverts every auto-apply declaration into the API schemas each schema
    /// builds in (C++ `_GetTypeToAutoAppliedAPISchemaNames`), expanding each
    /// target to the subtree derived from it and dropping what
    /// [`auto_apply`](Self::auto_apply)'s rules exclude.
    ///
    /// Each schema's list is sorted in reverse dictionary order, which places
    /// a later version of a family ahead of an earlier one. Composition takes
    /// one version per family, so that ordering is what makes the newest
    /// auto-applied version of a family the one that contributes.
    fn compute_auto_applied(&self) -> AutoApplied {
        // The base graph reversed, mapping each schema to the schemas
        // directly derived from it.
        let mut derived: HashMap<&tf::Token, Vec<&tf::Token>> = HashMap::new();
        for (identifier, info) in &self.infos {
            for base in &info.bases {
                derived.entry(base).or_default().push(identifier);
            }
        }

        let mut auto_applied = AutoApplied::new();
        for (api, info) in &self.infos {
            if info.kind != SchemaKind::SingleApplyApi {
                continue;
            }
            let mut pending: Vec<&tf::Token> = info
                .auto_apply_to
                .iter()
                .filter(|target| self.infos.contains_key(*target))
                .collect();

            // A manifest is data, so the bases it declares can cycle; the
            // reached set makes the walk terminate on that, and keeps a schema
            // reachable through two targets from building the API in twice.
            let mut reached = HashSet::new();
            while let Some(target) = pending.pop() {
                if !reached.insert(target) {
                    continue;
                }
                pending.extend(derived.get(target).into_iter().flatten().copied());
            }

            for target in reached {
                auto_applied.entry(target.clone()).or_default().push(api.clone());
            }
        }

        for names in auto_applied.values_mut() {
            names.sort_unstable_by(|a, b| sdf::element_cmp(b, a));
        }
        auto_applied
    }

    /// The registered identifiers matching `wanted`, in a stable order so a
    /// registry built twice from the same families is identical.
    fn sorted_identifiers(&self, wanted: impl Fn(&SchemaInfo) -> bool) -> Vec<tf::Token> {
        let mut identifiers: Vec<tf::Token> = self
            .infos
            .iter()
            .filter(|(_, info)| wanted(info))
            .map(|(identifier, _)| identifier.clone())
            .collect();
        identifiers.sort_by(|a, b| sdf::element_cmp(a, b));
        identifiers
    }

    /// Builds an applied API schema's definition, with the definitions of the
    /// API schemas it includes composed in beneath it.
    ///
    /// A schema that includes itself, directly or through another, stops
    /// expanding at the repeat and registers what it had reached by then.
    fn expand_api_definition(
        &self,
        identifier: &tf::Token,
        auto_applied: &AutoApplied,
        api_defs: &mut HashMap<tf::Token, Arc<PrimDefinition>>,
        expansion: &mut Expansion,
    ) -> Result<()> {
        if api_defs.contains_key(identifier) {
            return Ok(());
        }
        if !expansion.open.insert(identifier.clone()) {
            // The schema includes itself, directly or through another. Stop
            // here; everything still open is composing a partial view of its
            // own built-ins.
            expansion.truncated = true;
            return Ok(());
        }

        let mut pending = self.begin_definition(identifier, auto_applied)?;
        for name in mem::take(&mut pending.built_ins) {
            let (built_in, instance) = split_instance_name(&name);
            // A built-in no family registered contributes nothing; the schema
            // that names it is still worth defining.
            if !self.infos.contains_key(&built_in) {
                continue;
            }
            self.expand_api_definition(&built_in, auto_applied, api_defs, expansion)?;
            pending.compose_built_in(&built_in, instance.as_ref(), api_defs, &self.infos);
        }

        expansion.open.remove(identifier);
        if expansion.truncated {
            expansion.provisional.insert(identifier.clone());
        }
        api_defs.insert(identifier.clone(), Arc::new(pending.finish()));
        Ok(())
    }

    /// Builds a typed schema's definition. Its own properties are strongest;
    /// each built-in API schema contributes beneath them, in declared order.
    fn typed_definition(
        &self,
        identifier: &tf::Token,
        auto_applied: &AutoApplied,
        api_defs: &HashMap<tf::Token, Arc<PrimDefinition>>,
    ) -> Result<PrimDefinition> {
        let mut pending = self.begin_definition(identifier, auto_applied)?;
        for name in mem::take(&mut pending.built_ins) {
            let (built_in, instance) = split_instance_name(&name);
            pending.compose_built_in(&built_in, instance.as_ref(), api_defs, &self.infos);
        }
        Ok(pending.finish())
    }

    /// Starts one schema's definition from its own class prim, before any
    /// built-in API schema contributes.
    fn begin_definition(&self, identifier: &tf::Token, auto_applied: &AutoApplied) -> Result<PendingDefinition> {
        let info = self
            .infos
            .get(identifier)
            .with_context(|| format!("No manifest entry for schema {identifier}"))?;
        let schematics = self
            .source_of
            .get(identifier)
            .with_context(|| format!("No schematics registered for schema {identifier}"))?
            .clone();

        let class_prim = sdf::Path::abs_root().append_path(identifier.as_str())?;
        let overrides = override_property_names(&schematics, &class_prim);

        // A multiple-apply schema is a template: it contributes under a name
        // carrying the instance-name placeholder until an instance is chosen.
        let applied_name = match info.kind {
            SchemaKind::MultipleApplyApi => Some(make_name_template(identifier)),
            SchemaKind::SingleApplyApi => Some(identifier.clone()),
            _ => None,
        };

        // Claim this schema's own family version up front, so a built-in that
        // names a different version of the same family is refused rather than
        // composed in beside it. The claim is keyed the way the schema's own
        // applied name is, so a multiple-apply schema claims the placeholder
        // instance its template contributes under — otherwise the conflict goes
        // unnoticed until an instance name is chosen, where the rollback
        // discards the whole definition instead of just the bad built-in.
        //
        // C++ always claims the empty instance here, with an `XXX` noting the
        // multiple-apply case needs revisiting.
        let mut seen = FamilyVersions::new();
        if info.is_applied_api() {
            let instance = applied_name.as_ref().and_then(|name| split_instance_name(name).1);
            seen.insert((info.family.clone(), instance), info.version);
        }

        Ok(PendingDefinition {
            definition: PrimDefinition::from_class_prim(&schematics, identifier, applied_name, &overrides)?,
            built_ins: self.direct_built_ins(&schematics, &class_prim, info, auto_applied),
            schematics,
            class_prim,
            overrides,
            seen,
        })
    }

    /// The API schemas a class prim declares as built in, followed by the ones
    /// auto-applied to it (C++ `_GetDirectBuiltinAPISchemas`).
    ///
    /// An auto-applied schema comes last, so everything the class prim
    /// declares is stronger than anything applied to it from outside.
    ///
    /// A multiple-apply schema may only include other templates, and any other
    /// schema may only include non-templates: a template's properties are only
    /// meaningful once an instance name replaces the placeholder, so mixing the
    /// two would leave a placeholder in a concrete prim's properties. Names on
    /// the wrong side of that rule are dropped, which is also what keeps an
    /// auto-applied schema — never a template — out of a multiple-apply one.
    fn direct_built_ins(
        &self,
        schematics: &Schematics,
        class_prim: &sdf::Path,
        info: &SchemaInfo,
        auto_applied: &AutoApplied,
    ) -> Vec<tf::Token> {
        let declared = class_prim_field(schematics, class_prim, sdf::FieldKey::ApiSchemas)
            .and_then(|value| value.clone().try_as_token_list_op())
            .map(|list_op| list_op.compose_over(&[]))
            .unwrap_or_default();
        let auto_applied = auto_applied.get(info.identifier()).into_iter().flatten().cloned();

        let wants_templates = info.kind == SchemaKind::MultipleApplyApi;
        declared
            .into_iter()
            .chain(auto_applied)
            .filter(|name| is_name_template(name) == wants_templates)
            .filter(|name| {
                // The reference also has to agree with what it names: only a
                // multiple-apply schema is applied under an instance name, so a
                // single-apply schema dressed as a template would compose its
                // properties without the instance the name promises. A built-in
                // no family registered names no schema, so it drops here too.
                check_applied_shape(&self.infos, name).is_ok_and(|resolved| resolved.is_some())
            })
            .collect()
    }
}

/// Which API schemas are auto-applied to each schema identifier, strongest
/// first (C++ `_typeToAutoAppliedAPISchemaNames`).
type AutoApplied = HashMap<tf::Token, Vec<tf::Token>>;

/// State threaded through one root's recursive built-in expansion.
#[derive(Default)]
struct Expansion {
    /// The schemas whose expansion is still open, so a repeat is a cycle.
    open: HashSet<tf::Token>,
    /// Whether a cycle was reached anywhere under this root.
    truncated: bool,
    /// Definitions completed while a cycle was open, and so possibly missing
    /// built-ins. They are dropped once the root finishes.
    provisional: HashSet<tf::Token>,
}

/// A definition part-way through its build: the schema's own properties are
/// installed, and the built-in API schemas and property overrides still have to
/// be composed in.
///
/// Typed and applied API schemas share this shape; they differ only in how each
/// built-in's definition is obtained, which is why the caller drives the loop.
struct PendingDefinition {
    definition: PrimDefinition,
    /// The API schemas the class prim declares as built in, strongest first.
    built_ins: Vec<tf::Token>,
    schematics: Arc<Schematics>,
    class_prim: sdf::Path,
    /// Properties the class prim declares only to override a built-in's,
    /// composed once every built-in has contributed.
    overrides: Vec<tf::Token>,
    seen: FamilyVersions,
}

impl PendingDefinition {
    /// Composes one already-built built-in schema in as a weaker tier.
    fn compose_built_in(
        &mut self,
        built_in: &tf::Token,
        instance: Option<&tf::Token>,
        api_defs: &HashMap<tf::Token, Arc<PrimDefinition>>,
        infos: &HashMap<tf::Token, SchemaInfo>,
    ) {
        if let Some(weaker) = api_defs.get(built_in) {
            self.definition
                .compose_weaker_api(weaker, instance, infos, &mut self.seen);
        }
    }

    /// Applies the class prim's property overrides over what the built-ins
    /// contributed, yielding the finished definition.
    fn finish(mut self) -> PrimDefinition {
        for name in &self.overrides {
            self.definition
                .compose_override(name, &self.schematics, &self.class_prim);
        }
        self.definition.finish_composition();
        self.definition
    }
}

/// The property names a class prim declares only to override a built-in API
/// schema's, read from its `customData` (C++
/// `apiSchemaOverridePropertyNames`).
fn override_property_names(schematics: &Schematics, class_prim: &sdf::Path) -> Vec<tf::Token> {
    const OVERRIDE_NAMES: &str = "apiSchemaOverridePropertyNames";

    class_prim_field(schematics, class_prim, sdf::FieldKey::CustomData)
        .and_then(|value| value.clone().try_as_dictionary())
        .and_then(|mut custom_data| custom_data.remove(OVERRIDE_NAMES))
        .and_then(sdf::Value::try_as_token_vec)
        .unwrap_or_default()
}

/// Reads one field off a schema's class prim.
fn class_prim_field<'a>(
    schematics: &'a Schematics,
    class_prim: &sdf::Path,
    field: sdf::FieldKey,
) -> Option<&'a sdf::Value> {
    schematics.data().spec(class_prim)?.get(field.as_str())
}

/// The rule behind [`SchemaRegistry::check_applied_name`], over the schema
/// table alone so the builder can apply it before a registry exists.
///
/// `Ok(None)` for a name `infos` has no schema for.
fn check_applied_shape<'a>(
    infos: &'a HashMap<tf::Token, SchemaInfo>,
    name: &tf::Token,
) -> Result<Option<(&'a SchemaInfo, Option<tf::Token>)>, ApplyApiError> {
    let (schema, instance) = split_instance_name(name);
    let Some(info) = infos.get(&schema) else {
        return Ok(None);
    };
    if !info.is_applied_api() {
        return Err(ApplyApiError::NotAppliedApi { schema });
    }

    match (info.kind == SchemaKind::MultipleApplyApi, instance) {
        (true, None) => Err(ApplyApiError::MissingInstanceName { schema }),
        (false, Some(instance)) => Err(ApplyApiError::UnexpectedInstanceName { schema, instance }),
        (_, instance) => Ok(Some((info, instance))),
    }
}

/// The placeholder that stands in for an instance name in a multiple-apply
/// schema's property and built-in names (C++ `__INSTANCE_NAME__`).
const INSTANCE_NAME_PLACEHOLDER: &str = "__INSTANCE_NAME__";

/// Splits an applied-schema name into its schema identifier and, when the name
/// is an instance of a multiple-apply schema, its instance name
/// (C++ `GetTypeNameAndInstance`).
///
/// The split is at the first namespace delimiter: an identifier can never
/// contain one, while an instance name can.
///
/// A name carries an instance only when there is one to carry, so a trailing
/// delimiter (`CollectionAPI:`) reads as the bare identifier — C++ decides the
/// same question as `!instanceName.IsEmpty()`.
pub(super) fn split_instance_name(name: &tf::Token) -> (tf::Token, Option<tf::Token>) {
    match name.split_once(':') {
        Some((identifier, instance)) if !instance.is_empty() => {
            (tf::Token::from(identifier), Some(tf::Token::from(instance)))
        }
        Some((identifier, _)) => (tf::Token::from(identifier), None),
        None => (name.clone(), None),
    }
}

/// The name a multiple-apply schema's definition is applied under before any
/// instance name is chosen (C++ `MakeMultipleApplyNameTemplate`).
pub(super) fn make_name_template(identifier: &tf::Token) -> tf::Token {
    tf::Token::from(format!("{identifier}:{INSTANCE_NAME_PLACEHOLDER}"))
}

/// Substitutes `instance` for the placeholder in a multiple-apply template
/// name (C++ `MakeMultipleApplyNameInstance`).
///
/// Only the first placeholder component is replaced, so a nested template like
/// `Other:__INSTANCE_NAME__:foo` instantiates to `Other:<instance>:foo`. A name
/// with no placeholder is returned unchanged.
pub(super) fn make_instance_name(template: &tf::Token, instance: &tf::Token) -> tf::Token {
    match placeholder_position(template) {
        Some(start) => {
            let mut name = String::with_capacity(template.len() + instance.len());
            name.push_str(&template[..start]);
            name.push_str(instance);
            name.push_str(&template[start + INSTANCE_NAME_PLACEHOLDER.len()..]);
            tf::Token::from(name)
        }
        None => template.clone(),
    }
}

/// The part of a multiple-apply property name that follows the instance-name
/// placeholder (C++ `GetMultipleApplyNameTemplateBaseName`).
///
/// `collection:__INSTANCE_NAME__:includeRoot` bases to `includeRoot`; a name
/// ending at the placeholder bases to nothing, and one without a placeholder is
/// its own base.
pub(super) fn name_template_base(name: &tf::Token) -> &str {
    match placeholder_position(name) {
        Some(start) => name
            .get(start + INSTANCE_NAME_PLACEHOLDER.len() + 1..)
            .unwrap_or_default(),
        None => name,
    }
}

/// Whether `name` still carries the instance-name placeholder, which is what
/// distinguishes a multiple-apply template from an applied instance
/// (C++ `IsMultipleApplyNameTemplate`).
pub(super) fn is_name_template(name: &tf::Token) -> bool {
    placeholder_position(name).is_some()
}

/// Where the placeholder starts, matched as a whole namespace component so a
/// property merely containing the text does not count.
fn placeholder_position(name: &tf::Token) -> Option<usize> {
    let mut start = 0;
    for component in name.split(':') {
        if component == INSTANCE_NAME_PLACEHOLDER {
            return Some(start);
        }
        start += component.len() + 1;
    }
    None
}

/// The names of a parsed layer's root prims, in authored order.
fn root_prims(data: &sdf::Data) -> Vec<tf::Token> {
    prim_definition::child_names(data, &sdf::Path::abs_root(), sdf::ChildrenKey::PrimChildren)
}

/// Reads one schema's manifest entry from the prim at `/<identifier>`.
fn read_schema_info(manifest: &sdf::Data, identifier: &tf::Token) -> Result<SchemaInfo> {
    let prim = sdf::Path::abs_root().append_path(identifier.as_str())?;

    let kind = manifest_token(manifest, &prim, "schemaKind").context("schemaKind is required")?;
    let kind = SchemaKind::from_token(kind.as_str()).with_context(|| format!("Unknown schemaKind {kind}"))?;

    let (family, version) = SchemaRegistry::parse_identifier(identifier);

    Ok(SchemaInfo {
        identifier: identifier.clone(),
        family,
        version,
        kind,
        bases: manifest_token_vec(manifest, &prim, "bases"),
        property_namespace_prefix: manifest_token(manifest, &prim, "propertyNamespacePrefix"),
        auto_apply_to: manifest_token_vec(manifest, &prim, "apiSchemaAutoApplyTo"),
        can_only_apply_to: manifest_token_vec(manifest, &prim, "apiSchemaCanOnlyApplyTo"),
        allowed_instance_names: manifest_token_vec(manifest, &prim, "allowedInstanceNames"),
    })
}

/// Reads a manifest attribute's default value as a token.
fn manifest_token(manifest: &sdf::Data, prim: &sdf::Path, attribute: &str) -> Option<tf::Token> {
    manifest_default(manifest, prim, attribute)?.clone().try_as_token()
}

/// Reads a manifest attribute's default value as a token array, treating an
/// absent attribute as empty.
fn manifest_token_vec(manifest: &sdf::Data, prim: &sdf::Path, attribute: &str) -> Vec<tf::Token> {
    manifest_default(manifest, prim, attribute)
        .and_then(|value| value.clone().try_as_token_vec())
        .unwrap_or_default()
}

/// Reads the `default` field of a manifest attribute.
fn manifest_default<'a>(manifest: &'a sdf::Data, prim: &sdf::Path, attribute: &str) -> Option<&'a sdf::Value> {
    let path = prim.append_property(attribute).ok()?;
    manifest.spec(&path)?.get(sdf::FieldKey::Default.as_str())
}

/// Locates a schema identifier's version suffix: the index of the underscore
/// that is followed by digits only, with at least one digit.
///
/// Mirrors C++ `_FindVersionDelimiter`, which scans back from the end and
/// stops at the first character that is neither a digit nor the delimiter.
fn version_delimiter(identifier: &str) -> Option<usize> {
    let stem = identifier.trim_end_matches(|c: char| c.is_ascii_digit());
    if stem.len() == identifier.len() {
        return None;
    }
    stem.strip_suffix('_').map(str::len)
}

/// A miniature family shaped like the real OpenUSD schema data, shared by
/// every module's tests so they exercise the same topology the vendored data
/// will: a multiple-apply schema whose properties carry the instance-name
/// placeholder, a single-apply schema that declares a built-in and overrides
/// one of its properties, and a concrete type that in turn overrides one of
/// its own built-in's properties.
#[cfg(test)]
impl SchemaRegistry {
    const TEST_MANIFEST: &'static str = r#"#usda 1.0

def "APISchemaBase"
{
    uniform token schemaKind = "abstractBase"
}

def "Typed"
{
    uniform token schemaKind = "abstractBase"
}

def "CollectionAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
    uniform token[] bases = ["APISchemaBase"]
}

def "SlotAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
    uniform token[] bases = ["APISchemaBase"]
    uniform token[] allowedInstanceNames = ["left", "right"]
    uniform token[] apiSchemaCanOnlyApplyTo = ["NonboundableLightBase"]
}

def "LightAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] bases = ["APISchemaBase"]
    uniform token[] apiSchemaCanOnlyApplyTo = ["DistantLight"]
}

def "LightAPI_2"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] bases = ["APISchemaBase"]
}

def "NonboundableLightBase"
{
    uniform token schemaKind = "abstractTyped"
    uniform token[] bases = ["Typed"]
}

def "DistantLight"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["NonboundableLightBase"]
}

def "DomeLight"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["NonboundableLightBase"]
}

def "DomeLight_1"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["NonboundableLightBase"]
}
"#;

    const TEST_SCHEMATICS: &'static str = r#"#usda 1.0

class "APISchemaBase"
{
}

class "Typed"
{
}

class "CollectionAPI"
{
    uniform token collection:__INSTANCE_NAME__:expansionRule = "expandPrims" (
        allowedTokens = ["explicitOnly", "expandPrims", "expandPrimsAndProperties"]
    )
    uniform bool collection:__INSTANCE_NAME__:includeRoot
    rel collection:__INSTANCE_NAME__:includes
}

class "LightAPI" (
    apiSchemas = ["CollectionAPI:lightLink"]
    customData = {
        token[] apiSchemaOverridePropertyNames = ["collection:lightLink:includeRoot"]
    }
)
{
    uniform bool collection:lightLink:includeRoot = 1
    float inputs:intensity = 1
    uniform token light:shaderId = ""
}

class "SlotAPI"
{
    float slot:__INSTANCE_NAME__:depth = 0
}

class "LightAPI_2"
{
    float inputs:intensity = 2
}

class "NonboundableLightBase"
{
}

class DistantLight "DistantLight" (
    apiSchemas = ["LightAPI"]
    customData = {
        token[] apiSchemaOverridePropertyNames = ["inputs:intensity", "light:shaderId"]
    }
)
{
    float inputs:angle = 0.53
    float inputs:intensity = 50000
    uniform token light:shaderId = "DistantLight"
}

class DomeLight "DomeLight"
{
    float inputs:intensity = 1
}

class DomeLight_1 "DomeLight_1"
{
    float inputs:intensity = 1
    uniform token poleAxis = "scene"
}
"#;

    /// The miniature family, registered.
    pub(crate) fn test_registry() -> Arc<SchemaRegistry> {
        Self::test_family(Self::TEST_MANIFEST, Self::TEST_SCHEMATICS)
    }

    /// A registry of one family built from the given manifest and schematics.
    pub(crate) fn test_family(manifest: &str, schematics: &str) -> Arc<SchemaRegistry> {
        Self::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics,
                resolved_location: None,
            })
            .expect("test family registers")
            .build()
            .expect("test registry builds")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn manifest_infos() {
        let registry = SchemaRegistry::test_registry();

        let light = registry.schema_info(&tf::Token::new("LightAPI")).expect("LightAPI");
        assert_eq!(light.kind(), SchemaKind::SingleApplyApi);
        assert_eq!(light.bases(), [tf::Token::new("APISchemaBase")]);
        assert_eq!(light.can_only_apply_to(), [tf::Token::new("DistantLight")]);
        assert!(light.is_applied_api());

        let collection = registry
            .schema_info(&tf::Token::new("CollectionAPI"))
            .expect("CollectionAPI");
        assert_eq!(collection.kind(), SchemaKind::MultipleApplyApi);
        assert!(collection.auto_apply_to().is_empty());

        assert!(registry.schema_info(&tf::Token::new("Nonexistent")).is_none());
    }

    #[test]
    fn is_a_walks_bases() {
        let registry = SchemaRegistry::test_registry();
        let distant = tf::Token::new("DistantLight");

        // A type is itself, its direct base, and every base above that.
        assert!(registry.is_a(&distant, &distant));
        assert!(registry.is_a(&distant, &tf::Token::new("NonboundableLightBase")));
        assert!(registry.is_a(&distant, &tf::Token::new("Typed")));

        // Siblings and unrelated hierarchies do not match.
        assert!(!registry.is_a(&distant, &tf::Token::new("DomeLight_1")));
        assert!(!registry.is_a(&distant, &tf::Token::new("APISchemaBase")));
        // An unregistered name is not a schema, so it derives from nothing and
        // nothing derives from it — not even itself.
        assert!(!registry.is_a(&tf::Token::new("Bogus"), &tf::Token::new("Typed")));
        assert!(!registry.is_a(&tf::Token::new("Bogus"), &tf::Token::new("Bogus")));
        assert!(!registry.is_a(&distant, &tf::Token::default()));
    }

    #[test]
    fn allowed_instance_names() {
        let registry = SchemaRegistry::test_registry();
        let slot = tf::Token::new("SlotAPI");
        let collection = tf::Token::new("CollectionAPI");

        // A declared list restricts the schema to those names.
        assert!(registry.is_allowed_instance_name(&slot, &tf::Token::new("left")));
        assert!(!registry.is_allowed_instance_name(&slot, &tf::Token::new("middle")));
        // No list means any name, and an empty name is never one.
        assert!(registry.is_allowed_instance_name(&collection, &tf::Token::new("anything")));
        assert!(!registry.is_allowed_instance_name(&collection, &tf::Token::default()));

        // Only a registered multiple-apply schema has instances at all.
        assert!(!registry.is_allowed_instance_name(&tf::Token::new("LightAPI"), &tf::Token::new("x")));
        assert!(!registry.is_allowed_instance_name(&tf::Token::new("Bogus"), &tf::Token::new("x")));
    }

    #[test]
    fn family_version_filters() {
        let registry = SchemaRegistry::test_registry();
        let dome = tf::Token::new("DomeLight");
        let identifiers = |family, filter| {
            registry
                .schema_infos_in_family(family, filter)
                .map(|info| info.identifier().to_string())
                .collect::<Vec<_>>()
        };

        // A family answers newest version first, whatever order it registered
        // in, so the first hit is the best match.
        assert_eq!(identifiers(&dome, VersionFilter::All), ["DomeLight_1", "DomeLight"]);
        assert_eq!(identifiers(&dome, VersionFilter::GreaterThan(0)), ["DomeLight_1"]);
        assert_eq!(
            identifiers(&dome, VersionFilter::GreaterThanOrEqual(1)),
            ["DomeLight_1"]
        );
        assert_eq!(identifiers(&dome, VersionFilter::LessThan(1)), ["DomeLight"]);
        assert_eq!(
            identifiers(&dome, VersionFilter::LessThanOrEqual(1)),
            ["DomeLight_1", "DomeLight"]
        );
        assert!(identifiers(&dome, VersionFilter::GreaterThan(1)).is_empty());

        // An unregistered family has no schemas rather than being an error.
        assert!(identifiers(&tf::Token::new("Bogus"), VersionFilter::All).is_empty());
    }

    #[test]
    fn identifier_places_family() {
        let placed = |name| SchemaRegistry::parse_allowed_identifier(&tf::Token::new(name));
        let family = |name| placed(name).map(|(family, _)| family.to_string());

        // An identifier carries its own family and version, registered or not.
        assert_eq!(placed("DomeLight_1"), Some((tf::Token::new("DomeLight"), 1)));
        assert_eq!(placed("DistantLight"), Some((tf::Token::new("DistantLight"), 0)));
        assert_eq!(family("Bogus_2").as_deref(), Some("Bogus"));

        // A spelling that could never name a registered schema is in no family:
        // a non-canonical version suffix, or one on the family itself.
        assert_eq!(placed("DomeLight_01"), None);
        assert_eq!(placed("DomeLight_1_2"), None);
        assert_eq!(placed("1Light"), None);

        // A family never carries a version suffix, so it names no schema under
        // one that does, even though `DomeLight_1` is registered.
        let registry = SchemaRegistry::test_registry();
        assert!(
            registry
                .schema_info_in_family(&tf::Token::new("DomeLight_1"), 0)
                .is_none()
        );
    }

    #[test]
    fn instance_name_identifier() {
        let registry = SchemaRegistry::test_registry();
        let collection = tf::Token::new("CollectionAPI");

        // The name becomes a namespace component of every instantiated
        // property, so it has to be spellable as one.
        for bad in ["", "my instance", "render:", ":render", "a::b", "1st", "in.dot"] {
            let instance = tf::Token::from(bad);
            assert!(
                !registry.is_allowed_instance_name(&collection, &instance),
                "accepted {bad:?}"
            );
        }

        // A namespaced name is still fine when every component is one.
        assert!(registry.is_allowed_instance_name(&collection, &tf::Token::new("a:b")));
    }

    #[test]
    fn instance_name_property_collision() {
        let registry = SchemaRegistry::test_registry();

        // `CollectionAPI` declares `collection:__INSTANCE_NAME__:includeRoot`,
        // so an instance named `includeRoot` would make the instantiated
        // property ambiguous with the schema's own.
        let collection = tf::Token::new("CollectionAPI");
        assert!(!registry.is_allowed_instance_name(&collection, &tf::Token::new("includeRoot")));

        // The comparison is against the property's base name, so a namespaced
        // instance is judged by its last component.
        assert!(!registry.is_allowed_instance_name(&collection, &tf::Token::new("a:includeRoot")));
        assert!(registry.is_allowed_instance_name(&collection, &tf::Token::new("includeRoot:a")));
    }

    #[test]
    fn name_template_bases() {
        let cases = [
            ("collection:__INSTANCE_NAME__:includeRoot", "includeRoot"),
            ("collection:__INSTANCE_NAME__", ""),
            ("inputs:intensity", "inputs:intensity"),
        ];
        for (name, base) in cases {
            assert_eq!(name_template_base(&tf::Token::new(name)), base, "basing {name}");
        }
    }

    #[test]
    fn versioned_identifier() {
        let registry = SchemaRegistry::test_registry();

        let dome = registry
            .schema_info(&tf::Token::new("DomeLight_1"))
            .expect("DomeLight_1");
        assert_eq!(dome.family().as_str(), "DomeLight");
        assert_eq!(dome.version(), 1);

        // A bare identifier is version 0 of its own family, so both versions
        // are addressable through the family index.
        let family = tf::Token::new("DomeLight");
        let versioned = registry.schema_info_in_family(&family, 1).expect("DomeLight version 1");
        assert_eq!(versioned.identifier().as_str(), "DomeLight_1");
        let bare = registry.schema_info_in_family(&family, 0).expect("DomeLight version 0");
        assert_eq!(bare.identifier().as_str(), "DomeLight");
        assert!(registry.schema_info_in_family(&family, 2).is_none());
    }

    #[test]
    fn parse_identifier_cases() {
        let cases = [
            ("DomeLight", "DomeLight", 0),
            ("DomeLight_1", "DomeLight", 1),
            ("DomeLight_12", "DomeLight", 12),
            // No digits after the delimiter, so there is no version suffix.
            ("DomeLight_", "DomeLight_", 0),
            // Not a suffix at all: the trailing digits have no delimiter.
            ("Basis2Curves", "Basis2Curves", 0),
            // The delimiter search stops at the last underscore.
            ("Foo_1_2", "Foo_1", 2),
            ("_1", "", 1),
        ];
        for (identifier, family, version) in cases {
            let parsed = SchemaRegistry::parse_identifier(&tf::Token::new(identifier));
            assert_eq!((parsed.0.as_str(), parsed.1), (family, version), "parsing {identifier}");
        }
    }

    #[test]
    fn allowed_identifiers() {
        assert!(SchemaRegistry::is_allowed_identifier(&tf::Token::new("DomeLight")));
        assert!(SchemaRegistry::is_allowed_identifier(&tf::Token::new("DomeLight_1")));
        // A non-canonical version suffix does not round-trip.
        assert!(!SchemaRegistry::is_allowed_identifier(&tf::Token::new("DomeLight_01")));
        // The family may not itself carry a version suffix.
        assert!(!SchemaRegistry::is_allowed_identifier(&tf::Token::new("Foo_1_2")));
        assert!(!SchemaRegistry::is_allowed_family(&tf::Token::new("2Foo")));
        assert!(SchemaRegistry::is_allowed_family(&tf::Token::new("_Foo")));
    }

    #[test]
    fn instance_name_math() {
        let template = tf::Token::new("collection:__INSTANCE_NAME__:includeRoot");
        assert!(is_name_template(&template));
        assert_eq!(
            make_instance_name(&template, &tf::Token::new("lightLink")),
            tf::Token::new("collection:lightLink:includeRoot")
        );

        // Only the first placeholder component is substituted, so a nested
        // template keeps the rest of its shape.
        let nested = tf::Token::new("Other:__INSTANCE_NAME__:foo");
        assert_eq!(
            make_instance_name(&nested, &tf::Token::new("bar")),
            tf::Token::new("Other:bar:foo")
        );

        // A name without the placeholder is left alone, and the placeholder is
        // matched as a whole component rather than as text.
        let plain = tf::Token::new("inputs:intensity");
        assert!(!is_name_template(&plain));
        assert_eq!(make_instance_name(&plain, &tf::Token::new("x")), plain);
        assert!(!is_name_template(&tf::Token::new("my__INSTANCE_NAME__thing")));

        assert_eq!(
            make_name_template(&tf::Token::new("CollectionAPI")),
            tf::Token::new("CollectionAPI:__INSTANCE_NAME__")
        );
    }

    #[test]
    fn instance_name_split() {
        let (identifier, instance) = split_instance_name(&tf::Token::new("CollectionAPI:lightLink"));
        assert_eq!(identifier, tf::Token::new("CollectionAPI"));
        assert_eq!(instance, Some(tf::Token::new("lightLink")));

        // An instance name may itself be namespaced; the identifier never is,
        // so the split is at the first delimiter.
        let (identifier, instance) = split_instance_name(&tf::Token::new("CollectionAPI:a:b"));
        assert_eq!(identifier, tf::Token::new("CollectionAPI"));
        assert_eq!(instance, Some(tf::Token::new("a:b")));

        let (identifier, instance) = split_instance_name(&tf::Token::new("LightAPI"));
        assert_eq!(identifier, tf::Token::new("LightAPI"));
        assert_eq!(instance, None);

        // A trailing delimiter carries no instance to name.
        let (identifier, instance) = split_instance_name(&tf::Token::new("CollectionAPI:"));
        assert_eq!(identifier, tf::Token::new("CollectionAPI"));
        assert_eq!(instance, None);
    }

    #[test]
    fn composed_typeless_prim() {
        let registry = SchemaRegistry::test_registry();
        let definition =
            registry.build_composed_prim_definition(&tf::Token::default(), &[tf::Token::new("CollectionAPI:render")]);

        // A prim with no type still gets everything its applied schemas declare.
        assert_eq!(
            definition.attribute_fallback(&tf::Token::new("collection:render:expansionRule")),
            Some(sdf::Value::token("expandPrims"))
        );
        assert_eq!(
            definition.applied_api_schemas(),
            [tf::Token::new("CollectionAPI:render")]
        );
    }

    #[test]
    fn composed_typed_beats_authored() {
        let registry = SchemaRegistry::test_registry();
        let definition = registry.build_composed_prim_definition(
            &tf::Token::new("DistantLight"),
            &[tf::Token::new("CollectionAPI:render")],
        );

        // The type's own override still wins over everything authored.
        assert_eq!(
            definition.attribute_fallback(&tf::Token::new("inputs:intensity")),
            Some(sdf::Value::Float(50000.0))
        );
        assert_eq!(
            definition.applied_api_schemas(),
            [
                tf::Token::new("LightAPI"),
                tf::Token::new("CollectionAPI:lightLink"),
                tf::Token::new("CollectionAPI:render"),
            ]
        );
    }

    #[test]
    fn composed_skips_duplicates_and_unknowns() {
        let registry = SchemaRegistry::test_registry();
        let definition = registry.build_composed_prim_definition(
            &tf::Token::new("DistantLight"),
            &[
                // Already built in through LightAPI.
                tf::Token::new("CollectionAPI:lightLink"),
                tf::Token::new("Unregistered"),
                // A multiple-apply schema needs an instance name, and a
                // single-apply one cannot take one.
                tf::Token::new("CollectionAPI"),
                tf::Token::new("LightAPI:instance"),
            ],
        );

        assert_eq!(
            definition.applied_api_schemas(),
            [tf::Token::new("LightAPI"), tf::Token::new("CollectionAPI:lightLink")]
        );
    }

    #[test]
    fn composed_with_no_applied_shares_typed() {
        let registry = SchemaRegistry::test_registry();
        let type_name = tf::Token::new("DistantLight");

        let composed = registry.build_composed_prim_definition(&type_name, &[]);
        assert!(Arc::ptr_eq(
            &composed,
            registry.concrete_prim_definition(&type_name).expect("DistantLight")
        ));

        // An unknown type with nothing applied is the shared empty definition.
        let unknown = registry.build_composed_prim_definition(&tf::Token::new("Bogus"), &[]);
        assert!(Arc::ptr_eq(&unknown, registry.empty_prim_definition()));
    }

    #[test]
    fn kind_round_trip() {
        let kinds = [
            SchemaKind::AbstractBase,
            SchemaKind::AbstractTyped,
            SchemaKind::ConcreteTyped,
            SchemaKind::NonAppliedApi,
            SchemaKind::SingleApplyApi,
            SchemaKind::MultipleApplyApi,
        ];
        for kind in kinds {
            assert_eq!(SchemaKind::from_token(kind.as_str()), Some(kind));
        }
        assert_eq!(SchemaKind::from_token("bogus"), None);
    }

    #[test]
    fn global_is_shared_and_empty() {
        assert!(Arc::ptr_eq(SchemaRegistry::global(), SchemaRegistry::global()));
        assert_eq!(SchemaRegistry::global().schema_infos().count(), 0);
    }
}
