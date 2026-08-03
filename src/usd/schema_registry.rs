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
//! [`SchemaRegistry::global`] is the lazily built process registry every
//! [`Stage`](super::Stage) uses by default. It currently registers no families
//! — the machinery is here, the OpenUSD schema data is not vendored yet — so
//! fallback lookups uniformly find nothing. Registering families through
//! [`SchemaRegistry::builder`] and handing the result to
//! [`StageBuilder::schema_registry`](super::StageBuilder::schema_registry)
//! works today.

use std::collections::{HashMap, HashSet};
use std::mem;
use std::sync::{Arc, OnceLock, PoisonError, RwLock};

use anyhow::{bail, Context, Result};

use crate::{sdf, tf, usda};

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
    /// Reverse index over [`SchemaInfo::family`] and [`SchemaInfo::version`],
    /// so a versioned family can be queried without scanning `infos`.
    by_family: HashMap<(tf::Token, u32), tf::Token>,
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
}

/// Accumulates schema families into a [`SchemaRegistry`].
///
/// Each [`family`](Self::family) call parses one family's manifest and
/// schematics; [`build`](Self::build) then composes the prim definitions that
/// need every family present, such as a typed schema whose built-in API schema
/// comes from another family.
#[derive(Debug, Default)]
pub struct SchemaRegistryBuilder {
    infos: HashMap<tf::Token, SchemaInfo>,
    by_family: HashMap<(tf::Token, u32), tf::Token>,
    /// Which family's schematics holds each identifier's class prim.
    source_of: HashMap<tf::Token, Arc<Schematics>>,
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
    pub fn schema_info_in_family(&self, family: &tf::Token, version: u32) -> Option<&SchemaInfo> {
        let identifier = self.by_family.get(&(family.clone(), version))?;
        self.infos.get(identifier)
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
            let (identifier, instance) = split_instance_name(name);
            let (Some(info), Some(weaker)) = (self.infos.get(&identifier), self.api_defs.get(&identifier)) else {
                continue;
            };
            // A multiple-apply schema is only meaningful under an instance
            // name, and a single-apply one has no place for one.
            if (info.kind == SchemaKind::MultipleApplyApi) != instance.is_some() {
                continue;
            }
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
    /// (C++ `apiSchemaAutoApplyTo`).
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
    // TODO: take the schematics through `sdf::FileFormat` so a family can ship
    // a binary `generatedSchema.usdc`, as C++ does by opening it as a layer.
    pub fn family(mut self, source: FamilySource<'_>) -> Result<Self> {
        let family = tf::Token::from(source.name);

        let schematics = Arc::new(Schematics {
            family: family.clone(),
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
            if self.infos.contains_key(&identifier) {
                bail!("Duplicate schema identifier {identifier} registering family {family}");
            }
            if let Some(other) = self
                .by_family
                .insert((info.family.clone(), info.version), identifier.clone())
            {
                bail!(
                    "Schemas {other} and {identifier} are both version {} of family {}",
                    info.version,
                    info.family
                );
            }
            self.source_of.insert(identifier.clone(), schematics.clone());
            self.infos.insert(identifier, info);
        }

        Ok(self)
    }

    /// Composes the registered families into a registry.
    ///
    /// Applied API schemas are defined first and fully expanded, so a typed
    /// schema that includes one picks up everything that schema itself
    /// includes.
    pub fn build(self) -> Result<Arc<SchemaRegistry>> {
        let mut api_defs = HashMap::new();
        for identifier in self.sorted_identifiers(SchemaInfo::is_applied_api) {
            if api_defs.contains_key(&identifier) {
                continue;
            }
            let mut expansion = Expansion::default();
            self.expand_api_definition(&identifier, &mut api_defs, &mut expansion)?;
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
            let definition = self.typed_definition(&identifier, &api_defs)?;
            concrete_defs.insert(identifier, Arc::new(definition));
        }

        let empty_def = Arc::new(PrimDefinition::default());
        Ok(Arc::new(SchemaRegistry {
            infos: self.infos,
            by_family: self.by_family,
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

        let mut pending = self.begin_definition(identifier)?;
        for name in mem::take(&mut pending.built_ins) {
            let (built_in, instance) = split_instance_name(&name);
            // A built-in no family registered contributes nothing; the schema
            // that names it is still worth defining.
            if !self.infos.contains_key(&built_in) {
                continue;
            }
            self.expand_api_definition(&built_in, api_defs, expansion)?;
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
        api_defs: &HashMap<tf::Token, Arc<PrimDefinition>>,
    ) -> Result<PrimDefinition> {
        let mut pending = self.begin_definition(identifier)?;
        for name in mem::take(&mut pending.built_ins) {
            let (built_in, instance) = split_instance_name(&name);
            pending.compose_built_in(&built_in, instance.as_ref(), api_defs, &self.infos);
        }
        Ok(pending.finish())
    }

    /// Starts one schema's definition from its own class prim, before any
    /// built-in API schema contributes.
    fn begin_definition(&self, identifier: &tf::Token) -> Result<PendingDefinition> {
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
            built_ins: self.direct_built_ins(&schematics, &class_prim, info),
            schematics,
            class_prim,
            overrides,
            seen,
        })
    }

    /// The API schemas a class prim declares as built in (C++
    /// `_GetDirectBuiltinAPISchemas`).
    ///
    /// A multiple-apply schema may only include other templates, and any other
    /// schema may only include non-templates: a template's properties are only
    /// meaningful once an instance name replaces the placeholder, so mixing the
    /// two would leave a placeholder in a concrete prim's properties. Names on
    /// the wrong side of that rule are dropped.
    fn direct_built_ins(&self, schematics: &Schematics, class_prim: &sdf::Path, info: &SchemaInfo) -> Vec<tf::Token> {
        // TODO: append the API schemas whose `apiSchemaAutoApplyTo` names this
        // schema, which C++ treats as built-in after the declared ones.
        let Some(list_op) = class_prim_field(schematics, class_prim, sdf::FieldKey::ApiSchemas)
            .and_then(|value| value.clone().try_as_token_list_op())
        else {
            return Vec::new();
        };

        let wants_templates = info.kind == SchemaKind::MultipleApplyApi;
        list_op
            .compose_over(&[])
            .into_iter()
            .filter(|name| is_name_template(name) == wants_templates)
            .filter(|name| {
                // The reference also has to agree with what it names: only a
                // multiple-apply schema is applied under an instance name, so a
                // single-apply schema dressed as a template would compose its
                // properties without the instance the name promises.
                let (identifier, instance) = split_instance_name(name);
                self.infos
                    .get(&identifier)
                    .is_some_and(|built_in| (built_in.kind == SchemaKind::MultipleApplyApi) == instance.is_some())
            })
            .collect()
    }
}

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

/// The placeholder that stands in for an instance name in a multiple-apply
/// schema's property and built-in names (C++ `__INSTANCE_NAME__`).
const INSTANCE_NAME_PLACEHOLDER: &str = "__INSTANCE_NAME__";

/// Splits an applied-schema name into its schema identifier and, when the name
/// is an instance of a multiple-apply schema, its instance name
/// (C++ `GetTypeNameAndInstance`).
///
/// The split is at the first namespace delimiter: an identifier can never
/// contain one, while an instance name can.
pub(super) fn split_instance_name(name: &tf::Token) -> (tf::Token, Option<tf::Token>) {
    match name.split_once(':') {
        Some((identifier, instance)) => (tf::Token::from(identifier), Some(tf::Token::from(instance))),
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

def "LightAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] bases = ["APISchemaBase"]
    uniform token[] apiSchemaCanOnlyApplyTo = ["DistantLight"]
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

class DomeLight_1 "DomeLight_1"
{
    float inputs:intensity = 1
}
"#;

    /// The miniature family, registered.
    pub(crate) fn test_registry() -> Arc<SchemaRegistry> {
        Self::builder()
            .family(FamilySource {
                name: "test",
                manifest: Self::TEST_MANIFEST,
                schematics: Self::TEST_SCHEMATICS,
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
    fn is_a_unregistered_base() {
        // A family whose bases live in a family that was left out answers the
        // same as registering nothing: the walk could only reach one link of a
        // chain it cannot see, so it reports none of it.
        let manifest = r#"#usda 1.0

def "LightFilter"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["Xformable"]
}
"#;
        let registry = SchemaRegistry::builder()
            .family(FamilySource {
                name: "lux",
                manifest,
                schematics: "#usda 1.0\n\nclass LightFilter \"LightFilter\"\n{\n}\n",
            })
            .expect("family registers")
            .build()
            .expect("registry builds");

        let filter = tf::Token::new("LightFilter");
        assert!(registry.is_a(&filter, &filter));
        assert!(!registry.is_a(&filter, &tf::Token::new("Xformable")));
        assert!(!registry.is_a(&filter, &tf::Token::new("Imageable")));
    }

    #[test]
    fn is_a_cycle_terminates() {
        let manifest = r#"#usda 1.0

def "Loop"
{
    uniform token schemaKind = "abstractTyped"
    uniform token[] bases = ["Knot"]
}

def "Knot"
{
    uniform token schemaKind = "abstractTyped"
    uniform token[] bases = ["Loop"]
}
"#;
        let registry = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics: "#usda 1.0\n\nclass \"Loop\"\n{\n}\n\nclass \"Knot\"\n{\n}\n",
            })
            .expect("family registers")
            .build()
            .expect("registry builds");

        // A manifest is data, so a base cycle must not hang the query.
        assert!(registry.is_a(&tf::Token::new("Loop"), &tf::Token::new("Knot")));
        assert!(!registry.is_a(&tf::Token::new("Loop"), &tf::Token::new("Elsewhere")));
    }

    #[test]
    fn versioned_identifier() {
        let registry = SchemaRegistry::test_registry();

        let dome = registry
            .schema_info(&tf::Token::new("DomeLight_1"))
            .expect("DomeLight_1");
        assert_eq!(dome.family().as_str(), "DomeLight");
        assert_eq!(dome.version(), 1);

        let by_family = registry
            .schema_info_in_family(&tf::Token::new("DomeLight"), 1)
            .expect("DomeLight version 1");
        assert_eq!(by_family.identifier().as_str(), "DomeLight_1");
        assert!(registry
            .schema_info_in_family(&tf::Token::new("DomeLight"), 0)
            .is_none());
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
    }

    #[test]
    fn built_ins_reject_template_mismatch() {
        // A single-apply schema including a bare multiple-apply template has to
        // be dropped: the placeholder would survive into a concrete prim.
        let manifest = r#"#usda 1.0

def "APISchemaBase"
{
    uniform token schemaKind = "abstractBase"
}

def "MultiAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
}

def "SingleAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}
"#;
        let schematics = r#"#usda 1.0

class "APISchemaBase"
{
}

class "MultiAPI"
{
    float multi:__INSTANCE_NAME__:value = 1
}

class "SingleAPI" (
    apiSchemas = ["MultiAPI:__INSTANCE_NAME__"]
)
{
}
"#;
        let registry = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics,
            })
            .expect("family registers")
            .build()
            .expect("registry builds");

        let single = registry
            .api_prim_definition(&tf::Token::new("SingleAPI"))
            .expect("SingleAPI");
        assert_eq!(single.applied_api_schemas(), [tf::Token::new("SingleAPI")]);
        assert!(single.property_names().is_empty());
    }

    #[test]
    fn multi_apply_own_family_version_refused() {
        let manifest = r#"#usda 1.0

def "ThingAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
}

def "ThingAPI_2"
{
    uniform token schemaKind = "multipleApplyAPI"
}
"#;
        let schematics = r#"#usda 1.0

class "ThingAPI" (
    apiSchemas = ["ThingAPI_2:__INSTANCE_NAME__"]
)
{
    float thing:__INSTANCE_NAME__:one = 1
}

class "ThingAPI_2"
{
    float thing:__INSTANCE_NAME__:two = 2
}
"#;
        let registry = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics,
            })
            .expect("family registers")
            .build()
            .expect("registry builds");

        // The conflict is caught while building, not left to poison every
        // application of the schema once an instance name is chosen.
        let thing = registry
            .api_prim_definition(&tf::Token::new("ThingAPI"))
            .expect("ThingAPI");
        assert_eq!(
            thing.applied_api_schemas(),
            [tf::Token::new("ThingAPI:__INSTANCE_NAME__")]
        );

        // Applying it still yields the schema's own properties.
        let composed =
            registry.build_composed_prim_definition(&tf::Token::default(), &[tf::Token::new("ThingAPI:bar")]);
        assert_eq!(
            composed.attribute_fallback(&tf::Token::new("thing:bar:one")),
            Some(sdf::Value::Float(1.0))
        );
    }

    #[test]
    fn built_ins_reject_kind_mismatch() {
        // A single-apply schema wearing a template name has no instance to
        // substitute, so composing it would leave the placeholder in place.
        let manifest = r#"#usda 1.0

def "SingleAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "MultiAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
}
"#;
        let schematics = r#"#usda 1.0

class "SingleAPI"
{
    float single = 1
}

class "MultiAPI" (
    apiSchemas = ["SingleAPI:__INSTANCE_NAME__"]
)
{
    float multi:__INSTANCE_NAME__:value = 2
}
"#;
        let registry = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics,
            })
            .expect("family registers")
            .build()
            .expect("registry builds");

        let multi = registry
            .api_prim_definition(&tf::Token::new("MultiAPI"))
            .expect("MultiAPI");
        assert_eq!(
            multi.applied_api_schemas(),
            [tf::Token::new("MultiAPI:__INSTANCE_NAME__")]
        );
        assert!(!multi.has_property(&tf::Token::new("single")));
    }

    #[test]
    fn built_in_cycle_terminates() {
        let manifest = r#"#usda 1.0

def "FirstAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "SecondAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}
"#;
        let schematics = r#"#usda 1.0

class "FirstAPI" (
    apiSchemas = ["SecondAPI"]
)
{
    float first = 1
}

class "SecondAPI" (
    apiSchemas = ["FirstAPI"]
)
{
    float second = 2
}
"#;
        let registry = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics,
            })
            .expect("family registers")
            .build()
            .expect("registry builds");

        // The mutual inclusion stops where it repeats rather than expanding
        // forever, and each definition is built from its own root, so neither
        // keeps the partial view the other's expansion saw.
        let first = registry
            .api_prim_definition(&tf::Token::new("FirstAPI"))
            .expect("FirstAPI");
        assert!(first.has_property(&tf::Token::new("first")));
        assert!(first.has_property(&tf::Token::new("second")));

        let second = registry
            .api_prim_definition(&tf::Token::new("SecondAPI"))
            .expect("SecondAPI");
        assert!(second.has_property(&tf::Token::new("second")));
        assert!(second.has_property(&tf::Token::new("first")));
    }

    #[test]
    fn unknown_built_in_is_skipped() {
        let manifest = "#usda 1.0\n\ndef \"ThingAPI\"\n{\n    uniform token schemaKind = \"singleApplyAPI\"\n}\n";
        let schematics = r#"#usda 1.0

class "ThingAPI" (
    apiSchemas = ["FromAnotherFamily"]
)
{
    float thing = 1
}
"#;
        let registry = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics,
            })
            .expect("family registers")
            .build()
            .expect("an unregistered built-in does not fail the build");

        let thing = registry
            .api_prim_definition(&tf::Token::new("ThingAPI"))
            .expect("ThingAPI");
        assert!(thing.has_property(&tf::Token::new("thing")));
        assert_eq!(thing.applied_api_schemas(), [tf::Token::new("ThingAPI")]);
    }

    #[test]
    fn built_in_own_family_version_refused() {
        let manifest = r#"#usda 1.0

def "ThingAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "ThingAPI_2"
{
    uniform token schemaKind = "singleApplyAPI"
}
"#;
        let schematics = r#"#usda 1.0

class "ThingAPI" (
    apiSchemas = ["ThingAPI_2"]
)
{
    float one = 1
}

class "ThingAPI_2"
{
    float two = 2
}
"#;
        let registry = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics,
            })
            .expect("family registers")
            .build()
            .expect("registry builds");

        // A schema cannot build in a second version of its own family.
        let thing = registry
            .api_prim_definition(&tf::Token::new("ThingAPI"))
            .expect("ThingAPI");
        assert_eq!(thing.applied_api_schemas(), [tf::Token::new("ThingAPI")]);
        assert!(!thing.has_property(&tf::Token::new("two")));
    }

    #[test]
    fn non_canonical_identifier_rejected() {
        let manifest = r#"#usda 1.0

def "Foo_1"
{
    uniform token schemaKind = "abstractBase"
}

def "Foo_01"
{
    uniform token schemaKind = "abstractBase"
}
"#;
        // `Foo_01` parses to the same family and version as `Foo_1`, so letting
        // it register would silently shadow one of the two.
        let error = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics: "#usda 1.0\n",
            })
            .expect_err("a non-canonical identifier is rejected");
        assert!(format!("{error:#}").contains("not a valid identifier"), "{error:#}");
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
    fn composed_refuses_version_conflict() {
        let manifest = r#"#usda 1.0

def "ThingAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "ThingAPI_2"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
        let schematics = r#"#usda 1.0

class "ThingAPI"
{
    float version = 1
}

class "ThingAPI_2"
{
    float version = 2
    float extra = 0
}

class Widget "Widget" (
    apiSchemas = ["ThingAPI"]
)
{
}
"#;
        let registry = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics,
            })
            .expect("family registers")
            .build()
            .expect("registry builds");

        let definition =
            registry.build_composed_prim_definition(&tf::Token::new("Widget"), &[tf::Token::new("ThingAPI_2")]);

        // Widget already builds in version 1 of the family, so authoring
        // version 2 contributes nothing at all — not even its own properties.
        assert_eq!(definition.applied_api_schemas(), [tf::Token::new("ThingAPI")]);
        assert_eq!(
            definition.attribute_fallback(&tf::Token::new("version")),
            Some(sdf::Value::Float(1.0))
        );
        assert!(!definition.has_property(&tf::Token::new("extra")));
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
    fn unknown_kind_rejected() {
        let manifest = "#usda 1.0\n\ndef \"Thing\"\n{\n    uniform token schemaKind = \"bogus\"\n}\n";
        let error = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics: "#usda 1.0\n",
            })
            .expect_err("unknown kind is rejected");
        assert!(format!("{error:#}").contains("Unknown schemaKind"), "{error:#}");
    }

    #[test]
    fn missing_kind_rejected() {
        let manifest = "#usda 1.0\n\ndef \"Thing\"\n{\n}\n";
        let error = SchemaRegistry::builder()
            .family(FamilySource {
                name: "test",
                manifest,
                schematics: "#usda 1.0\n",
            })
            .expect_err("missing kind is rejected");
        assert!(format!("{error:#}").contains("schemaKind is required"), "{error:#}");
    }

    #[test]
    fn duplicate_identifier_rejected() {
        let manifest = "#usda 1.0\n\ndef \"Thing\"\n{\n    uniform token schemaKind = \"abstractBase\"\n}\n";
        let source = FamilySource {
            name: "test",
            manifest,
            schematics: "#usda 1.0\n",
        };
        let error = SchemaRegistry::builder()
            .family(source)
            .expect("first family registers")
            .family(FamilySource {
                name: "other",
                ..source
            })
            .expect_err("duplicate identifier is rejected");
        assert!(
            format!("{error:#}").contains("Duplicate schema identifier"),
            "{error:#}"
        );
    }

    #[test]
    fn global_is_shared_and_empty() {
        assert!(Arc::ptr_eq(SchemaRegistry::global(), SchemaRegistry::global()));
        assert_eq!(SchemaRegistry::global().schema_infos().count(), 0);
    }
}
