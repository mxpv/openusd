//! Stage-composed prim handle — a value-type wrapper around `(stage, path)`
//! that mirrors C++ `UsdPrim`, plus the [`VariantSets`] handle reached through
//! it. The property handles it returns, [`Attribute`] and [`Relationship`],
//! live in sibling modules.
//!
//! Each handle is freely [`Clone`], holds no borrow on the composition
//! cache, and re-acquires state from the [`Stage`] per call. They are
//! returned by [`Stage`]'s authoring methods so callers can chain
//! composed-scene edits without dropping to the Sdf tier.
//!
//! # Fluent setters
//!
//! Setters take `self` by value and return `Self`. Chaining writes is a
//! single statement that ends with the final handle bound:
//!
//! ```no_run
//! use openusd::{sdf, usd};
//!
//! let stage = usd::Stage::builder().in_memory("anon.usda").unwrap();
//! let mesh = stage
//!     .define_prim("/World/Mesh").unwrap()
//!     .set_type_name("Mesh").unwrap()
//!     .set_kind("component").unwrap();
//! let radius = mesh
//!     .create_attribute("radius", "double").unwrap()
//!     .set(sdf::Value::Double(1.0)).unwrap();
//! # let _ = radius;
//! ```
//!
//! Each setter does its own short `borrow_mut` on the composition cache and
//! routes invalidation through [`crate::pcp::Changes`], so only the prim
//! indices observably affected by the write are dropped.

use std::collections::HashSet;
use std::sync::Arc;

use super::{
    ApplyApiError, Attribute, EditTarget, EditTargetArc, PrimDefinition, PrimTypeInfo, Relationship, SchemaRegistry,
    Stage, StageAuthoringError, VersionFilter, schema_registry,
};
use crate::tf::Token;
use crate::{pcp, sdf};

/// Stage-composed prim handle. Mirrors C++ `UsdPrim`.
#[derive(Clone)]
pub struct Prim {
    stage: Stage,
    path: sdf::Path,
}

impl Prim {
    pub(crate) fn new(stage: &Stage, path: sdf::Path) -> Self {
        Self {
            stage: stage.clone(),
            path,
        }
    }

    /// Composed namespace path of the prim.
    pub fn path(&self) -> &sdf::Path {
        &self.path
    }

    /// The stage this handle is anchored to.
    pub fn stage(&self) -> &Stage {
        &self.stage
    }

    /// Edit target that authors into the source layer of this prim's strongest
    /// `arc` composition arc (C++ `UsdEditTarget(UsdPrim, ...)`). Delegates to
    /// [`Stage::edit_target_for_node`](Stage::edit_target_for_node).
    pub fn edit_target_for_arc(&self, arc: EditTargetArc) -> Result<EditTarget, StageAuthoringError> {
        self.stage.edit_target_for_node(&self.path, arc)
    }

    /// Set the prim's `typeName` field on the edit target's layer.
    pub fn set_type_name(self, name: impl Into<String>) -> Result<Self, StageAuthoringError> {
        let name = name.into();
        self.edit(|spec| spec.set_type_name(name))
    }

    /// Set the prim's `active` flag.
    pub fn set_active(self, active: bool) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| spec.set_active(active))
    }

    /// Set the prim's `kind` metadata.
    pub fn set_kind(self, kind: impl Into<String>) -> Result<Self, StageAuthoringError> {
        let kind = kind.into();
        self.edit(|spec| spec.set_kind(kind))
    }

    /// Set the prim's `hidden` flag.
    pub fn set_hidden(self, hidden: bool) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| spec.set_hidden(hidden))
    }

    /// Set the prim's `instanceable` flag.
    pub fn set_instanceable(self, instanceable: bool) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| spec.set_instanceable(instanceable))
    }

    /// Add an applied API schema name to this prim's `apiSchemas` metadata.
    ///
    /// This is the registry-free authoring operation behind C++
    /// `UsdPrim::AddAppliedSchema`: it edits the current edit target's
    /// `apiSchemas` list op in place rather than replacing existing list-op
    /// opinions, and authors `name` whatever it is. Reach for
    /// [`apply_api`](Self::apply_api) to have the registry check it first.
    ///
    /// The prim spec must already exist on the active edit target — chain
    /// after [`Stage::define_prim`] or [`Stage::override_prim`]; otherwise
    /// the call returns [`sdf::AuthoringError::InvalidPath`].
    ///
    /// [`Stage::define_prim`]: crate::usd::Stage::define_prim
    /// [`Stage::override_prim`]: crate::usd::Stage::override_prim
    pub fn add_applied_schema(self, name: impl Into<String>) -> Result<Self, StageAuthoringError> {
        let name = name.into();
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            super::edit_spec(
                layer.data_mut(),
                path,
                "no prim spec at path on the edit target layer",
                sdf::PrimSpecMut::get,
                |spec| {
                    spec.add_applied_schema(name)?;
                    Ok(())
                },
            )
        })?;
        Ok(self)
    }

    /// Apply an API schema to this prim, checking it against the registry
    /// first. Mirrors C++ `UsdPrim::ApplyAPI`.
    ///
    /// `name` carries the instance for a multiple-apply schema, as it does
    /// everywhere else applied names appear (`CollectionAPI:render`). The check
    /// is the one C++ makes here: the schema must be an applied API schema, and
    /// must be given an instance name exactly when it is multiple-apply. The
    /// restrictions a schema places on *where* it may be applied are advisory
    /// and are not enforced — ask [`can_apply_api`](Self::can_apply_api) for
    /// those.
    ///
    /// A name the registry does not know carries no rules to break, so it is
    /// authored as-is; that is what keeps applying schemas working while no
    /// schema data is registered.
    ///
    /// Authoring carries [`add_applied_schema`](Self::add_applied_schema)'s
    /// precondition: the prim spec must already exist on the active edit
    /// target, so chain after [`Stage::define_prim`] or
    /// [`Stage::override_prim`].
    ///
    /// [`Stage::define_prim`]: crate::usd::Stage::define_prim
    /// [`Stage::override_prim`]: crate::usd::Stage::override_prim
    // TODO: author the spec instead of requiring one, as C++ `ApplyAPI` does
    // through `_CreatePrimSpecForEditing`.
    pub fn apply_api(self, name: impl Into<Token>) -> Result<Self, StageAuthoringError> {
        let name = name.into();
        self.stage.schema_registry().check_applied_name(&name)?;
        self.add_applied_schema(name)
    }

    /// Whether [`apply_api`](Self::apply_api) would be accepted, and the whole
    /// of what the schema demands besides. Mirrors C++ `UsdPrim::CanApplyAPI`,
    /// whose `whyNot` this returns as the error.
    ///
    /// Beyond the shape `apply_api` enforces, this honours the prim itself and
    /// the restrictions a schema declares: the instance names a multiple-apply
    /// schema allows, and the prim types `apiSchemaCanOnlyApplyTo` limits it
    /// to — the latter satisfied by a type that derives from one of them,
    /// through [`is_a`](Self::is_a).
    pub fn can_apply_api(&self, name: impl Into<Token>) -> Result<(), ApplyApiError> {
        let name = name.into();
        if !self.is_valid()? {
            return Err(ApplyApiError::PrimNotValid {
                path: self.path.clone(),
            });
        }

        let registry = self.stage.schema_registry();
        let Some((info, instance)) = registry.check_applied_name(&name)? else {
            return Ok(());
        };
        let schema = info.identifier();

        if let Some(instance) = instance
            && !registry.is_allowed_instance_name(schema, &instance)
        {
            let schema = schema.clone();
            return Err(ApplyApiError::InstanceNameNotAllowed { schema, instance });
        }

        let allowed = info.can_only_apply_to();
        if !allowed.is_empty() {
            // The prim's type answers for every candidate, so it is resolved
            // before the scan.
            let type_info = self.prim_type_info()?;
            if !allowed.iter().any(|t| registry.is_a(type_info.schema_type_name(), t)) {
                return Err(ApplyApiError::PrimTypeNotAllowed {
                    schema: schema.clone(),
                    allowed: allowed.to_vec(),
                });
            }
        }
        Ok(())
    }

    /// Author a prim-level metadata field (e.g. `assetInfo`, `customData`,
    /// `kind`). Mirrors C++ `UsdObject::SetMetadata` for a prim.
    ///
    /// `key` is `&'static str` so the change-tracking layer can record it
    /// without copying; pass a `pub const FOO: &str = "..."` token rather than
    /// a runtime-built string.
    pub fn set_metadata(self, key: &'static str, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
        let value = value.into();
        self.update_metadata(key, |_| value)
    }

    /// Read-modify-write a prim-level metadata field on the edit-target layer.
    /// `f` receives the field's current opinion on that layer (`None` when it
    /// is unauthored locally) and returns the value to author.
    ///
    /// Reading the local opinion rather than the composed value keeps opinions
    /// on weaker layers from being flattened into the edit target. This matters
    /// for dictionary-valued metadata such as `assetInfo` / `customData`, which
    /// value resolution merges key-by-key across layers (spec 12.2.5): a caller
    /// that merges one nested key should leave the rest to composition.
    ///
    /// `key` is `&'static str` for the same change-tracking reason as
    /// [`set_metadata`](Self::set_metadata).
    pub fn update_metadata<F>(self, key: &'static str, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(Option<sdf::Value>) -> sdf::Value,
    {
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            // Author an `over` for the prim (and any missing ancestors) when the
            // edit target has no local spec, matching C++ `UsdObject::SetMetadata`
            // creating the spec for editing. The layer records the ancestor
            // adds and the metadata write.
            let mut spec = sdf::PrimSpec::over(layer.data_mut(), path)?;
            let value = f(spec.field(key).ok().flatten());
            spec.set(key, value);
            Ok(())
        })?;
        Ok(self)
    }

    /// Author an attribute spec named `name` under this prim. Mirrors C++
    /// `UsdPrim::CreateAttribute`. Defaults `variability = Varying`,
    /// `custom = true` — override via the returned [`Attribute`] handle's
    /// fluent setters.
    pub fn create_attribute(
        &self,
        name: impl Into<Token>,
        type_name: impl Into<String>,
    ) -> Result<Attribute, StageAuthoringError> {
        let name = name.into();
        let attr_path = self.path.append_property(&name).map_err(|_| {
            // Synthesize the would-be path so the error surfaces the
            // offending name rather than just the parent prim.
            StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath {
                path: sdf::Path::from(format!("{}.{}", self.path, name).as_str()),
                reason: "attribute name is not a valid property name",
            })
        })?;
        self.stage.create_attribute(attr_path, type_name)
    }

    /// Author a relationship spec named `name` under this prim. Mirrors C++
    /// `UsdPrim::CreateRelationship`.
    pub fn create_relationship(&self, name: impl Into<Token>) -> Result<Relationship, StageAuthoringError> {
        let name = name.into();
        let rel_path = self.path.append_property(&name).map_err(|_| {
            // Synthesize the would-be path so the error surfaces the
            // offending name rather than just the parent prim.
            StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath {
                path: sdf::Path::from(format!("{}.{}", self.path, name).as_str()),
                reason: "relationship name is not a valid property name",
            })
        })?;
        self.stage.create_relationship(rel_path)
    }

    /// Author a relationship `name` with the given target paths and the
    /// schema-authoring convention `custom = false`. Shortcut for
    /// `create_relationship(name) + set_custom(false) + set_targets`.
    pub fn author_relationship_targets<I, P>(&self, name: &str, targets: I) -> Result<Relationship, StageAuthoringError>
    where
        I: IntoIterator<Item = P>,
        P: Into<sdf::Path>,
    {
        self.create_relationship(name)?
            .set_custom(false)?
            .set_targets(targets.into_iter().map(Into::into))
    }

    /// Append `value` to the `uniform token[]` attribute named `name` on this
    /// prim, preserving insertion order. Reads the composed default across
    /// layers (so weaker-layer opinions get materialised into the edit target's
    /// new value), de-duplicates, and writes back via `create_attribute`.
    ///
    /// Returns `true` when `value` was appended, `false` when it was already
    /// present (or the attribute is bound to a non-token-array variant that
    /// can't be flattened).
    ///
    /// Useful for ordered token stacks like `xformOpOrder` or `apiSchemas`.
    pub fn append_to_uniform_token_array(&self, name: &str, value: impl Into<String>) -> anyhow::Result<bool> {
        let value = value.into();
        let attr_path = self.path.append_property(name)?;
        let existing: Vec<String> = match self.stage.field::<sdf::Value>(&attr_path, sdf::FieldKey::Default)? {
            Some(sdf::Value::TokenVec(v)) => v.into_iter().map(Into::into).collect(),
            Some(sdf::Value::StringVec(v)) => v,
            Some(sdf::Value::TokenListOp(op)) => op.flatten().into_iter().map(Into::into).collect(),
            Some(sdf::Value::StringListOp(op)) => op.flatten(),
            _ => Vec::new(),
        };
        if existing.iter().any(|t| t == &value) {
            return Ok(false);
        }
        let mut updated = existing;
        updated.push(value);
        self.stage
            .create_attribute(attr_path, "token[]")?
            .set_variability(sdf::Variability::Uniform)?
            .set_custom(false)?
            .set(sdf::Value::token_vec(updated))?;
        Ok(true)
    }

    /// Names of the value-clip sets composed onto this prim, sorted by name
    /// (spec 12.3.4). Reads the composed `clips` dictionary across layers;
    /// returns an empty vector when none are authored.
    ///
    /// This is read-only introspection — clip values are resolved through
    /// [`Attribute::get_at`]. The `clipSets` strength order is not applied to
    /// the returned names.
    pub fn clip_sets(&self) -> anyhow::Result<Vec<String>> {
        let Some(sdf::Value::Dictionary(sets)) = self.stage.field::<sdf::Value>(&self.path, sdf::FieldKey::Clips)?
        else {
            return Ok(Vec::new());
        };
        let mut names: Vec<String> = sets.into_keys().collect();
        names.sort();
        Ok(names)
    }

    /// Returns `true` when one or more value-clip sets are composed onto this
    /// prim (spec 12.3.4).
    pub fn has_clips(&self) -> anyhow::Result<bool> {
        Ok(!self.clip_sets()?.is_empty())
    }

    /// Composed `typeName`, if set. Mirrors C++ `UsdPrim::GetTypeName`.
    ///
    /// `typeName` is a token; a value of any other type is treated as untyped
    /// (`None`), matching C++ reading the field as an empty `TfToken`.
    pub fn type_name(&self) -> anyhow::Result<Option<Token>> {
        Ok(self
            .stage
            .field::<sdf::Value>(&self.path, sdf::FieldKey::TypeName)?
            .and_then(|v| v.try_as_token()))
    }

    /// Composed specifier, if one resolves. Mirrors C++ `UsdPrim::GetSpecifier`.
    pub fn specifier(&self) -> anyhow::Result<Option<sdf::Specifier>> {
        self.stage.field::<sdf::Specifier>(&self.path, sdf::FieldKey::Specifier)
    }

    /// Composed `kind` metadata, if authored. Mirrors C++ `UsdPrim::GetKind`.
    ///
    /// `kind` is a token; a value of any other type is treated as unauthored
    /// (`None`), matching C++ reading the field as an empty `TfToken`.
    pub fn kind(&self) -> anyhow::Result<Option<Token>> {
        Ok(self
            .stage
            .field::<sdf::Value>(&self.path, sdf::FieldKey::Kind)?
            .and_then(|v| v.try_as_token()))
    }

    /// Returns this prim's composed `customData` dictionary, if authored.
    /// Mirrors C++ `UsdObject::GetCustomData`.
    pub fn custom_data(&self) -> anyhow::Result<Option<sdf::Value>> {
        self.stage.field::<sdf::Value>(&self.path, sdf::FieldKey::CustomData)
    }

    /// The API schemas that apply to this prim, strongest first. Mirrors C++
    /// `UsdPrim::GetAppliedSchemas`.
    ///
    /// This is the prim definition's list, so it includes the schemas a typed
    /// schema or an applied schema builds in, not only the ones authored in
    /// `apiSchemas`. Multi-apply instances appear as-is (e.g.
    /// `PhysicsLimitAPI:rotZ`). Use
    /// [`authored_api_schemas`](Self::authored_api_schemas) for the authored
    /// list alone.
    pub fn api_schemas(&self) -> anyhow::Result<Vec<Token>> {
        let info = self.prim_type_info()?;
        let mut names = info.prim_definition().applied_api_schemas().to_vec();

        // An authored name the registry does not know composes into no
        // definition, but it is still what the prim asks for. Reporting it
        // keeps the answer from depending on how much of the scene's schema
        // data this build happens to have: C++ drops such a name, which it can
        // afford because its registry is always fully populated.
        let composed: HashSet<&Token> = names.iter().collect();
        let unknown: Vec<Token> = self
            .authored_api_schemas()?
            .into_iter()
            .filter(|name| !composed.contains(name))
            .collect();

        names.extend(unknown);
        Ok(names)
    }

    /// The prim's composed `apiSchemas` list op, flattened across all
    /// contributing opinions. Mirrors C++ `UsdPrim::GetAppliedSchemas` before
    /// the prim definition folds in built-ins.
    pub fn authored_api_schemas(&self) -> anyhow::Result<Vec<Token>> {
        self.stage
            .masked(&self.path, |g, cache| cache.api_schemas(g, &self.path))
    }

    /// `true` when this prim's type is `schema`, or derives from it. Mirrors
    /// C++ `UsdPrim::IsA`.
    ///
    /// Derivation is read from the stage's
    /// [`SchemaRegistry`](super::SchemaRegistry), so a query against an
    /// abstract ancestor (`Boundable`, `Imageable`) answers for the concrete
    /// types under it, and a type resolved through `fallbackPrimTypes` answers
    /// for the type it resolved to.
    ///
    /// The question is asked of the prim's schema type, which is empty unless a
    /// registered type backs it. So a prim whose `typeName` this registry does
    /// not know is nothing — including the very name it authors.
    pub fn is_a(&self, schema: impl Into<Token>) -> anyhow::Result<bool> {
        let info = self.prim_type_info()?;
        Ok(self
            .stage
            .schema_registry()
            .is_a(info.schema_type_name(), &schema.into()))
    }

    /// `true` when `name` is in the prim's composed `apiSchemas` (pass the full
    /// instance name for multi-apply schemas). Mirrors C++ `UsdPrim::HasAPI`.
    pub fn has_api_schema(&self, name: impl Into<Token>) -> anyhow::Result<bool> {
        let name = name.into();
        Ok(self.api_schemas()?.iter().any(|s| s.as_str() == name.as_str()))
    }

    /// The registered concrete schema backing this prim's type, or `None` when
    /// none does.
    ///
    /// `None` covers every prim while the stage's registry carries no schema
    /// data, a `typeName` that registry has never heard of, and a `typeName`
    /// naming an abstract schema — only a concrete type backs a prim, so only
    /// one is reported here.
    ///
    /// Deriving the type costs composed reads, so a registry with nothing in it
    /// answers `None` without paying them.
    pub fn schema_type(&self) -> anyhow::Result<Option<Token>> {
        if self.stage.schema_registry().is_empty() {
            return Ok(None);
        }
        let schema_type = self.prim_type_info()?.schema_type_name().clone();
        Ok(Some(schema_type).filter(|name| !name.as_str().is_empty()))
    }

    /// Whether this prim is any version of `family` that `filter` accepts.
    /// Mirrors C++ `UsdPrim::IsInFamily`.
    ///
    /// This is [`is_a`](Self::is_a) asked of a whole family rather than one
    /// identifier, so a caller does not have to name every version a schema has
    /// shipped under (`DomeLight`, `DomeLight_1`, …).
    pub fn is_in_family(&self, family: impl Into<Token>, filter: VersionFilter) -> anyhow::Result<bool> {
        Ok(self.version_in_family(family, filter)?.is_some())
    }

    /// The version of `family` this prim is, or `None` when it is none of them.
    /// Mirrors C++ `UsdPrim::GetVersionIfIsInFamily`.
    ///
    /// `family` names a family, not a schema: `DomeLight_1` is an identifier
    /// within the `DomeLight` family and places a prim in no family of its own,
    /// exactly as C++'s family-taking overload treats it.
    ///
    /// The newest accepted version the prim satisfies wins, which is the order
    /// [`SchemaRegistry::schema_infos_in_family`](super::SchemaRegistry::schema_infos_in_family)
    /// answers in.
    pub fn version_in_family(&self, family: impl Into<Token>, filter: VersionFilter) -> anyhow::Result<Option<u32>> {
        let family = family.into();
        let registry = self.stage.schema_registry();
        if let Some(schema_type) = self.schema_type()? {
            return Ok(registry.version_in_family(&schema_type, &family, filter));
        }

        // No registered schema backs the type, so the name it authors is all
        // there is to place it by — the arm that resolves a versioned family
        // while no schema data is registered.
        let Some((authored_family, version)) = self
            .type_name()?
            .as_ref()
            .and_then(SchemaRegistry::parse_allowed_identifier)
        else {
            return Ok(None);
        };
        Ok((authored_family == family && filter.accepts(version)).then_some(version))
    }

    /// Whether this prim has any version of the applied API schema `family`
    /// that `filter` accepts. Mirrors C++ `UsdPrim::HasAPIInFamily`.
    ///
    /// `instance` narrows a multiple-apply schema to one instance; without it
    /// any instance counts, as C++ matching on the `Schema:` prefix does.
    pub fn has_api_in_family(
        &self,
        family: impl Into<Token>,
        filter: VersionFilter,
        instance: Option<&Token>,
    ) -> anyhow::Result<bool> {
        Ok(self.api_version_in_family(family, filter, instance)?.is_some())
    }

    /// The version of the applied API schema `family` this prim has, or `None`.
    /// Mirrors C++ `UsdPrim::GetVersionIfHasAPIInFamily`.
    ///
    /// A registered schema answers from the composed prim definition, so the
    /// version reported is the one that actually contributes properties rather
    /// than every version the prim names. A name no registered schema backs was
    /// never composed at all, so it answers from what the prim authors, under
    /// the family its own name gives it.
    ///
    /// `family` names a family, not a schema, as it does for
    /// [`version_in_family`](Self::version_in_family).
    pub fn api_version_in_family(
        &self,
        family: impl Into<Token>,
        filter: VersionFilter,
        instance: Option<&Token>,
    ) -> anyhow::Result<Option<u32>> {
        let family = family.into();
        let registry = self.stage.schema_registry();
        let definition = self.prim_definition()?;

        // A version composition rejected — one conflicting with a stronger
        // built-in of the same family — is absent from the definition's list
        // (C++ `GetAppliedSchemas`).
        let composed = definition.applied_api_schemas().iter().filter_map(|name| {
            let (info, applied_instance) = registry.check_applied_name(name).ok().flatten()?;
            Some((info.family().clone(), info.version(), applied_instance))
        });

        let authored = self.authored_api_schemas()?;
        let unregistered = authored.iter().filter_map(|name| {
            let (schema, applied_instance) = schema_registry::split_instance_name(name);
            if registry.schema_info(&schema).is_some() {
                return None;
            }
            let (schema_family, version) = SchemaRegistry::parse_allowed_identifier(&schema)?;
            Some((schema_family, version, applied_instance))
        });

        // The newest accepted version among the matches answers.
        Ok(composed
            .chain(unregistered)
            .filter(|(schema_family, version, applied_instance)| {
                schema_family == &family
                    && filter.accepts(*version)
                    && instance.is_none_or(|wanted| applied_instance.as_ref() == Some(wanted))
            })
            .map(|(_, version, _)| version)
            .max())
    }

    /// The prim's schema type — its composed `typeName` and `apiSchemas`, and
    /// the definition they compose to. Mirrors C++ `UsdPrim::GetPrimTypeInfo`.
    ///
    /// Shared with every prim of the same type, and valid for as long as the
    /// stage's [`SchemaRegistry`](super::SchemaRegistry) lives.
    pub fn prim_type_info(&self) -> anyhow::Result<Arc<PrimTypeInfo>> {
        self.stage.prim_type_info(&self.path)
    }

    /// What this prim's schemas declare: their properties, and the fallback
    /// values those properties take when nothing is authored. Mirrors C++
    /// `UsdPrim::GetPrimDefinition`.
    pub fn prim_definition(&self) -> anyhow::Result<Arc<PrimDefinition>> {
        Ok(self.prim_type_info()?.prim_definition().clone())
    }

    /// `true` if the prim and all ancestors are active. Missing `active`
    /// opinions default to `true`; a non-existent prim is inactive. Mirrors C++
    /// `UsdPrim::IsActive`.
    pub fn is_active(&self) -> anyhow::Result<bool> {
        // `active` defaults to true, so an ancestor blocks only when it
        // explicitly authors `false`.
        self.all_ancestors(|stage, path| Ok(stage.field::<bool>(path, sdf::FieldKey::Active)?.unwrap_or(true)))
    }

    /// Composed `instanceable` flag (spec 11.3.1). Mirrors C++
    /// `UsdPrim::IsInstanceable`; an unauthored flag resolves to `false`.
    pub fn is_instanceable(&self) -> anyhow::Result<bool> {
        Ok(self
            .stage
            .field::<bool>(&self.path, sdf::FieldKey::Instanceable)?
            .unwrap_or(false))
    }

    /// `true` if the prim is loaded — active, and no payload-carrying prim at
    /// or above it (per the stage's runtime load rules) is excluded. Mirrors
    /// C++ `UsdPrim::IsLoaded`.
    pub fn is_loaded(&self) -> anyhow::Result<bool> {
        if !self.is_active()? {
            return Ok(false);
        }
        // No rule anywhere means every path resolves loaded (`LoadRules`'
        // documented default) -- skip the ancestor walk below entirely.
        if self.stage.cache().load_rules().is_empty() {
            return Ok(true);
        }
        for path in self.path.ancestors_below_root() {
            if has_payload(&self.stage, &path)? && !self.stage.is_path_loaded(&path) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// `true` if the prim and all ancestors have defining specifiers (`def` or
    /// `class`). `over`, missing specs, and missing specifier opinions are not
    /// defining. Mirrors C++ `UsdPrim::IsDefined`.
    pub fn is_defined(&self) -> anyhow::Result<bool> {
        self.all_ancestors(|stage, path| {
            let specifier = stage.field::<sdf::Specifier>(path, sdf::FieldKey::Specifier)?;
            Ok(matches!(specifier, Some(sdf::Specifier::Def | sdf::Specifier::Class)))
        })
    }

    /// `true` if the prim or any ancestor resolves to `class`. Mirrors C++
    /// `UsdPrim::IsAbstract`.
    pub fn is_abstract(&self) -> anyhow::Result<bool> {
        if self.path == sdf::Path::abs_root() || !self.stage.has_spec(&self.path)? {
            return Ok(false);
        }
        for path in self.path.ancestors_below_root() {
            if self.stage.field::<sdf::Specifier>(&path, sdf::FieldKey::Specifier)? == Some(sdf::Specifier::Class) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// `true` if the prim index contains at least one composition arc.
    pub fn has_composition_arc(&self) -> anyhow::Result<bool> {
        self.stage
            .masked(&self.path, |g, cache| cache.has_composition_arc(g, &self.path))
    }

    /// `true` if this prim is an instance (spec 11.3.3): `instanceable` resolves
    /// true and the prim has a composition arc. Mirrors C++ `UsdPrim::IsInstance`.
    pub fn is_instance(&self) -> anyhow::Result<bool> {
        if self.path == sdf::Path::abs_root()
            || !self.stage.mask().includes(&self.path)
            || !self.stage.has_spec(&self.path)?
        {
            return Ok(false);
        }
        if !self
            .stage
            .field::<bool>(&self.path, sdf::FieldKey::Instanceable)?
            .unwrap_or(false)
        {
            return Ok(false);
        }
        self.has_composition_arc()
    }

    /// `true` if the prim is in the contiguous model hierarchy: its `kind` is
    /// `group` / `assembly` / `component`, and every ancestor below the
    /// pseudo-root is `group` / `assembly`. Mirrors C++ `UsdPrim::IsModel`.
    pub fn is_model(&self) -> anyhow::Result<bool> {
        Ok(self.model_kind()?.is_some())
    }

    /// `true` if the prim is a group-like model (`group` or `assembly`).
    /// Mirrors C++ `UsdPrim::IsGroup`.
    pub fn is_group(&self) -> anyhow::Result<bool> {
        Ok(matches!(self.model_kind()?, Some("group" | "assembly")))
    }

    /// `true` if the prim is a component model in a valid model hierarchy.
    /// Mirrors C++ `UsdPrim::IsComponent`.
    pub fn is_component(&self) -> anyhow::Result<bool> {
        Ok(self.model_kind()? == Some("component"))
    }

    /// `true` if the prim has `kind = "subcomponent"`. Mirrors C++
    /// `UsdPrim::IsSubComponent`.
    pub fn is_subcomponent(&self) -> anyhow::Result<bool> {
        Ok(self.kind()?.as_deref() == Some("subcomponent"))
    }

    /// Returns the shared prototype path (`/__Prototype_N`) for this prim if it
    /// is an instance, else `None` (spec 11.3.3). Mirrors C++
    /// `UsdPrim::GetPrototype`.
    pub fn prototype(&self) -> anyhow::Result<Option<sdf::Path>> {
        self.stage
            .masked(&self.path, |g, cache| cache.prototype_of(g, &self.path))
    }

    /// Returns the instance prims sharing this prototype root (a
    /// `/__Prototype_N` prim), sorted by namespace path and filtered to the
    /// population mask. Mirrors C++ `UsdPrim::GetInstances`.
    ///
    /// The mask filters the *results* rather than gating the query (unlike the
    /// `self.path`-gated sibling queries such as [`is_instance`](Self::is_instance)):
    /// `self.path` here is the synthetic prototype root, which is never in a
    /// user population mask, so gating on it would always yield nothing.
    pub fn instances(&self) -> Vec<sdf::Path> {
        let mask = self.stage.mask();
        let instances = self.stage.cache().instances_of(&self.path);
        instances
            .into_iter()
            .filter(|instance| mask.includes(instance))
            .collect()
    }

    /// Returns `true` if this prim is a prototype root (`/__Prototype_N`).
    /// Mirrors C++ `UsdPrim::IsPrototype`.
    pub fn is_prototype(&self) -> bool {
        self.stage.cache().is_prototype(&self.path)
    }

    /// Returns `true` if this prim lies within a prototype's namespace.
    /// Mirrors C++ `UsdPrim::IsInPrototype`.
    pub fn is_in_prototype(&self) -> bool {
        self.stage.cache().is_in_prototype(&self.path)
    }

    /// `true` if this prim is an instance proxy — a descendant of an instance
    /// prim, in the instance's own namespace, standing in for a prim in the
    /// shared prototype (spec 11.3.3). Mirrors C++ `UsdPrim::IsInstanceProxy`.
    pub fn is_instance_proxy(&self) -> anyhow::Result<bool> {
        self.stage
            .masked(&self.path, |g, cache| cache.is_instance_proxy(g, &self.path))
    }

    /// Returns the prim in the shared prototype this instance proxy stands in
    /// for (a `/__Prototype_N/...` prim), or `None` when this prim is not an
    /// instance proxy (spec 11.3.3). Mirrors C++ `UsdPrim::GetPrimInPrototype`.
    pub fn prim_in_prototype(&self) -> anyhow::Result<Option<Prim>> {
        let path = self
            .stage
            .masked(&self.path, |g, cache| cache.prim_in_prototype(g, &self.path))?;
        Ok(path.map(|p| Prim::new(&self.stage, p)))
    }

    /// The model-hierarchy `kind` for the prim — `Some("group" | "assembly" |
    /// "component")` when the prim and all ancestors form a contiguous model
    /// hierarchy, else `None`.
    fn model_kind(&self) -> anyhow::Result<Option<&'static str>> {
        if self.path == sdf::Path::abs_root() || !self.stage.has_spec(&self.path)? {
            return Ok(None);
        }
        let leaf = match self.kind()?.as_deref() {
            Some("group") => "group",
            Some("assembly") => "assembly",
            Some("component") => "component",
            _ => return Ok(None),
        };
        let Some(parent) = self.path.parent() else {
            return Ok(Some(leaf));
        };
        for ancestor in parent.ancestors_below_root() {
            let kind = self
                .stage
                .field::<sdf::Value>(&ancestor, sdf::FieldKey::Kind)?
                .and_then(|v| v.try_as_token());
            if !matches!(kind.as_deref(), Some("group" | "assembly")) {
                return Ok(None);
            }
        }
        Ok(Some(leaf))
    }

    /// `true` when every ancestor (self included, up to but excluding the
    /// pseudo-root) satisfies `keep`. The pseudo-root is vacuously true; a prim
    /// with no composed spec is false. Shared skeleton of
    /// [`is_active`](Self::is_active) and [`is_defined`](Self::is_defined).
    fn all_ancestors<F>(&self, keep: F) -> anyhow::Result<bool>
    where
        F: Fn(&Stage, &sdf::Path) -> anyhow::Result<bool>,
    {
        if self.path == sdf::Path::abs_root() {
            return Ok(true);
        }
        if !self.stage.has_spec(&self.path)? {
            return Ok(false);
        }
        for path in self.path.ancestors_below_root() {
            if !keep(&self.stage, &path)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Returns the prim stack: each `(layer identifier, spec path)` site that
    /// contributes a prim spec to this prim, strongest first. Mirrors C++
    /// `UsdPrim::GetPrimStack`.
    pub fn prim_stack(&self) -> anyhow::Result<Vec<(String, sdf::Path)>> {
        self.stage.with_cache(|g, c| c.prim_stack(g, &self.path))
    }

    /// Returns a handle to this prim's composition index (C++
    /// `UsdPrim::GetPrimIndex`), through which the composition graph and composed
    /// child names + prohibited names are reachable. See
    /// [`PrimIndexRef`](crate::usd::PrimIndexRef).
    pub fn prim_index(&self) -> PrimIndexRef {
        PrimIndexRef::new(&self.stage, self.path.clone())
    }

    /// Returns an [`Attribute`] handle for the property `name` under this prim.
    /// Mirrors C++ `UsdPrim::GetAttribute`. This is a value-type wrapper; it
    /// neither authors a spec nor asserts the attribute is composed. An invalid
    /// property name yields a handle whose path falls back to the prim, which
    /// resolves as empty.
    pub fn attribute(&self, name: impl Into<Token>) -> Attribute {
        Attribute::new(&self.stage, self.property_path(name))
    }

    /// Returns a [`Relationship`] handle for the property `name` under this
    /// prim. Mirrors C++ `UsdPrim::GetRelationship`. See [`Self::attribute`]
    /// for the handle's non-authoring, non-validating contract.
    pub fn relationship(&self, name: impl Into<Token>) -> Relationship {
        Relationship::new(&self.stage, self.property_path(name))
    }

    /// Returns the composed child prim names, in strongest-layer order and
    /// filtered by the stage's population mask. The name-only counterpart of
    /// [`children`](Self::children).
    pub fn child_names(&self) -> anyhow::Result<Vec<Token>> {
        let names = self
            .stage
            .masked(&self.path, |g, cache| cache.prim_children(g, &self.path))?;
        Ok(self.stage.filter_child_names(&self.path, names))
    }

    /// Returns the composed child prims, in strongest-layer order and filtered
    /// by the stage's population mask. Mirrors C++ `UsdPrim::GetChildren`.
    pub fn children(&self) -> anyhow::Result<Vec<Prim>> {
        Ok(self
            .child_names()?
            .into_iter()
            .filter_map(|name| self.path.append_path(name.as_str()).ok())
            .map(|path| Prim::new(&self.stage, path))
            .collect())
    }

    /// Returns every property name of this prim — the ones layers author and
    /// the ones its schemas declare. Mirrors C++ `UsdPrim::GetPropertyNames`.
    ///
    /// The union is sorted into element order and then reordered by the prim's
    /// composed `propertyOrder`, so the result does not depend on which half a
    /// name came from. Use [`authored_property_names`](Self::authored_property_names)
    /// to scan only what layers actually author.
    pub fn property_names(&self) -> anyhow::Result<Vec<Token>> {
        let mut names = self.authored_property_names()?;

        // A schema-declared property is part of the prim's surface whether or
        // not a layer authors a spec for it, since it still resolves a type and
        // a fallback value.
        let info = self.prim_type_info()?;
        let declared = info.prim_definition().property_names();
        if !declared.is_empty() {
            let authored: HashSet<Token> = names.iter().cloned().collect();
            names.extend(declared.iter().filter(|name| !authored.contains(*name)).cloned());
            names.sort_by(|a, b| sdf::element_cmp(a, b));
        }

        if let Some(order) = self
            .stage
            .field::<sdf::Value>(&self.path, sdf::FieldKey::PropertyOrder)?
            .and_then(sdf::Value::try_as_token_vec)
        {
            sdf::apply_ordering(&mut names, &order);
        }
        Ok(names)
    }

    /// Returns the property names layers author on this prim, in composed
    /// order. Mirrors C++ `UsdPrim::GetAuthoredPropertyNames`.
    ///
    /// This is the set to scan when the question is "what did someone write?" —
    /// enumerating a schema's declarations would answer a different one.
    pub fn authored_property_names(&self) -> anyhow::Result<Vec<Token>> {
        self.stage
            .masked(&self.path, |g, cache| cache.prim_properties(g, &self.path))
    }

    /// Returns handles to the composed attributes with authored scene
    /// description. Mirrors C++ `UsdPrim::GetAuthoredAttributes`.
    pub fn authored_attributes(&self) -> anyhow::Result<Vec<Attribute>> {
        let mut attributes = Vec::new();
        for name in self.authored_property_names()? {
            let path = self.property_path(name);
            if self.stage.spec_type(&path)? == Some(sdf::SpecType::Attribute) {
                attributes.push(Attribute::new(&self.stage, path));
            }
        }
        Ok(attributes)
    }

    /// Returns handles to the composed attributes of this prim. Mirrors C++
    /// `UsdPrim::GetAttributes`.
    pub fn attributes(&self) -> anyhow::Result<Vec<Attribute>> {
        Ok(self
            .properties_of_type(sdf::SpecType::Attribute)?
            .into_iter()
            .map(|path| Attribute::new(&self.stage, path))
            .collect())
    }

    /// Returns handles to the composed relationships of this prim. Mirrors C++
    /// `UsdPrim::GetRelationships`.
    pub fn relationships(&self) -> anyhow::Result<Vec<Relationship>> {
        Ok(self
            .properties_of_type(sdf::SpecType::Relationship)?
            .into_iter()
            .map(|path| Relationship::new(&self.stage, path))
            .collect())
    }

    /// Returns `true` when a prim spec is composed at this path. Mirrors C++
    /// `UsdPrim::IsValid` for a handle obtained from
    /// [`Stage::prim`](crate::usd::Stage::prim): a path with no
    /// contributing spec yields a handle that is not valid.
    pub fn is_valid(&self) -> anyhow::Result<bool> {
        self.stage.has_spec(&self.path)
    }

    /// Property paths under this prim whose composed spec type matches `ty`,
    /// preserving the composed property order.
    fn properties_of_type(&self, ty: sdf::SpecType) -> anyhow::Result<Vec<sdf::Path>> {
        let info = self.prim_type_info()?;
        let definition = info.prim_definition();

        let mut paths = Vec::new();
        for name in self.property_names()? {
            let path = self.property_path(&name);
            // A property the prim only inherits from its schema has no composed
            // spec, so its kind comes from the declaration instead.
            let spec_type = self
                .stage
                .spec_type(&path)?
                .or_else(|| definition.property(&name).map(|property| property.spec_type()));
            if spec_type == Some(ty) {
                paths.push(path);
            }
        }
        Ok(paths)
    }

    /// Property path for `name` under this prim, falling back to the prim path
    /// for an invalid name (the handle then resolves as empty).
    fn property_path(&self, name: impl Into<Token>) -> sdf::Path {
        self.path.append_property(name).unwrap_or_else(|_| self.path.clone())
    }

    /// Returns the variant sets composed onto this prim. Mirrors C++
    /// `UsdPrim::GetVariantSets`.
    pub fn variant_sets(&self) -> VariantSets {
        VariantSets::new(&self.stage, self.path.clone())
    }

    /// Borrow the prim spec at `self.path` on the edit target's layer, apply
    /// `f`, and return `self` for chaining. The layer records whatever fields
    /// `f` writes. Returns `InvalidPath` if no prim spec exists at the path.
    fn edit<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::PrimSpecMut<'_>),
    {
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            super::edit_spec(
                layer.data_mut(),
                path,
                "no prim spec at path on the edit target layer",
                sdf::PrimSpecMut::get,
                |spec| {
                    f(spec);
                    Ok(())
                },
            )
        })?;
        Ok(self)
    }
}

/// `true` when a non-empty `payload` opinion is composed at `prim` — the
/// per-prim check behind [`Prim::is_loaded`].
pub(super) fn has_payload(stage: &Stage, prim: &sdf::Path) -> anyhow::Result<bool> {
    let payload = stage.field::<sdf::Value>(prim, sdf::FieldKey::Payload)?;
    Ok(match payload {
        Some(sdf::Value::Payload(payload)) => payload_has_target(&payload),
        Some(sdf::Value::PayloadListOp(op)) => op.reduced().flatten().iter().any(payload_has_target),
        _ => false,
    })
}

fn payload_has_target(payload: &sdf::Payload) -> bool {
    !payload.asset_path.is_empty() || !payload.prim_path.is_empty()
}

/// A handle to a single prim's composition index, the analog of C++
/// `PcpPrimIndex` reached via `UsdPrim::GetPrimIndex`.
///
/// Our [`pcp::PrimIndex`] is only the composition graph (its nodes hold layer
/// *indices*, not the layers); the cache owns the layer data. This handle pairs
/// the stage with the prim's path so the introspection that needs both — the
/// composed child names — is reachable here, alongside the raw graph via
/// [`graph`](Self::graph). Like [`Prim`], it is a cheap value handle: each query
/// borrows the cache briefly. Composition diagnostics remain available through
/// [`Stage::composition_errors`].
#[derive(Clone)]
pub struct PrimIndexRef {
    stage: Stage,
    path: sdf::Path,
}

impl PrimIndexRef {
    pub(super) fn new(stage: &Stage, path: sdf::Path) -> Self {
        Self {
            stage: stage.clone(),
            path,
        }
    }

    /// Returns this prim's composition graph (C++ `UsdPrim::GetPrimIndex`),
    /// building it if needed. A clone, since the cache owns the cached index.
    pub fn graph(&self) -> anyhow::Result<pcp::PrimIndex> {
        self.stage.with_cache(|g, c| Ok(c.index(g, &self.path)?.clone()))
    }

    /// Composes this prim's child names together with the names prohibited at it
    /// — children relocated away (renamed or deleted) that cannot be
    /// re-introduced — returned as `(children, prohibited)` (C++
    /// `PcpPrimIndex::ComputePrimChildNames`).
    pub fn child_names(&self) -> anyhow::Result<(Vec<Token>, Vec<Token>)> {
        self.stage.with_cache(|g, c| c.compute_prim_child_names(g, &self.path))
    }
}

/// The variant sets composed onto a prim. Mirrors C++ `UsdVariantSets`,
/// reached through [`Prim::variant_sets`].
//
// TODO: grow this to cover the rest of `UsdVariantSets`
// (`GetNames` / `HasVariantSet` / `GetVariantSet` / `SetSelection`). Until it
// carries more than `get_all_variant_selections`, the newtype earns its keep
// only as the C++ API shape; if those methods don't materialize, fold the one
// query back onto `Prim`.
#[derive(Clone)]
pub struct VariantSets {
    stage: Stage,
    prim: sdf::Path,
}

impl VariantSets {
    pub(super) fn new(stage: &Stage, prim: sdf::Path) -> Self {
        Self {
            stage: stage.clone(),
            prim,
        }
    }

    /// Returns the variant selections composed onto the prim, as `(set,
    /// selection)` pairs sorted by set name. Mirrors C++
    /// `UsdVariantSets::GetAllVariantSelections`. These are the effective
    /// selections — authored, fallback, or default — read from the variant
    /// selection sites that actually contribute to the prim.
    pub fn get_all_variant_selections(&self) -> anyhow::Result<Vec<(String, String)>> {
        self.stage.with_cache(|g, c| c.variant_selections(g, &self.prim))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::sync::Arc;

    use crate::sdf;
    use crate::tf::Token;
    use crate::usd::{ApplyApiError, SchemaRegistry, Stage, StageAuthoringError, VersionFilter};

    fn stage() -> anyhow::Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    /// A stage over the shared test schema family, so prim definitions have
    /// something to resolve against.
    fn schema_stage() -> anyhow::Result<Stage> {
        Stage::builder()
            .schema_registry(SchemaRegistry::test_registry())
            .in_memory("anon.usda")
    }

    #[test]
    fn prim_type_info_is_shared() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/A")?.set_type_name("DistantLight")?;
        stage.define_prim("/B")?.set_type_name("DistantLight")?;
        stage.define_prim("/C")?.set_type_name("DomeLight_1")?;

        // Two prims of the same type share one composed definition; a different
        // type gets its own.
        let a = stage.prim("/A").prim_type_info()?;
        let b = stage.prim("/B").prim_type_info()?;
        let c = stage.prim("/C").prim_type_info()?;
        assert!(Arc::ptr_eq(&a, &b));
        assert!(!Arc::ptr_eq(&a, &c));

        assert_eq!(
            a.prim_definition().attribute_fallback(&Token::new("inputs:intensity")),
            Some(sdf::Value::Float(50000.0))
        );
        Ok(())
    }

    #[test]
    fn prim_type_info_follows_edits() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        let prim = stage.define_prim("/Light")?;
        assert!(prim.prim_definition()?.is_empty());

        let prim = prim.set_type_name("DistantLight")?;
        assert!(prim.prim_definition()?.has_property(&Token::new("inputs:angle")));

        // Applying a schema recomposes the definition on the next read.
        let prim = prim.add_applied_schema("CollectionAPI:render")?;
        let definition = prim.prim_definition()?;
        assert_eq!(
            definition.attribute_fallback(&Token::new("collection:render:expansionRule")),
            Some(sdf::Value::token("expandPrims"))
        );
        assert_eq!(
            prim.prim_type_info()?.id().applied_api_schemas(),
            [Token::new("CollectionAPI:render")]
        );
        Ok(())
    }

    #[test]
    fn schema_properties_are_enumerated() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        let prim = stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        prim.create_attribute("authored", "double")?;

        // Authored names keep their composed order; the schema's declarations
        // follow, and a property appears once whether or not it is authored.
        let names = stage.prim("/Sun").property_names()?;
        assert_eq!(
            names,
            [
                Token::new("authored"),
                Token::new("collection:lightLink:expansionRule"),
                Token::new("collection:lightLink:includeRoot"),
                Token::new("collection:lightLink:includes"),
                Token::new("inputs:angle"),
                Token::new("inputs:intensity"),
                Token::new("light:shaderId"),
            ]
        );
        Ok(())
    }

    #[test]
    fn schema_properties_split_by_kind() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        let prim = stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        prim.create_attribute("authored", "double")?;
        prim.create_relationship("authoredRel")?;

        let authored = prim.authored_attributes()?;
        assert_eq!(authored.len(), 1);
        assert_eq!(authored[0].path().as_str(), "/Sun.authored");

        // A property with no authored spec still sorts into attributes or
        // relationships by what the schema declares it to be.
        let attributes = stage.prim("/Sun").attributes()?;
        let names: Vec<&str> = attributes.iter().map(|attr| attr.path().as_str()).collect();
        assert!(names.contains(&"/Sun.inputs:intensity"), "{names:?}");
        assert!(!names.iter().any(|name| name.ends_with("includes")), "{names:?}");

        let relationships = stage.prim("/Sun").relationships()?;
        assert_eq!(relationships.len(), 2);
        assert!(
            relationships
                .iter()
                .any(|relationship| relationship.path().as_str().ends_with("collection:lightLink:includes"))
        );
        assert!(
            relationships
                .iter()
                .any(|relationship| relationship.path().as_str() == "/Sun.authoredRel")
        );
        Ok(())
    }

    #[test]
    fn enumeration_ignores_unknown_schemas() -> anyhow::Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        prim.create_attribute("authored", "double")?;

        // The default registry knows no schemas, so only authored properties
        // are enumerated.
        assert_eq!(stage.prim("/Sun").property_names()?, [Token::new("authored")]);
        Ok(())
    }

    #[test]
    fn fallback_prim_type() -> anyhow::Result<()> {
        let stage = Stage::builder()
            .schema_registry(SchemaRegistry::test_registry())
            .in_memory("anon.usda")?;
        stage.define_prim("/Sun")?.set_type_name("MyStudioLight")?;

        // No registry knows `MyStudioLight`, so it resolves nothing on its own.
        assert!(stage.prim("/Sun").prim_definition()?.is_empty());

        let root_id = stage.root_layer().identifier.clone();
        {
            let mut root = stage.layer_mut(&root_id).expect("root layer");
            root.edit(|e| {
                e.pseudo_root_mut().unwrap().set(
                    "fallbackPrimTypes",
                    sdf::Value::Dictionary(HashMap::from([(
                        "MyStudioLight".to_owned(),
                        sdf::Value::token_vec(["Unregistered", "DistantLight"]),
                    )])),
                );
                Ok(())
            })?;
        }

        // The first registered fallback supplies the definition, while the
        // prim's own `typeName` still reads back as authored.
        let prim = stage.prim("/Sun");
        assert_eq!(prim.type_name()?, Some(Token::new("MyStudioLight")));
        assert_eq!(
            prim.prim_definition()?
                .attribute_fallback(&Token::new("inputs:intensity")),
            Some(sdf::Value::Float(50000.0))
        );

        // An `IsA` query answers for the type it resolved to. The authored name
        // is not a schema, so nothing is it.
        assert!(prim.is_a("DistantLight")?);
        assert!(prim.is_a("Typed")?);
        assert!(!prim.is_a("MyStudioLight")?);
        Ok(())
    }

    #[test]
    fn typeless_prim_has_empty_definition() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Plain")?;

        let info = stage.prim("/Plain").prim_type_info()?;
        assert!(info.id().is_empty());
        assert!(Arc::ptr_eq(&info, stage.schema_registry().empty_prim_type_info()));
        Ok(())
    }

    #[test]
    fn type_identity_survives_an_empty_registry() -> anyhow::Result<()> {
        let stage = stage()?;
        stage
            .define_prim("/Sun")?
            .set_type_name("DistantLight")?
            .add_applied_schema("CollectionAPI:render")?;

        // The registry knowing nothing means an empty *definition*, not an
        // empty identity — two unrelated types must not share one.
        let sun = stage.prim("/Sun").prim_type_info()?;
        assert_eq!(sun.id().type_name(), &Token::new("DistantLight"));
        assert_eq!(sun.id().applied_api_schemas(), [Token::new("CollectionAPI:render")]);
        assert!(sun.prim_definition().is_empty());

        stage.define_prim("/Ball")?.set_type_name("Sphere")?;
        assert!(!Arc::ptr_eq(&sun, &stage.prim("/Ball").prim_type_info()?));
        Ok(())
    }

    #[test]
    fn is_a_base_chain() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        let sun = stage.prim("/Sun");
        assert!(sun.is_a("DistantLight")?);
        assert!(sun.is_a("NonboundableLightBase")?);
        assert!(sun.is_a("Typed")?);
        assert!(!sun.is_a("DomeLight_1")?);
        Ok(())
    }

    #[test]
    fn is_a_needs_schema_data() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Nothing is registered, so `DistantLight` names no schema and the prim
        // is not it. The typed views keep resolving because their gate checks
        // the authored name before asking this question.
        let sun = stage.prim("/Sun");
        assert!(!sun.is_a("DistantLight")?);
        assert!(!sun.is_a("Typed")?);
        Ok(())
    }

    #[test]
    fn apply_api_checks_kind() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // A multiple-apply schema applies per instance; a single-apply one
        // applies whole. Getting that wrong is refused before anything is
        // authored.
        let missing = stage.prim("/Sun").apply_api("CollectionAPI").err().expect("rejected");
        assert!(matches!(
            missing,
            StageAuthoringError::Schema(ApplyApiError::MissingInstanceName { .. })
        ));
        let unexpected = stage.prim("/Sun").apply_api("LightAPI:extra").err().expect("rejected");
        assert!(matches!(
            unexpected,
            StageAuthoringError::Schema(ApplyApiError::UnexpectedInstanceName { .. })
        ));
        let typed = stage.prim("/Sun").apply_api("DistantLight").err().expect("rejected");
        assert!(matches!(
            typed,
            StageAuthoringError::Schema(ApplyApiError::NotAppliedApi { .. })
        ));
        assert!(stage.prim("/Sun").authored_api_schemas()?.is_empty());

        // The well-formed spellings author.
        stage.prim("/Sun").apply_api("LightAPI")?;
        stage.prim("/Sun").apply_api("CollectionAPI:render")?;
        assert_eq!(
            stage.prim("/Sun").authored_api_schemas()?,
            [Token::new("LightAPI"), Token::new("CollectionAPI:render")]
        );
        Ok(())
    }

    #[test]
    fn apply_api_unknown_schema() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // A name the registry does not know carries no rules to break.
        stage.prim("/Sun").apply_api("SomeUnregisteredAPI")?;
        stage.prim("/Sun").can_apply_api("SomeUnregisteredAPI")?;
        assert!(stage.prim("/Sun").has_api_schema("SomeUnregisteredAPI")?);
        Ok(())
    }

    #[test]
    fn can_apply_api_restrictions() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage.define_prim("/Plain")?.set_type_name("DomeLight_1")?;

        // `LightAPI` declares `apiSchemaCanOnlyApplyTo = ["DistantLight"]`.
        stage.prim("/Sun").can_apply_api("LightAPI")?;
        let wrong_type = stage.prim("/Plain").can_apply_api("LightAPI").unwrap_err();
        assert!(matches!(wrong_type, ApplyApiError::PrimTypeNotAllowed { .. }));

        // `SlotAPI` restricts itself to `NonboundableLightBase`, which `/Sun`
        // is not by name — it is a `DistantLight` deriving from it, so the
        // check runs through `is_a` rather than comparing type names. It also
        // restricts its instance names.
        stage.prim("/Sun").can_apply_api("SlotAPI:left")?;
        let wrong_instance = stage.prim("/Sun").can_apply_api("SlotAPI:middle").unwrap_err();
        assert!(matches!(wrong_instance, ApplyApiError::InstanceNameNotAllowed { .. }));

        // The restrictions are advisory: `apply_api` authors regardless, as
        // C++ `ApplyAPI` does.
        stage.prim("/Plain").apply_api("LightAPI")?;
        assert!(stage.prim("/Plain").has_api_schema("LightAPI")?);
        Ok(())
    }

    #[test]
    fn is_in_family_versions() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Old")?.set_type_name("DomeLight")?;
        stage.define_prim("/New")?.set_type_name("DomeLight_1")?;

        // Either version answers for the family, which is the point of asking
        // by family rather than by identifier.
        let family = Token::new("DomeLight");
        assert!(stage.prim("/Old").is_in_family(&family, VersionFilter::All)?);
        assert!(stage.prim("/New").is_in_family(&family, VersionFilter::All)?);
        assert_eq!(
            stage.prim("/Old").version_in_family(&family, VersionFilter::All)?,
            Some(0)
        );
        assert_eq!(
            stage.prim("/New").version_in_family(&family, VersionFilter::All)?,
            Some(1)
        );

        // The filter narrows which versions count.
        assert!(
            !stage
                .prim("/Old")
                .is_in_family(&family, VersionFilter::GreaterThan(0))?
        );
        assert!(
            stage
                .prim("/New")
                .is_in_family(&family, VersionFilter::GreaterThan(0))?
        );

        // A prim of another family is in none of it.
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        assert!(!stage.prim("/Sun").is_in_family(&family, VersionFilter::All)?);
        Ok(())
    }

    #[test]
    fn has_api_in_family_instance() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage
            .define_prim("/Sun")?
            .set_type_name("DistantLight")?
            .apply_api("CollectionAPI:render")?;

        // Any instance answers for the family; a named one has to match. Both
        // the instance the prim applies and the `lightLink` one it inherits
        // through `LightAPI` count, and nothing else does.
        let family = Token::new("CollectionAPI");
        let render = Token::new("render");
        assert!(
            stage
                .prim("/Sun")
                .has_api_in_family(&family, VersionFilter::All, None)?
        );
        assert!(
            stage
                .prim("/Sun")
                .has_api_in_family(&family, VersionFilter::All, Some(&render))?
        );
        assert!(
            stage
                .prim("/Sun")
                .has_api_in_family(&family, VersionFilter::All, Some(&Token::new("lightLink")))?
        );
        assert!(
            !stage
                .prim("/Sun")
                .has_api_in_family(&family, VersionFilter::All, Some(&Token::new("other")))?
        );

        // A single-apply schema is applied whole, so it has no instance to ask
        // after. `LightAPI` is built in to `DistantLight`.
        let light = Token::new("LightAPI");
        assert_eq!(
            stage
                .prim("/Sun")
                .api_version_in_family(&light, VersionFilter::All, None)?,
            Some(0)
        );
        assert!(
            !stage
                .prim("/Sun")
                .has_api_in_family(&light, VersionFilter::All, Some(&render))?
        );

        // Only an applied API schema is applied at all, so the prim's own typed
        // family answers nothing here.
        let typed = Token::new("DistantLight");
        assert!(!stage.prim("/Sun").has_api_in_family(&typed, VersionFilter::All, None)?);
        Ok(())
    }

    #[test]
    fn family_queries_without_registry() -> anyhow::Result<()> {
        // A plain stage registers no schema data, which is the state every
        // stage is in until it is vendored.
        let stage = stage()?;
        stage
            .define_prim("/New")?
            .set_type_name("DomeLight_1")?
            .add_applied_schema("CollectionAPI:render")?;

        // The prim query and the views' gate place a prim the same way, so
        // filtering a traversal cannot drop what a view would accept.
        assert!(stage.prim("/New").is_in_family("DomeLight", VersionFilter::All)?);
        assert_eq!(
            stage.prim("/New").version_in_family("DomeLight", VersionFilter::All)?,
            Some(1)
        );
        assert!(!stage.prim("/New").is_in_family("DistantLight", VersionFilter::All)?);

        // An applied schema no registry knows was never composed, so it answers
        // from what the prim authors — as `has_api_schema` does beside it.
        let collection = Token::new("CollectionAPI");
        let render = Token::new("render");
        assert!(stage.prim("/New").has_api_schema("CollectionAPI:render")?);
        assert!(
            stage
                .prim("/New")
                .has_api_in_family(&collection, VersionFilter::All, None)?
        );
        assert!(
            stage
                .prim("/New")
                .has_api_in_family(&collection, VersionFilter::All, Some(&render))?
        );
        assert!(
            !stage
                .prim("/New")
                .has_api_in_family(&collection, VersionFilter::All, Some(&Token::new("other")))?
        );
        Ok(())
    }

    #[test]
    fn api_family_rejected_version() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        // `DistantLight` builds in `LightAPI`, so authoring a second version of
        // that family conflicts and composition keeps the built-in.
        stage
            .define_prim("/Sun")?
            .set_type_name("DistantLight")?
            .add_applied_schema("LightAPI_2")?;

        let family = Token::new("LightAPI");
        assert_eq!(
            stage
                .prim("/Sun")
                .api_version_in_family(&family, VersionFilter::All, None)?,
            Some(0)
        );
        // The rejected version contributes nothing, so it answers for nothing.
        assert!(
            !stage
                .prim("/Sun")
                .has_api_in_family(&family, VersionFilter::GreaterThan(0), None)?
        );
        Ok(())
    }

    #[test]
    fn can_apply_api_invalid_prim() -> anyhow::Result<()> {
        let stage = schema_stage()?;

        // Nothing composes at the path, so there is nothing to apply to —
        // answered before any schema question, as C++ `CanApplyAPI` does.
        let missing = stage.prim("/Typo").can_apply_api("CollectionAPI:render").unwrap_err();
        assert!(matches!(missing, ApplyApiError::PrimNotValid { .. }));
        Ok(())
    }

    #[test]
    fn can_apply_api_malformed_instance() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // An instance name becomes a namespace component of every property the
        // schema instantiates, so one that cannot be spelled there is refused.
        for name in [
            "CollectionAPI:my instance",
            "CollectionAPI:render:",
            "CollectionAPI:1st",
        ] {
            let rejected = stage.prim("/Sun").can_apply_api(name).unwrap_err();
            assert!(
                matches!(rejected, ApplyApiError::InstanceNameNotAllowed { .. }),
                "{name} rejected as {rejected:?}"
            );
        }

        // A trailing delimiter names no instance at all, so a multiple-apply
        // schema is left without the instance it requires.
        let empty = stage.prim("/Sun").can_apply_api("CollectionAPI:").unwrap_err();
        assert!(matches!(empty, ApplyApiError::MissingInstanceName { .. }));
        Ok(())
    }

    #[test]
    fn unknown_api_schemas_survive_a_known_one() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage
            .define_prim("/Sun")?
            .set_type_name("DistantLight")?
            .add_applied_schema("Unregistered")?;

        // Adding a schema the registry knows must not make an unknown one
        // disappear: the built-ins come first, then what is authored on top.
        let names = stage.prim("/Sun").api_schemas()?;
        assert_eq!(
            names,
            [
                Token::new("LightAPI"),
                Token::new("CollectionAPI:lightLink"),
                Token::new("Unregistered"),
            ]
        );
        assert!(stage.prim("/Sun").has_api_schema("Unregistered")?);
        assert!(stage.prim("/Sun").has_api_schema("LightAPI")?);
        Ok(())
    }

    #[test]
    fn schema_relationship_is_uniform_and_not_custom() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // `rel collection:lightLink:includes` declares no variability, and a
        // relationship is uniform.
        let includes = stage.prim("/Sun").relationship("collection:lightLink:includes");
        let definition = stage.prim("/Sun").prim_definition()?;
        let declared = definition
            .property(&Token::new("collection:lightLink:includes"))
            .expect("includes");
        assert_eq!(declared.variability(), sdf::Variability::Uniform);

        // A schema declares it, so an authored `custom` is ignored.
        includes.clone().set_custom(true)?;
        assert!(
            !stage
                .prim("/Sun")
                .relationship("collection:lightLink:includes")
                .is_custom()?
        );
        Ok(())
    }

    #[test]
    fn schema_relationship_is_writable() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // `collection:lightLink:includes` is declared by the schema alone, so
        // authoring targets on it has to stamp the spec first.
        let includes = stage
            .prim("/Sun")
            .relationship("collection:lightLink:includes")
            .set_targets([sdf::path("/Sun")?])?;
        assert_eq!(includes.targets()?, vec![sdf::path("/Sun")?]);
        Ok(())
    }

    #[test]
    fn default_registry_knows_nothing() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/Light")?.set_type_name("DistantLight")?;

        // The process registry ships without schema data, so a real USD type
        // resolves to an empty definition.
        assert!(stage.prim("/Light").prim_definition()?.is_empty());
        Ok(())
    }

    /// Handles own a refcounted [`Stage`], so they can be collected and
    /// queried after the expression — and even the original `Stage`
    /// binding — that produced them is gone. The `'s` borrow used to forbid
    /// this.
    #[test]
    fn handles_outlive_stage() -> anyhow::Result<()> {
        let prims: Vec<super::Prim> = {
            let stage = stage()?;
            stage.define_prim("/A")?.set_type_name("Xform")?;
            stage.define_prim("/B")?.set_type_name("Scope")?;
            vec![stage.prim("/A"), stage.prim("/B")]
            // `stage` is dropped here; each handle's cloned `Rc` keeps the
            // shared state alive.
        };

        assert_eq!(prims[0].path().as_str(), "/A");
        let type_name = prims[1].stage().prim(prims[1].path()).type_name()?;
        assert_eq!(type_name.as_deref(), Some("Scope"));
        Ok(())
    }

    /// `Prim::has_clips`/`clip_sets` report composed clip sets, and
    /// `Attribute::get_at` resolves clip values (spec 12.3.4).
    #[test]
    fn clip_introspection() -> anyhow::Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/value_resolution/tests/assets/clip_basic/entry.usd",
            env!("CARGO_MANIFEST_DIR")
        );
        let stage = Stage::open(&path)?;

        let model = super::Prim::new(&stage, sdf::path("/Model")?);
        assert!(model.has_clips()?);
        assert_eq!(model.clip_sets()?, vec!["default".to_string()]);

        // get_at flows through clip resolution: the clip overrides the reference.
        let size = super::Attribute::new(&stage, sdf::path("/Model.size")?);
        assert_eq!(
            size.get_at(crate::usd::TimeCode::new(10.0))?,
            Some(sdf::Value::Float(10.0))
        );

        // A prim with no clips reports none.
        let other = super::Prim::new(&stage, sdf::path("/Model2")?);
        assert!(!other.has_clips()?);
        Ok(())
    }

    /// `Prim::is_instance`/`prototype`/`is_in_prototype` mirror the stage-level
    /// instancing queries (spec 11.3.3).
    #[test]
    fn prim_prototype_handle() -> anyhow::Result<()> {
        let path = format!("{}/fixtures/instancing_shared.usda", env!("CARGO_MANIFEST_DIR"));
        let stage = Stage::open(&path)?;

        let a = super::Prim::new(&stage, sdf::path("/A")?);
        assert!(a.is_instance()?);
        assert!(a.prototype()?.is_some());
        assert!(!a.is_in_prototype());

        let proto = super::Prim::new(&stage, sdf::path("/Proto")?);
        assert!(!proto.is_instance()?);
        assert!(proto.prototype()?.is_none());
        Ok(())
    }

    /// `Prim::specifier` mirrors C++ `UsdPrim::GetSpecifier`: `define_prim`
    /// resolves to `Def`, `override_prim` to `Over`.
    #[test]
    fn prim_specifier() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/Def")?;
        stage.override_prim("/Over")?;
        assert_eq!(stage.prim("/Def").specifier()?, Some(sdf::Specifier::Def));
        assert_eq!(stage.prim("/Over").specifier()?, Some(sdf::Specifier::Over));
        Ok(())
    }

    /// `Prim::custom_data` reads the composed `customData` dictionary
    /// (C++ `UsdObject::GetCustomData`).
    #[test]
    fn prim_custom_data() -> anyhow::Result<()> {
        let stage = stage()?;
        let dict = sdf::Value::Dictionary([("note".to_string(), sdf::Value::String("hi".into()))].into());
        stage
            .define_prim("/A")?
            .set_metadata(sdf::FieldKey::CustomData.as_str(), dict)?;
        let Some(sdf::Value::Dictionary(read)) = stage.prim("/A").custom_data()? else {
            panic!("customData should resolve to a dictionary");
        };
        assert_eq!(read.get("note"), Some(&sdf::Value::String("hi".into())));
        assert!(stage.prim("/B").custom_data()?.is_none());
        Ok(())
    }

    #[test]
    fn prim_chain() -> anyhow::Result<()> {
        let stage = stage()?;
        stage
            .define_prim("/World")?
            .set_type_name("Xform")?
            .set_kind("group")?
            .set_active(true)?;
        assert_eq!(
            stage.field::<sdf::Value>("/World", sdf::FieldKey::TypeName)?,
            Some(sdf::Value::Token("Xform".into())),
        );
        assert_eq!(stage.prim("/World").kind()?.as_deref(), Some("group"));
        Ok(())
    }

    #[test]
    fn add_api_schema() -> anyhow::Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?.add_applied_schema("MaterialBindingAPI")?;
        assert_eq!(
            stage.prim(prim.path()).api_schemas()?,
            vec![Token::from("MaterialBindingAPI")]
        );
        assert!(stage.prim(prim.path()).has_api_schema("MaterialBindingAPI")?);
        Ok(())
    }

    #[test]
    fn add_api_schema_merges() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/World")?;
        stage.with_target_layer_at(&sdf::Path::new("/World").expect("valid path"), |layer, _path| {
            let path = sdf::Path::new("/World").expect("valid path");
            layer.data_mut().set_field(
                &path,
                sdf::FieldKey::ApiSchemas.as_str(),
                sdf::Value::TokenListOp(sdf::TokenListOp {
                    appended_items: vec![Token::from("ExistingAPI")],
                    ..Default::default()
                }),
            );
            Ok(())
        })?;

        stage
            .override_prim("/World")?
            .add_applied_schema("ExistingAPI")?
            .add_applied_schema("NewAPI")?;

        let op = stage
            .root_layer()
            .prim("/World")
            .expect("authored on the root layer")
            .api_schemas()
            .expect("apiSchemas authored");
        assert_eq!(op.appended_items, vec![Token::from("ExistingAPI")]);
        assert_eq!(op.prepended_items, vec![Token::from("NewAPI")]);
        Ok(())
    }

    #[test]
    fn set_prim_metadata() -> anyhow::Result<()> {
        let stage = stage()?;
        let mut dict = std::collections::HashMap::new();
        dict.insert("hint".to_string(), sdf::Value::String("v".to_string()));
        stage
            .define_prim("/World")?
            .set_metadata("customData", sdf::Value::Dictionary(dict))?;

        let Some(sdf::Value::Dictionary(read)) = stage.field::<sdf::Value>("/World", "customData")? else {
            panic!("expected customData dictionary");
        };
        assert_eq!(read.get("hint"), Some(&sdf::Value::String("v".to_string())));
        Ok(())
    }

    #[test]
    fn update_metadata_reads_local() -> anyhow::Result<()> {
        let stage = stage()?;
        let mut dict = std::collections::HashMap::new();
        dict.insert("a".to_string(), sdf::Value::Int(1));
        stage
            .define_prim("/World")?
            .set_metadata("customData", sdf::Value::Dictionary(dict))?;

        // The closure receives the local opinion and merges into it.
        stage.define_prim("/World")?.update_metadata("customData", |local| {
            let Some(sdf::Value::Dictionary(mut d)) = local else {
                panic!("expected local customData dictionary");
            };
            d.insert("b".to_string(), sdf::Value::Int(2));
            sdf::Value::Dictionary(d)
        })?;

        let Some(sdf::Value::Dictionary(read)) = stage.field::<sdf::Value>("/World", "customData")? else {
            panic!("expected customData dictionary");
        };
        assert_eq!(read.get("a"), Some(&sdf::Value::Int(1)));
        assert_eq!(read.get("b"), Some(&sdf::Value::Int(2)));
        Ok(())
    }

    /// Authoring prim metadata on the pseudo-root reports an error rather than
    /// panicking — the pseudo-root carries no prim spec to author into.
    #[test]
    fn update_metadata_on_pseudo_root_errors() -> anyhow::Result<()> {
        let stage = stage()?;
        let result = stage
            .prim(sdf::path("/")?)
            .set_metadata("documentation", sdf::Value::String("x".into()));
        assert!(result.is_err());
        Ok(())
    }
}
