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

use super::{Attribute, Relationship, Stage, StageAuthoringError};
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

    /// Set the prim's `typeName` field on the edit target's layer.
    pub fn set_type_name(self, name: impl Into<String>) -> Result<Self, StageAuthoringError> {
        let name = name.into();
        self.edit(&[sdf::FieldKey::TypeName], |spec| spec.set_type_name(name))
    }

    /// Set the prim's `active` flag.
    pub fn set_active(self, active: bool) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::Active], |spec| spec.set_active(active))
    }

    /// Set the prim's `kind` metadata.
    pub fn set_kind(self, kind: impl Into<String>) -> Result<Self, StageAuthoringError> {
        let kind = kind.into();
        self.edit(&[sdf::FieldKey::Kind], |spec| spec.set_kind(kind))
    }

    /// Set the prim's `hidden` flag.
    pub fn set_hidden(self, hidden: bool) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::Hidden], |spec| spec.set_hidden(hidden))
    }

    /// Set the prim's `instanceable` flag.
    pub fn set_instanceable(self, instanceable: bool) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::Instanceable], |spec| {
            spec.set_instanceable(instanceable)
        })
    }

    /// Add an applied API schema name to this prim's `apiSchemas` metadata.
    ///
    /// This is the registry-free authoring operation behind C++
    /// `UsdPrim::AddAppliedSchema`: it edits the current edit target's
    /// `apiSchemas` list op in place rather than replacing existing list-op
    /// opinions. It does not validate that `name` is a registered API schema;
    /// schema-registry-backed `ApplyAPI` behavior is still future work.
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
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_prim_mut()) {
                Some(mut spec) => {
                    spec.add_applied_schema(name)?;
                    let mut cl = sdf::ChangeList::new();
                    cl.entry_mut(&path)
                        .info_changed
                        .insert(sdf::FieldKey::ApiSchemas.as_str());
                    Ok(cl)
                }
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no prim spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(self)
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
            // creating the spec for editing. Record `ADD_INERT_PRIM` for each
            // newly created spec so composition reslices.
            let had_spec = layer.data().has_spec(&path);
            // `missing_prim_ancestors` already filters out specs that exist, so
            // this is empty when the prim is already present.
            let auto_ancestors = layer.missing_prim_ancestors(&path);
            if !had_spec {
                layer.override_prim(path.clone())?;
            }
            let data = layer.writable_data_mut()?;
            let mut spec = data
                .spec_mut(&path)
                .and_then(|s| s.as_prim_mut())
                .expect("override_prim ensured a prim spec at the edit-target path");
            let value = f(spec.get(key).cloned());
            spec.add(key, value);

            let mut cl = sdf::ChangeList::new();
            if !had_spec {
                cl.entry_mut(&path).flags |= sdf::ChangeFlags::ADD_INERT_PRIM;
            }
            for anc in auto_ancestors {
                cl.entry_mut(&anc).flags |= sdf::ChangeFlags::ADD_INERT_PRIM;
            }
            cl.entry_mut(&path).info_changed.insert(key);
            Ok(cl)
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

    /// The prim's composed applied `apiSchemas`, flattened across all
    /// contributing opinions. Mirrors C++ `UsdPrim::GetAppliedSchemas`.
    /// Multi-apply instances appear as-is (e.g. `PhysicsLimitAPI:rotZ`).
    pub fn api_schemas(&self) -> anyhow::Result<Vec<Token>> {
        self.stage
            .masked(&self.path, |g, cache| cache.api_schemas(g, &self.path))
    }

    /// `true` when `name` is in the prim's composed `apiSchemas` (pass the full
    /// instance name for multi-apply schemas). Mirrors C++ `UsdPrim::HasAPI`.
    pub fn has_api_schema(&self, name: impl Into<Token>) -> anyhow::Result<bool> {
        let name = name.into();
        Ok(self.api_schemas()?.iter().any(|s| s.as_str() == name.as_str()))
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

    /// `true` if the prim is loaded — active, and no ancestor carries an
    /// unloaded payload. Mirrors C++ `UsdPrim::IsLoaded`.
    pub fn is_loaded(&self) -> anyhow::Result<bool> {
        if !self.is_active()? {
            return Ok(false);
        }
        if self.stage.load().load_payloads() {
            return Ok(true);
        }
        for path in Stage::prim_ancestors_inclusive(self.path.clone()) {
            if has_payload(&self.stage, &path)? {
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
        for path in Stage::prim_ancestors_inclusive(self.path.clone()) {
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
        for ancestor in Stage::prim_ancestors_inclusive(parent) {
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
        for path in Stage::prim_ancestors_inclusive(self.path.clone()) {
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

    /// Returns the composed property names of this prim. Mirrors C++
    /// `UsdPrim::GetPropertyNames`.
    pub fn property_names(&self) -> anyhow::Result<Vec<Token>> {
        self.stage
            .masked(&self.path, |g, cache| cache.prim_properties(g, &self.path))
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
    /// [`Stage::prim_at`](crate::usd::Stage::prim_at): a path with no
    /// contributing spec yields a handle that is not valid.
    pub fn is_valid(&self) -> anyhow::Result<bool> {
        self.stage.has_spec(&self.path)
    }

    /// Property paths under this prim whose composed spec type matches `ty`,
    /// preserving the composed property order.
    fn properties_of_type(&self, ty: sdf::SpecType) -> anyhow::Result<Vec<sdf::Path>> {
        let mut paths = Vec::new();
        for name in self.property_names()? {
            let path = self.property_path(&name);
            if self.stage.spec_type(&path)? == Some(ty) {
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
    /// `f`, and return `self` for chaining. `fields` names the metadata keys
    /// the closure intends to author so the cache invalidator can classify
    /// them. Surfaces `ReadOnly` if the layer can't be mutated, or
    /// `InvalidPath` if no prim spec exists at the path.
    fn edit<F>(self, fields: &[sdf::FieldKey], f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::PrimSpecMut<'_>),
    {
        let info_changed: Vec<&'static str> = fields.iter().map(sdf::FieldKey::as_str).collect();
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            // Detect the read-only case explicitly — otherwise `prim_mut`
            // returns `None` for both "no spec" and "layer not writable"
            // and we'd mask `ReadOnly` as `InvalidPath`.
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_prim_mut()) {
                Some(mut spec) => {
                    f(&mut spec);
                    let mut cl = sdf::ChangeList::new();
                    let entry = cl.entry_mut(&path);
                    for name in &info_changed {
                        entry.info_changed.insert(name);
                    }
                    Ok(cl)
                }
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no prim spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(self)
    }
}

/// `true` when a non-empty `payload` opinion is composed at `prim` — the
/// per-prim check behind [`Prim::is_loaded`].
fn has_payload(stage: &Stage, prim: &sdf::Path) -> anyhow::Result<bool> {
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
    use crate::sdf;
    use crate::tf::Token;
    use crate::usd::Stage;

    fn stage() -> anyhow::Result<Stage> {
        Stage::builder().in_memory("anon.usda")
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
            vec![stage.prim_at("/A"), stage.prim_at("/B")]
            // `stage` is dropped here; each handle's cloned `Rc` keeps the
            // shared state alive.
        };

        assert_eq!(prims[0].path().as_str(), "/A");
        let type_name = prims[1].stage().prim_at(prims[1].path()).type_name()?;
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
        assert_eq!(size.get_at(10.0)?, Some(sdf::Value::Float(10.0)));

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
        assert_eq!(stage.prim_at("/Def").specifier()?, Some(sdf::Specifier::Def));
        assert_eq!(stage.prim_at("/Over").specifier()?, Some(sdf::Specifier::Over));
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
        let Some(sdf::Value::Dictionary(read)) = stage.prim_at("/A").custom_data()? else {
            panic!("customData should resolve to a dictionary");
        };
        assert_eq!(read.get("note"), Some(&sdf::Value::String("hi".into())));
        assert!(stage.prim_at("/B").custom_data()?.is_none());
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
        assert_eq!(stage.prim_at("/World").kind()?.as_deref(), Some("group"));
        Ok(())
    }

    #[test]
    fn add_api_schema() -> anyhow::Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?.add_applied_schema("MaterialBindingAPI")?;
        assert_eq!(
            stage.prim_at(prim.path()).api_schemas()?,
            vec![Token::from("MaterialBindingAPI")]
        );
        assert!(stage.prim_at(prim.path()).has_api_schema("MaterialBindingAPI")?);
        Ok(())
    }

    #[test]
    fn add_api_schema_merges() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/World")?;
        stage.with_target_layer_at(&sdf::Path::new("/World").expect("valid path"), |layer, _path| {
            let data = layer.writable_data_mut()?;
            let spec = data
                .spec_mut(&sdf::Path::new("/World").expect("valid path"))
                .expect("prim spec");
            spec.add(
                sdf::FieldKey::ApiSchemas,
                sdf::Value::TokenListOp(sdf::TokenListOp {
                    appended_items: vec![Token::from("ExistingAPI")],
                    ..Default::default()
                }),
            );
            let mut cl = sdf::ChangeList::new();
            cl.entry_mut(&sdf::Path::new("/World").expect("valid path"))
                .info_changed
                .insert(sdf::FieldKey::ApiSchemas.as_str());
            Ok(cl)
        })?;

        stage
            .override_prim("/World")?
            .add_applied_schema("ExistingAPI")?
            .add_applied_schema("NewAPI")?;

        let local = stage.field::<sdf::Value>("/World", sdf::FieldKey::ApiSchemas)?;
        let Some(sdf::Value::TokenListOp(op)) = local else {
            panic!("expected apiSchemas TokenListOp");
        };
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
}
