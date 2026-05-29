//! Stage-composed handles — value-type wrappers around `(stage, path)` that
//! mirror C++ `UsdPrim`, `UsdAttribute`, and `UsdRelationship`.
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

use super::{Stage, StageAuthoringError};
use crate::sdf;

/// Stage-composed prim handle. Mirrors C++ `UsdPrim`.
#[derive(Clone)]
pub struct Prim<'s> {
    stage: &'s Stage,
    path: sdf::Path,
}

impl<'s> Prim<'s> {
    pub(crate) fn new(stage: &'s Stage, path: sdf::Path) -> Self {
        Self { stage, path }
    }

    /// Composed namespace path of the prim.
    pub fn path(&self) -> &sdf::Path {
        &self.path
    }

    /// The stage this handle is anchored to.
    pub fn stage(&self) -> &'s Stage {
        self.stage
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
        let path = self.path.clone();
        let name = name.into();
        self.stage.with_target_layer(|layer| {
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

    /// Author an attribute spec named `name` under this prim. Mirrors C++
    /// `UsdPrim::CreateAttribute`. Defaults `variability = Varying`,
    /// `custom = true` — override via the returned [`Attribute`] handle's
    /// fluent setters.
    pub fn create_attribute(
        &self,
        name: &str,
        type_name: impl Into<String>,
    ) -> Result<Attribute<'s>, StageAuthoringError> {
        let attr_path = self.path.append_property(name).map_err(|_| {
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
    pub fn create_relationship(&self, name: &str) -> Result<Relationship<'s>, StageAuthoringError> {
        let rel_path = self.path.append_property(name).map_err(|_| {
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
    pub fn author_relationship_targets<I, P>(
        &self,
        name: &str,
        targets: I,
    ) -> Result<Relationship<'s>, StageAuthoringError>
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
            Some(sdf::Value::TokenVec(v) | sdf::Value::StringVec(v)) => v,
            Some(sdf::Value::TokenListOp(op)) => op.flatten(),
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
            .set(sdf::Value::TokenVec(updated))?;
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

    /// Returns `true` if this prim is an instance (spec 11.3.3): `instanceable`
    /// resolves true and the prim has a composition arc.
    pub fn is_instance(&self) -> anyhow::Result<bool> {
        self.stage.is_instance(self.path.clone())
    }

    /// Returns the shared prototype path (`/__Prototype_N`) for this prim if it
    /// is an instance, else `None` (spec 11.3.3).
    pub fn prototype(&self) -> anyhow::Result<Option<sdf::Path>> {
        self.stage.get_prototype(self.path.clone())
    }

    /// Returns `true` if this prim is a prototype root (`/__Prototype_N`).
    pub fn is_prototype(&self) -> anyhow::Result<bool> {
        self.stage.is_prototype(self.path.clone())
    }

    /// Returns `true` if this prim lies within a prototype's namespace.
    pub fn is_in_prototype(&self) -> anyhow::Result<bool> {
        self.stage.is_in_prototype(self.path.clone())
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
        let path = self.path.clone();
        let info_changed: Vec<&'static str> = fields.iter().map(sdf::FieldKey::as_str).collect();
        self.stage.with_target_layer(|layer| {
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

/// Stage-composed attribute handle. Mirrors C++ `UsdAttribute`.
///
/// Returned by [`Stage::create_attribute`] / [`Prim::create_attribute`] with
/// defaults `variability = Varying`, `custom = true`, matching C++ generic
/// property authoring. Override via the fluent setters below.
#[derive(Clone)]
pub struct Attribute<'s> {
    stage: &'s Stage,
    path: sdf::Path,
}

impl<'s> Attribute<'s> {
    pub(super) fn new(stage: &'s Stage, path: sdf::Path) -> Self {
        Self { stage, path }
    }

    /// Composed namespace path of the attribute (e.g. `/World/Mesh.points`).
    pub fn path(&self) -> &sdf::Path {
        &self.path
    }

    /// The stage this handle is anchored to.
    pub fn stage(&self) -> &'s Stage {
        self.stage
    }

    /// Handle to the owning prim.
    pub fn prim(&self) -> Prim<'s> {
        Prim::new(self.stage, self.path.prim_path())
    }

    /// Set the attribute's `variability` field. Always authors an explicit
    /// opinion so weaker layers don't bubble up through composition; use
    /// the Sdf-tier `Spec::remove` directly if you instead want to clear the
    /// local opinion entirely.
    pub fn set_variability(self, v: sdf::Variability) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::Variability], |spec| {
            spec.add(sdf::FieldKey::Variability, sdf::Value::Variability(v))
        })
    }

    /// Set the attribute's `custom` flag. Always authors an explicit
    /// opinion (see [`Attribute::set_variability`] for the rationale).
    pub fn set_custom(self, custom: bool) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::Custom], |spec| {
            spec.add(sdf::FieldKey::Custom, sdf::Value::Bool(custom))
        })
    }

    /// Set the default value. Mirrors C++ `UsdAttribute::Set(value)`.
    pub fn set(self, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
        let value = value.into();
        self.edit(&[sdf::FieldKey::Default], |spec| spec.set_default(value))
    }

    /// Set a value at a specific time. Mirrors C++
    /// `UsdAttribute::Set(value, time)`.
    pub fn set_at(self, time: f64, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
        let value = value.into();
        self.edit(&[sdf::FieldKey::TimeSamples], |spec| spec.set_time_sample(time, value))
    }

    /// Block opinions from weaker layers by authoring a value block on the
    /// default and every authored time sample. Mirrors C++
    /// `UsdAttribute::Block()`.
    pub fn block(self) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::Default, sdf::FieldKey::TimeSamples], |spec| {
            spec.set_default(sdf::Value::ValueBlock);
            // Block every authored time sample too — otherwise `get_at` would
            // still resolve weaker opinions through the cached samples.
            if let Some(sdf::Value::TimeSamples(samples)) = spec.get_mut(sdf::FieldKey::TimeSamples.as_str()) {
                for (_, value) in samples.iter_mut() {
                    *value = sdf::Value::ValueBlock;
                }
            }
        })
    }

    /// Set the `colorSpace` token.
    pub fn set_color_space(self, color_space: impl Into<String>) -> Result<Self, StageAuthoringError> {
        let color_space = color_space.into();
        self.edit(&[sdf::FieldKey::ColorSpace], |spec| spec.set_color_space(color_space))
    }

    /// Author a generic metadata field on the attribute spec. Mirrors C++
    /// `UsdAttribute::SetMetadata(name, value)`.
    ///
    /// Used for fields the schema layers on top of the core attribute
    /// metadata (e.g. UsdSkel's `weight` on `inbetweens:NAME`, UsdGeom's
    /// `elementSize` / `interpolation` on primvars). The dedicated setters
    /// above (`set_variability`, `set_custom`, `set_color_space`) cover the
    /// common cases — reach for this one when the schema requires a custom
    /// field key not represented by [`sdf::FieldKey`].
    ///
    /// `key` is `&'static str` so the change-tracking layer can record it
    /// without copying; pass a `pub const FOO: &str = "..."` token rather than
    /// a runtime-built string.
    pub fn set_metadata(self, key: &'static str, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
        let value = value.into();
        let path = self.path.clone();
        self.stage.with_target_layer(|layer| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_attr_mut()) {
                Some(mut spec) => {
                    spec.add(key, value);
                    let mut cl = sdf::ChangeList::new();
                    cl.entry_mut(&path).info_changed.insert(key);
                    Ok(cl)
                }
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no attribute spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(self)
    }

    /// Author the attribute's `connectionPaths` — the `.connect` targets
    /// that wire this attribute to other properties. Mirrors C++
    /// `UsdAttribute::SetConnections` / `UsdShadeInput::ConnectToSource`.
    ///
    /// Each path is a full property path including its namespace, e.g.
    /// `</Mat/Tex.outputs:rgb>` or `</Mat.inputs:diffuseColor>`. Replaces
    /// any previously authored connections (the list op is written
    /// `explicit`). This is the primitive every UsdShade input/output
    /// connection is built on.
    pub fn set_connections<I>(self, targets: I) -> Result<Self, StageAuthoringError>
    where
        I: IntoIterator<Item = sdf::Path>,
    {
        let targets: Vec<sdf::Path> = targets.into_iter().collect();
        self.edit(&[sdf::FieldKey::ConnectionPaths], |spec| {
            spec.set_connection_paths(targets)
        })
    }

    /// Add a single connection target at the default USD list position.
    /// No-op if already present (skips cache invalidation in that case).
    /// Joins the prepended-items list op, matching C++
    /// `UsdAttribute::AddConnection`'s default back-of-prepend position.
    pub fn add_connection(self, target: sdf::Path) -> Result<Self, StageAuthoringError> {
        self.add_connection_at(target, true)
    }

    /// Add a single connection target to the prepended list op. No-op if
    /// already present. This is the explicit spelling of the default USD
    /// AddConnection position.
    pub fn add_connection_prepended(self, target: sdf::Path) -> Result<Self, StageAuthoringError> {
        self.add_connection_at(target, true)
    }

    /// Add a single connection target to the appended list op. No-op if
    /// already present. Use this when the new target should compose behind
    /// prepended opinions from this layer.
    pub fn add_connection_appended(self, target: sdf::Path) -> Result<Self, StageAuthoringError> {
        self.add_connection_at(target, false)
    }

    fn add_connection_at(self, target: sdf::Path, prepend: bool) -> Result<Self, StageAuthoringError> {
        let path = self.path.clone();
        // Dedup against the composed result, not just the local edit-target
        // op. Otherwise adding a weaker-layer target would author a stronger
        // duplicate and could accidentally reorder it.
        if self.stage.connection_paths(&path)?.iter().any(|p| p == &target) {
            return Ok(self);
        }
        self.edit_connection(move |spec| spec.add_connection_path(target, prepend))
    }

    /// Remove a single connection target. Returns `Ok(true)` if it was
    /// present. Takes `&self` (returns `bool`, not `Self`, so it doesn't
    /// chain). Mirrors C++ `UsdAttribute::RemoveConnection`.
    pub fn remove_connection(&self, target: &sdf::Path) -> Result<bool, StageAuthoringError> {
        let path = self.path.clone();
        let target = target.clone();
        // The target may exist only through weaker layers. Check the composed
        // list first so this call can author a delete opinion even when the
        // edit-target layer has no local connection item to remove.
        if !self.stage.connection_paths(&path)?.iter().any(|p| p == &target) {
            return Ok(false);
        }
        let type_name = self.stage.field::<String>(&path, sdf::FieldKey::TypeName)?;
        let mut removed = false;
        self.stage.with_target_layer(|layer| {
            let created_attr = !layer.data().has_spec(&path);
            let auto_ancestors = if !created_attr {
                Vec::new()
            } else {
                // A delete list-op still needs a property spec to carry it.
                // Use the composed type name and leave `custom` unauthored so
                // the spec is only as strong as needed for the connection edit.
                let type_name = type_name.clone().ok_or_else(|| sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "cannot author connection delete for typeless composed attribute",
                })?;
                let owning_prim = path.prim_path();
                let auto_ancestors = layer.missing_prim_chain_inclusive(&owning_prim);
                layer.create_attribute(path.clone(), type_name, sdf::Variability::Varying, false)?;
                auto_ancestors
            };
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_attr_mut()) {
                Some(mut spec) => {
                    removed = spec.delete_connection_path(&target);
                    let mut cl = sdf::ChangeList::new();
                    if removed {
                        let entry = cl.entry_mut(&path);
                        if created_attr {
                            entry.flags |= sdf::ChangeFlags::ADD_PROPERTY;
                        }
                        entry.flags |= sdf::ChangeFlags::CHANGE_ATTRIBUTE_CONNECTION;
                        entry.info_changed.insert(sdf::FieldKey::ConnectionPaths.as_str());
                    }
                    for anc in auto_ancestors {
                        cl.entry_mut(&anc).flags |= sdf::ChangeFlags::ADD_INERT_PRIM;
                    }
                    Ok(cl)
                }
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no attribute spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(removed)
    }

    /// Clear all authored `connectionPaths` on the edit target. Skips
    /// cache invalidation when no opinion was authored. Mirrors C++
    /// `UsdAttribute::ClearConnections`.
    pub fn clear_connections(self) -> Result<Self, StageAuthoringError> {
        self.edit_connection(|spec| spec.clear_connection_paths())
    }

    /// Run `f` on the attribute spec at the edit target's layer, and only
    /// record a `ChangeList` entry (driving cache invalidation) when `f`
    /// reports an actual mutation. The shared helper for the connection
    /// authoring methods above.
    fn edit_connection<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>) -> bool,
    {
        let path = self.path.clone();
        self.stage.with_target_layer(|layer| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_attr_mut()) {
                Some(mut spec) => {
                    let mut cl = sdf::ChangeList::new();
                    if f(&mut spec) {
                        let entry = cl.entry_mut(&path);
                        entry.flags |= sdf::ChangeFlags::CHANGE_ATTRIBUTE_CONNECTION;
                        entry.info_changed.insert(sdf::FieldKey::ConnectionPaths.as_str());
                    }
                    Ok(cl)
                }
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no attribute spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(self)
    }

    /// `true` when any connection opinion is authored — including an
    /// explicit-empty list op (`.connect = []`), the canonical way to
    /// block weaker-layer connections. Mirrors C++
    /// `UsdAttribute::HasAuthoredConnections`.
    //
    // TODO: drop `anyhow::Result` once `Stage::field` returns a typed error.
    pub fn has_authored_connections(&self) -> anyhow::Result<bool> {
        Ok(self
            .stage
            .field::<sdf::Value>(&self.path, sdf::FieldKey::ConnectionPaths)?
            .is_some())
    }

    /// Composed `connectionPaths`, with list-op edits folded across every
    /// contributing layer. Returns an empty vec when no connection is
    /// authored. Mirrors C++ `UsdAttribute::GetConnections`.
    //
    // TODO: drop `anyhow::Result` once `Stage::connection_paths` returns
    // a typed error.
    pub fn get_connections(&self) -> anyhow::Result<Vec<sdf::Path>> {
        self.stage.connection_paths(&self.path)
    }

    /// Composed default value, if any layer authored one.
    //
    // TODO: drop `anyhow::Result` once `Stage::field` returns a typed error.
    pub fn get(&self) -> anyhow::Result<Option<sdf::Value>> {
        self.stage.field::<sdf::Value>(&self.path, sdf::FieldKey::Default)
    }

    /// Composed value at `time`, applying the stage's interpolation type.
    /// Mirrors C++ `UsdAttribute::Get(time)`.
    //
    // TODO: drop `anyhow::Result` once `Stage::value_at` returns a typed
    // error.
    pub fn get_at(&self, time: f64) -> anyhow::Result<Option<sdf::Value>> {
        self.stage.value_at(&self.path, time)
    }

    /// Composed `timeSamples` map.
    //
    // TODO: drop `anyhow::Result` once `Stage::time_samples` returns a typed
    // error.
    pub fn time_samples(&self) -> anyhow::Result<Option<sdf::TimeSampleMap>> {
        self.stage.time_samples(&self.path)
    }

    /// Borrow the attribute spec at `self.path` on the edit target's layer,
    /// apply `f`, and return `self` for chaining. `fields` names the metadata
    /// keys the closure intends to author so the cache invalidator can
    /// classify them. See [`Prim::edit`] for the `ReadOnly` vs `InvalidPath`
    /// discrimination.
    fn edit<F>(self, fields: &[sdf::FieldKey], f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>),
    {
        let path = self.path.clone();
        let info_changed: Vec<&'static str> = fields.iter().map(sdf::FieldKey::as_str).collect();
        self.stage.with_target_layer(|layer| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_attr_mut()) {
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
                    reason: "no attribute spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(self)
    }
}

/// Stage-composed relationship handle. Mirrors C++ `UsdRelationship`.
///
/// Returned by [`Stage::create_relationship`] / [`Prim::create_relationship`]
/// with defaults `variability = Varying`, `custom = true`, matching C++
/// generic property authoring. Override via the fluent setters below.
#[derive(Clone)]
pub struct Relationship<'s> {
    stage: &'s Stage,
    path: sdf::Path,
}

impl<'s> Relationship<'s> {
    pub(super) fn new(stage: &'s Stage, path: sdf::Path) -> Self {
        Self { stage, path }
    }

    /// Composed namespace path of the relationship.
    pub fn path(&self) -> &sdf::Path {
        &self.path
    }

    /// The stage this handle is anchored to.
    pub fn stage(&self) -> &'s Stage {
        self.stage
    }

    /// Handle to the owning prim.
    pub fn prim(&self) -> Prim<'s> {
        Prim::new(self.stage, self.path.prim_path())
    }

    /// Set the relationship's `variability` field. Always authors an
    /// explicit opinion (see [`Attribute::set_variability`] for rationale).
    pub fn set_variability(self, v: sdf::Variability) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::Variability], false, |spec| {
            spec.add(sdf::FieldKey::Variability, sdf::Value::Variability(v))
        })
    }

    /// Set the relationship's `custom` flag. Always authors an explicit
    /// opinion (see [`Attribute::set_variability`] for rationale).
    pub fn set_custom(self, custom: bool) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::Custom], false, |spec| {
            spec.add(sdf::FieldKey::Custom, sdf::Value::Bool(custom))
        })
    }

    /// Append a target path. No-op if already present.
    pub fn add_target(self, target: sdf::Path) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::TargetPaths], true, |spec| spec.add_target(target))
    }

    /// Replace the entire target list.
    pub fn set_targets<I: IntoIterator<Item = sdf::Path>>(self, targets: I) -> Result<Self, StageAuthoringError> {
        let targets: Vec<sdf::Path> = targets.into_iter().collect();
        self.edit(&[sdf::FieldKey::TargetPaths], true, |spec| {
            spec.set_target_paths(targets)
        })
    }

    /// Remove a target path. Returns `Ok(true)` if it was present. Takes
    /// `&self` rather than consuming — `remove_target` returns a `bool` (not
    /// `Self`), so it doesn't fit the chain pattern. Skips cache invalidation
    /// when the target wasn't authored (no mutation occurred).
    pub fn remove_target(&self, target: &sdf::Path) -> Result<bool, StageAuthoringError> {
        let path = self.path.clone();
        let target = target.clone();
        let mut removed = false;
        self.stage.with_target_layer(|layer| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_relationship_mut()) {
                Some(mut spec) => {
                    removed = spec.remove_target(&target);
                    let mut cl = sdf::ChangeList::new();
                    if removed {
                        let entry = cl.entry_mut(&path);
                        entry.flags |= sdf::ChangeFlags::CHANGE_RELATIONSHIP_TARGETS;
                        entry.info_changed.insert(sdf::FieldKey::TargetPaths.as_str());
                    }
                    Ok(cl)
                }
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no relationship spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(removed)
    }

    /// `true` when any target opinion is authored — including an
    /// explicit-empty list op (`rel r = []`), the canonical way to block
    /// weaker-layer targets. Mirrors C++ `UsdRelationship::HasAuthoredTargets`.
    //
    // TODO: drop `anyhow::Result` once `Stage::field` returns a typed error.
    pub fn has_authored_targets(&self) -> anyhow::Result<bool> {
        Ok(self
            .stage
            .field::<sdf::Value>(&self.path, sdf::FieldKey::TargetPaths)?
            .is_some())
    }

    /// Composed raw `targetPaths`, with list-op edits folded across every
    /// contributing layer. Returns an empty vec when no target is authored.
    /// Mirrors C++ `UsdRelationship::GetTargets`.
    ///
    /// These are the raw targets (spec 12.4); target forwarding — recursively
    /// chasing relationship-to-relationship chains — is not applied.
    //
    // TODO: drop `anyhow::Result` once `Stage::relationship_targets` returns
    // a typed error.
    pub fn get_targets(&self) -> anyhow::Result<Vec<sdf::Path>> {
        self.stage.relationship_targets(&self.path)
    }

    /// Composed forwarded targets: any target that resolves to another
    /// relationship is replaced, recursively, by that relationship's forwarded
    /// targets, leaving only prim and attribute paths (spec 12.4). Cycles are
    /// broken and duplicates collapse. Mirrors C++
    /// `UsdRelationship::GetForwardedTargets`.
    //
    // TODO: drop `anyhow::Result` once `Stage::forwarded_relationship_targets`
    // returns a typed error.
    pub fn get_forwarded_targets(&self) -> anyhow::Result<Vec<sdf::Path>> {
        self.stage.forwarded_relationship_targets(&self.path)
    }

    /// Borrow the relationship spec at `self.path` on the edit target's
    /// layer, apply `f`, and return `self` for chaining. `fields` names the
    /// authored metadata keys; `targets_changed` sets the target-list flag
    /// in the change list. See [`Prim::edit`] for the `ReadOnly` vs
    /// `InvalidPath` discrimination.
    //
    // The change-list entry is recorded at the relationship's property
    // path, which `pcp::Changes::did_change` currently skips (no consumer
    // for relationship-target invalidation). Flag and `info_changed`
    // opinions are still emitted here so the producer side is in place
    // when a consumer lands.
    //
    // TODO: wire the consumer. When `Cache` starts memoizing per-attribute
    // composed values or per-relationship resolved-target lists:
    //   1. Add a `classify_property_entry` branch in `pcp/change.rs`
    //      mirroring `classify_prim_entry`, gated on
    //      `path.is_property_path()`. Inspect
    //      `entry.flags & CHANGE_RELATIONSHIP_TARGETS` and the
    //      `TargetPaths` / `ConnectionPaths` keys in `info_changed`.
    //   2. Decide tier: relationship/connection target list changes
    //      are conceptually tier-3 (spec-stack refresh) — they don't
    //      reshape the prim graph but they do invalidate composed
    //      target resolution. Insert the owning prim path into
    //      `did_change_specs` (or a new `did_change_targets` set keyed
    //      by property path).
    //   3. Extend `Changes::apply` to consume the new set by either
    //      dropping the owner's resolved-target cache or refreshing it
    //      in place. The current `did_change_specs` field is already
    //      reserved for this; right now the entry is dropped on the
    //      floor (see CacheChanges docs).
    //   4. Remove the `targets_changed` parameter from `edit` and the
    //      flag emission here if the classifier ends up not needing
    //      either signal (e.g. it can infer everything from
    //      `info_changed[TargetPaths]`). Until then both stay for
    //      forward-compat.
    fn edit<F>(self, fields: &[sdf::FieldKey], targets_changed: bool, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::RelationshipSpecMut<'_>),
    {
        let path = self.path.clone();
        let info_changed: Vec<&'static str> = fields.iter().map(sdf::FieldKey::as_str).collect();
        self.stage.with_target_layer(|layer| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_relationship_mut()) {
                Some(mut spec) => {
                    f(&mut spec);
                    let mut cl = sdf::ChangeList::new();
                    let entry = cl.entry_mut(&path);
                    if targets_changed {
                        entry.flags |= sdf::ChangeFlags::CHANGE_RELATIONSHIP_TARGETS;
                    }
                    for name in &info_changed {
                        entry.info_changed.insert(name);
                    }
                    Ok(cl)
                }
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no relationship spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use crate::sdf;
    use crate::usd::Stage;

    fn stage() -> anyhow::Result<Stage> {
        Stage::builder().in_memory("anon.usda")
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
        assert!(!a.is_in_prototype()?);

        let proto = super::Prim::new(&stage, sdf::path("/Proto")?);
        assert!(!proto.is_instance()?);
        assert!(proto.prototype()?.is_none());
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
        assert_eq!(stage.kind("/World")?.as_deref(), Some("group"));
        Ok(())
    }

    #[test]
    fn attribute_chain() -> anyhow::Result<()> {
        let stage = stage()?;
        let radius = stage
            .define_prim("/Sphere")?
            .set_type_name("Sphere")?
            .create_attribute("radius", "double")?
            .set_variability(sdf::Variability::Uniform)?
            .set(sdf::Value::Double(1.5))?;
        assert_eq!(radius.get()?, Some(sdf::Value::Double(1.5)));
        assert_eq!(
            stage.field::<sdf::Value>(radius.path(), sdf::FieldKey::Custom)?,
            Some(sdf::Value::Bool(true)),
        );
        assert_eq!(radius.path().as_str(), "/Sphere.radius");
        assert_eq!(radius.prim().path().as_str(), "/Sphere");
        Ok(())
    }

    #[test]
    fn attribute_time_samples() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(0.0, sdf::Value::Double(1.0))?
            .set_at(10.0, sdf::Value::Double(3.0))?;
        // Linear interpolation default → halfway = 2.0.
        assert_eq!(attr.get_at(5.0)?, Some(sdf::Value::Double(2.0)));
        let samples = attr.time_samples()?.expect("samples");
        assert_eq!(samples.len(), 2);
        Ok(())
    }

    #[test]
    fn attribute_block() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set(sdf::Value::Double(1.0))?
            .block()?;
        // ValueBlock resolves to None through Stage::field / value_at.
        assert_eq!(attr.get()?, None);
        assert_eq!(attr.get_at(0.0)?, None);
        Ok(())
    }

    /// `block()` must also replace every authored time-sample value with
    /// `ValueBlock` — otherwise the default block is silently bypassed for
    /// `get_at` queries that fall onto an authored sample.
    #[test]
    fn attribute_block_clears_time_samples() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(0.0, sdf::Value::Double(1.0))?
            .set_at(10.0, sdf::Value::Double(3.0))?
            .block()?;
        assert_eq!(attr.get_at(0.0)?, None);
        assert_eq!(attr.get_at(5.0)?, None);
        assert_eq!(attr.get_at(10.0)?, None);
        Ok(())
    }

    #[test]
    fn relationship_chain() -> anyhow::Result<()> {
        let stage = stage()?;
        let mesh = stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
        stage.define_prim("/World/Material")?.set_type_name("Material")?;
        stage.define_prim("/World/Material2")?.set_type_name("Material")?;
        let binding = mesh
            .create_relationship("material:binding")?
            .set_variability(sdf::Variability::Uniform)?
            .add_target(sdf::Path::new("/World/Material")?)?
            .add_target(sdf::Path::new("/World/Material2")?)?;
        assert!(binding.remove_target(&sdf::Path::new("/World/Material2")?)?);
        assert_eq!(stage.spec_type(binding.path())?, Some(sdf::SpecType::Relationship));
        assert_eq!(
            stage.field::<sdf::Value>(binding.path(), sdf::FieldKey::Custom)?,
            Some(sdf::Value::Bool(true)),
        );
        Ok(())
    }

    #[test]
    fn relationship_targets() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/World/Material")?.set_type_name("Material")?;
        stage.define_prim("/World/Material2")?.set_type_name("Material")?;
        let mesh = stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;

        let binding = mesh
            .create_relationship("material:binding")?
            .add_target(sdf::Path::new("/World/Material")?)?
            .add_target(sdf::Path::new("/World/Material2")?)?;
        assert!(binding.has_authored_targets()?);
        assert_eq!(
            binding.get_targets()?,
            vec![sdf::Path::new("/World/Material")?, sdf::Path::new("/World/Material2")?]
        );

        // Removing a target updates the composed list.
        assert!(binding.remove_target(&sdf::Path::new("/World/Material2")?)?);
        assert_eq!(binding.get_targets()?, vec![sdf::Path::new("/World/Material")?]);
        Ok(())
    }

    #[test]
    fn relationship_targets_unauthored() -> anyhow::Result<()> {
        let stage = stage()?;
        let rel = stage
            .define_prim("/World/Mesh")?
            .set_type_name("Mesh")?
            .create_relationship("material:binding")?;
        assert!(!rel.has_authored_targets()?);
        assert!(rel.get_targets()?.is_empty());
        Ok(())
    }

    /// Spec 12.4 example: `/foo.myRel` targets a prim and a relationship; the
    /// relationship forwards to two prims. Forwarding flattens the chain to
    /// only prim/attribute paths, while the raw targets keep the relationship.
    #[test]
    fn forwarded_targets_spec_example() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/foo")?;
        stage.define_prim("/foo/bar")?;
        stage.define_prim("/foo/foobar")?;
        stage.define_prim("/foo/foobar/barbaz")?;
        stage
            .define_prim("/baz")?
            .create_relationship("bazrel")?
            .set_targets([sdf::path("/foo/foobar")?, sdf::path("/foo/foobar/barbaz")?])?;
        let my_rel = stage
            .define_prim("/foo")?
            .create_relationship("myRel")?
            .set_targets([sdf::path("/foo/bar")?, sdf::path("/baz.bazrel")?])?;

        assert_eq!(
            my_rel.get_forwarded_targets()?,
            vec![
                sdf::path("/foo/bar")?,
                sdf::path("/foo/foobar")?,
                sdf::path("/foo/foobar/barbaz")?,
            ]
        );
        assert_eq!(
            my_rel.get_targets()?,
            vec![sdf::path("/foo/bar")?, sdf::path("/baz.bazrel")?]
        );
        Ok(())
    }

    /// Forwarding follows a multi-hop relationship chain to its terminal prim.
    #[test]
    fn forwarded_targets_multi_hop() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/Geom")?;
        let p = stage.define_prim("/P")?;
        p.create_relationship("c")?.set_targets([sdf::path("/Geom")?])?;
        p.create_relationship("b")?.set_targets([sdf::path("/P.c")?])?;
        let a = p.create_relationship("a")?.set_targets([sdf::path("/P.b")?])?;

        assert_eq!(a.get_forwarded_targets()?, vec![sdf::path("/Geom")?]);
        Ok(())
    }

    /// A pure relationship cycle forwards to no terminal targets without
    /// hanging.
    #[test]
    fn forwarded_targets_cycle() -> anyhow::Result<()> {
        let stage = stage()?;
        let p = stage.define_prim("/P")?;
        let a = p.create_relationship("a")?.set_targets([sdf::path("/P.b")?])?;
        p.create_relationship("b")?.set_targets([sdf::path("/P.a")?])?;

        assert!(a.get_forwarded_targets()?.is_empty());
        Ok(())
    }

    #[test]
    fn attribute_connections() -> anyhow::Result<()> {
        let stage = stage()?;
        let mat = stage.define_prim("/Mat")?.set_type_name("Material")?;
        mat.create_attribute("inputs:diffuseColor", "color3f")?;
        let tex_out = stage
            .define_prim("/Mat/Tex")?
            .set_type_name("Shader")?
            .create_attribute("outputs:rgb", "color3f")?;

        let input = stage
            .define_prim("/Mat/Surface")?
            .set_type_name("Shader")?
            .create_attribute("inputs:diffuseColor", "color3f")?
            .set_connections([tex_out.path().clone()])?;

        let conns = input.get_connections()?;
        assert_eq!(conns, vec![tex_out.path().clone()]);
        assert!(input.has_authored_connections()?);

        // Re-authoring replaces, doesn't append.
        let iface = sdf::Path::new("/Mat.inputs:diffuseColor")?;
        let input = input.set_connections([iface.clone()])?;
        assert_eq!(input.get_connections()?, vec![iface.clone()]);

        // add_connection prepends by default; dedups.
        let input = input.add_connection(tex_out.path().clone())?;
        assert_eq!(input.get_connections()?, vec![tex_out.path().clone(), iface.clone()]);
        let input = input.add_connection(tex_out.path().clone())?;
        assert_eq!(input.get_connections()?.len(), 2);

        // remove_connection.
        assert!(input.remove_connection(&iface)?);
        assert_eq!(input.get_connections()?, vec![tex_out.path().clone()]);
        assert!(!input.remove_connection(&iface)?);

        // clear_connections.
        let input = input.clear_connections()?;
        assert!(!input.has_authored_connections()?);
        assert!(input.get_connections()?.is_empty());
        Ok(())
    }

    #[test]
    fn authored_connections_explicit_empty() -> anyhow::Result<()> {
        // `set_connections([])` authors an explicit-empty list op, the
        // canonical way to block weaker-layer connection opinions.
        // `has_authored_connections` must see this as authored even though
        // the flattened list is empty.
        let stage = stage()?;
        let attr = stage
            .define_prim("/Surface")?
            .set_type_name("Shader")?
            .create_attribute("inputs:diffuseColor", "color3f")?
            .set_connections::<[sdf::Path; 0]>([])?;
        assert!(attr.has_authored_connections()?);
        assert!(attr.get_connections()?.is_empty());
        Ok(())
    }

    #[test]
    fn add_connection_prepends() -> anyhow::Result<()> {
        // First-time `add_connection` on a no-prior-opinion attribute must
        // author a non-explicit (prepended) list op, so weaker-layer
        // connection opinions still compose. Authoring `explicit` here
        // would silently block weaker layers.
        let stage = stage()?;
        let target = sdf::Path::new("/Tex.outputs:rgb")?;
        let attr = stage
            .define_prim("/Surface")?
            .set_type_name("Shader")?
            .create_attribute("inputs:diffuseColor", "color3f")?
            .add_connection(target.clone())?;

        let op = stage
            .field::<sdf::Value>(attr.path(), sdf::FieldKey::ConnectionPaths)?
            .unwrap()
            .try_as_path_list_op()
            .unwrap();
        assert!(!op.explicit, "first add_connection must not flip the op to explicit");
        assert!(op.explicit_items.is_empty());
        assert_eq!(op.prepended_items, vec![target]);
        assert!(op.appended_items.is_empty());
        Ok(())
    }

    #[test]
    fn add_connection_appended() -> anyhow::Result<()> {
        let stage = stage()?;
        let target = sdf::Path::new("/Tex.outputs:rgb")?;
        let attr = stage
            .define_prim("/Surface")?
            .set_type_name("Shader")?
            .create_attribute("inputs:diffuseColor", "color3f")?
            .add_connection_appended(target.clone())?;

        let op = stage
            .field::<sdf::Value>(attr.path(), sdf::FieldKey::ConnectionPaths)?
            .unwrap()
            .try_as_path_list_op()
            .unwrap();
        assert!(!op.explicit);
        assert_eq!(op.appended_items, vec![target]);
        assert!(op.prepended_items.is_empty());
        Ok(())
    }

    #[test]
    fn add_connection_prepend_on_explicit() -> anyhow::Result<()> {
        // When the existing op is `explicit` (e.g. authored via
        // `set_connections`), `add_connection_prepended` must honour the
        // prepend position by inserting at the front of `explicit_items`
        // rather than silently routing to the back.
        let stage = stage()?;
        let a = sdf::Path::new("/A.outputs:out")?;
        let b = sdf::Path::new("/B.outputs:out")?;
        let attr = stage
            .define_prim("/Surface")?
            .set_type_name("Shader")?
            .create_attribute("inputs:diffuseColor", "color3f")?
            .set_connections([a.clone()])?
            .add_connection_prepended(b.clone())?;

        let op = stage
            .field::<sdf::Value>(attr.path(), sdf::FieldKey::ConnectionPaths)?
            .unwrap()
            .try_as_path_list_op()
            .unwrap();
        assert!(op.explicit);
        assert_eq!(op.explicit_items, vec![b, a]);
        Ok(())
    }

    #[test]
    fn add_api_schema() -> anyhow::Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?.add_applied_schema("MaterialBindingAPI")?;
        assert_eq!(stage.api_schemas(prim.path())?, vec!["MaterialBindingAPI".to_string()]);
        assert!(stage.has_api_schema(prim.path(), "MaterialBindingAPI")?);
        Ok(())
    }

    #[test]
    fn add_api_schema_merges() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/World")?;
        stage.with_target_layer(|layer| {
            let data = layer.writable_data_mut()?;
            let spec = data
                .spec_mut(&sdf::Path::new("/World").expect("valid path"))
                .expect("prim spec");
            spec.add(
                sdf::FieldKey::ApiSchemas,
                sdf::Value::TokenListOp(sdf::TokenListOp {
                    appended_items: vec!["ExistingAPI".to_string()],
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
        assert_eq!(op.appended_items, vec!["ExistingAPI".to_string()]);
        assert_eq!(op.prepended_items, vec!["NewAPI".to_string()]);
        Ok(())
    }
}
