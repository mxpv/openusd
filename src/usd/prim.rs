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
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_prim_mut()) {
                Some(mut spec) => {
                    let value = f(spec.get(key).cloned());
                    spec.add(key, value);
                    let mut cl = sdf::ChangeList::new();
                    cl.entry_mut(&path).info_changed.insert(key);
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
    pub fn create_attribute(&self, name: &str, type_name: impl Into<String>) -> Result<Attribute, StageAuthoringError> {
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
    pub fn create_relationship(&self, name: &str) -> Result<Relationship, StageAuthoringError> {
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

    /// Returns the prim stack: each `(layer identifier, spec path)` site that
    /// contributes a prim spec to this prim, strongest first. Mirrors C++
    /// `UsdPrim::GetPrimStack`.
    //
    // TODO: drop `anyhow::Result` once the cache plumbing returns a typed error.
    pub fn prim_stack(&self) -> anyhow::Result<Vec<(String, sdf::Path)>> {
        self.stage.try_or_handle(|cache| cache.prim_stack(&self.path))
    }

    /// Returns the `Time Offsets` composition-dump rows for this prim: one row
    /// per composition node carrying its cumulative time offset, plus a row for
    /// each non-identity sublayer member. Empty unless some node carries a
    /// non-identity offset. Used by the composition-results dump.
    pub fn time_offsets(&self) -> anyhow::Result<Vec<pcp::TimeOffset>> {
        self.stage.try_or_handle(|cache| cache.time_offsets(&self.path))
    }

    /// Returns the prohibited child names for this prim: names of children
    /// relocated away (renamed or deleted), sorted. Mirrors the prohibited-names
    /// out-param of C++ `PcpPrimIndex::ComputePrimChildNames`.
    pub fn prohibited_children(&self) -> anyhow::Result<Vec<String>> {
        self.stage.try_or_handle(|cache| cache.prohibited_children(&self.path))
    }

    /// Returns an [`Attribute`] handle for the property `name` under this prim.
    /// Mirrors C++ `UsdPrim::GetAttribute`. This is a value-type wrapper; it
    /// neither authors a spec nor asserts the attribute is composed. An invalid
    /// property name yields a handle whose path falls back to the prim, which
    /// resolves as empty.
    pub fn attribute(&self, name: &str) -> Attribute {
        Attribute::new(&self.stage, self.property_path(name))
    }

    /// Returns a [`Relationship`] handle for the property `name` under this
    /// prim. Mirrors C++ `UsdPrim::GetRelationship`. See [`Self::attribute`]
    /// for the handle's non-authoring, non-validating contract.
    pub fn relationship(&self, name: &str) -> Relationship {
        Relationship::new(&self.stage, self.property_path(name))
    }

    /// Property path for `name` under this prim, falling back to the prim path
    /// for an invalid name (the handle then resolves as empty).
    fn property_path(&self, name: &str) -> sdf::Path {
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
    //
    // TODO: drop `anyhow::Result` once the cache plumbing returns a typed error.
    pub fn get_all_variant_selections(&self) -> anyhow::Result<Vec<(String, String)>> {
        self.stage.try_or_handle(|cache| cache.variant_selections(&self.prim))
    }
}

#[cfg(test)]
mod tests {
    use crate::sdf;
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
            vec![stage.prim_at_path("/A"), stage.prim_at_path("/B")]
            // `stage` is dropped here; each handle's cloned `Rc` keeps the
            // shared state alive.
        };

        assert_eq!(prims[0].path().as_str(), "/A");
        let type_name = prims[1].stage().type_name(prims[1].path())?;
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
        stage.with_target_layer_at(&sdf::Path::new("/World").expect("valid path"), |layer, _path| {
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
