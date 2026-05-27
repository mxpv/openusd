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
//! triggers [`crate::pcp::Cache::invalidate_all`] on completion. The
//! per-call rebuild cost will drop once surgical, `PcpChanges`-style
//! invalidation lands; the per-call pattern itself stays.

use super::{Stage, StageAuthoringError};
use crate::sdf;

/// Stage-composed prim handle. Mirrors C++ `UsdPrim`.
#[derive(Clone)]
pub struct Prim<'s> {
    stage: &'s Stage,
    path: sdf::Path,
}

impl<'s> Prim<'s> {
    pub(super) fn new(stage: &'s Stage, path: sdf::Path) -> Self {
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
                Some(mut spec) => spec.add_applied_schema(name).map_err(Into::into),
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

    /// Borrow the prim spec at `self.path` on the edit target's layer, apply
    /// `f`, and return `self` for chaining. Surfaces `ReadOnly` if the layer
    /// can't be mutated, or `InvalidPath` if no prim spec exists at the path.
    fn edit<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::PrimSpecMut<'_>),
    {
        let path = self.path.clone();
        self.stage.with_target_layer(|layer| {
            // Detect the read-only case explicitly — otherwise `prim_mut`
            // returns `None` for both "no spec" and "layer not writable"
            // and we'd mask `ReadOnly` as `InvalidPath`.
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_prim_mut()) {
                Some(mut spec) => {
                    f(&mut spec);
                    Ok(true)
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
        self.edit(|spec| spec.add(sdf::FieldKey::Variability, sdf::Value::Variability(v)))
    }

    /// Set the attribute's `custom` flag. Always authors an explicit
    /// opinion (see [`Attribute::set_variability`] for the rationale).
    pub fn set_custom(self, custom: bool) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| spec.add(sdf::FieldKey::Custom, sdf::Value::Bool(custom)))
    }

    /// Set the default value. Mirrors C++ `UsdAttribute::Set(value)`.
    pub fn set(self, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
        let value = value.into();
        self.edit(|spec| spec.set_default(value))
    }

    /// Set a value at a specific time. Mirrors C++
    /// `UsdAttribute::Set(value, time)`.
    pub fn set_at(self, time: f64, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
        let value = value.into();
        self.edit(|spec| spec.set_time_sample(time, value))
    }

    /// Block opinions from weaker layers by authoring a value block on the
    /// default and every authored time sample. Mirrors C++
    /// `UsdAttribute::Block()`.
    pub fn block(self) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| {
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
        self.edit(|spec| spec.set_color_space(color_space))
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
    /// apply `f`, and return `self` for chaining. See [`Prim::edit`] for the
    /// `ReadOnly` vs `InvalidPath` discrimination.
    fn edit<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>),
    {
        let path = self.path.clone();
        self.stage.with_target_layer(|layer| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_attr_mut()) {
                Some(mut spec) => {
                    f(&mut spec);
                    Ok(true)
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
        self.edit(|spec| spec.add(sdf::FieldKey::Variability, sdf::Value::Variability(v)))
    }

    /// Set the relationship's `custom` flag. Always authors an explicit
    /// opinion (see [`Attribute::set_variability`] for rationale).
    pub fn set_custom(self, custom: bool) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| spec.add(sdf::FieldKey::Custom, sdf::Value::Bool(custom)))
    }

    /// Append a target path. No-op if already present.
    pub fn add_target(self, target: sdf::Path) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| spec.add_target(target))
    }

    /// Replace the entire target list.
    pub fn set_targets<I: IntoIterator<Item = sdf::Path>>(self, targets: I) -> Result<Self, StageAuthoringError> {
        let targets: Vec<sdf::Path> = targets.into_iter().collect();
        self.edit(|spec| spec.set_target_paths(targets))
    }

    /// Remove a target path. Returns `Ok(true)` if it was present. Takes
    /// `&self` rather than consuming — `remove_target` returns a `bool` (not
    /// `Self`), so it doesn't fit the chain pattern. Skips cache invalidation
    /// when the target wasn't authored (no mutation occurred).
    pub fn remove_target(&self, target: &sdf::Path) -> Result<bool, StageAuthoringError> {
        let path = self.path.clone();
        let target = target.clone();
        self.stage.with_target_layer(|layer| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_relationship_mut()) {
                Some(mut spec) => Ok(spec.remove_target(&target)),
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no relationship spec at path on the edit target layer",
                }),
            }
        })
    }

    /// Borrow the relationship spec at `self.path` on the edit target's
    /// layer, apply `f`, and return `self` for chaining. See [`Prim::edit`]
    /// for the `ReadOnly` vs `InvalidPath` discrimination.
    fn edit<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::RelationshipSpecMut<'_>),
    {
        let path = self.path.clone();
        self.stage.with_target_layer(|layer| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_relationship_mut()) {
                Some(mut spec) => {
                    f(&mut spec);
                    Ok(true)
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
            Ok(true)
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
