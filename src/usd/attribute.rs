//! Stage-composed attribute handle — a value-type wrapper around
//! `(stage, path)` that mirrors C++ `UsdAttribute`.
//!
//! Like [`Prim`], the handle is freely [`Clone`], holds no borrow on the
//! composition cache, and re-acquires state from the [`Stage`] per call. Its
//! fluent setters take `self` by value and return `Self`, so writes chain in a
//! single statement that ends with the final handle bound.

use super::{Prim, Stage, StageAuthoringError};
use crate::sdf;

/// Stage-composed attribute handle. Mirrors C++ `UsdAttribute`.
///
/// Returned by [`Stage::create_attribute`] / [`Prim::create_attribute`] with
/// defaults `variability = Varying`, `custom = true`, matching C++ generic
/// property authoring. Override via the fluent setters below.
#[derive(Clone)]
pub struct Attribute {
    stage: Stage,
    path: sdf::Path,
}

impl Attribute {
    pub(super) fn new(stage: &Stage, path: sdf::Path) -> Self {
        Self {
            stage: stage.clone(),
            path,
        }
    }

    /// Composed namespace path of the attribute (e.g. `/World/Mesh.points`).
    pub fn path(&self) -> &sdf::Path {
        &self.path
    }

    /// The stage this handle is anchored to.
    pub fn stage(&self) -> &Stage {
        &self.stage
    }

    /// Handle to the owning prim.
    pub fn prim(&self) -> Prim {
        Prim::new(&self.stage, self.path.prim_path())
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
        self.stage.with_target_layer_at(&self.path, |layer, path| {
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

    /// Wire this attribute to a single `source` property, replacing any
    /// existing connections. The connectable shorthand for
    /// [`set_connections`](Attribute::set_connections) over one source; mirrors
    /// C++ `UsdShadeInput` / `UsdShadeOutput::ConnectToSource`. Chains after
    /// [`create_attribute`](Prim::create_attribute) / a UsdShade
    /// `create_input` / `create_output`, since the connection is authored on
    /// this (the consuming) property's spec.
    pub fn connect_to(self, source: &Attribute) -> Result<Self, StageAuthoringError> {
        self.set_connections([source.path().clone()])
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
        let target = target.clone();
        // The target may exist only through weaker layers. Check the composed
        // list first so this call can author a delete opinion even when the
        // edit-target layer has no local connection item to remove.
        if !self.stage.connection_paths(&self.path)?.iter().any(|p| p == &target) {
            return Ok(false);
        }
        let type_name = self.stage.field::<String>(&self.path, sdf::FieldKey::TypeName)?;
        let mut removed = false;
        self.stage.with_target_layer_at(&self.path, |layer, spec_path| {
            let created_attr = !layer.data().has_spec(&spec_path);
            let auto_ancestors = if !created_attr {
                Vec::new()
            } else {
                // A delete list-op still needs a property spec to carry it.
                // Use the composed type name and leave `custom` unauthored so
                // the spec is only as strong as needed for the connection edit.
                let type_name = type_name.clone().ok_or_else(|| sdf::AuthoringError::InvalidPath {
                    path: spec_path.clone(),
                    reason: "cannot author connection delete for typeless composed attribute",
                })?;
                let owning_prim = spec_path.prim_path();
                let auto_ancestors = layer.missing_prim_chain_inclusive(&owning_prim);
                layer.create_attribute(spec_path.clone(), type_name, sdf::Variability::Varying, false)?;
                auto_ancestors
            };
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&spec_path).and_then(|s| s.as_attr_mut()) {
                Some(mut spec) => {
                    removed = spec.delete_connection_path(&target);
                    let mut cl = sdf::ChangeList::new();
                    if removed {
                        let entry = cl.entry_mut(&spec_path);
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
                    path: spec_path.clone(),
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
        self.stage.with_target_layer_at(&self.path, |layer, path| {
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

    /// Composes this attribute's connection paths together with the paths its
    /// list-op deletes, returned as `(connections, deleted)` (C++
    /// `PcpBuildFilteredTargetIndex` and its `deletedPaths` out-param). Both are
    /// empty when the owning prim is outside the population mask.
    pub fn compute_connections(&self) -> anyhow::Result<(Vec<sdf::Path>, Vec<sdf::Path>)> {
        self.stage
            .masked_property(&self.path, |cache| cache.compute_attribute_connection_paths(&self.path))
    }

    /// Composed default value decoded to `T`, if any layer authored one.
    /// Mirrors C++ `UsdAttribute::Get`.
    ///
    /// `T` is any type implementing `TryFrom<sdf::Value>` — a scalar
    /// (`get::<f32>()`), an array (`get::<Vec<f32>>()`), or [`sdf::Value`]
    /// itself (`get::<sdf::Value>()`) for the raw value. A type mismatch
    /// against the authored value surfaces as an `Err`, not `None`.
    //
    // TODO: drop `anyhow::Result` once `Stage::field` returns a typed error.
    pub fn get<T>(&self) -> anyhow::Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        self.stage.field::<T>(&self.path, sdf::FieldKey::Default)
    }

    /// Composed value at `time` decoded to `T`, applying the stage's
    /// interpolation type. The time-sampled counterpart of [`Attribute::get`];
    /// mirrors C++ `UsdAttribute::Get(time)`.
    //
    // TODO: drop `anyhow::Result` once `Stage::value_at` returns a typed
    // error.
    pub fn get_at<T>(&self, time: f64) -> anyhow::Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        Ok(self.stage.value_at(&self.path, time)?.map(T::try_from).transpose()?)
    }

    /// Composed value of a generic metadata field on the attribute decoded to
    /// `T`, if any layer authored one. Mirrors C++
    /// `UsdObject::GetMetadata(name, &value)`.
    ///
    /// The read counterpart of [`Attribute::set_metadata`]; used for the
    /// schema-layered fields it authors (UsdGeom's `interpolation` /
    /// `elementSize` on primvars, UsdSkel's inbetween `weight`, …). Decode to
    /// the field's type (`get_metadata::<i32>("elementSize")`) or to
    /// [`sdf::Value`] for the raw value.
    //
    // TODO: drop `anyhow::Result` once `Stage::field` returns a typed error.
    pub fn get_metadata<T>(&self, key: &str) -> anyhow::Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        self.stage.field::<T>(&self.path, key)
    }

    /// Composed `timeSamples` map.
    //
    // TODO: drop `anyhow::Result` once `Stage::time_samples` returns a typed
    // error.
    pub fn time_samples(&self) -> anyhow::Result<Option<sdf::TimeSampleMap>> {
        self.stage.time_samples(&self.path)
    }

    /// Returns the property stack: each `(layer identifier, spec path)` site
    /// that authors a spec for this attribute, strongest first. Mirrors C++
    /// `UsdProperty::GetPropertyStack`.
    //
    // TODO: drop `anyhow::Result` once the cache plumbing returns a typed error.
    pub fn property_stack(&self) -> anyhow::Result<Vec<(String, sdf::Path)>> {
        self.stage.try_or_handle(|cache| cache.property_stack(&self.path))
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
        let info_changed: Vec<&'static str> = fields.iter().map(sdf::FieldKey::as_str).collect();
        self.stage.with_target_layer_at(&self.path, |layer, path| {
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

#[cfg(test)]
mod tests {
    use crate::sdf;
    use crate::usd::Stage;

    fn stage() -> anyhow::Result<Stage> {
        Stage::builder().in_memory("anon.usda")
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
        assert_eq!(attr.get::<sdf::Value>()?, None);
        assert_eq!(attr.get_at::<sdf::Value>(0.0)?, None);
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
        assert_eq!(attr.get_at::<sdf::Value>(0.0)?, None);
        assert_eq!(attr.get_at::<sdf::Value>(5.0)?, None);
        assert_eq!(attr.get_at::<sdf::Value>(10.0)?, None);
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
}
