//! Stage-composed attribute handle — a value-type wrapper around
//! `(stage, path)` that mirrors C++ `UsdAttribute`.
//!
//! Like [`Prim`], the handle is freely [`Clone`], holds no borrow on the
//! composition cache, and re-acquires state from the [`Stage`] per call. Its
//! fluent setters take `self` by value and return `Self`, so writes chain in a
//! single statement that ends with the final handle bound.

use std::borrow::Cow;
use std::cell::RefCell;
use std::sync::Arc;

use super::{Prim, PrimTypeInfo, Stage, StageAuthoringError, TimeCode, interp};
use crate::pcp::AttributeValueSource;
use crate::sdf;
use crate::tf;

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

/// Where an attribute's resolved value comes from, reported by
/// [`Attribute::value_source`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueSource {
    /// A layer authors the value.
    Authored,
    /// No layer authors a value that survives composition, and the attribute's
    /// schema declares a fallback.
    Fallback,
    /// Neither, so the attribute reads back as no value at all.
    None,
}

impl Attribute {
    pub(crate) fn new(stage: &Stage, path: sdf::Path) -> Self {
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
        self.edit(|spec| {
            spec.set(sdf::FieldKey::Variability.as_str(), sdf::Value::Variability(v));
            Ok(())
        })
    }

    /// Set the attribute's `custom` flag. Always authors an explicit
    /// opinion (see [`Attribute::set_variability`] for the rationale).
    pub fn set_custom(self, custom: bool) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| {
            spec.set(sdf::FieldKey::Custom.as_str(), sdf::Value::Bool(custom));
            Ok(())
        })
    }

    /// Set the attribute's default value. The convenience spelling of
    /// `set_at(value, None)`; mirrors C++ `UsdAttribute::Set(value)`.
    pub fn set(self, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
        self.set_at(value, None)
    }

    /// Set the attribute's value at `time`. Mirrors C++
    /// `UsdAttribute::Set(value, time)`.
    ///
    /// `time` is `None` to author the default value, or `Some(tc)` (a
    /// [`usd::TimeCode`](super::TimeCode), which a bare `TimeCode` coerces
    /// into) to author a time sample. A numeric time is in stage (composed)
    /// time: when the current edit target is an arc with a non-identity layer
    /// offset, the sample is keyed at the inverse-mapped source-layer time (C++
    /// `UsdEditTarget::MapToSpecTime`), so it reads back at `time` once
    /// composition re-applies the offset.
    pub fn set_at(
        self,
        value: impl Into<sdf::Value>,
        time: impl Into<Option<super::TimeCode>>,
    ) -> Result<Self, StageAuthoringError> {
        let value = value.into();
        match time.into() {
            None => self.edit(|spec| {
                spec.set_default(value);
                Ok(())
            }),
            Some(time) => {
                let spec_time = self.stage.map_to_spec_time(time.value());
                self.edit(|spec| {
                    spec.set_time_sample(spec_time, value);
                    Ok(())
                })
            }
        }
    }

    /// Block opinions from weaker layers by authoring a value block on the
    /// default and every authored time sample. Mirrors C++
    /// `UsdAttribute::Block()`.
    pub fn block(self) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| {
            spec.set_default(sdf::Value::ValueBlock);
            // Block every authored time sample too — otherwise `get_at` would
            // still resolve weaker opinions through the cached samples.
            if let Some(mut samples) = spec.time_samples() {
                for (_, value) in samples.iter_mut() {
                    *value = sdf::Value::ValueBlock;
                }
                spec.set(sdf::FieldKey::TimeSamples.as_str(), sdf::Value::TimeSamples(samples));
            }
            Ok(())
        })
    }

    /// Set the `colorSpace` token.
    pub fn set_color_space(self, color_space: impl Into<String>) -> Result<Self, StageAuthoringError> {
        let color_space = color_space.into();
        self.edit(|spec| {
            spec.set_color_space(color_space);
            Ok(())
        })
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
        self.edit(|spec| {
            spec.set(key, value);
            Ok(())
        })
    }

    /// Remove a metadata field's opinion from the attribute's spec on the
    /// edit-target layer. Mirrors C++ `UsdObject::ClearMetadata`.
    ///
    /// Only the local opinion goes away; one on a weaker layer still composes.
    /// Erasing reaches only an attribute spec the layer already holds, so a
    /// property it says nothing about stays absent from it.
    pub fn clear_metadata(self, key: &'static str) -> Result<Self, StageAuthoringError> {
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            erase_attribute_field(layer.data_mut(), path, key);
            Ok(())
        })?;
        Ok(self)
    }

    /// Read-modify-write a metadata field on the attribute's spec at the edit
    /// target. `f` receives the field's current opinion on that layer (`None`
    /// when it is unauthored locally) and returns the value to author, or
    /// `None` to remove the local opinion.
    ///
    /// The attribute-level sibling of [`Prim::update_metadata`]: reading the
    /// local opinion rather than the composed value keeps opinions on weaker
    /// layers from being flattened into the edit target, which matters for the
    /// dictionary-valued fields value resolution merges key-by-key across
    /// layers (spec 12.2.5), such as UsdShade's `sdrMetadata`.
    ///
    /// The read is fallible so an undecodable local field surfaces instead of
    /// reading back as absent and being overwritten.
    ///
    /// `key` is `&'static str` for the same change-tracking reason as
    /// [`set_metadata`](Self::set_metadata).
    pub fn update_metadata<F>(self, key: &'static str, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(Option<sdf::Value>) -> Option<sdf::Value>,
    {
        let declared = self.declared_spec().map_err(StageAuthoringError::Composition)?;
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            let local = layer.data_mut().try_field(&path, key)?.map(Cow::into_owned);
            // Erasing reaches only an attribute spec this layer already holds,
            // so a property it says nothing about stays absent from it.
            let Some(value) = f(local) else {
                erase_attribute_field(layer.data_mut(), path, key);
                return Ok(());
            };
            // Authoring needs a spec, which the schema declaration supplies when
            // the layer has none.
            declare_spec(layer.data_mut(), &path, &declared)?;
            super::edit_spec(
                layer.data_mut(),
                path,
                "no attribute spec at path on the edit target layer",
                sdf::AttributeSpecMut::get,
                |spec| {
                    spec.set(key, value);
                    Ok(())
                },
            )
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
    pub fn set_connections(self, targets: impl IntoIterator<Item: sdf::IntoPath>) -> Result<Self, StageAuthoringError> {
        let targets: Vec<sdf::Path> = targets.into_iter().map(sdf::try_into_path).collect::<Result<_, _>>()?;
        self.edit(|spec| Ok(spec.set_connection_paths(targets)?))
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
    pub fn add_connection(self, target: impl sdf::IntoPath) -> Result<Self, StageAuthoringError> {
        self.add_connection_at(sdf::try_into_path(target)?, true)
    }

    /// Add a single connection target to the prepended list op. No-op if
    /// already present. This is the explicit spelling of the default USD
    /// `AddConnection` position.
    pub fn add_connection_prepended(self, target: impl sdf::IntoPath) -> Result<Self, StageAuthoringError> {
        self.add_connection_at(sdf::try_into_path(target)?, true)
    }

    /// Add a single connection target to the appended list op. No-op if
    /// already present. Use this when the new target should compose behind
    /// prepended opinions from this layer.
    pub fn add_connection_appended(self, target: impl sdf::IntoPath) -> Result<Self, StageAuthoringError> {
        self.add_connection_at(sdf::try_into_path(target)?, false)
    }

    fn add_connection_at(self, target: sdf::Path, prepend: bool) -> Result<Self, StageAuthoringError> {
        // Dedup against the composed result, not just the local edit-target
        // op. Otherwise adding a weaker-layer target would author a stronger
        // duplicate and could accidentally reorder it.
        if self.connections()?.iter().any(|p| p == &target) {
            return Ok(self);
        }
        self.edit_connection(move |spec| Ok(spec.add_connection_path(target, prepend)?))
    }

    /// Remove a single connection target. Returns `Ok(true)` if it was
    /// present. Takes `&self` (returns `bool`, not `Self`, so it doesn't
    /// chain). Mirrors C++ `UsdAttribute::RemoveConnection`.
    pub fn remove_connection(&self, target: impl sdf::IntoPath) -> Result<bool, StageAuthoringError> {
        let target = sdf::try_into_path(target)?;
        // The target may exist only through weaker layers. Check the composed
        // list first so this call can author a delete opinion even when the
        // edit-target layer has no local connection item to remove.
        if !self.connections()?.iter().any(|p| p == &target) {
            return Ok(false);
        }
        let type_name = self.stage.field::<tf::Token>(&self.path, sdf::FieldKey::TypeName)?;
        let mut removed = false;
        self.stage.with_target_layer_at(&self.path, |layer, spec_path| {
            if !layer.data().has_spec(&spec_path) {
                // A delete list-op still needs a property spec to carry it.
                // Use the composed type name and leave `custom` unauthored so
                // the spec is only as strong as needed for the connection edit.
                let type_name = type_name.clone().ok_or_else(|| sdf::AuthoringError::InvalidPath {
                    path: spec_path.clone(),
                    reason: "cannot author connection delete for typeless composed attribute",
                })?;
                sdf::AttributeSpec::new(
                    layer.data_mut(),
                    spec_path.clone(),
                    type_name,
                    sdf::Variability::Varying,
                    false,
                )?;
            }
            super::edit_spec(
                layer.data_mut(),
                spec_path,
                "no attribute spec at path on the edit target layer",
                sdf::AttributeSpecMut::get,
                |spec| {
                    removed = spec.delete_connection_path(&target)?;
                    Ok(())
                },
            )
        })?;
        Ok(removed)
    }

    /// Clear all authored `connectionPaths` on the edit target. Skips
    /// cache invalidation when no opinion was authored. Mirrors C++
    /// `UsdAttribute::ClearConnections`.
    pub fn clear_connections(self) -> Result<Self, StageAuthoringError> {
        self.edit_connection(|spec| Ok(spec.clear_connection_paths()))
    }

    /// Run `f` on the attribute spec at the edit target's layer. The layer
    /// records a `connectionPaths` change (driving cache invalidation) only
    /// when `f` actually mutates the field. The shared
    /// helper for the connection authoring methods above.
    fn edit_connection<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>) -> Result<bool, sdf::AuthoringError>,
    {
        self.edit_spec(|spec| f(spec).map(|_| ()))?;
        Ok(self)
    }

    /// `true` when any connection opinion is authored — including an
    /// explicit-empty list op (`.connect = []`), the canonical way to
    /// block weaker-layer connections. Mirrors C++
    /// `UsdAttribute::HasAuthoredConnections`.
    pub fn has_authored_connections(&self) -> anyhow::Result<bool> {
        Ok(self
            .stage
            .field::<sdf::Value>(&self.path, sdf::FieldKey::ConnectionPaths)?
            .is_some())
    }

    /// Composed `connectionPaths`, with list-op edits folded across every
    /// contributing layer (prepend / append / add / delete). Returns an empty
    /// vec when no connection is authored, the path is not a property, or the
    /// owning prim is outside the population mask. Mirrors C++
    /// `UsdAttribute::GetConnections`.
    pub fn connections(&self) -> anyhow::Result<Vec<sdf::Path>> {
        self.stage
            .masked(&self.path, |g, cache| cache.connection_paths(g, &self.path))
    }

    /// Composes this attribute's connection paths together with the paths its
    /// list-op deletes, returned as `(connections, deleted)` (C++
    /// `PcpBuildFilteredTargetIndex` and its `deletedPaths` out-param). Both are
    /// empty when the owning prim is outside the population mask.
    pub fn compute_connections(&self) -> anyhow::Result<(Vec<sdf::Path>, Vec<sdf::Path>)> {
        self.stage.masked(&self.path, |g, cache| {
            cache.compute_attribute_connection_paths(g, &self.path)
        })
    }

    /// Composed `variability` for this attribute (spec 12.2.3: the weakest
    /// authored opinion wins). Mirrors C++ `UsdAttribute::GetVariability`.
    ///
    /// A schema that declares this attribute wins outright: variability is part
    /// of the declaration, so an authored opinion cannot make a `uniform`
    /// attribute animate.
    pub fn variability(&self) -> anyhow::Result<Option<sdf::Variability>> {
        if let Some(declared) = self.declared_variability()? {
            return Ok(Some(declared));
        }
        self.stage
            .field::<sdf::Variability>(&self.path, sdf::FieldKey::Variability)
    }

    /// The variability this attribute's schema declares, if a schema declares
    /// the attribute at all.
    ///
    /// A schema that omits the field declares the default, so this is a
    /// property of the declaration existing — not of the field being authored.
    fn declared_variability(&self) -> anyhow::Result<Option<sdf::Variability>> {
        let Some((info, name)) = self.declaring_property()? else {
            return Ok(None);
        };
        Ok(info
            .prim_definition()
            .property(&name)
            .map(|property| property.variability()))
    }

    /// `true` when this attribute is composed as `custom` (spec 12.2.4: true if
    /// *any* opinion in the stack is true). Mirrors C++ `UsdProperty::IsCustom`;
    /// an unauthored `custom` field resolves to `false`.
    ///
    /// A property a schema declares is never custom — that is what `custom`
    /// means — so an authored `custom` opinion on one is ignored.
    pub fn is_custom(&self) -> anyhow::Result<bool> {
        if self.declaring_property()?.is_some() {
            return Ok(false);
        }
        Ok(self
            .stage
            .field::<bool>(&self.path, sdf::FieldKey::Custom)?
            .unwrap_or(false))
    }

    /// `true` when an attribute is composed at this path — an authored spec,
    /// or a declaration from the owning prim's schema. Mirrors C++
    /// `UsdAttribute::IsDefined`.
    ///
    /// The composed spec answers first and a schema declaration answers for a
    /// path no layer authors, so a relationship composed where a schema
    /// declares an attribute is not one.
    pub fn is_defined(&self) -> anyhow::Result<bool> {
        let spec_type = match self.stage.spec_type(&self.path)? {
            Some(spec_type) => Some(spec_type),
            None => self.declared_spec_type()?,
        };
        Ok(spec_type == Some(sdf::SpecType::Attribute))
    }

    /// Composed value type (the `typeName` field), if set. Mirrors C++
    /// `UsdAttribute::GetTypeName`.
    ///
    /// A schema that declares this attribute wins outright, as it does for
    /// [`variability`](Self::variability): the value type is part of the
    /// declaration, so an authored `typeName` cannot redeclare a schema
    /// attribute as a different type. Composition answers only for an
    /// attribute no schema declares. `typeName` is a token; a value of any
    /// other type is treated as untyped (`None`).
    pub fn type_name(&self) -> anyhow::Result<Option<tf::Token>> {
        if let Some(declared) = self.definition_field(sdf::FieldKey::TypeName)? {
            return Ok(declared.try_as_token());
        }
        Ok(self
            .stage
            .field::<sdf::Value>(&self.path, sdf::FieldKey::TypeName)?
            .and_then(sdf::Value::try_as_token))
    }

    /// Composed default value decoded to `T`. The convenience spelling of
    /// `get_at(None)`; mirrors C++ `UsdAttribute::Get`.
    ///
    /// `T` is any type implementing `TryFrom<sdf::Value>` — a scalar
    /// (`get::<f32>()`), an array (`get::<Vec<f32>>()`), or [`sdf::Value`]
    /// itself (`get::<sdf::Value>()`) for the raw value. A type mismatch
    /// against the authored value surfaces as an `Err`, not `None`.
    pub fn get<T>(&self) -> anyhow::Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        self.get_at(None)
    }

    /// Composed value at `time` decoded to `T`. Mirrors C++
    /// `UsdAttribute::Get(value, time)`.
    ///
    /// `time` is `None` to read the default value, or `Some(tc)` (a
    /// [`usd::TimeCode`](super::TimeCode), which a bare `TimeCode` coerces
    /// into) to resolve a time sample under the stage's [`InterpolationType`].
    ///
    /// When no layer authors a value, the attribute's schema supplies its
    /// fallback; [`value_source`](Self::value_source) reports which answered.
    ///
    /// [`InterpolationType`]: super::InterpolationType
    pub fn get_at<T>(&self, time: impl Into<Option<super::TimeCode>>) -> anyhow::Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        let value = match time.into() {
            None => self.stage.field::<sdf::Value>(&self.path, sdf::FieldKey::Default)?,
            Some(time) => self.stage.resolve_at(&self.path, time.value())?,
        };
        let value = match value {
            Some(value) => Some(value),
            None => self.fallback_value()?,
        };
        Ok(value.map(T::try_from).transpose()?)
    }

    /// The value this attribute's schema declares when nothing is authored
    /// (C++ `UsdPrimDefinition::GetAttributeFallbackValue`).
    ///
    /// Resolved against the stage's
    /// [`SchemaRegistry`](super::SchemaRegistry), from the owning
    /// prim's composed `typeName` and `apiSchemas`. `None` when no schema
    /// declares this attribute, or declares it without a fallback.
    ///
    /// An `asset` fallback is anchored against the schematics that declared it,
    /// on the terms
    /// [`resolved_location`](super::FamilySource::resolved_location) states.
    pub fn fallback_value(&self) -> anyhow::Result<Option<sdf::Value>> {
        let Some((info, name)) = self.declaring_definition()? else {
            return Ok(None);
        };
        let Some(property) = info.prim_definition().property(&name) else {
            return Ok(None);
        };
        let Some(value) = property.attribute_fallback() else {
            return Ok(None);
        };
        // Anchoring passes a non-asset value through untouched, so this gates
        // only to keep the ordinary read off the composition borrow it takes.
        if !value.is_asset_valued() {
            return Ok(Some(value));
        }
        Ok(Some(self.stage.resolve_schema_asset(property.fallback_source(), value)))
    }

    /// Reads one field from the schema declaration of this attribute, if a
    /// schema declares it (C++ `UsdStage::_GetSchemaAttribute`).
    ///
    /// This is the metadata counterpart of
    /// [`fallback_value`](Self::fallback_value): everything a schema states
    /// about a property — its type, its variability, its display metadata —
    /// lives on the same declaration, whether or not any layer authors a spec.
    fn definition_field(&self, field: impl AsRef<str>) -> anyhow::Result<Option<sdf::Value>> {
        let Some((info, name)) = self.declaring_definition()? else {
            return Ok(None);
        };
        let Some(property) = info.prim_definition().property(&name) else {
            return Ok(None);
        };
        Ok(property.field(field).cloned())
    }

    /// The spec type the owning prim's schema declares for this property, or
    /// `None` when no schema declares it.
    fn declared_spec_type(&self) -> anyhow::Result<Option<sdf::SpecType>> {
        let Some((info, name)) = self.declaring_definition()? else {
            return Ok(None);
        };
        Ok(info
            .prim_definition()
            .property(&name)
            .map(|property| property.spec_type()))
    }

    /// The schema of the prim this attribute hangs off, with the attribute's
    /// own name — the pair every declaration lookup starts from.
    fn declaring_definition(&self) -> anyhow::Result<Option<(Arc<PrimTypeInfo>, tf::Token)>> {
        let Some((prim, name)) = self.path.split_property() else {
            return Ok(None);
        };
        Ok(Some((self.stage.prim_type_info(prim)?, tf::Token::from(name))))
    }

    /// Like [`declaring_definition`](Self::declaring_definition), but `None`
    /// unless a schema actually declares this property.
    fn declaring_property(&self) -> anyhow::Result<Option<(Arc<PrimTypeInfo>, tf::Token)>> {
        let Some((info, name)) = self.declaring_definition()? else {
            return Ok(None);
        };
        Ok(info.prim_definition().has_property(&name).then_some((info, name)))
    }

    /// Where the value [`get`](Self::get) returns comes from.
    ///
    /// A blocked attribute reports [`ValueSource::Fallback`] when its schema
    /// declares one: blocking removes the authored opinions, and resolution
    /// then falls through to the schema, per spec §12.3.6.
    pub fn value_source(&self) -> anyhow::Result<ValueSource> {
        let authored = match self.stage.resolve_value_source(&self.path)? {
            AttributeValueSource::Static(value) => value.is_some(),
            AttributeValueSource::TimeSamples { .. } | AttributeValueSource::Clips => true,
        };
        if authored {
            return Ok(ValueSource::Authored);
        }
        Ok(match self.definition_field(sdf::FieldKey::Default)?.is_some() {
            true => ValueSource::Fallback,
            false => ValueSource::None,
        })
    }

    /// Retrieves the composed default [`sdf::Value`] and casts it to `T` via the
    /// registered coercions ([`sdf::Value::cast`]).
    ///
    /// Unlike [`get`](Attribute::get) — a strict fetch that requires the exact
    /// held variant (`get::<String>()` reads a `Value::String` but not a
    /// `Value::Token`) — `cast` *converts* the value to `T` (numeric scalars
    /// range-checked, `token` ↔ `string`, vector/quaternion precision) and
    /// returns an error if no conversion to `T` applies. `None` when no layer
    /// authored an opinion.
    pub fn cast<T: sdf::FromValueCast>(&self) -> anyhow::Result<Option<T>> {
        match self.get::<sdf::Value>()? {
            Some(value) => Ok(Some(value.cast::<T>()?)),
            None => Ok(None),
        }
    }

    /// Composed value of a generic metadata field on the attribute decoded to
    /// `T`, falling back to what the attribute's schema declares. Mirrors C++
    /// `UsdObject::GetMetadata(name, &value)`.
    ///
    /// The read counterpart of [`Attribute::set_metadata`]; used for the
    /// schema-layered fields it authors (UsdGeom's `interpolation` /
    /// `elementSize` on primvars, UsdSkel's inbetween `weight`, …). Decode to
    /// the field's type (`get_metadata::<i32>("elementSize")`) or to
    /// [`sdf::Value`] for the raw value.
    pub fn get_metadata<T>(&self, key: &str) -> anyhow::Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        // `typeName`, `variability` and `custom` each resolve by their own rule
        // rather than plain strongest-opinion composition, and reading them
        // generically has to give the same answer as the accessor that owns the
        // rule (C++ `_GetSpecialPropMetadataImpl`).
        if let Some(special) = self.special_metadata(key)? {
            return Ok(T::try_from(special).ok());
        }
        if let Some(authored) = self.stage.field::<T>(&self.path, key)? {
            return Ok(Some(authored));
        }
        // Schema metadata parses untyped, so a declaration may hold a variant
        // the caller did not ask for; that is "not declared", not an error.
        Ok(self.definition_field(key)?.and_then(|value| T::try_from(value).ok()))
    }

    /// The value of a field whose resolution is not plain composition, or
    /// `None` when `key` is an ordinary metadata field.
    fn special_metadata(&self, key: &str) -> anyhow::Result<Option<sdf::Value>> {
        if key == sdf::FieldKey::TypeName.as_str() {
            return Ok(self.type_name()?.map(sdf::Value::Token));
        }
        if key == sdf::FieldKey::Variability.as_str() {
            return Ok(self.variability()?.map(sdf::Value::Variability));
        }
        if key == sdf::FieldKey::Custom.as_str() {
            return Ok(Some(sdf::Value::Bool(self.is_custom()?)));
        }
        Ok(None)
    }

    /// Composed `timeSamples` map.
    pub fn time_samples(&self) -> anyhow::Result<Option<sdf::TimeSampleMap>> {
        self.stage.time_samples(&self.path)
    }

    /// Builds an [`AttributeQuery`] for this attribute — a cached value source
    /// for repeated time-code reads. Mirrors C++ `UsdAttributeQuery(attr)`.
    /// Prefer this over calling [`get_at`](Attribute::get_at) in a loop when
    /// sampling one attribute at many time codes, since the query resolves the
    /// value source once.
    pub fn query(&self) -> AttributeQuery {
        AttributeQuery::new(self)
    }

    /// The authored sample times in ascending order, or empty when none are
    /// authored. Mirrors C++ `UsdAttribute::GetTimeSamples`.
    ///
    /// Gathers the times from the strongest value source — local `timeSamples`,
    /// then value clips (spec 12.3.4), then `timeSamples` across reference /
    /// payload arcs — each retimed to stage time.
    pub fn time_sample_times(&self) -> anyhow::Result<Vec<f64>> {
        Ok(self.stage.time_sample_times(&self.path)?.unwrap_or_default())
    }

    /// The authored sample times within the closed interval `interval`, in
    /// ascending order. Mirrors C++ `UsdAttribute::GetTimeSamplesInInterval`.
    ///
    /// The interval is inclusive at both ends. For samples authored at
    /// `{0, 5, 10}`, `time_samples_in_interval(2.0..=8.0)` returns `[5.0]`,
    /// while `time_samples_in_interval(0.0..=5.0)` returns `[0.0, 5.0]`.
    pub fn time_samples_in_interval(&self, interval: std::ops::RangeInclusive<f64>) -> anyhow::Result<Vec<f64>> {
        Ok(self
            .time_sample_times()?
            .into_iter()
            .filter(|t| interval.contains(t))
            .collect())
    }

    /// The number of authored time samples, zero when none. Mirrors C++
    /// `UsdAttribute::GetNumTimeSamples`.
    pub fn num_time_samples(&self) -> anyhow::Result<usize> {
        self.stage.num_time_samples(&self.path)
    }

    /// The pair of authored sample times bracketing `time`, or `None` when no
    /// samples are authored. Mirrors C++
    /// `UsdAttribute::GetBracketingTimeSamples`: the pair collapses to one
    /// repeated time at or beyond an end sample, or when `time` lands exactly
    /// on a sample; otherwise `lower < time < upper`. The two-sample primitive
    /// behind motion-blur and shutter sampling.
    pub fn bracketing_time_samples(&self, time: impl Into<super::TimeCode>) -> anyhow::Result<Option<(f64, f64)>> {
        let time = time.into();
        let times = self.time_sample_times()?;
        Ok(interp::bracketing_time_samples(&times, time.value()))
    }

    /// `true` when the value may change over time, the fast check behind
    /// motion-blur and animation queries. Mirrors C++
    /// `UsdAttribute::ValueMightBeTimeVarying`: `true` when more than one sample
    /// is composed, and conservatively when a participating value-clip set has
    /// more than one active clip (spec 12.3.4) — those clips can each serve a
    /// different value even where the reported sample count collapses to one.
    pub fn value_might_be_time_varying(&self) -> anyhow::Result<bool> {
        self.stage.value_might_be_time_varying(&self.path)
    }

    /// Returns the property stack: each `(layer identifier, spec path)` site
    /// that authors a spec for this attribute, strongest first. Mirrors C++
    /// `UsdProperty::GetPropertyStack`.
    pub fn property_stack(&self) -> anyhow::Result<Vec<(String, sdf::Path)>> {
        self.stage.with_cache(|g, c| c.property_stack(g, &self.path))
    }

    /// Borrow the attribute spec at `self.path` on the edit target's layer,
    /// apply `f`, and return `self` for chaining. The layer records whatever
    /// fields `f` writes.
    ///
    /// When the edit target has no spec but a schema declares the attribute,
    /// one is stamped from the declaration first (C++
    /// `UsdStage::_CreateNewPropertySpecFromSchema`), so a property that reads
    /// back a fallback can also be authored. Returns `InvalidPath` when neither
    /// a spec nor a declaration exists.
    fn edit<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>) -> Result<(), sdf::AuthoringError>,
    {
        self.edit_spec(f)?;
        Ok(self)
    }

    /// Runs `f` on this attribute's spec at the edit target's layer, stamping
    /// one from the schema declaration first when the target has none.
    ///
    /// Every mutation goes through here, so a property that reads back a
    /// fallback can be authored whichever setter the caller reaches for.
    fn edit_spec<F>(&self, f: F) -> Result<(), StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>) -> Result<(), sdf::AuthoringError>,
    {
        let declared = self.declared_spec().map_err(StageAuthoringError::Composition)?;
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            declare_spec(layer.data_mut(), &path, &declared)?;
            super::edit_spec(
                layer.data_mut(),
                path,
                "no attribute spec at path on the edit target layer",
                sdf::AttributeSpecMut::get,
                f,
            )
        })?;
        Ok(())
    }

    /// The type and variability a schema declares for this attribute, which is
    /// what a spec authored for it has to be created with.
    fn declared_spec(&self) -> anyhow::Result<Option<(tf::Token, sdf::Variability)>> {
        let Some((info, name)) = self.declaring_property()? else {
            return Ok(None);
        };
        let definition = info.prim_definition();
        let Some(property) = definition.property(&name) else {
            return Ok(None);
        };
        if property.spec_type() != sdf::SpecType::Attribute {
            return Ok(None);
        }
        Ok(property
            .type_name()
            .map(|type_name| (type_name, property.variability())))
    }
}

/// Removes `key` from the attribute spec at `path`, when `data` holds one.
///
/// Going through the typed view keeps the erase to an attribute: a path
/// addressing a prim, a relationship, or nothing at all owns fields this handle
/// has no business removing.
fn erase_attribute_field(data: &mut dyn sdf::AbstractData, path: sdf::Path, key: &str) {
    if let Some(mut spec) = sdf::AttributeSpecMut::get(data, path) {
        spec.erase(key);
    }
}

/// Stamps a spec for the attribute at `path` from `declared`, the type and
/// variability a schema states for it, when `data` holds none. Mirrors C++
/// `UsdStage::_CreateNewPropertySpecFromSchema`, so a property that reads back a
/// fallback can be authored.
fn declare_spec(
    data: &mut dyn sdf::AbstractData,
    path: &sdf::Path,
    declared: &Option<(tf::Token, sdf::Variability)>,
) -> Result<(), sdf::AuthoringError> {
    if let Some((type_name, variability)) = declared
        && sdf::AttributeSpecMut::get(&mut *data, path.clone()).is_none()
    {
        sdf::AttributeSpec::new(data, path.clone(), type_name.as_str(), *variability, false)?;
    }
    Ok(())
}

/// Cached value query for one attribute. Mirrors C++ `UsdAttributeQuery`.
///
/// [`Attribute::get_at`] re-resolves the attribute's value source — the opinion
/// walk down the composition graph — on every call. When the same attribute is
/// sampled at many time codes (motion blur, baking, a playback scrub), an
/// `AttributeQuery` resolves that source once and replays it, so each
/// [`get_at`](AttributeQuery::get_at) is just an interpolation rather than a
/// fresh composition.
///
/// The cached source is snapshotted against the stage's composition revision: a
/// timed [`get_at`](AttributeQuery::get_at) reuses it until an edit advances the
/// revision, at which point the next query rebuilds it — so the handle stays
/// correct across authoring without the caller re-creating it.
///
/// The fast path covers attributes resolved from `default` opinions or
/// `timeSamples`. An attribute resolved through value clips (spec 12.3.4) is
/// time-dependent at the source level, so the query transparently falls back to
/// the full resolution path for it; results stay correct, without the speedup.
pub struct AttributeQuery {
    attr: Attribute,
    cached: RefCell<Option<CachedSource>>,
}

impl Clone for AttributeQuery {
    /// Clones the attribute handle but not the resolved-source memo: the clone
    /// resolves its source lazily on first use, like a fresh query.
    fn clone(&self) -> Self {
        Self::new(&self.attr)
    }
}

/// A resolved value source paired with the composition revision it was resolved
/// against. Stale once the stage's revision advances past `revision`.
struct CachedSource {
    revision: u64,
    source: AttributeValueSource,
}

impl AttributeQuery {
    /// Builds a query for `attr`. The value source resolves lazily on the first
    /// timed [`get_at`](Self::get_at). Mirrors C++ `UsdAttributeQuery`'s
    /// attribute constructor.
    pub fn new(attr: &Attribute) -> Self {
        Self {
            attr: attr.clone(),
            cached: RefCell::new(None),
        }
    }

    /// The attribute this query is anchored to.
    pub fn attribute(&self) -> &Attribute {
        &self.attr
    }

    /// Composed default value decoded to `T`. The convenience spelling of
    /// `get_at(None)`; mirrors C++ `UsdAttributeQuery::Get()`.
    pub fn get<T>(&self) -> anyhow::Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        self.get_at(None)
    }

    /// Composed value at `time` decoded to `T`. Mirrors C++
    /// `UsdAttributeQuery::Get(value, time)`.
    ///
    /// `time` is `None` to read the default value, or `Some(tc)` (a
    /// [`TimeCode`], which a bare `TimeCode` coerces into) to resolve a time
    /// sample under the stage's [`InterpolationType`](super::InterpolationType).
    /// A timed read reuses the cached value source; the default read delegates
    /// to the attribute, since a `default` opinion is resolved from a separate
    /// field.
    pub fn get_at<T>(&self, time: impl Into<Option<TimeCode>>) -> anyhow::Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        let value = match time.into() {
            // The untimed read goes through the attribute, which resolves the
            // `default` field and the schema fallback behind it.
            None => self.attr.get_at::<sdf::Value>(None)?,
            Some(time) => match self.value_at(time.value())? {
                Some(value) => Some(value),
                None => self.attr.fallback_value()?,
            },
        };
        Ok(value.map(T::try_from).transpose()?)
    }

    /// `true` when more than one time sample is authored — the cached-source
    /// counterpart of [`Attribute::value_might_be_time_varying`]. Mirrors C++
    /// `UsdAttributeQuery::ValueMightBeTimeVarying`.
    pub fn value_might_be_time_varying(&self) -> anyhow::Result<bool> {
        self.attr.value_might_be_time_varying()
    }

    /// The authored sample times in ascending order, or empty when none are
    /// authored. Mirrors C++ `UsdAttributeQuery::GetTimeSamples`.
    pub fn time_sample_times(&self) -> anyhow::Result<Vec<f64>> {
        self.attr.time_sample_times()
    }

    /// Resolves the value at stage `time` through the cached source, rebuilding
    /// it when the stage's composition revision has advanced.
    fn value_at(&self, time: f64) -> anyhow::Result<Option<sdf::Value>> {
        let stage = self.attr.stage();
        let revision = stage.cache_revision();

        // Reuse a cached source still valid at the current revision.
        if let Some(cached) = self.cached.borrow().as_ref()
            && cached.revision == revision
        {
            return self.evaluate(&cached.source, time);
        }

        // Miss: resolve the source once and evaluate it. An empty source is as
        // final as any other — a query on a `/__Prototype_N` path completes
        // stage population before it is answered
        // (`Stage::resolve_prototype_path`), so nothing composes into that
        // namespace afterwards without an edit.
        let source = stage.resolve_value_source(self.attr.path())?;
        let value = self.evaluate(&source, time)?;
        // Stamped with the revision as it stands *after* resolving: resolving
        // drains the pending edits, and a sink authoring during that drain
        // advances the revision, which would leave the entry stale the moment
        // it was written.
        self.cached.replace(Some(CachedSource {
            revision: stage.cache_revision(),
            source,
        }));
        Ok(value)
    }

    /// Evaluates an already-resolved value source at stage `time`.
    fn evaluate(&self, source: &AttributeValueSource, time: f64) -> anyhow::Result<Option<sdf::Value>> {
        let stage = self.attr.stage();
        match source {
            AttributeValueSource::Static(value) => Ok(value.clone()),
            // Interpolate in the node's layer-time frame, mapping `time` back
            // through the inverse offset — matching `PrimIndex::resolve_value_at`.
            AttributeValueSource::TimeSamples { samples, offset, site } => {
                let value = interp::evaluate(samples, offset.inverse().apply(time), stage.interpolation_type());
                // Only the interpolated result is anchored and evaluated, not
                // the held map: resolving every sample here would report a
                // malformed expression authored at a time this read never
                // selected. A non-asset value skips the cache borrow entirely,
                // which is what keeps an ordinary animated read off this path.
                if !value.as_ref().is_some_and(sdf::Value::is_asset_valued) {
                    return Ok(value);
                }
                // `with_cache` takes an `FnMut`, so the closure cannot consume
                // `value`.
                stage.with_cache(|g, c| Ok(c.resolve_asset_values(g, value.clone(), Some(site))))
            }
            AttributeValueSource::Clips => stage.resolve_at(self.attr.path(), time),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::usd::SchemaRegistry;
    use crate::usd::{AttributeQuery, Stage, TimeCode, ValueSource};
    use crate::{sdf, tf};

    fn stage() -> anyhow::Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    /// A stage whose prims resolve against the shared test schema family, on
    /// which `DistantLight.inputs:intensity` falls back to 50000.
    fn schema_stage() -> anyhow::Result<Stage> {
        Stage::builder()
            .schema_registry(SchemaRegistry::test_registry())
            .in_memory("anon.usda")
    }

    #[test]
    fn defined_by_schema_or_spec() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // A schema declaration defines an attribute no layer authors.
        assert!(stage.attribute("/Sun.inputs:intensity")?.is_defined()?);
        // A name no schema declares and no layer authors is nothing.
        assert!(!stage.attribute("/Sun.inputs:nope")?.is_defined()?);
        // A declared relationship is not an attribute.
        assert!(!stage.attribute("/Sun.collection:lightLink:includes")?.is_defined()?);

        stage.prim("/Sun")?.create_attribute("authored", "double")?;
        assert!(stage.attribute("/Sun.authored")?.is_defined()?);
        stage.prim("/Sun")?.create_relationship("authoredRel")?;
        assert!(!stage.attribute("/Sun.authoredRel")?.is_defined()?);
        Ok(())
    }

    #[test]
    fn unauthored_reads_fallback() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Nothing authored the attribute at all — not even a spec — so the
        // value comes entirely from the schema.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.get::<f32>()?, Some(50000.0));
        assert_eq!(intensity.value_source()?, ValueSource::Fallback);
        Ok(())
    }

    #[test]
    fn authored_beats_fallback() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage.create_attribute("/Sun.inputs:intensity", "float")?.set(3.0_f32)?;

        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.get::<f32>()?, Some(3.0));
        assert_eq!(intensity.value_source()?, ValueSource::Authored);
        Ok(())
    }

    #[test]
    fn fallback_matches_across_time() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // The untimed and timed reads funnel through the same fallback step, so
        // they agree by construction — through the query handle too.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.get::<f32>()?, Some(50000.0));
        assert_eq!(intensity.get_at::<f32>(TimeCode::new(0.0))?, Some(50000.0));

        let query = AttributeQuery::new(&intensity);
        assert_eq!(query.get::<f32>()?, Some(50000.0));
        assert_eq!(query.get_at::<f32>(TimeCode::new(0.0))?, Some(50000.0));
        Ok(())
    }

    #[test]
    fn blocked_falls_back_to_schema() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage
            .create_attribute("/Sun.inputs:intensity", "float")?
            .set(sdf::Value::ValueBlock)?;

        // Blocking removes the authored opinion; resolution then reaches the
        // schema, per spec 12.3.6.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.get::<f32>()?, Some(50000.0));
        assert_eq!(intensity.value_source()?, ValueSource::Fallback);
        Ok(())
    }

    #[test]
    fn applied_schema_supplies_fallback() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage
            .define_prim("/Group")?
            .add_applied_schema("CollectionAPI:render")?;

        // A typeless prim still gets what its applied schemas declare, with the
        // multiple-apply template instantiated under the applied instance name.
        let rule = stage.attribute("/Group.collection:render:expansionRule")?;
        assert_eq!(rule.get::<tf::Token>()?, Some(tf::Token::new("expandPrims")));
        assert_eq!(
            stage
                .attribute("/Group.collection:other:expansionRule")?
                .get::<tf::Token>()?,
            None
        );
        Ok(())
    }

    #[test]
    fn schema_property_reports_its_type() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Nothing is authored, so the type and variability come from the
        // schema's declaration alongside the fallback value.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.type_name()?, Some(tf::Token::new("float")));
        assert_eq!(intensity.variability()?, Some(sdf::Variability::Varying));

        let rule = stage.attribute("/Sun.collection:lightLink:expansionRule")?;
        assert_eq!(rule.type_name()?, Some(tf::Token::new("token")));
        assert_eq!(rule.variability()?, Some(sdf::Variability::Uniform));
        Ok(())
    }

    #[test]
    fn schema_property_metadata_reads_back() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Declaration metadata is readable for a property with no authored
        // spec. Property metadata parses untyped, so the token list reads back
        // as a string array.
        let rule = stage.attribute("/Sun.collection:lightLink:expansionRule")?;
        let allowed = rule.get_metadata::<sdf::Value>("allowedTokens")?;
        assert_eq!(
            allowed,
            Some(sdf::Value::StringVec(vec![
                "explicitOnly".into(),
                "expandPrims".into(),
                "expandPrimsAndProperties".into(),
            ]))
        );
        Ok(())
    }

    #[test]
    fn declared_varying_beats_authored_uniform() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // The schematics declare `inputs:angle` varying by omitting the field
        // entirely, so the declaration still has to win.
        let angle = stage.attribute("/Sun.inputs:angle")?;
        assert_eq!(angle.variability()?, Some(sdf::Variability::Varying));

        angle.clone().set_variability(sdf::Variability::Uniform)?;
        assert_eq!(
            stage.attribute("/Sun.inputs:angle")?.variability()?,
            Some(sdf::Variability::Varying)
        );
        Ok(())
    }

    #[test]
    fn schema_property_is_writable() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Nothing authors `inputs:angle`, so there is no spec to edit — the
        // declaration supplies the type and variability to create one with.
        let angle = stage.attribute("/Sun.inputs:angle")?;
        assert_eq!(angle.get::<f32>()?, Some(0.53));
        angle.set(1.5_f32)?;

        let angle = stage.attribute("/Sun.inputs:angle")?;
        assert_eq!(angle.get::<f32>()?, Some(1.5));
        assert_eq!(angle.type_name()?, Some(tf::Token::new("float")));
        // A schema property is not custom, however it was created.
        assert!(!angle.is_custom()?);
        Ok(())
    }

    #[test]
    fn round_trip_over_enumerated_attributes() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Every handle `attributes()` hands back can be written, not just the
        // authored ones.
        for attr in stage.prim("/Sun")?.attributes()? {
            if let Some(sdf::Value::Float(value)) = attr.get::<sdf::Value>()? {
                attr.set(value * 2.0)?;
            }
        }
        assert_eq!(stage.attribute("/Sun.inputs:angle")?.get::<f32>()?, Some(1.06));
        assert_eq!(stage.attribute("/Sun.inputs:intensity")?.get::<f32>()?, Some(100000.0));
        Ok(())
    }

    #[test]
    fn every_setter_stamps_the_schema_spec() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Each of these reaches the edit target through a different path; none
        // may fail just because only the schema declares the attribute.
        stage
            .attribute("/Sun.inputs:angle")?
            .set_metadata("displayGroup", sdf::Value::String("Basic".into()))?;
        assert_eq!(
            stage
                .attribute("/Sun.inputs:angle")?
                .get_metadata::<String>("displayGroup")?,
            Some("Basic".to_owned())
        );

        stage.attribute("/Sun.inputs:intensity")?.clear_connections()?;
        stage
            .attribute("/Sun.collection:lightLink:expansionRule")?
            .set_color_space("srgb")?;
        Ok(())
    }

    #[test]
    fn schema_property_is_not_custom() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage
            .create_attribute("/Sun.inputs:intensity", "float")?
            .set_custom(true)?;

        // A schema declares the property, so an authored `custom` is ignored.
        assert!(!stage.attribute("/Sun.inputs:intensity")?.is_custom()?);
        // A property no schema declares still reports what layers author.
        assert!(stage.create_attribute("/Sun.mine", "double")?.is_custom()?);
        Ok(())
    }

    #[test]
    fn time_samples_count_as_authored() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage
            .create_attribute("/Sun.inputs:intensity", "float")?
            .set_at(100.0_f32, TimeCode::new(0.0))?
            .set_at(200.0_f32, TimeCode::new(10.0))?;

        // The only authored opinion is time samples, and it is what `get_at`
        // resolves, so the source is authored rather than the schema fallback.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.value_source()?, ValueSource::Authored);
        assert_eq!(intensity.get_at::<f32>(TimeCode::new(5.0))?, Some(150.0));
        Ok(())
    }

    #[test]
    fn declared_type_beats_authored() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage.create_attribute("/Sun.inputs:angle", "double")?;

        // The value type is part of the declaration, so a layer cannot
        // redeclare a schema attribute as a different type.
        assert_eq!(
            stage.attribute("/Sun.inputs:angle")?.type_name()?,
            Some(tf::Token::new("float"))
        );
        // A property no schema declares still reports what layers author.
        assert_eq!(
            stage.create_attribute("/Sun.mine", "double")?.type_name()?,
            Some(tf::Token::new("double"))
        );
        Ok(())
    }

    #[test]
    fn generic_metadata_matches_its_accessor() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage
            .create_attribute("/Sun.collection:lightLink:expansionRule", "double")?
            .set_variability(sdf::Variability::Varying)?
            .set_custom(true)?;

        // Reading these generically has to give what the accessor that owns the
        // rule gives, not the raw composed opinion.
        let rule = stage.attribute("/Sun.collection:lightLink:expansionRule")?;
        assert_eq!(
            rule.get_metadata::<sdf::Variability>(sdf::FieldKey::Variability.as_str())?,
            rule.variability()?
        );
        assert_eq!(
            rule.get_metadata::<tf::Token>(sdf::FieldKey::TypeName.as_str())?,
            rule.type_name()?
        );
        assert_eq!(
            rule.get_metadata::<bool>(sdf::FieldKey::Custom.as_str())?,
            Some(rule.is_custom()?)
        );
        assert_eq!(rule.variability()?, Some(sdf::Variability::Uniform));
        Ok(())
    }

    #[test]
    fn schema_metadata_type_mismatch_is_not_an_error() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Schema metadata parses untyped, so asking for a variant it does not
        // hold reads as undeclared rather than failing.
        let rule = stage.attribute("/Sun.collection:lightLink:expansionRule")?;
        assert_eq!(rule.get_metadata::<Vec<tf::Token>>("allowedTokens")?, None);
        Ok(())
    }

    #[test]
    fn authored_variability_cannot_override_schema() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage
            .create_attribute("/Sun.collection:lightLink:expansionRule", "token")?
            .set_variability(sdf::Variability::Varying)?;

        // The schema declares it uniform, and that is part of the declaration.
        assert_eq!(
            stage
                .attribute("/Sun.collection:lightLink:expansionRule")?
                .variability()?,
            Some(sdf::Variability::Uniform)
        );
        Ok(())
    }

    #[test]
    fn unknown_schema_has_no_fallback() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        let unknown = stage.attribute("/Sun.notASchemaProperty")?;
        assert_eq!(unknown.get::<sdf::Value>()?, None);
        assert_eq!(unknown.value_source()?, ValueSource::None);
        Ok(())
    }

    #[test]
    fn masked_prim_has_no_fallback() -> anyhow::Result<()> {
        let stage = Stage::builder()
            .schema_registry(SchemaRegistry::test_registry())
            .mask(crate::usd::StagePopulationMask::new(["/Keep"])?)
            .in_memory("anon.usda")?;
        stage.define_prim("/Keep")?.set_type_name("DistantLight")?;
        stage.define_prim("/Drop")?.set_type_name("DistantLight")?;

        assert_eq!(stage.attribute("/Keep.inputs:intensity")?.get::<f32>()?, Some(50000.0));
        // An excluded prim resolves no type, so it resolves no fallback either.
        assert_eq!(stage.attribute("/Drop.inputs:intensity")?.get::<f32>()?, None);
        Ok(())
    }

    #[test]
    fn registry_without_data_has_no_fallback() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // The default process registry ships without schema data.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.get::<sdf::Value>()?, None);
        assert_eq!(intensity.value_source()?, ValueSource::None);
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

    /// `Attribute::variability`/`is_custom` read the composed core fields
    /// (C++ `UsdAttribute::GetVariability` / `UsdProperty::IsCustom`).
    #[test]
    fn attribute_variability_custom() -> anyhow::Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/A")?.set_type_name("Xform")?;
        let uniform = prim
            .create_attribute("u", "double")?
            .set_variability(sdf::Variability::Uniform)?
            .set_custom(true)?;
        assert_eq!(uniform.variability()?, Some(sdf::Variability::Uniform));
        assert!(uniform.is_custom()?);

        // A schema-style attribute authored with `custom = false` resolves false.
        let schema_attr = prim.create_attribute("v", "double")?.set_custom(false)?;
        assert!(!schema_attr.is_custom()?);
        Ok(())
    }

    #[test]
    fn attribute_time_samples() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(sdf::Value::Double(1.0), TimeCode::new(0.0))?
            .set_at(sdf::Value::Double(3.0), TimeCode::new(10.0))?;
        // Linear interpolation default → halfway = 2.0.
        assert_eq!(attr.get_at(TimeCode::new(5.0))?, Some(sdf::Value::Double(2.0)));
        let samples = attr.time_samples()?.expect("samples");
        assert_eq!(samples.len(), 2);
        Ok(())
    }

    /// The time-sample introspection accessors over `timeSamples = {0, 10}`.
    #[test]
    fn time_sample_queries() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(sdf::Value::Double(1.0), TimeCode::new(0.0))?
            .set_at(sdf::Value::Double(3.0), TimeCode::new(10.0))?;

        assert_eq!(attr.num_time_samples()?, 2);
        assert_eq!(attr.time_sample_times()?, vec![0.0, 10.0]);
        assert_eq!(attr.time_samples_in_interval(1.0..=10.0)?, vec![10.0]);
        assert!(attr.value_might_be_time_varying()?);

        // Before / after the ends clamp to a single repeated endpoint; a time
        // between the two samples brackets them; an exact hit collapses.
        assert_eq!(attr.bracketing_time_samples(-5.0)?, Some((0.0, 0.0)));
        assert_eq!(attr.bracketing_time_samples(5.0)?, Some((0.0, 10.0)));
        assert_eq!(attr.bracketing_time_samples(10.0)?, Some((10.0, 10.0)));
        assert_eq!(attr.bracketing_time_samples(100.0)?, Some((10.0, 10.0)));

        // An attribute with no time samples reports empty / none.
        let plain = stage.define_prim("/B")?.create_attribute("y", "double")?;
        assert_eq!(plain.num_time_samples()?, 0);
        assert!(plain.time_sample_times()?.is_empty());
        assert!(!plain.value_might_be_time_varying()?);
        assert_eq!(plain.bracketing_time_samples(0.0)?, None);
        Ok(())
    }

    /// The times-only / count-only accessors match the keys and length of the
    /// full `time_samples()` map (identity offset).
    #[test]
    fn time_sample_times_parity() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(sdf::Value::Double(1.0), TimeCode::new(0.0))?
            .set_at(sdf::Value::Double(2.0), TimeCode::new(5.0))?
            .set_at(sdf::Value::Double(3.0), TimeCode::new(10.0))?;

        let map = attr.time_samples()?.expect("samples");
        let keys: Vec<f64> = map.iter().map(|(t, _)| *t).collect();
        assert_eq!(attr.time_sample_times()?, keys);
        assert_eq!(attr.num_time_samples()?, map.len());
        Ok(())
    }

    /// A `ValueBlock` authored on the `timeSamples` field resolves to no
    /// samples on the times-only path, matching `time_samples()`.
    #[test]
    fn time_sample_times_blocked() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(sdf::Value::Double(1.0), TimeCode::new(0.0))?
            .set_at(sdf::Value::Double(3.0), TimeCode::new(10.0))?
            .set_metadata(sdf::FieldKey::TimeSamples.as_str(), sdf::Value::ValueBlock)?;
        assert!(attr.time_samples()?.is_none());
        assert!(attr.time_sample_times()?.is_empty());
        assert_eq!(attr.num_time_samples()?, 0);
        assert!(!attr.value_might_be_time_varying()?);
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
        // ValueBlock resolves to None through the default and time-sample paths.
        assert_eq!(attr.get::<sdf::Value>()?, None);
        assert_eq!(attr.get_at::<sdf::Value>(TimeCode::new(0.0))?, None);
        Ok(())
    }

    /// `block()` must also replace every authored time-sample value with
    /// `ValueBlock` — otherwise the default block is silently bypassed for
    /// time-code queries that fall onto an authored sample.
    #[test]
    fn attribute_block_clears_time_samples() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(sdf::Value::Double(1.0), TimeCode::new(0.0))?
            .set_at(sdf::Value::Double(3.0), TimeCode::new(10.0))?
            .block()?;
        assert_eq!(attr.get_at::<sdf::Value>(TimeCode::new(0.0))?, None);
        assert_eq!(attr.get_at::<sdf::Value>(TimeCode::new(5.0))?, None);
        assert_eq!(attr.get_at::<sdf::Value>(TimeCode::new(10.0))?, None);
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

        let conns = input.connections()?;
        assert_eq!(conns, vec![tex_out.path().clone()]);
        assert!(input.has_authored_connections()?);

        // Re-authoring replaces, doesn't append.
        let iface = sdf::Path::new("/Mat.inputs:diffuseColor")?;
        let input = input.set_connections([iface.clone()])?;
        assert_eq!(input.connections()?, vec![iface.clone()]);

        // add_connection prepends by default; dedups.
        let input = input.add_connection(tex_out.path().clone())?;
        assert_eq!(input.connections()?, vec![tex_out.path().clone(), iface.clone()]);
        let input = input.add_connection(tex_out.path().clone())?;
        assert_eq!(input.connections()?.len(), 2);

        // remove_connection.
        assert!(input.remove_connection(&iface)?);
        assert_eq!(input.connections()?, vec![tex_out.path().clone()]);
        assert!(!input.remove_connection(&iface)?);

        // clear_connections.
        let input = input.clear_connections()?;
        assert!(!input.has_authored_connections()?);
        assert!(input.connections()?.is_empty());
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
            .set_connections(Vec::<sdf::Path>::new())?;
        assert!(attr.has_authored_connections()?);
        assert!(attr.connections()?.is_empty());
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
            .root_layer()
            .attribute(attr.path().clone())?
            .expect("authored on the root layer")
            .connection_path_list()
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
            .root_layer()
            .attribute(attr.path().clone())?
            .expect("authored on the root layer")
            .connection_path_list()
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
            .root_layer()
            .attribute(attr.path().clone())?
            .expect("authored on the root layer")
            .connection_path_list()
            .unwrap();
        assert!(op.explicit);
        assert_eq!(op.explicit_items, vec![b, a]);
        Ok(())
    }

    /// A query reproduces `get_at` at every time code over a time-sampled
    /// attribute: before, between, exact, and after the authored samples.
    #[test]
    fn query_matches_get_at() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(sdf::Value::Double(1.0), TimeCode::new(0.0))?
            .set_at(sdf::Value::Double(3.0), TimeCode::new(10.0))?;
        let q = attr.query();
        for t in [-5.0, 0.0, 5.0, 10.0, 100.0] {
            assert_eq!(
                q.get_at::<sdf::Value>(TimeCode::new(t))?,
                attr.get_at(TimeCode::new(t))?
            );
        }
        assert_eq!(q.get_at::<f64>(TimeCode::new(5.0))?, Some(2.0));
        Ok(())
    }

    /// An attribute with only a default resolves to that default at every time
    /// code, and `get()` returns it.
    #[test]
    fn query_static_default() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set(sdf::Value::Double(7.0))?;
        let q = attr.query();
        assert_eq!(q.get::<f64>()?, Some(7.0));
        assert_eq!(q.get_at::<f64>(TimeCode::new(0.0))?, Some(7.0));
        assert_eq!(q.get_at::<f64>(TimeCode::new(50.0))?, Some(7.0));
        Ok(())
    }

    /// The cached source rebuilds after an edit: re-authoring a sample value is
    /// reflected on the next query, since the composition revision advances.
    #[test]
    fn query_rebuilds_after_edit() -> anyhow::Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(sdf::Value::Double(1.0), TimeCode::new(0.0))?
            .set_at(sdf::Value::Double(3.0), TimeCode::new(10.0))?;
        let q = attr.query();
        assert_eq!(q.get_at::<f64>(TimeCode::new(5.0))?, Some(2.0));

        // Re-author the t=10 sample; the next query must reflect it.
        let _attr = attr.set_at(sdf::Value::Double(5.0), TimeCode::new(10.0))?;
        assert_eq!(q.get_at::<f64>(TimeCode::new(5.0))?, Some(3.0));
        Ok(())
    }

    /// A query over samples brought in through a non-identity arc offset
    /// interpolates identically to `get_at`, proving the layer-time mapping.
    #[test]
    fn query_retimed_offset() -> anyhow::Result<()> {
        let stage = stage()?;
        stage
            .define_prim("/Source")?
            .create_attribute("x", "double")?
            .set_at(sdf::Value::Double(1.0), TimeCode::new(0.0))?
            .set_at(sdf::Value::Double(3.0), TimeCode::new(10.0))?;
        stage.define_prim("/Prim")?.set_metadata(
            sdf::FieldKey::References.as_str(),
            sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                prim_path: sdf::path("/Source")?,
                layer_offset: sdf::LayerOffset::new(10.0, 1.0),
                ..Default::default()
            }])),
        )?;

        let attr = stage.attribute("/Prim.x")?;
        let q = attr.query();
        // Sample at source 0/10 reads back at stage 10/20 through the offset.
        for t in [10.0, 15.0, 20.0] {
            assert_eq!(
                q.get_at::<sdf::Value>(TimeCode::new(t))?,
                attr.get_at(TimeCode::new(t))?
            );
        }
        assert_eq!(q.get_at::<f64>(TimeCode::new(10.0))?, Some(1.0));
        assert_eq!(q.get_at::<f64>(TimeCode::new(20.0))?, Some(3.0));
        Ok(())
    }

    /// Clearing metadata off an attribute the edit target does not author leaves
    /// the layer alone: no spec is stamped from the schema declaration just to
    /// hold the absence.
    #[test]
    fn clear_metadata_keeps_layer() -> anyhow::Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert!(intensity.is_defined()?, "the schema declares it");
        intensity.clear_metadata("documentation")?;

        let root = stage.root_layer().export_to_string()?;
        assert!(!root.contains("inputs:intensity"));
        Ok(())
    }

    /// An attribute handle at a non-property path addresses no attribute, so
    /// clearing through it must not reach the prim's own metadata.
    #[test]
    fn clear_metadata_wrong_spec() -> anyhow::Result<()> {
        let stage = stage()?;
        stage
            .define_prim("/P")?
            .set_metadata("documentation", sdf::Value::String("keep".into()))?;

        let _ = stage.attribute("/P")?.clear_metadata("documentation");

        assert_eq!(
            stage.prim("/P")?.get_metadata::<String>("documentation")?.as_deref(),
            Some("keep"),
            "the prim's own metadata is not an attribute's to clear"
        );
        Ok(())
    }

    /// A property neither authored nor declared has no opinion to clear, so
    /// clearing one reports success without authoring anything.
    #[test]
    fn clear_metadata_absent_spec() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/P")?;

        stage.attribute("/P.nope")?.clear_metadata("documentation")?;

        assert!(!stage.root_layer().export_to_string()?.contains("nope"));
        Ok(())
    }
}
