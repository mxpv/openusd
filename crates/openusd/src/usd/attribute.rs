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

use super::{
    Prim, PrimTypeInfo, ResolveInfo, ResolveInfoSource, SpecSite, Stage, StageAuthoringError, TimeCode, TypeConflict,
    authoring, interp,
};
use crate::Result;
use crate::pcp;
use crate::pcp::AttributeValueSource;
use crate::sdf;
use crate::tf;

/// Stage-composed attribute handle. Mirrors C++ `UsdAttribute`.
///
/// Returned by [`Stage::create_attribute`] / [`Prim::create_attribute`] with
/// defaults `variability = Varying`, `custom = true`, matching C++ generic
/// property authoring. Override via the fluent setters below.
#[derive(Clone, Debug)]
pub struct Attribute {
    stage: Stage,
    path: sdf::Path,
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
    /// The value is validated against the composed declaration — exactly, no
    /// coercion, a block always passing — and the edit-target layer's own
    /// declaration must agree with the composed one (§6.5.1 of the core spec:
    /// a `color3f` value may land in a local `float3`, not in a local
    /// `point3f` or `double`), so a layer never holds a value of a kind it
    /// does not declare. The value is then written as validated, never
    /// recast against the local declaration. A spec the target lacks is
    /// stamped first from the declaration composition finds — the schema's,
    /// else the strongest authored spec's (C++
    /// `UsdStage::_CreatePropertySpecForEditing`).
    ///
    /// `time` is `None` to author the default value, or `Some(tc)` (a
    /// [`usd::TimeCode`](super::TimeCode), which a bare `TimeCode` coerces
    /// into) to author a time sample. A numeric time is in stage (composed)
    /// time: when the current edit target is an arc with a non-identity layer
    /// offset, the sample is keyed at the inverse-mapped source-layer time (C++
    /// `UsdEditTarget::MapToSpecTime`), so it reads back at `time` once
    /// composition re-applies the offset.
    ///
    /// A `timecode` value is a time coordinate in that same frame, so it is
    /// inverse-mapped alongside the key it is authored at, and a relative
    /// `pathExpression` is anchored against the owning prim and mapped into
    /// the target's namespace (C++ `_StageValueToFieldXf`); both read back
    /// unchanged.
    pub fn set_at(
        self,
        value: impl Into<sdf::Value>,
        time: impl Into<Option<super::TimeCode>>,
    ) -> Result<Self, StageAuthoringError> {
        let plan = self.plan_authoring(value.into(), time.into())?;
        self.stage.with_target_layer_at(&self.path, |layer, spec_path| {
            let mut spec = plan.prepare(layer.data_mut(), &spec_path)?;
            match plan.spec_time {
                None => spec.set_default_raw(plan.value),
                Some(time) => spec.set_time_sample_raw(time, plan.value)?,
            }
            Ok(())
        })?;
        Ok(self)
    }

    /// Block opinions from weaker layers: every local value opinion is
    /// removed and `default` becomes a value block, so nothing weaker resolves
    /// through (C++ `UsdAttribute::Block`, which is `Clear` followed by a
    /// block). The spec is prepared like a write — stamped when the target
    /// lacks it, its local declaration read fallibly — and the `timeSamples`
    /// field is erased whole, without decoding samples the block discards.
    pub fn block(self) -> Result<Self, StageAuthoringError> {
        let plan = self.plan_authoring(sdf::Value::ValueBlock, None)?;
        self.stage.with_target_layer_at(&self.path, |layer, spec_path| {
            let mut spec = plan.prepare(layer.data_mut(), &spec_path)?;
            spec.erase(sdf::FieldKey::TimeSamples.as_str());
            spec.set_default_raw(sdf::Value::ValueBlock);
            Ok(())
        })?;
        Ok(self)
    }

    /// Remove every local value opinion — `default` and the whole
    /// `timeSamples` field — from the edit target (C++ `UsdAttribute::Clear`),
    /// so weaker layers' opinions resolve again. A target holding no spec is
    /// left alone, and the sample field is erased without decoding it.
    pub fn clear(self) -> Result<Self, StageAuthoringError> {
        self.edit_existing(|spec| {
            spec.clear_default();
            spec.erase(sdf::FieldKey::TimeSamples.as_str());
            Ok(())
        })
    }

    /// Remove the local `default` opinion (C++ `UsdAttribute::ClearDefault`);
    /// a target holding no spec is left alone.
    pub fn clear_default(self) -> Result<Self, StageAuthoringError> {
        self.edit_existing(|spec| {
            spec.clear_default();
            Ok(())
        })
    }

    /// Remove the local opinion at `time` (C++ `UsdAttribute::ClearAtTime`):
    /// the `default` for `None`, otherwise the one sample keyed at the
    /// inverse-mapped time, through the fallible sample-map update, so a
    /// malformed map is an error. A missing sample, a
    /// whole-field block and a target holding no spec are left alone.
    pub fn clear_at(self, time: impl Into<Option<super::TimeCode>>) -> Result<Self, StageAuthoringError> {
        let Some(time) = time.into() else {
            return self.clear_default();
        };
        let spec_time = self.stage.map_to_spec_time(time.value());
        self.edit_existing(|spec| {
            spec.erase_time_sample(spec_time)?;
            Ok(())
        })
    }

    /// Redeclare the attribute's value type on the edit target (C++
    /// `UsdAttribute::SetTypeName`). It authors at the edit target like every
    /// setter: a schema- or weaker-defined attribute with no local spec gets
    /// one stamped from its declaration first, and a handle nothing defines
    /// is an error. The local spec's values must fit the new type, on the
    /// terms [`sdf::AttributeSpecMut::set_type_name`] states.
    pub fn set_type_name(self, type_name: impl Into<sdf::ValueTypeName>) -> Result<Self, StageAuthoringError> {
        let type_name = type_name.into();
        self.edit(|spec| Ok(spec.set_type_name(type_name)?))
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
    ///
    /// `value` is in stage time, so any `timecode` it holds is mapped into the
    /// edit target's own time frame, and any path expression into its
    /// namespace (C++ `_StageValueToFieldXf`).
    ///
    /// A field with a dedicated setter — `default`, `timeSamples`,
    /// `typeName`, `connectionPaths`, `variability`, `custom` — is refused as
    /// [`ReservedField`](StageAuthoringError::ReservedField): those setters
    /// validate what they write, and this call must not bypass them.
    pub fn set_metadata(self, key: &'static str, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
        authoring::check_reserved(sdf::SpecType::Attribute, key)?;
        let value = self.stage.map_to_spec_value(&self.path, value);
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
        authoring::check_reserved(sdf::SpecType::Attribute, key)?;
        self.edit_existing(|spec| {
            spec.erase(key);
            Ok(())
        })
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
    /// Both sides of `f` are in the target layer's own time frame, since it
    /// reads and writes that one layer: a `timecode` arrives as the layer holds
    /// it and is authored back the same way.
    ///
    /// `key` is `&'static str` for the same change-tracking reason as
    /// [`set_metadata`](Self::set_metadata).
    pub fn update_metadata<F>(self, key: &'static str, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(Option<sdf::Value>) -> Option<sdf::Value>,
    {
        authoring::check_reserved(sdf::SpecType::Attribute, key)?;
        // Resolved before the transaction, consulted only when there is a
        // value to author: an erase never stamps a spec.
        let ensure = authoring::plan_property_spec(&self.stage, &self.path, sdf::SpecType::Attribute, None);
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            let local = layer.data_mut().try_field(&path, key)?.map(Cow::into_owned);
            // Erasing reaches only an attribute spec this layer already holds,
            // so a property it says nothing about stays absent from it.
            let Some(value) = f(local) else {
                return authoring::edit_existing_spec(
                    layer.data_mut(),
                    path,
                    sdf::SpecType::Attribute,
                    sdf::AttributeSpecMut::get,
                    |spec| {
                        spec.erase(key);
                        Ok(())
                    },
                );
            };
            authoring::apply_plan(layer.data_mut(), &path, sdf::SpecType::Attribute, &ensure?)?;
            authoring::edit_spec(
                layer.data_mut(),
                path,
                sdf::SpecType::Attribute,
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
        if self.connections_composed()?.iter().any(|p| p == &target) {
            return Ok(self);
        }
        self.edit(move |spec| {
            spec.add_connection_path(target, prepend)?;
            Ok(())
        })
    }

    /// Remove a single connection target. Returns `Ok(true)` if it was
    /// present. Takes `&self` (returns `bool`, not `Self`, so it doesn't
    /// chain). Mirrors C++ `UsdAttribute::RemoveConnection`.
    pub fn remove_connection(&self, target: impl sdf::IntoPath) -> Result<bool, StageAuthoringError> {
        let target = sdf::try_into_path(target)?;
        // The target may exist only through weaker layers. Check the composed
        // list first so this call can author a delete opinion even when the
        // edit-target layer has no local connection item to remove.
        if !self.connections_composed()?.iter().any(|p| p == &target) {
            return Ok(false);
        }
        // A delete list-op still needs a property spec to carry it, stamped
        // as any other write stamps it.
        let mut removed = false;
        self.edit_spec(|spec| {
            removed = spec.delete_connection_path(&target)?;
            Ok(())
        })?;
        Ok(removed)
    }

    /// Clear all authored `connectionPaths` on the edit target (C++
    /// `UsdAttribute::ClearConnections`). A target holding no spec is left
    /// alone, and the layer records a change only when an opinion went away.
    pub fn clear_connections(self) -> Result<Self, StageAuthoringError> {
        self.edit_existing(|spec| {
            spec.clear_connection_paths();
            Ok(())
        })
    }

    /// `true` when any connection opinion is authored — including an
    /// explicit-empty list op (`.connect = []`), the canonical way to
    /// block weaker-layer connections. Mirrors C++
    /// `UsdAttribute::HasAuthoredConnections`.
    pub fn has_authored_connections(&self) -> Result<bool> {
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
    pub fn connections(&self) -> Result<Vec<sdf::Path>> {
        Ok(self.connections_composed()?)
    }

    /// [`connections`](Self::connections) at the composition tier, for the
    /// authoring paths that dedup against the composed list.
    fn connections_composed(&self) -> Result<Vec<sdf::Path>, pcp::QueryError> {
        self.stage
            .masked(&self.path, |g, cache| cache.connection_paths(g, &self.path))
    }

    /// Composes this attribute's connection paths together with the paths its
    /// list-op deletes, returned as `(connections, deleted)` (C++
    /// `PcpBuildFilteredTargetIndex` and its `deletedPaths` out-param). Both are
    /// empty when the owning prim is outside the population mask.
    pub fn compute_connections(&self) -> Result<(Vec<sdf::Path>, Vec<sdf::Path>)> {
        Ok(self.stage.masked(&self.path, |g, cache| {
            cache.compute_attribute_connection_paths(g, &self.path)
        })?)
    }

    /// Composed `variability` for this attribute (spec 12.2.3: the weakest
    /// authored opinion wins). Mirrors C++ `UsdAttribute::GetVariability`.
    ///
    /// A schema that declares this attribute wins outright: variability is part
    /// of the declaration, so an authored opinion cannot make a `uniform`
    /// attribute animate.
    pub fn variability(&self) -> Result<Option<sdf::Variability>> {
        if let Some(declared) = self.declared_variability()? {
            return Ok(Some(declared));
        }
        Ok(self
            .stage
            .field::<sdf::Variability>(&self.path, sdf::FieldKey::Variability)?)
    }

    /// The variability this attribute's schema declares, if a schema declares
    /// the attribute at all.
    ///
    /// A schema that omits the field declares the default, so this is a
    /// property of the declaration existing — not of the field being authored.
    fn declared_variability(&self) -> Result<Option<sdf::Variability>, pcp::QueryError> {
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
    pub fn is_custom(&self) -> Result<bool> {
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
    pub fn is_defined(&self) -> Result<bool> {
        let spec_type = match self.stage.spec_type(&self.path)? {
            Some(spec_type) => Some(spec_type),
            None => self.declared_spec_type()?,
        };
        Ok(spec_type == Some(sdf::SpecType::Attribute))
    }

    /// Composed value type (the `typeName` field) as a registered type name
    /// (C++ `UsdAttribute::GetTypeName`): `None` when nothing declares one, or
    /// the declared spelling is not in the type table. The spelling itself is
    /// metadata, `get_metadata::<tf::Token>(sdf::FieldKey::TypeName)`.
    ///
    /// A schema that declares this attribute wins outright, as it does for
    /// [`variability`](Self::variability): the value type is part of the
    /// declaration, so an authored `typeName` cannot redeclare a schema
    /// attribute as a different type. Composition answers only for an
    /// attribute no schema declares.
    pub fn type_name(&self) -> Result<Option<sdf::ValueTypeName>> {
        Ok(self
            .declared_type_token()?
            .and_then(|token| sdf::ValueTypeName::find(token.as_str())))
    }

    /// The semantic role of the composed value type (C++
    /// `UsdAttribute::GetRoleName`): `Some(Role::Color)` for a `color3f`,
    /// `None` for a foundational type or an attribute with no registered type.
    pub fn role(&self) -> Result<Option<sdf::Role>> {
        Ok(self.type_name()?.and_then(|type_name| type_name.role()))
    }

    /// The `typeName` token as declared — by the schema first, else by the
    /// strongest composed opinion — whatever its spelling. The read behind
    /// [`type_name`](Self::type_name), [`role`](Self::role) and the value
    /// checks; it never feeds spec creation.
    fn declared_type_token(&self) -> Result<Option<tf::Token>, pcp::QueryError> {
        if let Some(declared) = self.definition_field(sdf::FieldKey::TypeName)? {
            return Ok(declared.try_as_token());
        }
        Ok(self
            .stage
            .field::<sdf::Value>(&self.path, sdf::FieldKey::TypeName)?
            .and_then(sdf::Value::try_as_token))
    }

    /// The read phase of a value write (see [`AttributeAuthoringPlan`]): the
    /// value validated against the composed declaration, the spec plan, and
    /// the value and time mapped for the edit target. Runs outside any
    /// transaction, so every composition query happens here.
    ///
    /// The spec plan resolves first because a plan that stamps a spec has
    /// already found the declaration to stamp it from, which is the composed
    /// declaration the value is checked against; only a target that holds the
    /// spec already leaves the plan with nothing to say about the type, and
    /// that one case reads it.
    fn plan_authoring(
        &self,
        value: sdf::Value,
        time: Option<super::TimeCode>,
    ) -> Result<AttributeAuthoringPlan, StageAuthoringError> {
        let ensure = authoring::plan_property_spec(&self.stage, &self.path, sdf::SpecType::Attribute, None)?;
        let effective = if value.is_value_block() {
            None
        } else {
            let declared = match ensure.attribute_type() {
                Some(declared) => declared.clone(),
                None => sdf::ValueTypeName::from(self.declared_type_token()?.ok_or(sdf::ValueTypeError::Empty)?),
            };
            declared.validate(&value)?;
            Some(declared)
        };
        let value = self.stage.map_to_spec_value(&self.path, value);
        let spec_time = time.map(|time| self.stage.map_to_spec_time(time.value()));
        Ok(AttributeAuthoringPlan {
            effective,
            ensure,
            value,
            spec_time,
        })
    }

    /// Composed default value decoded to `T`. The convenience spelling of
    /// `get_at(None)`; mirrors C++ `UsdAttribute::Get`.
    ///
    /// `T` is any type implementing `TryFrom<sdf::Value>` — a scalar
    /// (`get::<f32>()`), an array (`get::<Vec<f32>>()`), or [`sdf::Value`]
    /// itself (`get::<sdf::Value>()`) for the raw value. A type mismatch
    /// against the authored value surfaces as an `Err`, not `None`.
    pub fn get<T>(&self) -> Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: Into<crate::Error>,
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
    /// fallback; [`resolve_info`](Self::resolve_info) reports which answered.
    ///
    /// [`InterpolationType`]: super::InterpolationType
    pub fn get_at<T>(&self, time: impl Into<Option<super::TimeCode>>) -> Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: Into<crate::Error>,
    {
        let value = match time.into() {
            None => self.stage.field::<sdf::Value>(&self.path, sdf::FieldKey::Default)?,
            Some(time) => self.stage.resolve_at(&self.path, time.value())?,
        };
        let value = match value {
            Some(value) => Some(value),
            None => self.fallback_value()?,
        };
        super::decode_value(value)
    }

    /// The value this attribute's schema declares when nothing is authored
    /// (C++ `UsdPrimDefinition::GetAttributeFallbackValue`).
    ///
    /// Resolved against the stage's
    /// [`SchemaRegistry`](super::SchemaRegistry), from the owning
    /// prim's composed `typeName` and `apiSchemas`. `None` when no schema
    /// declares this attribute, or declares it without a fallback.
    ///
    /// An `asset` fallback is anchored against the schematics that declared
    /// it, at wherever that layer resolved from.
    pub fn fallback_value(&self) -> Result<Option<sdf::Value>> {
        let Some((info, name)) = authoring::schema_definition(&self.stage, &self.path)? else {
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
    fn definition_field(&self, field: impl AsRef<str>) -> Result<Option<sdf::Value>, pcp::QueryError> {
        let Some((info, name)) = authoring::schema_definition(&self.stage, &self.path)? else {
            return Ok(None);
        };
        let Some(property) = info.prim_definition().property(&name) else {
            return Ok(None);
        };
        Ok(property.field(field).cloned())
    }

    /// Whether the declaring schema supplies a value to fall back on.
    ///
    /// Reads the filtered fallback, not the raw field: a composed schema
    /// property can retract an inherited fallback by authoring a value block,
    /// which leaves the field present but supplies nothing.
    fn has_schema_fallback(&self) -> Result<bool, pcp::QueryError> {
        let Some((info, name)) = authoring::schema_definition(&self.stage, &self.path)? else {
            return Ok(false);
        };
        Ok(info.prim_definition().attribute_fallback(&name).is_some())
    }

    /// The spec type the owning prim's schema declares for this property, or
    /// `None` when no schema declares it.
    fn declared_spec_type(&self) -> Result<Option<sdf::SpecType>, pcp::QueryError> {
        let Some((info, name)) = authoring::schema_definition(&self.stage, &self.path)? else {
            return Ok(None);
        };
        Ok(info
            .prim_definition()
            .property(&name)
            .map(|property| property.spec_type()))
    }

    /// The schema of the prim this attribute hangs off, with the attribute's
    /// own name, but `None` unless a schema actually declares this property.
    fn declaring_property(&self) -> Result<Option<(Arc<PrimTypeInfo>, tf::Token)>, pcp::QueryError> {
        let Some((info, name)) = authoring::schema_definition(&self.stage, &self.path)? else {
            return Ok(None);
        };
        Ok(info.prim_definition().has_property(&name).then_some((info, name)))
    }

    /// Where the value [`get`](Self::get) returns comes from, without producing
    /// it (C++ `UsdAttribute::GetResolveInfo`).
    ///
    /// Reports the *proximal* source: the one that answers without naming a
    /// time. That is not necessarily what [`get`](Self::get) returns, which
    /// resolves at the default time — use
    /// [`resolve_info_at`](Self::resolve_info_at) to ask about a specific time.
    pub fn resolve_info(&self) -> Result<ResolveInfo> {
        self.build_resolve_info(pcp::ResolveMode::Proximal)
    }

    /// Where the value at `time` comes from, without producing it.
    ///
    /// `time` is `None` for the default time — matching
    /// [`get_at`](Self::get_at) — or `Some(tc)` for a numeric one.
    pub fn resolve_info_at(&self, time: impl Into<Option<TimeCode>>) -> Result<ResolveInfo> {
        let mode = match time.into() {
            None => pcp::ResolveMode::Default,
            Some(time) => pcp::ResolveMode::Numeric(time.value()),
        };
        self.build_resolve_info(mode)
    }

    /// Adds the schema tier `pcp` knows nothing about to the authored source it
    /// resolved: a blocked or absent authored value falls through to the
    /// prim definition's fallback (spec §12.3.6).
    fn build_resolve_info(&self, mode: pcp::ResolveMode) -> Result<ResolveInfo> {
        let resolved = self.stage.resolve_info(&self.path, mode)?;
        let source = match resolved.source {
            pcp::ResolveSourceKind::Default => ResolveInfoSource::Default,
            pcp::ResolveSourceKind::TimeSamples => ResolveInfoSource::TimeSamples,
            pcp::ResolveSourceKind::ValueClips => ResolveInfoSource::ValueClips,
            pcp::ResolveSourceKind::None => match self.has_schema_fallback()? {
                true => ResolveInfoSource::Fallback,
                false => ResolveInfoSource::None,
            },
        };
        // A schema fallback and an absent value come from no composition node,
        // even when a block at one is what sent resolution there.
        let node = match source {
            ResolveInfoSource::Fallback | ResolveInfoSource::None => None,
            _ => resolved.node,
        };
        Ok(ResolveInfo {
            source,
            node,
            value_is_blocked: resolved.value == pcp::ValueState::Blocked,
            has_authored_opinion: resolved.authored,
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
    pub fn cast<T: sdf::FromValueCast>(&self) -> Result<Option<T>> {
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
    pub fn get_metadata<T>(&self, key: &str) -> Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: Into<crate::Error>,
    {
        // `typeName`, `variability` and `custom` each resolve by their own rule
        // rather than plain strongest-opinion composition, and reading them
        // generically has to give the same answer as the accessor that owns the
        // rule (C++ `_GetSpecialPropMetadataImpl`).
        if let Some(special) = self.special_metadata(key)? {
            return Ok(T::try_from(special).ok());
        }
        if let Some(authored) = self.stage.field::<sdf::Value>(&self.path, key)? {
            return super::decode_value(Some(authored));
        }
        // Schema metadata parses untyped, so a declaration may hold a variant
        // the caller did not ask for; that is "not declared", not an error.
        Ok(self.definition_field(key)?.and_then(|value| T::try_from(value).ok()))
    }

    /// The value of a field whose resolution is not plain composition, or
    /// `None` when `key` is an ordinary metadata field.
    fn special_metadata(&self, key: &str) -> Result<Option<sdf::Value>> {
        if key == sdf::FieldKey::TypeName.as_str() {
            return Ok(self.declared_type_token()?.map(sdf::Value::Token));
        }
        if key == sdf::FieldKey::Variability.as_str() {
            return Ok(self.variability()?.map(sdf::Value::Variability));
        }
        if key == sdf::FieldKey::Custom.as_str() {
            return Ok(Some(sdf::Value::Bool(self.is_custom()?)));
        }
        Ok(None)
    }

    /// The `timeSamples` map [`get_at`](Self::get_at) resolves the value from,
    /// retimed to stage time, or `None` when the source that answers is not a
    /// `timeSamples` opinion.
    ///
    /// A winning value-clip set answers with a schedule rather than a map, so it
    /// reports `None` here; its times reach
    /// [`time_sample_times`](Self::time_sample_times).
    pub fn time_samples(&self) -> Result<Option<sdf::TimeSampleMap>> {
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
    /// The times belong to whichever source [`get_at`](Self::get_at) resolves
    /// the value from, retimed to stage time. A source that answers with a
    /// constant contributes none, so a `default` that hides a weaker layer's
    /// samples leaves this empty.
    pub fn time_sample_times(&self) -> Result<Vec<f64>> {
        Ok(self.stage.time_sample_times(&self.path)?.unwrap_or_default())
    }

    /// The authored sample times within the closed interval `interval`, in
    /// ascending order. Mirrors C++ `UsdAttribute::GetTimeSamplesInInterval`.
    ///
    /// The interval is inclusive at both ends. For samples authored at
    /// `{0, 5, 10}`, `time_samples_in_interval(2.0..=8.0)` returns `[5.0]`,
    /// while `time_samples_in_interval(0.0..=5.0)` returns `[0.0, 5.0]`.
    pub fn time_samples_in_interval(&self, interval: std::ops::RangeInclusive<f64>) -> Result<Vec<f64>> {
        Ok(self
            .time_sample_times()?
            .into_iter()
            .filter(|t| interval.contains(t))
            .collect())
    }

    /// The number of authored time samples, zero when none. Mirrors C++
    /// `UsdAttribute::GetNumTimeSamples`.
    pub fn num_time_samples(&self) -> Result<usize> {
        self.stage.num_time_samples(&self.path)
    }

    /// The pair of authored sample times bracketing `time`, or `None` when no
    /// samples are authored. Mirrors C++
    /// `UsdAttribute::GetBracketingTimeSamples`: the pair collapses to one
    /// repeated time at or beyond an end sample, or when `time` lands exactly
    /// on a sample; otherwise `lower < time < upper`. The two-sample primitive
    /// behind motion-blur and shutter sampling.
    pub fn bracketing_time_samples(&self, time: impl Into<super::TimeCode>) -> Result<Option<(f64, f64)>> {
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
    pub fn value_might_be_time_varying(&self) -> Result<bool> {
        self.stage.value_might_be_time_varying(&self.path)
    }

    /// Every spec that authors an opinion for this attribute, strongest first,
    /// each with the cumulative layer offset that reaches it. Mirrors C++
    /// `UsdProperty::GetPropertyStack` at the default time.
    ///
    /// Meant for debugging and introspection: the makeup of a stack can itself
    /// vary with time, so a repeated value read should use
    /// [`Stage::attribute_query`](super::Stage::attribute_query) rather than a
    /// retained stack.
    pub fn property_stack(&self) -> Result<Vec<SpecSite>> {
        self.stage.property_stack(&self.path, None)
    }

    /// [`property_stack`](Self::property_stack) at a numeric time, which also
    /// lists the value-clip layer each participating clip set supplies the
    /// property from there.
    ///
    /// That clip layer is the one the value would come from: the active clip
    /// when it authors samples for the property, and the set's manifest
    /// otherwise — including where `interpolateMissingClipValues` fills the gap
    /// from surrounding clips, matching C++. Each participating set contributes
    /// one site, since a stack collects every contributor rather than stopping
    /// at the one that answers.
    ///
    /// Only offered for a numeric time: clips contribute no `default`, so the
    /// default-time stack is [`property_stack`](Self::property_stack).
    pub fn property_stack_at(&self, time: TimeCode) -> Result<Vec<SpecSite>> {
        self.stage.property_stack(&self.path, Some(time.value()))
    }

    /// Borrow the attribute spec at `self.path` on the edit target's layer,
    /// apply `f`, and return `self` for chaining. The layer records whatever
    /// fields `f` writes.
    ///
    /// When the edit target has no spec, one is stamped first from the
    /// declaration composition finds — the schema's, else the strongest
    /// authored spec's (C++ `UsdStage::_CreatePropertySpecForEditing`) — so a
    /// property that reads back a fallback can also be authored. Returns
    /// `InvalidPath` when nothing declares the attribute at all.
    fn edit<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>) -> Result<(), StageAuthoringError>,
    {
        self.edit_spec(f)?;
        Ok(self)
    }

    /// Runs `f` on this attribute's spec at the edit target's layer, stamping
    /// one from the declaration composition finds when the target has none.
    /// Every creating mutation goes through here.
    fn edit_spec<F>(&self, f: F) -> Result<(), StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>) -> Result<(), StageAuthoringError>,
    {
        let ensure = authoring::plan_property_spec(&self.stage, &self.path, sdf::SpecType::Attribute, None)?;
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            authoring::apply_plan(layer.data_mut(), &path, sdf::SpecType::Attribute, &ensure)?;
            authoring::edit_spec(
                layer.data_mut(),
                path,
                sdf::SpecType::Attribute,
                sdf::AttributeSpecMut::get,
                f,
            )
        })?;
        Ok(())
    }

    /// Runs `f` on this attribute's spec at the edit target's layer when the
    /// layer holds one, and does nothing when it holds none: the path every
    /// clear takes, so removing an opinion never stamps a spec to remove it
    /// from. A relationship at the path is an error.
    fn edit_existing<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>) -> Result<(), StageAuthoringError>,
    {
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            authoring::edit_existing_spec(
                layer.data_mut(),
                path,
                sdf::SpecType::Attribute,
                sdf::AttributeSpecMut::get,
                f,
            )
        })?;
        Ok(self)
    }
}

/// The read phase of a value write ([`Attribute::set_at`],
/// [`Attribute::block`]), resolved before the transaction: the composed
/// declaration the value was validated against (`None` only for a block,
/// which every declaration takes), the spec plan, and the value and time
/// already mapped for the edit target. The transaction closure receives only
/// this, which is what keeps a composition query out of it.
struct AttributeAuthoringPlan {
    effective: Option<sdf::ValueTypeName>,
    ensure: authoring::EnsurePlan,
    value: sdf::Value,
    spec_time: Option<f64>,
}

impl AttributeAuthoringPlan {
    /// The write phase, inside the transaction: apply the spec plan, read the
    /// edit-target spec's own declaration fallibly (a missing `typeName` is
    /// rejected, never repaired), and unless the value is a block require it
    /// to agree with the composed declaration (§6.5.1 of the core spec).
    /// Returns the spec ready for the raw write.
    fn prepare<'a>(
        &self,
        data: &'a mut dyn sdf::AbstractData,
        path: &sdf::Path,
    ) -> Result<sdf::AttributeSpecMut<'a>, StageAuthoringError> {
        authoring::apply_plan(data, path, sdf::SpecType::Attribute, &self.ensure)?;
        let spec = sdf::AttributeSpecMut::get(data, path.clone())
            .ok_or_else(|| authoring::missing_spec(path, sdf::SpecType::Attribute))?;
        let local = spec.declared_type()?.ok_or(sdf::ValueTypeError::Empty)?;
        if let Some(effective) = &self.effective
            && !effective.agrees_with(&local)
        {
            return Err(StageAuthoringError::LocalTypeConflict(Box::new(TypeConflict {
                path: path.clone(),
                effective: effective.as_token(),
                local: local.as_token(),
            })));
        }
        Ok(spec)
    }
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
/// The cached source is stamped with the composed prim it was resolved from: a
/// timed [`get_at`](AttributeQuery::get_at) reuses it until an edit moves that
/// prim, at which point the next query rebuilds it — so the handle stays correct
/// across authoring without the caller re-creating it, and an edit elsewhere on
/// the stage leaves it standing.
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

/// A resolved value source paired with the stamp it stays replayable under: the
/// composed prim it came from and that prim's composition revision, plus the
/// population epoch when the answer was reached through an instance-proxy
/// redirection. Stale as soon as either stops matching the stage.
struct CachedSource {
    prim: sdf::Path,
    revision: pcp::PrimRevision,
    redirect_epoch: Option<u64>,
    source: AttributeValueSource,
}

impl CachedSource {
    /// Whether the memo still describes what `stage` would resolve now: the prim
    /// it resolved from carries the same revision, and — for an answer reached
    /// by redirection — the epoch that redirection was memoized under still
    /// stands.
    ///
    /// Reads a settled stage, so the caller settles before borrowing the memo
    /// this is called on.
    fn is_current(&self, stage: &Stage) -> bool {
        let (revision, population) = stage.value_stamp(&self.prim);
        revision == Some(self.revision) && self.redirect_epoch.is_none_or(|epoch| epoch == population)
    }
}

#[cfg(test)]
impl AttributeQuery {
    /// Whether a memoized source is present and still valid — what a test asks
    /// to tell "the answer was replayed" from "the answer was recomposed", which
    /// the returned value alone cannot distinguish.
    pub(crate) fn memo_is_current(&self) -> bool {
        let stage = self.attr.stage();
        stage.process_pending();
        self.cached
            .borrow()
            .as_ref()
            .is_some_and(|cached| cached.is_current(stage))
    }
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
    pub fn get<T>(&self) -> Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: Into<crate::Error>,
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
    pub fn get_at<T>(&self, time: impl Into<Option<TimeCode>>) -> Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: Into<crate::Error>,
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
        super::decode_value(value)
    }

    /// `true` when more than one time sample is authored — the cached-source
    /// counterpart of [`Attribute::value_might_be_time_varying`]. Mirrors C++
    /// `UsdAttributeQuery::ValueMightBeTimeVarying`.
    pub fn value_might_be_time_varying(&self) -> Result<bool> {
        self.attr.value_might_be_time_varying()
    }

    /// The authored sample times in ascending order, or empty when none are
    /// authored. Mirrors C++ `UsdAttributeQuery::GetTimeSamples`.
    pub fn time_sample_times(&self) -> Result<Vec<f64>> {
        self.attr.time_sample_times()
    }

    /// Resolves the value at stage `time` through the cached source, rebuilding
    /// it when the stamp it was resolved under no longer holds.
    fn value_at(&self, time: f64) -> Result<Option<sdf::Value>> {
        let stage = self.attr.stage();
        // Settle before the memo is borrowed, not while: draining commits queued
        // edits and fires the stage sinks, and a sink that reads this very query
        // would find the memo already borrowed.
        stage.process_pending();

        // Reuse a cached source whose stamp still stands.
        if let Some(cached) = self.cached.borrow().as_ref()
            && cached.is_current(stage)
        {
            return self.evaluate(&cached.source, time);
        }

        // Miss: resolve the source once and evaluate it. An empty source is as
        // final as any other — a query on a `/__Prototype_N` path completes
        // stage population before it is answered
        // (`Stage::resolve_prototype_path`), so nothing composes into that
        // namespace afterwards without an edit.
        let resolved = stage.resolve_value_source(self.attr.path())?;
        let value = self.evaluate(&resolved.source, time)?;
        // The stamp travels with the source out of the resolving borrow, so an
        // edit a sink authored while the pending queue drained cannot slip
        // between the answer and the token guarding it. Without a stamp — no
        // index is cached at the answering prim, so nothing can say when the
        // answer expires — the source is used once and not memoized.
        if let Some(revision) = resolved.revision {
            self.cached.replace(Some(CachedSource {
                prim: resolved.prim,
                revision,
                redirect_epoch: resolved.redirect_epoch,
                source: resolved.source,
            }));
        }
        Ok(value)
    }

    /// Evaluates an already-resolved value source at stage `time`.
    fn evaluate(&self, source: &AttributeValueSource, time: f64) -> Result<Option<sdf::Value>> {
        let stage = self.attr.stage();
        match source {
            AttributeValueSource::Static(value) => Ok(value.clone()),
            AttributeValueSource::TimeSamples { samples, offset, site } => {
                let value = offset.sample_in_stage_time(samples, time, |map, layer_time| {
                    interp::evaluate(map, layer_time, stage.interpolation_type())
                });
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
                Ok(stage.with_cache(|g, c| Ok(c.resolve_asset_values(g, value.clone(), Some(site))))?)
            }
            AttributeValueSource::Clips => stage.resolve_at(self.attr.path(), time),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Result;
    use crate::usd::SchemaRegistry;

    /// A downstream value type with its own conversion error, standing in for
    /// an application extending the generic accessors.
    #[derive(Debug, PartialEq)]
    struct Meters(f64);

    #[derive(Debug, thiserror::Error)]
    #[error("not a length")]
    struct NotALength;

    impl TryFrom<sdf::Value> for Meters {
        type Error = NotALength;

        fn try_from(value: sdf::Value) -> std::result::Result<Self, Self::Error> {
            match value {
                sdf::Value::Double(v) => Ok(Meters(v)),
                _ => Err(NotALength),
            }
        }
    }

    impl From<NotALength> for crate::Error {
        fn from(error: NotALength) -> Self {
            crate::Error::convert(error)
        }
    }

    #[test]
    fn custom_value_type_reads() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/P")?;
        stage.create_attribute("/P.depth", "double")?.set(2.5_f64)?;

        assert_eq!(stage.attribute("/P.depth")?.get::<Meters>()?, Some(Meters(2.5)));

        stage.create_attribute("/P.name", "string")?.set("x".to_string())?;
        let error = stage.attribute("/P.name")?.get::<Meters>().expect_err("not a double");
        assert!(matches!(error, crate::Error::Convert(_)), "got: {error}");
        Ok(())
    }
    use std::borrow::Cow;
    use std::cell::Cell;
    use std::collections::HashMap;
    use std::fs;
    use std::rc::Rc;

    use crate::usd::{
        Attribute, AttributeQuery, CommittedChange, EditTarget, EditTargetArc, ResolveInfoSource, Stage,
        StageAuthoringError, TimeCode, TypeConflict,
    };
    use crate::{gf, sdf, tf};

    fn stage() -> Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    /// A stage whose prims resolve against the shared test schema family, on
    /// which `DistantLight.inputs:intensity` falls back to 50000.
    fn schema_stage() -> Result<Stage> {
        Stage::builder()
            .schema_registry(SchemaRegistry::test_registry())
            .in_memory("anon.usda")
    }

    #[test]
    fn defined_by_schema_or_spec() -> Result<()> {
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
    fn unauthored_reads_fallback() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Nothing authored the attribute at all — not even a spec — so the
        // value comes entirely from the schema.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.get::<f32>()?, Some(50000.0));
        assert_eq!(intensity.resolve_info()?.source(), ResolveInfoSource::Fallback);
        Ok(())
    }

    /// A `Fallback` source and a usable fallback value are the same question:
    /// the source is read from the filtered fallback, so a schema property whose
    /// `default` is a value block reports `None`, not `Fallback`.
    #[test]
    fn fallback_source_tracks_value() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        for name in ["inputs:intensity", "mine"] {
            let attr = match name {
                "mine" => stage.create_attribute("/Sun.mine", "double")?,
                _ => stage.attribute(format!("/Sun.{name}"))?,
            };
            let is_fallback = attr.resolve_info()?.source() == ResolveInfoSource::Fallback;
            assert_eq!(is_fallback, attr.fallback_value()?.is_some(), "{name}");
        }
        Ok(())
    }

    /// A schema fallback comes from no composition node, even when a block at
    /// one is what sent resolution there.
    #[test]
    fn fallback_names_no_node() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage.create_attribute("/Sun.inputs:intensity", "float")?.block()?;

        let info = stage.attribute("/Sun.inputs:intensity")?.resolve_info()?;
        assert_eq!(info.source(), ResolveInfoSource::Fallback);
        assert!(info.value_is_blocked());
        assert!(info.node().is_none());
        Ok(())
    }

    #[test]
    fn authored_beats_fallback() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage.create_attribute("/Sun.inputs:intensity", "float")?.set(3.0_f32)?;

        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.get::<f32>()?, Some(3.0));
        assert_eq!(intensity.resolve_info()?.source(), ResolveInfoSource::Default);
        Ok(())
    }

    #[test]
    fn fallback_matches_across_time() -> Result<()> {
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
    fn blocked_falls_back_to_schema() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage
            .create_attribute("/Sun.inputs:intensity", "float")?
            .set(sdf::Value::ValueBlock)?;

        // Blocking removes the authored opinion; resolution then reaches the
        // schema, per spec 12.3.6.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.get::<f32>()?, Some(50000.0));
        assert_eq!(intensity.resolve_info()?.source(), ResolveInfoSource::Fallback);
        Ok(())
    }

    #[test]
    fn applied_schema_supplies_fallback() -> Result<()> {
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

    /// The core `usd` family is compiled into the crate, so a stage that
    /// registers nothing of its own still resolves what `CollectionAPI`
    /// declares.
    #[test]
    fn core_family_supplies_fallback() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/Group")?.apply_api("CollectionAPI:render")?;

        let rule = stage.attribute("/Group.collection:render:expansionRule")?;
        assert_eq!(rule.get::<tf::Token>()?, Some(tf::Token::new("expandPrims")));
        Ok(())
    }

    #[test]
    fn schema_property_reports_its_type() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Nothing is authored, so the type and variability come from the
        // schema's declaration alongside the fallback value.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.type_name()?, Some(sdf::ValueTypeName::from("float")));
        assert_eq!(intensity.variability()?, Some(sdf::Variability::Varying));

        let rule = stage.attribute("/Sun.collection:lightLink:expansionRule")?;
        assert_eq!(rule.type_name()?, Some(sdf::ValueTypeName::from("token")));
        assert_eq!(rule.variability()?, Some(sdf::Variability::Uniform));
        Ok(())
    }

    #[test]
    fn schema_property_metadata_reads_back() -> Result<()> {
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
    fn declared_varying_beats_authored_uniform() -> Result<()> {
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
    fn schema_property_is_writable() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Nothing authors `inputs:angle`, so there is no spec to edit — the
        // declaration supplies the type and variability to create one with.
        let angle = stage.attribute("/Sun.inputs:angle")?;
        assert_eq!(angle.get::<f32>()?, Some(0.53));
        angle.set(1.5_f32)?;

        let angle = stage.attribute("/Sun.inputs:angle")?;
        assert_eq!(angle.get::<f32>()?, Some(1.5));
        assert_eq!(angle.type_name()?, Some(sdf::ValueTypeName::from("float")));
        // A schema property is not custom, however it was created.
        assert!(!angle.is_custom()?);
        Ok(())
    }

    #[test]
    fn round_trip_over_enumerated_attributes() -> Result<()> {
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
    fn every_setter_stamps_the_schema_spec() -> Result<()> {
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
    fn schema_property_is_not_custom() -> Result<()> {
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
    fn time_samples_count_as_authored() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage
            .create_attribute("/Sun.inputs:intensity", "float")?
            .set_at(100.0_f32, TimeCode::new(0.0))?
            .set_at(200.0_f32, TimeCode::new(10.0))?;

        // The only authored opinion is time samples, and it is what `get_at`
        // resolves, so the source is that rather than the schema fallback.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.resolve_info()?.source(), ResolveInfoSource::TimeSamples);
        assert!(intensity.resolve_info()?.has_authored_value());
        assert_eq!(intensity.get_at::<f32>(TimeCode::new(5.0))?, Some(150.0));
        Ok(())
    }

    #[test]
    fn declared_type_beats_authored() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage.create_attribute("/Sun.inputs:angle", "double")?;

        // The value type is part of the declaration, so a layer cannot
        // redeclare a schema attribute as a different type.
        assert_eq!(
            stage.attribute("/Sun.inputs:angle")?.type_name()?,
            Some(sdf::ValueTypeName::FLOAT)
        );
        // A property no schema declares still reports what layers author.
        assert_eq!(
            stage.create_attribute("/Sun.mine", "double")?.type_name()?,
            Some(sdf::ValueTypeName::DOUBLE)
        );
        Ok(())
    }

    #[test]
    fn generic_metadata_matches_its_accessor() -> Result<()> {
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
            rule.type_name()?.map(|type_name| type_name.as_token())
        );
        assert_eq!(
            rule.get_metadata::<bool>(sdf::FieldKey::Custom.as_str())?,
            Some(rule.is_custom()?)
        );
        assert_eq!(rule.variability()?, Some(sdf::Variability::Uniform));
        Ok(())
    }

    #[test]
    fn schema_metadata_type_mismatch_is_not_an_error() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // Schema metadata parses untyped, so asking for a variant it does not
        // hold reads as undeclared rather than failing.
        let rule = stage.attribute("/Sun.collection:lightLink:expansionRule")?;
        assert_eq!(rule.get_metadata::<Vec<tf::Token>>("allowedTokens")?, None);
        Ok(())
    }

    #[test]
    fn authored_variability_cannot_override_schema() -> Result<()> {
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
    fn unknown_schema_has_no_fallback() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        let unknown = stage.attribute("/Sun.notASchemaProperty")?;
        assert_eq!(unknown.get::<sdf::Value>()?, None);
        assert_eq!(unknown.resolve_info()?.source(), ResolveInfoSource::None);
        Ok(())
    }

    #[test]
    fn masked_prim_has_no_fallback() -> Result<()> {
        let stage = Stage::builder()
            .schema_registry(SchemaRegistry::test_registry())
            .mask(crate::usd::StagePopulationMask::new(["/Keep"])?)
            .in_memory("anon.usda")?;
        stage.define_prim("/Keep")?.set_type_name("DistantLight")?;
        // Outside the mask nothing composes to take a setter, so the type is
        // authored with the definition.
        stage.define_typed_prim("/Drop", "DistantLight")?;

        assert_eq!(stage.attribute("/Keep.inputs:intensity")?.get::<f32>()?, Some(50000.0));
        // An excluded prim resolves no type, so it resolves no fallback either.
        assert_eq!(stage.attribute("/Drop.inputs:intensity")?.get::<f32>()?, None);
        Ok(())
    }

    #[test]
    fn unregistered_type_has_no_fallback() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // The default process registry carries the core `usd` family alone,
        // which declares no `DistantLight`.
        let intensity = stage.attribute("/Sun.inputs:intensity")?;
        assert_eq!(intensity.get::<sdf::Value>()?, None);
        assert_eq!(intensity.resolve_info()?.source(), ResolveInfoSource::None);
        Ok(())
    }

    #[test]
    fn attribute_chain() -> Result<()> {
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
    fn attribute_variability_custom() -> Result<()> {
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
    fn attribute_time_samples() -> Result<()> {
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
    fn time_sample_queries() -> Result<()> {
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
    fn time_sample_times_parity() -> Result<()> {
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
    fn time_sample_times_blocked() -> Result<()> {
        let stage = stage()?;
        let attr = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(sdf::Value::Double(1.0), TimeCode::new(0.0))?
            .set_at(sdf::Value::Double(3.0), TimeCode::new(10.0))?;
        root_edit(&stage, |e| {
            e.attribute_mut(attr.path())?
                .expect("the attribute spec is on the root layer")
                .set(sdf::FieldKey::TimeSamples.as_str(), sdf::Value::ValueBlock);
            Ok(())
        })?;
        assert!(attr.time_samples()?.is_none());
        assert!(attr.time_sample_times()?.is_empty());
        assert_eq!(attr.num_time_samples()?, 0);
        assert!(!attr.value_might_be_time_varying()?);
        Ok(())
    }

    #[test]
    fn attribute_block() -> Result<()> {
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
    fn attribute_block_clears_time_samples() -> Result<()> {
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
    fn attribute_connections() -> Result<()> {
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
    fn authored_connections_explicit_empty() -> Result<()> {
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
    fn add_connection_prepends() -> Result<()> {
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
    fn add_connection_appended() -> Result<()> {
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
    fn add_connection_prepend_on_explicit() -> Result<()> {
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
    fn query_matches_get_at() -> Result<()> {
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
    fn query_static_default() -> Result<()> {
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
    /// reflected on the next query, since the edit restales the prim the source
    /// was resolved from.
    #[test]
    fn query_rebuilds_after_edit() -> Result<()> {
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

    /// An edit retires only the queries whose prims it moved: a warmed query on
    /// an unrelated prim keeps replaying its source, which is the whole point of
    /// stamping per prim rather than per stage.
    #[test]
    fn query_survives_unrelated_edit() -> Result<()> {
        let stage = stage()?;
        let edited = stage
            .define_prim("/A")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set_at(sdf::Value::Double(1.0), TimeCode::new(0.0))?;
        let bystander = stage
            .define_prim("/B")?
            .set_type_name("Xform")?
            .create_attribute("y", "double")?
            .set_at(sdf::Value::Double(2.0), TimeCode::new(0.0))?;

        let edited_query = edited.query();
        let bystander_query = bystander.query();
        assert_eq!(edited_query.get_at::<f64>(TimeCode::new(0.0))?, Some(1.0));
        assert_eq!(bystander_query.get_at::<f64>(TimeCode::new(0.0))?, Some(2.0));

        edited.set_at(sdf::Value::Double(9.0), TimeCode::new(0.0))?;

        assert!(
            !edited_query.memo_is_current(),
            "the edited prim's cached source must be retired"
        );
        assert!(
            bystander_query.memo_is_current(),
            "an edit to /A says nothing about /B, whose source must survive"
        );
        assert_eq!(edited_query.get_at::<f64>(TimeCode::new(0.0))?, Some(9.0));
        assert_eq!(bystander_query.get_at::<f64>(TimeCode::new(0.0))?, Some(2.0));
        Ok(())
    }

    /// A query on an attribute with no spec resolves to nothing and memoizes
    /// nothing — there is no composed source to stamp it against — so the value
    /// authored afterwards is picked up.
    #[test]
    fn query_authored_after_miss() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/A")?.set_type_name("Xform")?;
        let q = stage.attribute("/A.x")?.query();
        assert_eq!(q.get_at::<f64>(TimeCode::new(0.0))?, None);

        prim.create_attribute("x", "double")?.set(sdf::Value::Double(4.0))?;
        assert_eq!(q.get_at::<f64>(TimeCode::new(0.0))?, Some(4.0));
        Ok(())
    }

    /// A query on an instance proxy replays a source resolved from the
    /// prototype, so an edit to the shared source reaches it even though no
    /// index is cached at the proxy's own path (spec 11.3.3).
    #[test]
    fn query_proxy_tracks_source() -> Result<()> {
        let stage = stage()?;
        let source = stage
            .define_prim("/Source/Child")?
            .set_type_name("Xform")?
            .create_attribute("x", "double")?
            .set(sdf::Value::Double(1.0))?;
        stage
            .define_prim("/Inst")?
            .set_metadata(
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    prim_path: sdf::path("/Source")?,
                    ..Default::default()
                }])),
            )?
            .set_instanceable(true)?;

        assert!(
            stage.prim("/Inst/Child")?.is_instance_proxy()?,
            "the query must resolve through a prototype for this to test the redirect"
        );
        let q = stage.attribute("/Inst/Child.x")?.query();
        assert_eq!(q.get_at::<f64>(TimeCode::new(0.0))?, Some(1.0));

        let _source = source.set(sdf::Value::Double(2.0))?;
        assert_eq!(q.get_at::<f64>(TimeCode::new(0.0))?, Some(2.0));
        Ok(())
    }

    /// A query over samples brought in through a non-identity arc offset
    /// interpolates identically to `get_at`, proving the layer-time mapping.
    #[test]
    fn query_retimed_offset() -> Result<()> {
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
    fn clear_metadata_keeps_layer() -> Result<()> {
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
    fn clear_metadata_wrong_spec() -> Result<()> {
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
    fn clear_metadata_absent_spec() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/P")?;

        stage.attribute("/P.nope")?.clear_metadata("documentation")?;

        assert!(!stage.root_layer().export_to_string()?.contains("nope"));
        Ok(())
    }

    // Value-type validation and stage-tier authoring.

    /// A session layer, a root layer with one sublayer, each holding `def "A"`
    /// with the given property declaration (empty for none). The edit target
    /// is the root. The directory keeps the files alive for the stage.
    fn stack(session: &str, root: &str, sub: &str) -> Result<(tempfile::TempDir, Stage)> {
        let dir = tempfile::tempdir()?;
        let prim = |decl: &str| format!("#usda 1.0\ndef \"A\" {{\n    {decl}\n}}\n");
        fs::write(dir.path().join("session.usda"), prim(session))?;
        fs::write(dir.path().join("sub.usda"), prim(sub))?;
        fs::write(
            dir.path().join("root.usda"),
            format!("#usda 1.0\n(\n    subLayers = [@sub.usda@]\n)\ndef \"A\" {{\n    {root}\n}}\n"),
        )?;
        let stage = Stage::builder()
            .session_layer(dir.path().join("session.usda").to_str().expect("utf-8 path"))
            .open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        Ok((dir, stage))
    }

    /// Edit the root layer directly, below the stage-tier setters.
    fn root_edit(
        stage: &Stage,
        f: impl FnOnce(&mut sdf::LayerEdit<'_>) -> Result<(), sdf::AuthoringError>,
    ) -> Result<()> {
        let root_id = stage.root_layer().identifier().to_string();
        stage.layer_mut(&root_id).expect("root layer is live").edit(f)?;
        Ok(())
    }

    /// The raw `field` of the spec at `path` on the layer `layer_id`.
    fn layer_field(stage: &Stage, layer_id: &str, path: &str, field: &str) -> Option<sdf::Value> {
        let layer = stage.layer(layer_id).expect("layer is live");
        layer
            .data()
            .try_field(&sdf::path(path).expect("valid path"), field)
            .expect("readable")
            .map(Cow::into_owned)
    }

    /// The raw `field` of the spec at `path` on the root layer.
    fn root_field(stage: &Stage, path: &str, field: &str) -> Option<sdf::Value> {
        let root_id = stage.root_layer().identifier().to_string();
        layer_field(stage, &root_id, path, field)
    }

    fn root_has_spec(stage: &Stage, path: &str) -> bool {
        stage
            .root_layer()
            .data()
            .has_spec(&sdf::path(path).expect("valid path"))
    }

    fn type_conflict(error: StageAuthoringError) -> TypeConflict {
        match error {
            StageAuthoringError::LocalTypeConflict(conflict) => *conflict,
            other => panic!("expected a local type conflict, got {other:?}"),
        }
    }

    #[test]
    fn set_mismatch_rejected() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage.create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?;
        let error = attr.clone().set(tf::Token::from("x")).expect_err("a token is no float");
        assert!(matches!(
            error,
            StageAuthoringError::ValueType(sdf::ValueTypeError::Mismatch { .. })
        ));
        // Exact: the stage tier never coerces.
        let error = attr.clone().set(4_i32).expect_err("an int is no float");
        assert!(matches!(
            error,
            StageAuthoringError::ValueType(sdf::ValueTypeError::Mismatch { .. })
        ));
        assert_eq!(attr.get::<sdf::Value>()?, None);
        Ok(())
    }

    #[test]
    fn unknown_block_allowed() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage.create_attribute("/A.x", "double3d[]")?;
        attr.clone().set(sdf::Value::ValueBlock)?;
        assert!(attr.resolve_info()?.value_is_blocked());
        let error = attr.set(1.0_f64).expect_err("no value fits an unknown type");
        assert!(matches!(
            error,
            StageAuthoringError::ValueType(sdf::ValueTypeError::Unregistered { .. })
        ));
        Ok(())
    }

    #[test]
    fn set_opaque_rejected() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage.create_attribute("/A.x", sdf::ValueTypeName::OPAQUE)?;
        for value in [sdf::Value::Opaque, sdf::Value::Float(1.0)] {
            let error = attr.clone().set(value).expect_err("opaque holds no value");
            assert!(matches!(
                error,
                StageAuthoringError::ValueType(sdf::ValueTypeError::Opaque)
            ));
        }
        attr.set(sdf::Value::ValueBlock)?;
        Ok(())
    }

    #[test]
    fn role_of_color_attr() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let color = stage.create_attribute("/A.c", sdf::ValueTypeName::COLOR3F)?;
        assert_eq!(color.role()?, Some(sdf::Role::Color));
        let plain = stage.create_attribute("/A.f", sdf::ValueTypeName::FLOAT3)?;
        assert_eq!(plain.role()?, None);
        Ok(())
    }

    #[test]
    fn unknown_type_reads_none() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage.create_attribute("/A.x", "double3d[]")?;
        assert_eq!(attr.type_name()?, None);
        assert_eq!(attr.role()?, None);
        assert_eq!(
            attr.get_metadata::<tf::Token>(sdf::FieldKey::TypeName.as_str())?,
            Some(tf::Token::from("double3d[]"))
        );
        Ok(())
    }

    #[test]
    fn raw_spelling_via_metadata() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage.create_attribute("/A.x", "Color")?;
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::COLOR3D));
        assert_eq!(
            attr.get_metadata::<tf::Token>(sdf::FieldKey::TypeName.as_str())?,
            Some(tf::Token::from("Color")),
            "the spelling is kept as authored"
        );
        Ok(())
    }

    #[test]
    fn local_type_conflict() -> Result<()> {
        let (_dir, stage) = stack("float x", "double x", "")?;
        let error = stage
            .attribute("/A.x")?
            .set(2.0_f32)
            .expect_err("double does not agree with float");
        let conflict = type_conflict(error);
        assert_eq!(conflict.effective, tf::Token::from("float"));
        assert_eq!(conflict.local, tf::Token::from("double"));
        assert_eq!(root_field(&stage, "/A.x", "default"), None);
        Ok(())
    }

    #[test]
    fn local_agrees_writes_raw() -> Result<()> {
        let (_dir, stage) = stack("color3f x", "float3 x", "")?;
        stage.attribute("/A.x")?.set(gf::Vec3f::from([1.0, 0.5, 0.0]))?;
        assert_eq!(
            root_field(&stage, "/A.x", "default"),
            Some(sdf::Value::Vec3f(gf::Vec3f::from([1.0, 0.5, 0.0])))
        );
        assert_eq!(
            root_field(&stage, "/A.x", "typeName"),
            Some(sdf::Value::Token(tf::Token::from("float3"))),
            "the local declaration is untouched"
        );
        Ok(())
    }

    #[test]
    fn local_roles_conflict() -> Result<()> {
        let (_dir, stage) = stack("color3f x", "point3f x", "")?;
        let error = stage
            .attribute("/A.x")?
            .set(gf::Vec3f::from([1.0, 0.5, 0.0]))
            .expect_err("two roles never agree");
        let conflict = type_conflict(error);
        assert_eq!(conflict.local, tf::Token::from("point3f"));
        assert_eq!(root_field(&stage, "/A.x", "default"), None);
        Ok(())
    }

    #[test]
    fn local_type_missing() -> Result<()> {
        let (_dir, stage) = stack("float x", "double x", "")?;
        root_edit(&stage, |e| {
            e.attribute_mut("/A.x")?.expect("root spec").erase("typeName");
            Ok(())
        })?;
        let error = stage
            .attribute("/A.x")?
            .set(1.0_f32)
            .expect_err("a spec without a type is not repaired");
        assert!(matches!(
            error,
            StageAuthoringError::ValueType(sdf::ValueTypeError::Empty)
        ));
        assert_eq!(root_field(&stage, "/A.x", "default"), None);
        Ok(())
    }

    #[test]
    fn local_type_not_token() -> Result<()> {
        let (_dir, stage) = stack("float x", "double x", "")?;
        root_edit(&stage, |e| {
            e.attribute_mut("/A.x")?
                .expect("root spec")
                .set("typeName", sdf::Value::Int(3));
            Ok(())
        })?;
        let error = stage
            .attribute("/A.x")?
            .set(1.0_f32)
            .expect_err("a malformed declaration is reported");
        assert!(matches!(
            error,
            StageAuthoringError::Layer(sdf::AuthoringError::Spec(sdf::SpecError::FieldType {
                field: "typeName",
                ..
            }))
        ));
        assert_eq!(root_field(&stage, "/A.x", "default"), None);
        Ok(())
    }

    #[test]
    fn local_type_unregistered() -> Result<()> {
        let (_dir, stage) = stack("float x", "custom double3d[] x", "")?;
        let error = stage
            .attribute("/A.x")?
            .set(1.0_f32)
            .expect_err("an unknown local type agrees with nothing");
        assert_eq!(type_conflict(error).local, tf::Token::from("double3d[]"));
        stage.attribute("/A.x")?.set(sdf::Value::ValueBlock)?;
        assert_eq!(root_field(&stage, "/A.x", "default"), Some(sdf::Value::ValueBlock));
        Ok(())
    }

    #[test]
    fn block_over_conflict() -> Result<()> {
        let (_dir, stage) = stack("float x", "double x", "")?;
        stage.attribute("/A.x")?.set(sdf::Value::ValueBlock)?;
        assert_eq!(root_field(&stage, "/A.x", "default"), Some(sdf::Value::ValueBlock));
        Ok(())
    }

    #[test]
    fn new_spec_effective_type() -> Result<()> {
        let (_dir, stage) = stack("float x", "", "")?;
        assert!(!root_has_spec(&stage, "/A.x"));
        stage.attribute("/A.x")?.set(1.0_f32)?;
        assert_eq!(
            root_field(&stage, "/A.x", "typeName"),
            Some(sdf::Value::Token(tf::Token::from("float")))
        );
        assert_eq!(root_field(&stage, "/A.x", "default"), Some(sdf::Value::Float(1.0)));
        Ok(())
    }

    #[test]
    fn block_missing_type() -> Result<()> {
        let (_dir, stage) = stack("float x", "double x", "")?;
        root_edit(&stage, |e| {
            e.attribute_mut("/A.x")?.expect("root spec").erase("typeName");
            Ok(())
        })?;
        let error = stage
            .attribute("/A.x")?
            .block()
            .expect_err("a block still needs a declaration");
        assert!(matches!(
            error,
            StageAuthoringError::ValueType(sdf::ValueTypeError::Empty)
        ));
        assert_eq!(root_field(&stage, "/A.x", "default"), None);
        Ok(())
    }

    #[test]
    fn block_type_not_token() -> Result<()> {
        let (_dir, stage) = stack("float x", "double x", "")?;
        root_edit(&stage, |e| {
            e.attribute_mut("/A.x")?
                .expect("root spec")
                .set("typeName", sdf::Value::Int(3));
            Ok(())
        })?;
        let error = stage
            .attribute("/A.x")?
            .block()
            .expect_err("a malformed declaration is reported");
        assert!(matches!(
            error,
            StageAuthoringError::Layer(sdf::AuthoringError::Spec(sdf::SpecError::FieldType { .. }))
        ));
        Ok(())
    }

    #[test]
    fn block_unknown_type() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        stage.create_attribute("/A.x", "double3d[]")?.block()?;
        assert_eq!(root_field(&stage, "/A.x", "default"), Some(sdf::Value::ValueBlock));
        Ok(())
    }

    #[test]
    fn block_bad_samples() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage.create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?;
        root_edit(&stage, |e| {
            e.attribute_mut("/A.x")?
                .expect("root spec")
                .set("timeSamples", sdf::Value::String("junk".into()));
            Ok(())
        })?;
        attr.block()?;
        assert_eq!(
            root_field(&stage, "/A.x", "timeSamples"),
            None,
            "the field is erased whole"
        );
        assert_eq!(root_field(&stage, "/A.x", "default"), Some(sdf::Value::ValueBlock));
        Ok(())
    }

    #[test]
    fn block_erases_samples() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage
            .create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?
            .set_at(1.0_f32, TimeCode::new(0.0))?
            .set_at(3.0_f32, TimeCode::new(10.0))?
            .block()?;
        assert_eq!(root_field(&stage, "/A.x", "timeSamples"), None);
        assert_eq!(root_field(&stage, "/A.x", "default"), Some(sdf::Value::ValueBlock));
        assert_eq!(attr.num_time_samples()?, 0);
        assert_eq!(attr.get_at::<f32>(TimeCode::new(0.0))?, None);
        Ok(())
    }

    #[test]
    fn clear_default() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage
            .create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?
            .set(1.0_f32)?
            .set_at(2.0_f32, TimeCode::new(5.0))?
            .clear_default()?;
        assert_eq!(root_field(&stage, "/A.x", "default"), None);
        assert_eq!(attr.get_at::<f32>(TimeCode::new(5.0))?, Some(2.0), "samples survive");
        Ok(())
    }

    #[test]
    fn clear_at() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage
            .create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?
            .set(1.0_f32)?
            .set_at(2.0_f32, TimeCode::new(0.0))?
            .set_at(3.0_f32, TimeCode::new(10.0))?
            .clear_at(TimeCode::new(0.0))?;
        assert_eq!(attr.time_samples()?, Some(vec![(10.0, sdf::Value::Float(3.0))]));
        let attr = attr.clear_at(None)?;
        assert_eq!(root_field(&stage, "/A.x", "default"), None);

        root_edit(&stage, |e| {
            e.attribute_mut("/A.x")?
                .expect("root spec")
                .set("timeSamples", sdf::Value::String("junk".into()));
            Ok(())
        })?;
        let error = attr
            .clear_at(TimeCode::new(10.0))
            .expect_err("a malformed map is reported");
        assert!(matches!(
            error,
            StageAuthoringError::Layer(sdf::AuthoringError::Spec(sdf::SpecError::FieldType { .. }))
        ));
        Ok(())
    }

    #[test]
    fn clear_all() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage
            .create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?
            .set(1.0_f32)?
            .set_at(2.0_f32, TimeCode::new(0.0))?
            .clear()?;
        assert_eq!(root_field(&stage, "/A.x", "default"), None);
        assert_eq!(root_field(&stage, "/A.x", "timeSamples"), None);
        assert!(root_has_spec(&stage, "/A.x"), "the spec itself stays");
        assert_eq!(attr.resolve_info()?.source(), ResolveInfoSource::None);
        Ok(())
    }

    #[test]
    fn set_type_name() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage
            .create_attribute("/A.x", sdf::ValueTypeName::DOUBLE)?
            .set(1.0_f64)?;
        let error = attr
            .clone()
            .set_type_name(sdf::ValueTypeName::FLOAT)
            .expect_err("the stored double does not fit float");
        assert!(matches!(
            error,
            StageAuthoringError::ValueType(sdf::ValueTypeError::Mismatch { .. })
        ));
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::DOUBLE));

        let attr = attr.clear_default()?.set_type_name(sdf::ValueTypeName::FLOAT)?;
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::FLOAT));

        let attr = attr.set(sdf::Value::ValueBlock)?.set_type_name("double3d[]")?;
        assert_eq!(attr.type_name()?, None, "blocks fit even an unknown type");
        let attr = attr.set_type_name(sdf::ValueTypeName::FLOAT)?.set(1.0_f32)?;
        let error = attr
            .set_type_name("double3d[]")
            .expect_err("a value never fits an unknown type");
        assert!(matches!(error, StageAuthoringError::ValueType(_)));
        Ok(())
    }

    #[test]
    fn set_type_name_opaque() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage
            .create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?
            .set(1.0_f32)?;
        let error = attr
            .clone()
            .set_type_name(sdf::ValueTypeName::OPAQUE)
            .expect_err("a value never fits opaque");
        assert!(matches!(
            error,
            StageAuthoringError::ValueType(sdf::ValueTypeError::Opaque)
        ));
        let attr = attr
            .set(sdf::Value::ValueBlock)?
            .set_type_name(sdf::ValueTypeName::OPAQUE)?;
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::OPAQUE));
        Ok(())
    }

    #[test]
    fn create_attribute_repeat() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        stage
            .create_attribute("/A.x", sdf::ValueTypeName::DOUBLE)?
            .set(1.0_f64)?;
        let again = stage.create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?;
        assert_eq!(again.type_name()?, Some(sdf::ValueTypeName::DOUBLE));
        assert_eq!(again.get::<f64>()?, Some(1.0));
        Ok(())
    }

    #[test]
    fn create_attribute_schema_type() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        let attr = stage.create_attribute("/Sun.inputs:intensity", sdf::ValueTypeName::DOUBLE)?;
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::FLOAT));
        assert_eq!(
            root_field(&stage, "/Sun.inputs:intensity", "typeName"),
            Some(sdf::Value::Token(tf::Token::from("float"))),
            "the schema's declaration is stamped"
        );
        assert!(!attr.is_custom()?);
        Ok(())
    }

    #[test]
    fn create_attribute_strongest_type() -> Result<()> {
        let (_dir, stage) = stack("", "", "double x")?;
        assert!(!root_has_spec(&stage, "/A.x"));
        stage.create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?;
        assert_eq!(
            root_field(&stage, "/A.x", "typeName"),
            Some(sdf::Value::Token(tf::Token::from("double"))),
            "the sublayer's declaration is copied"
        );
        assert_eq!(root_field(&stage, "/A.x", "custom"), None, "absent means not custom");
        assert!(!stage.attribute("/A.x")?.is_custom()?);
        Ok(())
    }

    #[test]
    fn create_attribute_new() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage.create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?;
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::FLOAT));
        assert!(attr.is_custom()?);
        assert_eq!(root_field(&stage, "/A.x", "custom"), Some(sdf::Value::Bool(true)));
        assert_eq!(root_field(&stage, "/A.x", "variability"), None, "absent means varying");
        Ok(())
    }

    #[test]
    fn create_attribute_wrong_kind() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        stage.create_relationship("/A.r")?;
        let error = stage
            .create_attribute("/A.r", sdf::ValueTypeName::FLOAT)
            .expect_err("a relationship is at the path");
        assert!(matches!(
            error,
            StageAuthoringError::SpecKindMismatch {
                expected: sdf::SpecType::Attribute,
                found: sdf::SpecType::Relationship,
                ..
            }
        ));
        Ok(())
    }

    #[test]
    fn create_relationship_repeat() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        stage.create_relationship("/A.r")?.add_target("/A")?;
        let again = stage.create_relationship("/A.r")?;
        assert_eq!(again.targets()?, vec![sdf::path("/A")?]);
        Ok(())
    }

    #[test]
    fn create_relationship_schema() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        let rel = stage.create_relationship("/Sun.collection:lightLink:includes")?;
        assert_eq!(
            stage
                .root_layer()
                .data()
                .spec_type(&sdf::path("/Sun.collection:lightLink:includes")?),
            Some(sdf::SpecType::Relationship),
            "the schema declaration is stamped"
        );
        assert!(!rel.is_custom()?);
        Ok(())
    }

    #[test]
    fn create_relationship_strongest() -> Result<()> {
        let (_dir, stage) = stack("", "", "rel r")?;
        stage.create_relationship("/A.r")?;
        assert_eq!(
            stage.root_layer().data().spec_type(&sdf::path("/A.r")?),
            Some(sdf::SpecType::Relationship)
        );
        assert_eq!(root_field(&stage, "/A.r", "custom"), None, "absent means not custom");
        assert!(!stage.relationship("/A.r")?.is_custom()?);
        Ok(())
    }

    #[test]
    fn create_relationship_wrong_kind() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        stage.create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?;
        let error = stage
            .create_relationship("/A.x")
            .expect_err("an attribute is at the path");
        assert!(matches!(
            error,
            StageAuthoringError::SpecKindMismatch {
                expected: sdf::SpecType::Relationship,
                found: sdf::SpecType::Attribute,
                ..
            }
        ));
        Ok(())
    }

    #[test]
    fn attribute_schema_conflict() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        let error = stage
            .create_attribute("/Sun.collection:lightLink:includes", sdf::ValueTypeName::FLOAT)
            .expect_err("the schema declares a relationship");
        assert!(matches!(error, StageAuthoringError::SpecKindMismatch { .. }));
        assert!(!root_has_spec(&stage, "/Sun.collection:lightLink:includes"));
        Ok(())
    }

    #[test]
    fn relationship_schema_conflict() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        let error = stage
            .create_relationship("/Sun.inputs:intensity")
            .expect_err("the schema declares an attribute");
        assert!(matches!(error, StageAuthoringError::SpecKindMismatch { .. }));
        Ok(())
    }

    #[test]
    fn attribute_stack_conflict() -> Result<()> {
        let (_dir, stage) = stack("rel x", "", "float x")?;
        let error = stage
            .create_attribute("/A.x", sdf::ValueTypeName::FLOAT)
            .expect_err("the strongest spec is a relationship");
        assert!(matches!(error, StageAuthoringError::SpecKindMismatch { .. }));
        assert!(!root_has_spec(&stage, "/A.x"));
        Ok(())
    }

    #[test]
    fn relationship_stack_conflict() -> Result<()> {
        let (_dir, stage) = stack("float x", "", "rel x")?;
        let error = stage
            .create_relationship("/A.x")
            .expect_err("the strongest spec is an attribute");
        assert!(matches!(error, StageAuthoringError::SpecKindMismatch { .. }));
        assert!(!root_has_spec(&stage, "/A.x"));
        Ok(())
    }

    #[test]
    fn set_type_name_creates_spec() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        assert!(!root_has_spec(&stage, "/Sun.inputs:intensity"));
        stage
            .attribute("/Sun.inputs:intensity")?
            .set_type_name(sdf::ValueTypeName::DOUBLE)?;
        assert_eq!(
            root_field(&stage, "/Sun.inputs:intensity", "typeName"),
            Some(sdf::Value::Token(tf::Token::from("double")))
        );
        assert_eq!(
            root_field(&stage, "/Sun.inputs:intensity", "custom"),
            None,
            "the rest of the declaration is stamped: absent means not custom"
        );
        assert!(!stage.attribute("/Sun.inputs:intensity")?.is_custom()?);
        Ok(())
    }

    #[test]
    fn set_type_name_undefined() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let error = stage
            .attribute("/A.nope")?
            .set_type_name(sdf::ValueTypeName::FLOAT)
            .expect_err("nothing defines the attribute");
        assert!(matches!(
            error,
            StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath { .. })
        ));
        Ok(())
    }

    #[test]
    fn ensure_local_wins() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        let path = "/Sun.collection:lightLink:includes";
        root_edit(&stage, |e| {
            sdf::AttributeSpec::new(e.data_mut(), path, "float", sdf::Variability::Varying, true)?;
            Ok(())
        })?;
        // The local attribute spec is used even though the schema declares a
        // relationship of that name.
        stage.attribute(path)?.set(1.0_f32)?;
        assert_eq!(root_field(&stage, path, "default"), Some(sdf::Value::Float(1.0)));
        Ok(())
    }

    #[test]
    fn ensure_one_transaction() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        let path = "/Sun.inputs:intensity";
        let commits = Rc::new(Cell::new(0));
        let _token = {
            let commits = commits.clone();
            stage.add_sink(move |_stage: &Stage, _change: &CommittedChange<'_>| commits.set(commits.get() + 1))
        };

        // The mutation fails after the spec plan says to stamp one: nothing is
        // committed, so no spec and no notice survive.
        let error = stage
            .attribute(path)?
            .edit_spec(|_spec| Err(StageAuthoringError::ReservedField { field: "probe" }))
            .expect_err("the closure's error");
        assert!(matches!(error, StageAuthoringError::ReservedField { field: "probe" }));
        assert!(!root_has_spec(&stage, path));
        assert_eq!(commits.get(), 0);

        // A succeeding retype stamps and retypes the spec in one commit.
        stage.attribute(path)?.set_type_name(sdf::ValueTypeName::DOUBLE)?;
        assert!(root_has_spec(&stage, path));
        assert_eq!(commits.get(), 1);
        Ok(())
    }

    #[test]
    fn strongest_declaration_malformed() -> Result<()> {
        for (bad, kind) in [(None, "missing"), (Some(sdf::Value::Int(3)), "not a token")] {
            let (_dir, stage) = stack("", "float x", "double x")?;
            root_edit(&stage, |e| {
                let mut spec = e.attribute_mut("/A.x")?.expect("root spec");
                match bad.clone() {
                    None => spec.erase("typeName"),
                    Some(value) => spec.set("typeName", value),
                }
                Ok(())
            })?;
            // Author on the session layer, where no spec exists: the strongest
            // authored spec (the root's) is malformed, and the weaker sublayer's
            // sound declaration is never consulted.
            let session_id = stage.session_layer().expect("session layer").identifier().to_string();
            stage.set_edit_target(EditTarget::for_layer(session_id.clone()))?;
            let error = stage
                .create_attribute("/A.x", sdf::ValueTypeName::FLOAT)
                .expect_err("the strongest declaration is malformed");
            match bad {
                None => assert!(
                    matches!(error, StageAuthoringError::ValueType(sdf::ValueTypeError::Empty)),
                    "{kind}: {error:?}"
                ),
                Some(_) => assert!(
                    matches!(
                        error,
                        StageAuthoringError::Layer(sdf::AuthoringError::Spec(sdf::SpecError::FieldType { .. }))
                    ),
                    "{kind}: {error:?}"
                ),
            }
            assert!(
                !stage
                    .layer(&session_id)
                    .expect("session layer")
                    .data()
                    .has_spec(&sdf::path("/A.x")?),
                "{kind}: no spec is stamped"
            );
        }
        Ok(())
    }

    #[test]
    fn create_ignores_empty() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        let attr = stage.create_attribute("/Sun.inputs:intensity", "")?;
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::FLOAT));
        Ok(())
    }

    #[test]
    fn create_rejects_empty() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let error = stage
            .create_attribute("/A.x", "")
            .expect_err("a new attribute needs a type");
        assert!(matches!(
            error,
            StageAuthoringError::ValueType(sdf::ValueTypeError::Empty)
        ));
        assert!(!root_has_spec(&stage, "/A.x"));
        Ok(())
    }

    /// An attribute whose `timeSamples` field is a whole-field block.
    fn field_blocked() -> Result<(Stage, Attribute)> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage.create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?;
        root_edit(&stage, |e| {
            e.attribute_mut("/A.x")?
                .expect("root spec")
                .set("timeSamples", sdf::Value::ValueBlock);
            Ok(())
        })?;
        Ok((stage, attr))
    }

    #[test]
    fn retype_over_field_block() -> Result<()> {
        let (stage, attr) = field_blocked()?;
        attr.set_type_name(sdf::ValueTypeName::DOUBLE)?;
        assert_eq!(root_field(&stage, "/A.x", "timeSamples"), Some(sdf::Value::ValueBlock));
        Ok(())
    }

    #[test]
    fn set_over_field_block() -> Result<()> {
        let (stage, attr) = field_blocked()?;
        attr.set_at(1.0_f32, TimeCode::new(1.0))?;
        assert_eq!(
            root_field(&stage, "/A.x", "timeSamples"),
            Some(sdf::Value::TimeSamples(vec![(1.0, sdf::Value::Float(1.0))]))
        );
        Ok(())
    }

    #[test]
    fn clear_at_field_block() -> Result<()> {
        let (stage, attr) = field_blocked()?;
        attr.clear_at(TimeCode::new(1.0))?;
        assert_eq!(root_field(&stage, "/A.x", "timeSamples"), Some(sdf::Value::ValueBlock));
        Ok(())
    }

    #[test]
    fn update_metadata_uses_plan() -> Result<()> {
        let (_dir, stage) = stack("", "", "custom double x")?;
        stage
            .attribute("/A.x")?
            .update_metadata("documentation", |_| Some(sdf::Value::String("doc".into())))?;
        assert_eq!(
            root_field(&stage, "/A.x", "typeName"),
            Some(sdf::Value::Token(tf::Token::from("double")))
        );
        assert_eq!(root_field(&stage, "/A.x", "custom"), Some(sdf::Value::Bool(true)));
        Ok(())
    }

    #[test]
    fn remove_connection_uses_plan() -> Result<()> {
        let (_dir, stage) = stack("", "", "custom double x.connect = </A.y>")?;
        assert!(stage.attribute("/A.x")?.remove_connection("/A.y")?);
        assert_eq!(
            root_field(&stage, "/A.x", "typeName"),
            Some(sdf::Value::Token(tf::Token::from("double"))),
            "the sublayer's declaration carries the delete opinion"
        );
        assert_eq!(root_field(&stage, "/A.x", "custom"), Some(sdf::Value::Bool(true)));
        assert_eq!(stage.attribute("/A.x")?.connections()?, vec![]);

        let (_dir, stage) = stack("", "rel x", "custom double x.connect = </A.y>")?;
        let error = stage
            .attribute("/A.x")?
            .remove_connection("/A.y")
            .expect_err("a relationship is at the path");
        assert!(matches!(error, StageAuthoringError::SpecKindMismatch { .. }));
        Ok(())
    }

    #[test]
    fn value_type_error_normalized() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage.create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?;
        let error = attr.clone().set(tf::Token::from("x")).expect_err("mismatch");
        assert!(matches!(error, StageAuthoringError::ValueType(_)), "{error:?}");

        root_edit(&stage, |e| {
            e.attribute_mut("/A.x")?.expect("root spec").erase("typeName");
            Ok(())
        })?;
        let error = attr.set(sdf::Value::ValueBlock).expect_err("missing local type");
        assert!(matches!(error, StageAuthoringError::ValueType(_)), "{error:?}");
        Ok(())
    }

    #[test]
    fn clear_connections_no_spec() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage.attribute("/Sun.inputs:intensity")?.clear_connections()?;
        assert!(!root_has_spec(&stage, "/Sun.inputs:intensity"));
        Ok(())
    }

    #[test]
    fn clear_targets() -> Result<()> {
        let (_dir, stage) = stack("", "rel r = [</B>]", "rel r = [</C>]")?;
        let rel = stage.relationship("/A.r")?;
        assert_eq!(
            rel.targets()?,
            vec![sdf::path("/B")?],
            "the explicit root list blocks the sublayer"
        );
        let rel = rel.clear_targets()?;
        assert_eq!(
            rel.targets()?,
            vec![sdf::path("/C")?],
            "the sublayer's targets compose again"
        );
        assert!(root_has_spec(&stage, "/A.r"));
        let rel = rel.set_targets(Vec::<sdf::Path>::new())?;
        assert_eq!(rel.targets()?, vec![], "an explicit empty list blocks again");
        Ok(())
    }

    #[test]
    fn clear_targets_no_spec() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;
        stage
            .relationship("/Sun.collection:lightLink:includes")?
            .clear_targets()?;
        assert!(!root_has_spec(&stage, "/Sun.collection:lightLink:includes"));
        Ok(())
    }

    #[test]
    fn clear_existing_wrong_kind() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        stage.create_relationship("/A.r")?;
        let error = stage
            .attribute("/A.r")?
            .clear()
            .expect_err("a relationship is at the path");
        assert!(matches!(error, StageAuthoringError::SpecKindMismatch { .. }));
        Ok(())
    }

    #[test]
    fn reserved_field_rejected() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/A")?;
        let attr = stage.create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?;
        for key in [
            "default",
            "timeSamples",
            "typeName",
            "connectionPaths",
            "variability",
            "custom",
        ] {
            let reserved = |error: StageAuthoringError| {
                assert!(
                    matches!(error, StageAuthoringError::ReservedField { field } if field == key),
                    "{key}: {error:?}"
                );
            };
            reserved(attr.clone().set_metadata(key, 1.0_f32).expect_err(key));
            reserved(attr.clone().update_metadata(key, |_| None).expect_err(key));
            reserved(attr.clone().clear_metadata(key).expect_err(key));
        }
        let rel = stage.create_relationship("/A.r")?;
        for key in ["targetPaths", "variability", "custom"] {
            let error = rel.clone().set_metadata(key, true).expect_err(key);
            assert!(
                matches!(error, StageAuthoringError::ReservedField { field } if field == key),
                "{key}: {error:?}"
            );
        }
        // An ordinary field still goes through.
        attr.set_metadata("documentation", sdf::Value::String("doc".into()))?;
        Ok(())
    }

    // Path-expression normalization for the edit target.

    /// The reference fixture with the edit target on the referenced layer,
    /// where `/World/MyPrim` maps to `/Source`.
    fn referenced_target() -> Result<(Stage, String)> {
        let stage = Stage::open(concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures/ref_external.usda"))?;
        let target = stage.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
        let layer_id = target.layer_identifier().to_string();
        stage.set_edit_target(target)?;
        Ok((stage, layer_id))
    }

    fn expr_field(stage: &Stage, layer_id: &str, path: &str, field: &str) -> String {
        layer_field(stage, layer_id, path, field)
            .expect("field authored")
            .try_as_path_expression()
            .expect("a path expression")
            .to_string()
    }

    #[test]
    fn path_expr_arc_target() -> Result<()> {
        let (stage, layer_id) = referenced_target()?;
        stage
            .create_attribute("/World/MyPrim.expr", sdf::ValueTypeName::PATH_EXPRESSION)?
            .set(sdf::Value::PathExpression(sdf::PathExpression::parse("Child")))?;
        assert_eq!(
            expr_field(&stage, &layer_id, "/Source.expr", "default"),
            "/Source/Child"
        );
        // The absolute form is anchored in stage namespace, then mapped.
        stage
            .attribute("/World/MyPrim.expr")?
            .set(sdf::Value::PathExpression(sdf::PathExpression::parse(
                "/World/MyPrim/Child//",
            )))?;
        assert_eq!(
            expr_field(&stage, &layer_id, "/Source.expr", "default"),
            "/Source/Child//"
        );
        Ok(())
    }

    #[test]
    fn path_expr_variant_target() -> Result<()> {
        let stage = stage()?;
        let root = stage.edit_target().layer_identifier().to_string();
        stage.define_prim("/Prim")?;
        stage.set_edit_target(EditTarget::for_local_direct_variant(
            root.clone(),
            sdf::path("/Prim{set=sel}")?,
        )?)?;
        let attr = stage.create_attribute("/Prim.expr", sdf::ValueTypeName::PATH_EXPRESSION)?;
        // Select the variant so the attribute composes. The anchor is the
        // stage-namespace prim; the mapping then moves the pattern into the
        // variant's namespace, where the spec itself lives.
        root_edit(&stage, |e| {
            let mut prim = e.prim_mut("/Prim")?.expect("the prim spec");
            prim.set(
                sdf::FieldKey::VariantSetNames.as_str(),
                sdf::Value::TokenListOp(sdf::TokenListOp::prepended([tf::Token::from("set")])),
            );
            prim.set(
                sdf::FieldKey::VariantSelection.as_str(),
                sdf::Value::VariantSelectionMap(HashMap::from([("set".to_string(), "sel".to_string())])),
            );
            Ok(())
        })?;
        attr.set(sdf::Value::PathExpression(sdf::PathExpression::parse("Child")))?;
        assert_eq!(
            expr_field(&stage, &root, "/Prim{set=sel}.expr", "default"),
            "/Prim{set=sel}Child"
        );
        Ok(())
    }

    #[test]
    fn path_expr_vec() -> Result<()> {
        let (stage, layer_id) = referenced_target()?;
        stage
            .create_attribute("/World/MyPrim.exprs", sdf::ValueTypeName::PATH_EXPRESSION_ARRAY)?
            .set(sdf::Value::PathExpressionVec(vec![
                sdf::PathExpression::parse("Child"),
                sdf::PathExpression::parse("/World/MyPrim"),
            ]))?;
        let exprs = layer_field(&stage, &layer_id, "/Source.exprs", "default")
            .expect("authored")
            .try_as_path_expression_vec()
            .expect("an expression array");
        let spelled: Vec<String> = exprs.iter().map(ToString::to_string).collect();
        assert_eq!(spelled, ["/Source/Child", "/Source"]);
        Ok(())
    }

    #[test]
    fn path_expr_metadata() -> Result<()> {
        let (stage, layer_id) = referenced_target()?;
        stage.prim("/World/MyPrim")?.set_metadata(
            "customExpr",
            sdf::Value::PathExpression(sdf::PathExpression::parse("Child")),
        )?;
        assert_eq!(expr_field(&stage, &layer_id, "/Source", "customExpr"), "/Source/Child");

        stage.create_relationship("/World/MyPrim.rel")?.set_metadata(
            "customExpr",
            sdf::Value::PathExpression(sdf::PathExpression::parse("Child")),
        )?;
        assert_eq!(
            expr_field(&stage, &layer_id, "/Source.rel", "customExpr"),
            "/Source/Child"
        );

        stage
            .create_attribute("/World/MyPrim.x", sdf::ValueTypeName::FLOAT)?
            .set_metadata(
                "customExpr",
                sdf::Value::PathExpression(sdf::PathExpression::parse("Child")),
            )?;
        assert_eq!(
            expr_field(&stage, &layer_id, "/Source.x", "customExpr"),
            "/Source/Child"
        );
        Ok(())
    }

    /// A path expression authors straight through `set`, and is anchored to
    /// the edit target like any other path-expression opinion.
    #[test]
    fn set_path_expression() -> Result<()> {
        let (stage, layer_id) = referenced_target()?;
        stage
            .create_attribute("/World/MyPrim.expr", sdf::ValueTypeName::PATH_EXPRESSION)?
            .set(sdf::PathExpression::parse("Child"))?;
        assert_eq!(
            expr_field(&stage, &layer_id, "/Source.expr", "default"),
            "/Source/Child"
        );
        Ok(())
    }

    #[test]
    fn path_expr_nested_dict() -> Result<()> {
        let (stage, layer_id) = referenced_target()?;
        stage.prim("/World/MyPrim")?.set_metadata(
            "customData",
            sdf::Value::Dictionary(HashMap::from([(
                "expr".to_string(),
                sdf::Value::PathExpression(sdf::PathExpression::parse("Child")),
            )])),
        )?;
        let dict = layer_field(&stage, &layer_id, "/Source", "customData").expect("authored");
        let entries = dict.try_as_dictionary().expect("a dictionary");
        let expr = entries["expr"]
            .clone()
            .try_as_path_expression()
            .expect("a path expression");
        assert_eq!(expr.to_string(), "/Source/Child");
        Ok(())
    }

    #[test]
    fn path_expr_time_samples() -> Result<()> {
        let (stage, layer_id) = referenced_target()?;
        stage
            .create_attribute("/World/MyPrim.expr", sdf::ValueTypeName::PATH_EXPRESSION)?
            .set_at(
                sdf::Value::PathExpression(sdf::PathExpression::parse("Child")),
                TimeCode::new(1.0),
            )?;
        let samples = layer_field(&stage, &layer_id, "/Source.expr", "timeSamples").expect("authored");
        let samples = samples.try_as_time_samples().expect("a sample map");
        let expr = samples[0]
            .1
            .clone()
            .try_as_path_expression()
            .expect("a path expression");
        assert_eq!(expr.to_string(), "/Source/Child");
        Ok(())
    }

    #[test]
    fn path_expr_named_ref() -> Result<()> {
        let (stage, layer_id) = referenced_target()?;
        stage
            .create_attribute("/World/MyPrim.expr", sdf::ValueTypeName::PATH_EXPRESSION)?
            .set(sdf::Value::PathExpression(sdf::PathExpression::parse("%:lights Child")))?;
        assert_eq!(
            expr_field(&stage, &layer_id, "/Source.expr", "default"),
            "%:lights /Source/Child",
            "a named reference keeps its empty path"
        );
        Ok(())
    }
}
