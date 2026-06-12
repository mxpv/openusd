//! Stage-composed attribute handle — a value-type wrapper around
//! `(stage, path)` that mirrors C++ `UsdAttribute`.
//!
//! Like [`Prim`], the handle is freely [`Clone`], holds no borrow on the
//! composition cache, and re-acquires state from the [`Stage`] per call. Its
//! fluent setters take `self` by value and return `Self`, so writes chain in a
//! single statement that ends with the final handle bound.

use std::cell::RefCell;

use super::{interp, Prim, Stage, StageAuthoringError, TimeCode};
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
        self.edit(|spec| spec.set(sdf::FieldKey::Variability.as_str(), sdf::Value::Variability(v)))
    }

    /// Set the attribute's `custom` flag. Always authors an explicit
    /// opinion (see [`Attribute::set_variability`] for the rationale).
    pub fn set_custom(self, custom: bool) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| spec.set(sdf::FieldKey::Custom.as_str(), sdf::Value::Bool(custom)))
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
            None => self.edit(|spec| spec.set_default(value)),
            Some(time) => {
                let spec_time = self.stage.map_to_spec_time(time.value());
                self.edit(|spec| spec.set_time_sample(spec_time, value))
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
        })
    }

    /// Set the `colorSpace` token.
    pub fn set_color_space(self, color_space: impl Into<String>) -> Result<Self, StageAuthoringError> {
        let color_space = color_space.into();
        self.edit(|spec| spec.set_color_space(color_space))
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
    pub fn set_connections<I>(self, targets: I) -> Result<Self, StageAuthoringError>
    where
        I: IntoIterator<Item = sdf::Path>,
    {
        let targets: Vec<sdf::Path> = targets.into_iter().collect();
        self.edit(|spec| spec.set_connection_paths(targets))
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
        // Dedup against the composed result, not just the local edit-target
        // op. Otherwise adding a weaker-layer target would author a stronger
        // duplicate and could accidentally reorder it.
        if self.connections()?.iter().any(|p| p == &target) {
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
                    removed = spec.delete_connection_path(&target);
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
        self.edit_connection(|spec| spec.clear_connection_paths())
    }

    /// Run `f` on the attribute spec at the edit target's layer. The layer's
    /// `EditProxy` records a `connectionPaths` change (driving cache
    /// invalidation) only when `f` actually mutates the field. The shared
    /// helper for the connection authoring methods above.
    fn edit_connection<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>) -> bool,
    {
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            super::edit_spec(
                layer.data_mut(),
                path,
                "no attribute spec at path on the edit target layer",
                sdf::AttributeSpecMut::get,
                |spec| {
                    f(spec);
                    Ok(())
                },
            )
        })?;
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
    /// authored opinion wins), if any layer authored one. Mirrors C++
    /// `UsdAttribute::GetVariability`.
    pub fn variability(&self) -> anyhow::Result<Option<sdf::Variability>> {
        self.stage
            .field::<sdf::Variability>(&self.path, sdf::FieldKey::Variability)
    }

    /// `true` when this attribute is composed as `custom` (spec 12.2.4: true if
    /// *any* opinion in the stack is true). Mirrors C++ `UsdProperty::IsCustom`;
    /// an unauthored `custom` field resolves to `false`.
    pub fn is_custom(&self) -> anyhow::Result<bool> {
        Ok(self
            .stage
            .field::<bool>(&self.path, sdf::FieldKey::Custom)?
            .unwrap_or(false))
    }

    /// Composed value type (the `typeName` field), if set. Mirrors C++
    /// `UsdAttribute::GetTypeName`.
    ///
    /// `typeName` is a token; a value of any other type is treated as untyped
    /// (`None`).
    pub fn type_name(&self) -> anyhow::Result<Option<tf::Token>> {
        Ok(self
            .stage
            .field::<sdf::Value>(&self.path, sdf::FieldKey::TypeName)?
            .and_then(|v| v.try_as_token()))
    }

    /// Composed default value decoded to `T`, if any layer authored one. The
    /// convenience spelling of `get_at(None)`; mirrors C++ `UsdAttribute::Get`.
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
        Ok(value.map(T::try_from).transpose()?)
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
    /// `T`, if any layer authored one. Mirrors C++
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
        self.stage.field::<T>(&self.path, key)
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

    /// `true` when more than one time sample is authored, the fast check for
    /// "this value may change over time". Mirrors C++
    /// `UsdAttribute::ValueMightBeTimeVarying`. Counts value-clip-contributed
    /// times (spec 12.3.4) alongside the composed `timeSamples`.
    pub fn value_might_be_time_varying(&self) -> anyhow::Result<bool> {
        Ok(self.num_time_samples()? > 1)
    }

    /// Returns the property stack: each `(layer identifier, spec path)` site
    /// that authors a spec for this attribute, strongest first. Mirrors C++
    /// `UsdProperty::GetPropertyStack`.
    pub fn property_stack(&self) -> anyhow::Result<Vec<(String, sdf::Path)>> {
        self.stage.with_cache(|g, c| c.property_stack(g, &self.path))
    }

    /// Borrow the attribute spec at `self.path` on the edit target's layer,
    /// apply `f`, and return `self` for chaining. The layer's `EditProxy`
    /// records whatever fields `f` writes. Returns `InvalidPath` if no
    /// attribute spec exists at the path.
    fn edit<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::AttributeSpecMut<'_>),
    {
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            super::edit_spec(
                layer.data_mut(),
                path,
                "no attribute spec at path on the edit target layer",
                sdf::AttributeSpecMut::get,
                |spec| {
                    f(spec);
                    Ok(())
                },
            )
        })?;
        Ok(self)
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

    /// Composed default value decoded to `T`, if any layer authored one. The
    /// convenience spelling of `get_at(None)`; mirrors C++
    /// `UsdAttributeQuery::Get()`.
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
            None => self.attr.get_at::<sdf::Value>(None)?,
            Some(time) => self.value_at(time.value())?,
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
        if let Some(cached) = self.cached.borrow().as_ref() {
            if cached.revision == revision {
                return self.evaluate(&cached.source, time);
            }
        }

        // Miss: resolve the source once and evaluate it. Snapshot the revision
        // *after* resolving, so a prototype materialized lazily during the
        // resolve (which advances the revision) is captured rather than leaving
        // the entry instantly stale.
        let source = stage.resolve_value_source(self.attr.path())?;
        let value = self.evaluate(&source, time)?;
        // Don't memoize an empty source. A synthetic `/__Prototype_N` path
        // resolves to `Static(None)` until its prototype materializes — a lazy
        // composition step that does not bump the revision — and then gains a
        // value. Re-resolving each call lets the query self-heal; a real source
        // only changes on an edit, which does bump the revision.
        if !matches!(source, AttributeValueSource::Static(None)) {
            self.cached.replace(Some(CachedSource {
                revision: stage.cache_revision(),
                source,
            }));
        }
        Ok(value)
    }

    /// Evaluates an already-resolved value source at stage `time`.
    fn evaluate(&self, source: &AttributeValueSource, time: f64) -> anyhow::Result<Option<sdf::Value>> {
        let stage = self.attr.stage();
        match source {
            AttributeValueSource::Static(value) => Ok(value.clone()),
            // Interpolate in the node's layer-time frame, mapping `time` back
            // through the inverse offset — matching `PrimIndex::resolve_value_at`.
            AttributeValueSource::TimeSamples { samples, offset } => Ok(interp::evaluate(
                samples,
                offset.inverse().apply(time),
                stage.interpolation_type(),
            )),
            AttributeValueSource::Clips => stage.resolve_at(self.attr.path(), time),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::sdf;
    use crate::usd::{Stage, TimeCode};

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
            .set_connections::<[sdf::Path; 0]>([])?;
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

        let attr = stage.attribute("/Prim.x");
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
}
