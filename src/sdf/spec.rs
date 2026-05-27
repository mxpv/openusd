//! [`Spec`] — the flat per-path field container — and its typed views
//! ([`PrimSpec`], [`AttributeSpec`], [`RelationshipSpec`], [`PseudoRootSpec`]
//! and their `*Mut` pairs).
//!
//! `Spec` parallels C++ `SdfData`'s per-spec entry; the typed views parallel
//! the C++ `Sdf*Spec` subclasses (`SdfPrimSpec`, `SdfAttributeSpec`, …).
//! Where C++ models per-spec-type APIs through inheritance, we use a tagged
//! container plus typed views: the storage stays uniform for readers,
//! writers, and composition, while the views give compile-time guarantees
//! that variant-specific accessors won't be called on the wrong spec kind.
//!
//! The primary entry points for authoring and inspection are
//! [`Layer::create_prim`](crate::sdf::Layer::create_prim) and friends;
//! the `Spec::as_*` downcasts here are the low-level building block
//! equivalent to C++'s `TfDynamic_cast<SdfPrimSpec>(spec)`.

use std::ops::{Deref, DerefMut};

use crate::sdf::schema::ChildrenKey;
use crate::sdf::{FieldKey, Path, PathListOp, SpecType, Specifier, Value, Variability};

// =========================================================================
// Spec
// =========================================================================

/// A single spec in a scene description layer — a (type, fields) entry
/// keyed by [`Path`] within a [`Data`](crate::sdf::Data) store.
///
/// See [SdfSpec](https://openusd.org/dev/api/class_sdf_spec.html) in the
/// USD documentation.
///
/// Fields are stored in authored order. This mirrors the C++ `SdfData`
/// representation and is required for faithful text round-tripping.
///
/// Per-spec-type APIs (typeName setters, time samples, target paths, …)
/// live on the [`PrimSpec`] / [`AttributeSpec`] / [`RelationshipSpec`] /
/// [`PseudoRootSpec`] newtype views and their `*Mut` pairs. C++ does this
/// through inheritance (`SdfPrimSpec : SdfSpec`); we use a tagged container
/// plus typed views. `Spec::as_prim` / `as_attr` / `as_relationship` /
/// `as_pseudo_root` (and their `_mut` variants) are the Rust equivalent of
/// `TfDynamic_cast<SdfPrimSpec>(spec)` — a low-level downcast. The intended
/// primary entry points are the path-keyed methods on
/// [`Layer`](crate::sdf::Layer) (e.g. `Layer::create_prim`,
/// `Layer::prim_mut`), which mirror `SdfLayer::CreatePrimSpec` /
/// `SdfLayer::GetPrimAtPath` and handle the write-side bookkeeping.
#[derive(Debug, Clone)]
pub struct Spec {
    /// The type of this spec (prim, attribute, relationship, etc.).
    pub ty: SpecType,
    /// The fields stored on this spec, in authored order.
    pub fields: Vec<(String, Value)>,
}

impl Spec {
    /// Creates a new empty spec of the given type.
    pub fn new(ty: SpecType) -> Self {
        Self { ty, fields: Vec::new() }
    }

    /// Insert or replace a field. If the key already exists, its value is
    /// overwritten in place and its position is preserved.
    pub fn add(&mut self, key: impl AsRef<str>, value: impl Into<Value>) {
        let key = key.as_ref();
        let value = value.into();
        if let Some(slot) = self.fields.iter_mut().find(|(k, _)| k == key) {
            slot.1 = value;
        } else {
            self.fields.push((key.to_owned(), value));
        }
    }

    /// Look up a field by name.
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.fields.iter().find(|(k, _)| k == key).map(|(_, v)| v)
    }

    /// Mutably look up a field by name. Useful for in-place edits to composite
    /// values (time-sample maps, list ops) without cloning.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut Value> {
        self.fields.iter_mut().find(|(k, _)| k == key).map(|(_, v)| v)
    }

    /// Returns `true` if the spec has a field with the given name.
    pub fn contains(&self, key: &str) -> bool {
        self.fields.iter().any(|(k, _)| k == key)
    }

    /// Remove a field by name, returning its value if present.
    pub fn remove(&mut self, key: &str) -> Option<Value> {
        let idx = self.fields.iter().position(|(k, _)| k == key)?;
        Some(self.fields.remove(idx).1)
    }

    /// Merge fields from `other` into `self`, upserting each by name.
    pub fn extend_from(&mut self, other: Spec) {
        for (k, v) in other.fields {
            self.add(k, v);
        }
    }

    /// Returns a read-only [`PrimSpec`] view if this spec is of type
    /// [`SpecType::Prim`].
    pub fn as_prim(&self) -> Option<PrimSpec<'_>> {
        (self.ty == SpecType::Prim).then_some(PrimSpec(self))
    }

    /// Returns a mutable [`PrimSpecMut`] view if this spec is of type
    /// [`SpecType::Prim`].
    pub fn as_prim_mut(&mut self) -> Option<PrimSpecMut<'_>> {
        (self.ty == SpecType::Prim).then_some(PrimSpecMut(self))
    }

    /// Returns a read-only [`AttributeSpec`] view if this spec is of type
    /// [`SpecType::Attribute`].
    pub fn as_attr(&self) -> Option<AttributeSpec<'_>> {
        (self.ty == SpecType::Attribute).then_some(AttributeSpec(self))
    }

    /// Returns a mutable [`AttributeSpecMut`] view if this spec is of type
    /// [`SpecType::Attribute`].
    pub fn as_attr_mut(&mut self) -> Option<AttributeSpecMut<'_>> {
        (self.ty == SpecType::Attribute).then_some(AttributeSpecMut(self))
    }

    /// Returns a read-only [`RelationshipSpec`] view if this spec is of type
    /// [`SpecType::Relationship`].
    pub fn as_relationship(&self) -> Option<RelationshipSpec<'_>> {
        (self.ty == SpecType::Relationship).then_some(RelationshipSpec(self))
    }

    /// Returns a mutable [`RelationshipSpecMut`] view if this spec is of type
    /// [`SpecType::Relationship`].
    pub fn as_relationship_mut(&mut self) -> Option<RelationshipSpecMut<'_>> {
        (self.ty == SpecType::Relationship).then_some(RelationshipSpecMut(self))
    }

    /// Returns a read-only [`PseudoRootSpec`] view if this spec is of type
    /// [`SpecType::PseudoRoot`].
    pub fn as_pseudo_root(&self) -> Option<PseudoRootSpec<'_>> {
        (self.ty == SpecType::PseudoRoot).then_some(PseudoRootSpec(self))
    }

    /// Returns a mutable [`PseudoRootSpecMut`] view if this spec is of type
    /// [`SpecType::PseudoRoot`].
    pub fn as_pseudo_root_mut(&mut self) -> Option<PseudoRootSpecMut<'_>> {
        (self.ty == SpecType::PseudoRoot).then_some(PseudoRootSpecMut(self))
    }
}

// =========================================================================
// PrimSpec
// =========================================================================

/// Read-only typed view of a prim [`Spec`]. Parallel to C++ `SdfPrimSpec`.
#[derive(Debug)]
pub struct PrimSpec<'a>(pub(crate) &'a Spec);

impl<'a> Deref for PrimSpec<'a> {
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.0
    }
}

impl<'a> PrimSpec<'a> {
    /// Authored `typeName` (e.g. `"Xform"`, `"Mesh"`). `None` if unset.
    pub fn type_name(&self) -> Option<&str> {
        match self.get(FieldKey::TypeName.as_str())? {
            Value::Token(t) => Some(t.as_str()),
            _ => None,
        }
    }

    /// Authored `specifier` (`def`, `over`, `class`). `None` if unset.
    pub fn specifier(&self) -> Option<Specifier> {
        match self.get(FieldKey::Specifier.as_str())? {
            Value::Specifier(s) => Some(*s),
            _ => None,
        }
    }

    /// Authored `kind` metadata (e.g. `"component"`, `"group"`).
    pub fn kind(&self) -> Option<&str> {
        match self.get(FieldKey::Kind.as_str())? {
            Value::Token(t) => Some(t.as_str()),
            _ => None,
        }
    }

    /// Authored `active` flag. `None` if unset (USD defaults to active).
    pub fn is_active(&self) -> Option<bool> {
        match self.get(FieldKey::Active.as_str())? {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Authored `hidden` flag.
    pub fn is_hidden(&self) -> Option<bool> {
        match self.get(FieldKey::Hidden.as_str())? {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Authored `instanceable` flag.
    pub fn is_instanceable(&self) -> Option<bool> {
        match self.get(FieldKey::Instanceable.as_str())? {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Names of child prims, in declared order. `None` if unset.
    pub fn prim_children(&self) -> Option<&[String]> {
        match self.get(ChildrenKey::PrimChildren.as_str())? {
            Value::TokenVec(v) => Some(v.as_slice()),
            _ => None,
        }
    }

    /// Names of child properties, in declared order. `None` if unset.
    pub fn property_children(&self) -> Option<&[String]> {
        match self.get(ChildrenKey::PropertyChildren.as_str())? {
            Value::TokenVec(v) => Some(v.as_slice()),
            _ => None,
        }
    }
}

/// Mutable typed view of a prim [`Spec`]. Parallel to C++ `SdfPrimSpec`.
#[derive(Debug)]
pub struct PrimSpecMut<'a>(pub(crate) &'a mut Spec);

impl<'a> Deref for PrimSpecMut<'a> {
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.0
    }
}

impl<'a> DerefMut for PrimSpecMut<'a> {
    fn deref_mut(&mut self) -> &mut Spec {
        self.0
    }
}

impl<'a> PrimSpecMut<'a> {
    /// Borrow as a read-only [`PrimSpec`] view.
    pub fn as_prim(&self) -> PrimSpec<'_> {
        PrimSpec(self.0)
    }

    /// Set the `typeName` field.
    pub fn set_type_name(&mut self, name: impl Into<String>) {
        self.add(FieldKey::TypeName, Value::Token(name.into()));
    }

    /// Set the `specifier` field.
    pub fn set_specifier(&mut self, specifier: Specifier) {
        self.add(FieldKey::Specifier, Value::Specifier(specifier));
    }

    /// Set the `kind` metadata.
    pub fn set_kind(&mut self, kind: impl Into<String>) {
        self.add(FieldKey::Kind, Value::Token(kind.into()));
    }

    /// Set the `active` flag.
    pub fn set_active(&mut self, active: bool) {
        self.add(FieldKey::Active, Value::Bool(active));
    }

    /// Set the `hidden` flag.
    pub fn set_hidden(&mut self, hidden: bool) {
        self.add(FieldKey::Hidden, Value::Bool(hidden));
    }

    /// Set the `instanceable` flag.
    pub fn set_instanceable(&mut self, instanceable: bool) {
        self.add(FieldKey::Instanceable, Value::Bool(instanceable));
    }
}

// =========================================================================
// AttributeSpec
// =========================================================================

/// Read-only typed view of an attribute [`Spec`]. Parallel to C++ `SdfAttributeSpec`.
#[derive(Debug)]
pub struct AttributeSpec<'a>(pub(crate) &'a Spec);

impl<'a> Deref for AttributeSpec<'a> {
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.0
    }
}

impl<'a> AttributeSpec<'a> {
    /// Attribute value type name (e.g. `"double"`, `"float3[]"`).
    pub fn type_name(&self) -> Option<&str> {
        match self.get(FieldKey::TypeName.as_str())? {
            Value::Token(t) => Some(t.as_str()),
            _ => None,
        }
    }

    /// Attribute variability. Defaults to [`Variability::Varying`] if unset.
    pub fn variability(&self) -> Variability {
        match self.get(FieldKey::Variability.as_str()) {
            Some(Value::Variability(v)) => *v,
            _ => Variability::Varying,
        }
    }

    /// Whether the attribute is `custom`. Defaults to `false` if unset.
    pub fn is_custom(&self) -> bool {
        match self.get(FieldKey::Custom.as_str()) {
            Some(Value::Bool(b)) => *b,
            _ => false,
        }
    }

    /// Default value, if authored.
    pub fn default(&self) -> Option<&Value> {
        self.get(FieldKey::Default.as_str())
    }

    /// Time-sample map, if authored, in storage order. Samples authored
    /// through [`AttributeSpecMut::set_time_sample`] are kept sorted by time;
    /// samples loaded from a parsed layer reflect on-disk ordering.
    pub fn time_samples(&self) -> Option<&[(f64, Value)]> {
        match self.get(FieldKey::TimeSamples.as_str())? {
            Value::TimeSamples(map) => Some(map.as_slice()),
            _ => None,
        }
    }

    /// Color-space token, if authored.
    pub fn color_space(&self) -> Option<&str> {
        match self.get(FieldKey::ColorSpace.as_str())? {
            Value::Token(t) => Some(t.as_str()),
            _ => None,
        }
    }

    /// `allowedTokens` array, if authored.
    pub fn allowed_tokens(&self) -> Option<&[String]> {
        match self.get(FieldKey::AllowedTokens.as_str())? {
            Value::TokenVec(v) => Some(v.as_slice()),
            _ => None,
        }
    }

    /// Authored `connectionPaths` list op, if present.
    pub fn connection_path_list(&self) -> Option<&PathListOp> {
        match self.get(FieldKey::ConnectionPaths.as_str())? {
            Value::PathListOp(op) => Some(op),
            _ => None,
        }
    }
}

/// Mutable typed view of an attribute [`Spec`]. Parallel to C++ `SdfAttributeSpec`.
#[derive(Debug)]
pub struct AttributeSpecMut<'a>(pub(crate) &'a mut Spec);

impl<'a> Deref for AttributeSpecMut<'a> {
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.0
    }
}

impl<'a> DerefMut for AttributeSpecMut<'a> {
    fn deref_mut(&mut self) -> &mut Spec {
        self.0
    }
}

impl<'a> AttributeSpecMut<'a> {
    /// Borrow as a read-only [`AttributeSpec`] view.
    pub fn as_attr(&self) -> AttributeSpec<'_> {
        AttributeSpec(self.0)
    }

    /// Set the `default` value.
    pub fn set_default(&mut self, value: impl Into<Value>) {
        self.add(FieldKey::Default, value.into());
    }

    /// Clear any authored `default`.
    pub fn clear_default(&mut self) {
        self.remove(FieldKey::Default.as_str());
    }

    /// Insert or replace a time sample at `time`. Samples are kept sorted
    /// by time so consumers can binary-search. A pre-existing value of a
    /// non-`TimeSamples` variant is overwritten — debug builds assert.
    pub fn set_time_sample(&mut self, time: f64, value: impl Into<Value>) {
        let value = value.into();
        match self.get_mut(FieldKey::TimeSamples.as_str()) {
            Some(Value::TimeSamples(map)) => upsert_time_sample(map, time, value),
            Some(other) => {
                debug_assert!(false, "timeSamples field is not a TimeSamples (got {other:?})");
                let mut map = Vec::new();
                upsert_time_sample(&mut map, time, value);
                self.add(FieldKey::TimeSamples, Value::TimeSamples(map));
            }
            None => {
                let mut map = Vec::new();
                upsert_time_sample(&mut map, time, value);
                self.add(FieldKey::TimeSamples, Value::TimeSamples(map));
            }
        }
    }

    /// Erase the time sample at `time`. Returns `true` if a sample was removed.
    /// If this was the last sample, the `timeSamples` field is cleared entirely
    /// so the spec round-trips identically to one that never authored samples.
    pub fn erase_time_sample(&mut self, time: f64) -> bool {
        let key = FieldKey::TimeSamples.as_str();
        let Some(Value::TimeSamples(map)) = self.get_mut(key) else {
            return false;
        };
        // `total_cmp` gives a deterministic total ordering for `f64` (including
        // NaN and signed zero), so a NaN sample inserted via `set_time_sample`
        // can be located here.
        let Some(idx) = map.iter().position(|(t, _)| t.total_cmp(&time).is_eq()) else {
            return false;
        };
        map.remove(idx);
        if map.is_empty() {
            self.remove(key);
        }
        true
    }

    /// Set the `custom` flag.
    pub fn set_custom(&mut self, custom: bool) {
        self.add(FieldKey::Custom, Value::Bool(custom));
    }

    /// Set the `colorSpace` token.
    pub fn set_color_space(&mut self, color_space: impl Into<String>) {
        self.add(FieldKey::ColorSpace, Value::Token(color_space.into()));
    }

    /// Set the `allowedTokens` array.
    pub fn set_allowed_tokens<I, S>(&mut self, tokens: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let tokens: Vec<String> = tokens.into_iter().map(Into::into).collect();
        self.add(FieldKey::AllowedTokens, Value::TokenVec(tokens));
    }

    /// Set the `connectionPaths`.
    pub fn set_connection_paths<I>(&mut self, paths: I)
    where
        I: IntoIterator<Item = Path>,
    {
        let paths: Vec<Path> = paths.into_iter().collect();
        self.add(
            FieldKey::ConnectionPaths,
            Value::PathListOp(PathListOp::explicit(paths)),
        );
    }
}

fn upsert_time_sample(map: &mut Vec<(f64, Value)>, time: f64, value: Value) {
    // `total_cmp` provides a deterministic total ordering over `f64`,
    // including NaN and signed zero. `partial_cmp` would return `None` for
    // NaN, which (with `unwrap_or(Equal)`) collapses NaN keys with every
    // existing sample and silently corrupts the sorted invariant.
    match map.binary_search_by(|(t, _)| t.total_cmp(&time)) {
        Ok(idx) => map[idx].1 = value,
        Err(idx) => map.insert(idx, (time, value)),
    }
}

// =========================================================================
// RelationshipSpec
// =========================================================================

/// Read-only typed view of a relationship [`Spec`]. Parallel to C++ `SdfRelationshipSpec`.
#[derive(Debug)]
pub struct RelationshipSpec<'a>(pub(crate) &'a Spec);

impl<'a> Deref for RelationshipSpec<'a> {
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.0
    }
}

impl<'a> RelationshipSpec<'a> {
    /// Authored `targetPaths` list op, if present.
    pub fn target_path_list(&self) -> Option<&PathListOp> {
        match self.get(FieldKey::TargetPaths.as_str())? {
            Value::PathListOp(op) => Some(op),
            _ => None,
        }
    }

    /// Whether the relationship is `custom`.
    pub fn is_custom(&self) -> bool {
        match self.get(FieldKey::Custom.as_str()) {
            Some(Value::Bool(b)) => *b,
            _ => false,
        }
    }

    /// Relationship variability. Defaults to [`Variability::Varying`].
    pub fn variability(&self) -> Variability {
        match self.get(FieldKey::Variability.as_str()) {
            Some(Value::Variability(v)) => *v,
            _ => Variability::Varying,
        }
    }
}

/// Mutable typed view of a relationship [`Spec`]. Parallel to C++ `SdfRelationshipSpec`.
#[derive(Debug)]
pub struct RelationshipSpecMut<'a>(pub(crate) &'a mut Spec);

impl<'a> Deref for RelationshipSpecMut<'a> {
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.0
    }
}

impl<'a> DerefMut for RelationshipSpecMut<'a> {
    fn deref_mut(&mut self) -> &mut Spec {
        self.0
    }
}

impl<'a> RelationshipSpecMut<'a> {
    /// Borrow as a read-only [`RelationshipSpec`] view.
    pub fn as_relationship(&self) -> RelationshipSpec<'_> {
        RelationshipSpec(self.0)
    }

    /// Replace `targetPaths` with the given list.
    pub fn set_target_paths<I>(&mut self, paths: I)
    where
        I: IntoIterator<Item = Path>,
    {
        let paths: Vec<Path> = paths.into_iter().collect();
        self.add(FieldKey::TargetPaths, Value::PathListOp(PathListOp::explicit(paths)));
    }

    /// Append a single target path. No-op if already present. A pre-existing
    /// value of a non-`PathListOp` variant is overwritten — debug builds assert.
    pub fn add_target(&mut self, path: Path) {
        match self.get_mut(FieldKey::TargetPaths.as_str()) {
            Some(Value::PathListOp(op)) => {
                if !op.iter().any(|p| p == &path) {
                    if op.explicit {
                        op.explicit_items.push(path);
                    } else {
                        op.added_items.push(path);
                    }
                }
            }
            Some(other) => {
                debug_assert!(false, "targetPaths field is not a PathListOp (got {other:?})");
                self.add(FieldKey::TargetPaths, Value::PathListOp(PathListOp::explicit([path])));
            }
            None => {
                self.add(FieldKey::TargetPaths, Value::PathListOp(PathListOp::explicit([path])));
            }
        }
    }

    /// Remove a single target path. Returns `true` if the path was present.
    pub fn remove_target(&mut self, path: &Path) -> bool {
        if let Some(Value::PathListOp(op)) = self.get_mut(FieldKey::TargetPaths.as_str()) {
            return remove_path(&mut op.explicit_items, path)
                | remove_path(&mut op.added_items, path)
                | remove_path(&mut op.prepended_items, path)
                | remove_path(&mut op.appended_items, path);
        }
        false
    }

    /// Set the `custom` flag.
    pub fn set_custom(&mut self, custom: bool) {
        self.add(FieldKey::Custom, Value::Bool(custom));
    }
}

fn remove_path(paths: &mut Vec<Path>, path: &Path) -> bool {
    let Some(idx) = paths.iter().position(|p| p == path) else {
        return false;
    };
    paths.remove(idx);
    true
}

// =========================================================================
// PseudoRootSpec
// =========================================================================

/// Read-only typed view of the layer's root pseudo-spec. Parallel to C++
/// `SdfPseudoRootSpec`; carries layer-wide metadata (`defaultPrim`,
/// `subLayers`, time codes, etc.).
#[derive(Debug)]
pub struct PseudoRootSpec<'a>(pub(crate) &'a Spec);

impl<'a> Deref for PseudoRootSpec<'a> {
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.0
    }
}

impl<'a> PseudoRootSpec<'a> {
    /// `defaultPrim` token, if authored.
    pub fn default_prim(&self) -> Option<&str> {
        match self.get(FieldKey::DefaultPrim.as_str())? {
            Value::Token(t) => Some(t.as_str()),
            _ => None,
        }
    }

    /// Sublayer asset paths in strength order (strongest first).
    pub fn sublayers(&self) -> Option<&[String]> {
        match self.get(FieldKey::SubLayers.as_str())? {
            Value::StringVec(v) | Value::TokenVec(v) => Some(v.as_slice()),
            _ => None,
        }
    }

    /// Layer documentation string.
    pub fn documentation(&self) -> Option<&str> {
        match self.get(FieldKey::Documentation.as_str())? {
            Value::String(s) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Layer start time code.
    pub fn start_time_code(&self) -> Option<f64> {
        match self.get(FieldKey::StartTimeCode.as_str())? {
            Value::Double(v) => Some(*v),
            _ => None,
        }
    }

    /// Layer end time code.
    pub fn end_time_code(&self) -> Option<f64> {
        match self.get(FieldKey::EndTimeCode.as_str())? {
            Value::Double(v) => Some(*v),
            _ => None,
        }
    }

    /// Time codes per second.
    pub fn time_codes_per_second(&self) -> Option<f64> {
        match self.get(FieldKey::TimeCodesPerSecond.as_str())? {
            Value::Double(v) => Some(*v),
            _ => None,
        }
    }

    /// Frames per second.
    pub fn frames_per_second(&self) -> Option<f64> {
        match self.get(FieldKey::FramesPerSecond.as_str())? {
            Value::Double(v) => Some(*v),
            _ => None,
        }
    }

    /// Names of root prims in declared order.
    pub fn prim_children(&self) -> Option<&[String]> {
        match self.get(ChildrenKey::PrimChildren.as_str())? {
            Value::TokenVec(v) => Some(v.as_slice()),
            _ => None,
        }
    }
}

/// Mutable typed view of the layer's root pseudo-spec. Parallel to C++ `SdfPseudoRootSpec`.
#[derive(Debug)]
pub struct PseudoRootSpecMut<'a>(pub(crate) &'a mut Spec);

impl<'a> Deref for PseudoRootSpecMut<'a> {
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.0
    }
}

impl<'a> DerefMut for PseudoRootSpecMut<'a> {
    fn deref_mut(&mut self) -> &mut Spec {
        self.0
    }
}

impl<'a> PseudoRootSpecMut<'a> {
    /// Borrow as a read-only [`PseudoRootSpec`] view.
    pub fn as_pseudo_root(&self) -> PseudoRootSpec<'_> {
        PseudoRootSpec(self.0)
    }

    /// Set the `defaultPrim` token without validation.
    ///
    /// This spec-tier setter writes whatever token it is given. The
    /// validating front door is [`crate::sdf::Layer::set_default_prim`],
    /// which rejects malformed values; use this method when you need to
    /// bypass that check (e.g. round-tripping spec data verbatim).
    pub fn set_default_prim(&mut self, name: impl Into<String>) {
        self.add(FieldKey::DefaultPrim, Value::Token(name.into()));
    }

    /// Replace the sublayer list with the given asset paths.
    pub fn set_sublayers<I, S>(&mut self, paths: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let paths: Vec<String> = paths.into_iter().map(Into::into).collect();
        self.add(FieldKey::SubLayers, Value::StringVec(paths));
    }

    /// Append a sublayer asset path. Duplicate entries are preserved because
    /// USD layer offsets and strength ordering make repeated sublayer arcs
    /// meaningful. Always writes the field as `Value::StringVec` so the
    /// USDA/USDC writers emit it (they match `StringVec` only); a
    /// pre-existing `TokenVec` is migrated in place.
    pub fn add_sublayer(&mut self, path: impl Into<String>) {
        let path = path.into();
        let mut paths: Vec<String> = match self.remove(FieldKey::SubLayers.as_str()) {
            Some(Value::StringVec(v)) | Some(Value::TokenVec(v)) => v,
            _ => Vec::new(),
        };
        paths.push(path);
        self.add(FieldKey::SubLayers, Value::StringVec(paths));
    }

    /// Set the layer documentation string.
    pub fn set_documentation(&mut self, doc: impl Into<String>) {
        self.add(FieldKey::Documentation, Value::String(doc.into()));
    }

    /// Set the layer start time code.
    pub fn set_start_time_code(&mut self, time: f64) {
        self.add(FieldKey::StartTimeCode, Value::Double(time));
    }

    /// Set the layer end time code.
    pub fn set_end_time_code(&mut self, time: f64) {
        self.add(FieldKey::EndTimeCode, Value::Double(time));
    }

    /// Set the time codes per second.
    pub fn set_time_codes_per_second(&mut self, rate: f64) {
        self.add(FieldKey::TimeCodesPerSecond, Value::Double(rate));
    }

    /// Set the frames per second.
    pub fn set_frames_per_second(&mut self, rate: f64) {
        self.add(FieldKey::FramesPerSecond, Value::Double(rate));
    }
}
