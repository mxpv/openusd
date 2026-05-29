//! [`Spec`] — the flat per-path field container — and its typed views
//! ([`PrimSpec`], [`AttributeSpec`], [`RelationshipSpec`], [`PseudoRootSpec`]
//! and their `*Mut` aliases).
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

use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use crate::sdf;

/// A single spec in a scene description layer — a (type, fields) entry
/// keyed by [`sdf::Path`] within a [`Data`](crate::sdf::Data) store.
///
/// See [SdfSpec](https://openusd.org/dev/api/class_sdf_spec.html) in the
/// USD documentation.
///
/// Fields are stored in authored order. This mirrors the C++ `SdfData`
/// representation and is required for faithful text round-tripping.
///
/// Per-spec-type APIs (typeName setters, time samples, target paths, …)
/// live on the [`PrimSpec`] / [`AttributeSpec`] / [`RelationshipSpec`] /
/// [`PseudoRootSpec`] typed views and their `*Mut` aliases. C++ does this
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
    pub ty: sdf::SpecType,
    /// The fields stored on this spec, in authored order.
    pub fields: Vec<(String, sdf::Value)>,
}

/// Errors raised by typed spec-level authoring helpers.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum SpecError {
    /// A field exists with a value type that cannot be edited by the requested helper.
    #[error("field {field} exists with non-{expected} value")]
    FieldType {
        /// The authored field name.
        field: &'static str,
        /// The required value type.
        expected: &'static str,
    },
}

impl Spec {
    /// Creates a new empty spec of the given type.
    pub fn new(ty: sdf::SpecType) -> Self {
        Self { ty, fields: Vec::new() }
    }

    /// Insert or replace a field. If the key already exists, its value is
    /// overwritten in place and its position is preserved.
    pub fn add(&mut self, key: impl AsRef<str>, value: impl Into<sdf::Value>) {
        let key = key.as_ref();
        let value = value.into();
        if let Some(slot) = self.fields.iter_mut().find(|(k, _)| k == key) {
            slot.1 = value;
        } else {
            self.fields.push((key.to_owned(), value));
        }
    }

    /// Look up a field by name.
    pub fn get(&self, key: &str) -> Option<&sdf::Value> {
        self.fields.iter().find(|(k, _)| k == key).map(|(_, v)| v)
    }

    /// Mutably look up a field by name. Useful for in-place edits to composite
    /// values (time-sample maps, list ops) without cloning.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut sdf::Value> {
        self.fields.iter_mut().find(|(k, _)| k == key).map(|(_, v)| v)
    }

    /// Returns `true` if the spec has a field with the given name.
    pub fn contains(&self, key: &str) -> bool {
        self.fields.iter().any(|(k, _)| k == key)
    }

    /// Remove a field by name, returning its value if present.
    pub fn remove(&mut self, key: &str) -> Option<sdf::Value> {
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
    /// [`sdf::SpecType::Prim`].
    pub fn as_prim(&self) -> Option<PrimSpec<'_>> {
        (self.ty == sdf::SpecType::Prim).then_some(PrimSpec::new(self))
    }

    /// Returns a mutable [`PrimSpecMut`] view if this spec is of type
    /// [`sdf::SpecType::Prim`].
    pub fn as_prim_mut(&mut self) -> Option<PrimSpecMut<'_>> {
        (self.ty == sdf::SpecType::Prim).then_some(PrimSpec::new(self))
    }

    /// Returns a read-only [`AttributeSpec`] view if this spec is of type
    /// [`sdf::SpecType::Attribute`].
    pub fn as_attr(&self) -> Option<AttributeSpec<'_>> {
        (self.ty == sdf::SpecType::Attribute).then_some(AttributeSpec::new(self))
    }

    /// Returns a mutable [`AttributeSpecMut`] view if this spec is of type
    /// [`sdf::SpecType::Attribute`].
    pub fn as_attr_mut(&mut self) -> Option<AttributeSpecMut<'_>> {
        (self.ty == sdf::SpecType::Attribute).then_some(AttributeSpec::new(self))
    }

    /// Returns a read-only [`RelationshipSpec`] view if this spec is of type
    /// [`sdf::SpecType::Relationship`].
    pub fn as_relationship(&self) -> Option<RelationshipSpec<'_>> {
        (self.ty == sdf::SpecType::Relationship).then_some(RelationshipSpec::new(self))
    }

    /// Returns a mutable [`RelationshipSpecMut`] view if this spec is of type
    /// [`sdf::SpecType::Relationship`].
    pub fn as_relationship_mut(&mut self) -> Option<RelationshipSpecMut<'_>> {
        (self.ty == sdf::SpecType::Relationship).then_some(RelationshipSpec::new(self))
    }

    /// Returns a read-only [`PseudoRootSpec`] view if this spec is of type
    /// [`sdf::SpecType::PseudoRoot`].
    pub fn as_pseudo_root(&self) -> Option<PseudoRootSpec<'_>> {
        (self.ty == sdf::SpecType::PseudoRoot).then_some(PseudoRootSpec::new(self))
    }

    /// Returns a mutable [`PseudoRootSpecMut`] view if this spec is of type
    /// [`sdf::SpecType::PseudoRoot`].
    pub fn as_pseudo_root_mut(&mut self) -> Option<PseudoRootSpecMut<'_>> {
        (self.ty == sdf::SpecType::PseudoRoot).then_some(PseudoRootSpec::new(self))
    }
}

/// Typed view of a prim [`Spec`]. Parallel to C++ `SdfPrimSpec`.
///
/// The default borrow mode is read-only. [`PrimSpecMut`] aliases this same
/// wrapper with an exclusive borrow, so it has both read and write methods.
#[derive(Debug)]
pub struct PrimSpec<'a, B = &'a Spec> {
    spec: B,
    _marker: PhantomData<&'a Spec>,
}

/// Mutable typed view of a prim [`Spec`]. Parallel to C++ `SdfPrimSpec`.
pub type PrimSpecMut<'a> = PrimSpec<'a, &'a mut Spec>;

impl<'a, B> PrimSpec<'a, B> {
    fn new(spec: B) -> Self {
        Self {
            spec,
            _marker: PhantomData,
        }
    }
}

impl<'a, B> Deref for PrimSpec<'a, B>
where
    B: Deref<Target = Spec>,
{
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.spec.deref()
    }
}

impl<'a, B> DerefMut for PrimSpec<'a, B>
where
    B: DerefMut<Target = Spec>,
{
    fn deref_mut(&mut self) -> &mut Spec {
        self.spec.deref_mut()
    }
}

impl<'a, B> PrimSpec<'a, B>
where
    B: Deref<Target = Spec>,
{
    /// Authored `typeName` (e.g. `"Xform"`, `"Mesh"`). `None` if unset.
    pub fn type_name(&self) -> Option<&str> {
        match self.get(sdf::FieldKey::TypeName.as_str())? {
            sdf::Value::Token(t) => Some(t.as_str()),
            _ => None,
        }
    }

    /// Authored `specifier` (`def`, `over`, `class`). `None` if unset.
    pub fn specifier(&self) -> Option<sdf::Specifier> {
        match self.get(sdf::FieldKey::Specifier.as_str())? {
            sdf::Value::Specifier(s) => Some(*s),
            _ => None,
        }
    }

    /// Authored `kind` metadata (e.g. `"component"`, `"group"`).
    pub fn kind(&self) -> Option<&str> {
        match self.get(sdf::FieldKey::Kind.as_str())? {
            sdf::Value::Token(t) => Some(t.as_str()),
            _ => None,
        }
    }

    /// Authored `active` flag. `None` if unset (USD defaults to active).
    pub fn is_active(&self) -> Option<bool> {
        match self.get(sdf::FieldKey::Active.as_str())? {
            sdf::Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Authored `hidden` flag.
    pub fn is_hidden(&self) -> Option<bool> {
        match self.get(sdf::FieldKey::Hidden.as_str())? {
            sdf::Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Authored `instanceable` flag.
    pub fn is_instanceable(&self) -> Option<bool> {
        match self.get(sdf::FieldKey::Instanceable.as_str())? {
            sdf::Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Names of child prims, in declared order. `None` if unset.
    pub fn prim_children(&self) -> Option<&[String]> {
        match self.get(sdf::ChildrenKey::PrimChildren.as_str())? {
            sdf::Value::TokenVec(v) => Some(v.as_slice()),
            _ => None,
        }
    }

    /// Names of child properties, in declared order. `None` if unset.
    pub fn property_children(&self) -> Option<&[String]> {
        match self.get(sdf::ChildrenKey::PropertyChildren.as_str())? {
            sdf::Value::TokenVec(v) => Some(v.as_slice()),
            _ => None,
        }
    }

    /// Authored `apiSchemas` list op, if present.
    pub fn api_schemas(&self) -> Option<&sdf::TokenListOp> {
        match self.get(sdf::FieldKey::ApiSchemas.as_str())? {
            sdf::Value::TokenListOp(op) => Some(op),
            _ => None,
        }
    }
}

impl<'a, B> PrimSpec<'a, B>
where
    B: DerefMut<Target = Spec>,
{
    /// Set the `typeName` field. An empty `name` clears the field instead
    /// of authoring `sdf::Value::Token("")` — matching the empty-string skip in
    /// [`crate::sdf::Layer::create_prim`] so the two write paths stay in
    /// lockstep.
    pub fn set_type_name(&mut self, name: impl Into<String>) {
        let name = name.into();
        if name.is_empty() {
            self.remove(sdf::FieldKey::TypeName.as_str());
        } else {
            self.add(sdf::FieldKey::TypeName, sdf::Value::Token(name));
        }
    }

    /// Set the `specifier` field.
    pub fn set_specifier(&mut self, specifier: sdf::Specifier) {
        self.add(sdf::FieldKey::Specifier, sdf::Value::Specifier(specifier));
    }

    /// Set the `kind` metadata.
    pub fn set_kind(&mut self, kind: impl Into<String>) {
        self.add(sdf::FieldKey::Kind, sdf::Value::Token(kind.into()));
    }

    /// Set the `active` flag.
    pub fn set_active(&mut self, active: bool) {
        self.add(sdf::FieldKey::Active, sdf::Value::Bool(active));
    }

    /// Set the `hidden` flag.
    pub fn set_hidden(&mut self, hidden: bool) {
        self.add(sdf::FieldKey::Hidden, sdf::Value::Bool(hidden));
    }

    /// Set the `instanceable` flag.
    pub fn set_instanceable(&mut self, instanceable: bool) {
        self.add(sdf::FieldKey::Instanceable, sdf::Value::Bool(instanceable));
    }

    /// Add an applied API schema token to this prim's `apiSchemas` list op.
    ///
    /// Mirrors C++ `UsdPrim::AddAppliedSchema`. When the schema is not yet
    /// authored locally in any opinion bucket, the name is pushed onto
    /// `explicit_items` for explicit ops, otherwise onto `prepended_items`.
    /// Existing explicit/prepended/appended opinions are left in place and
    /// treated as already applied (no duplicate add). A local delete of the
    /// same name is always removed so applying a schema in the same edit
    /// target cancels an earlier removal.
    ///
    /// Returns `Ok(true)` whenever the local list op changed (whether by
    /// adding the schema, by clearing a pending delete, or both); `Ok(false)`
    /// when the call was a no-op.
    pub fn add_applied_schema(&mut self, name: impl Into<String>) -> Result<bool, SpecError> {
        let name = name.into();
        match self.get_mut(sdf::FieldKey::ApiSchemas.as_str()) {
            Some(sdf::Value::TokenListOp(op)) => Ok(add_applied_schema_to_list_op(op, name)),
            Some(_) => Err(SpecError::FieldType {
                field: sdf::FieldKey::ApiSchemas.as_str(),
                expected: "sdf::TokenListOp",
            }),
            None => {
                self.add(
                    sdf::FieldKey::ApiSchemas,
                    sdf::Value::TokenListOp(sdf::TokenListOp::prepended([name])),
                );
                Ok(true)
            }
        }
    }
}

fn add_applied_schema_to_list_op(op: &mut sdf::TokenListOp, name: String) -> bool {
    let already_applied = op.explicit_items.iter().any(|n| n == &name)
        || op.prepended_items.iter().any(|n| n == &name)
        || op.appended_items.iter().any(|n| n == &name)
        // Non-explicit `add` opinions already contribute the schema without changing list position.
        || (!op.explicit && op.added_items.iter().any(|n| n == &name));

    let before = op.deleted_items.len();
    op.deleted_items.retain(|n| n != &name);
    let mut changed = op.deleted_items.len() != before;

    if already_applied {
        return changed;
    }

    if op.explicit {
        op.explicit_items.push(name);
    } else {
        op.prepended_items.push(name);
    }
    changed = true;

    changed
}

/// Typed view of an attribute [`Spec`]. Parallel to C++ `SdfAttributeSpec`.
///
/// The default borrow mode is read-only. [`AttributeSpecMut`] aliases this
/// same wrapper with an exclusive borrow, so it has both read and write methods.
#[derive(Debug)]
pub struct AttributeSpec<'a, B = &'a Spec> {
    spec: B,
    _marker: PhantomData<&'a Spec>,
}

/// Mutable typed view of an attribute [`Spec`]. Parallel to C++ `SdfAttributeSpec`.
pub type AttributeSpecMut<'a> = AttributeSpec<'a, &'a mut Spec>;

impl<'a, B> AttributeSpec<'a, B> {
    fn new(spec: B) -> Self {
        Self {
            spec,
            _marker: PhantomData,
        }
    }
}

impl<'a, B> Deref for AttributeSpec<'a, B>
where
    B: Deref<Target = Spec>,
{
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.spec.deref()
    }
}

impl<'a, B> DerefMut for AttributeSpec<'a, B>
where
    B: DerefMut<Target = Spec>,
{
    fn deref_mut(&mut self) -> &mut Spec {
        self.spec.deref_mut()
    }
}

impl<'a, B> AttributeSpec<'a, B>
where
    B: Deref<Target = Spec>,
{
    /// Attribute value type name (e.g. `"double"`, `"float3[]"`).
    pub fn type_name(&self) -> Option<&str> {
        match self.get(sdf::FieldKey::TypeName.as_str())? {
            sdf::Value::Token(t) => Some(t.as_str()),
            _ => None,
        }
    }

    /// Attribute variability. Defaults to [`sdf::Variability::Varying`] if unset.
    pub fn variability(&self) -> sdf::Variability {
        match self.get(sdf::FieldKey::Variability.as_str()) {
            Some(sdf::Value::Variability(v)) => *v,
            _ => sdf::Variability::Varying,
        }
    }

    /// Whether the attribute is `custom`. Defaults to `false` if unset.
    pub fn is_custom(&self) -> bool {
        match self.get(sdf::FieldKey::Custom.as_str()) {
            Some(sdf::Value::Bool(b)) => *b,
            _ => false,
        }
    }

    /// Default value, if authored.
    pub fn default(&self) -> Option<&sdf::Value> {
        self.get(sdf::FieldKey::Default.as_str())
    }

    /// Time-sample map, if authored, in storage order. Samples authored
    /// through [`AttributeSpecMut::set_time_sample`] are kept sorted by time;
    /// samples loaded from a parsed layer reflect on-disk ordering.
    pub fn time_samples(&self) -> Option<&[(f64, sdf::Value)]> {
        match self.get(sdf::FieldKey::TimeSamples.as_str())? {
            sdf::Value::TimeSamples(map) => Some(map.as_slice()),
            _ => None,
        }
    }

    /// Color-space token, if authored.
    pub fn color_space(&self) -> Option<&str> {
        match self.get(sdf::FieldKey::ColorSpace.as_str())? {
            sdf::Value::Token(t) => Some(t.as_str()),
            _ => None,
        }
    }

    /// `allowedTokens` array, if authored.
    pub fn allowed_tokens(&self) -> Option<&[String]> {
        match self.get(sdf::FieldKey::AllowedTokens.as_str())? {
            sdf::Value::TokenVec(v) => Some(v.as_slice()),
            _ => None,
        }
    }

    /// Authored `connectionPaths` list op, if present.
    pub fn connection_path_list(&self) -> Option<&sdf::PathListOp> {
        match self.get(sdf::FieldKey::ConnectionPaths.as_str())? {
            sdf::Value::PathListOp(op) => Some(op),
            _ => None,
        }
    }
}

impl<'a, B> AttributeSpec<'a, B>
where
    B: DerefMut<Target = Spec>,
{
    /// Set the `default` value.
    pub fn set_default(&mut self, value: impl Into<sdf::Value>) {
        self.add(sdf::FieldKey::Default, value.into());
    }

    /// Clear any authored `default`.
    pub fn clear_default(&mut self) {
        self.remove(sdf::FieldKey::Default.as_str());
    }

    /// Insert or replace a time sample at `time`. Samples are kept sorted
    /// by time so consumers can binary-search. A pre-existing value of a
    /// non-`TimeSamples` variant is overwritten — debug builds assert.
    pub fn set_time_sample(&mut self, time: f64, value: impl Into<sdf::Value>) {
        let value = value.into();
        match self.get_mut(sdf::FieldKey::TimeSamples.as_str()) {
            Some(sdf::Value::TimeSamples(map)) => upsert_time_sample(map, time, value),
            Some(other) => {
                debug_assert!(false, "timeSamples field is not a TimeSamples (got {other:?})");
                let mut map = Vec::new();
                upsert_time_sample(&mut map, time, value);
                self.add(sdf::FieldKey::TimeSamples, sdf::Value::TimeSamples(map));
            }
            None => {
                let mut map = Vec::new();
                upsert_time_sample(&mut map, time, value);
                self.add(sdf::FieldKey::TimeSamples, sdf::Value::TimeSamples(map));
            }
        }
    }

    /// Erase the time sample at `time`. Returns `true` if a sample was removed.
    /// If this was the last sample, the `timeSamples` field is cleared entirely
    /// so the spec round-trips identically to one that never authored samples.
    pub fn erase_time_sample(&mut self, time: f64) -> bool {
        let key = sdf::FieldKey::TimeSamples.as_str();
        let Some(sdf::Value::TimeSamples(map)) = self.get_mut(key) else {
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
        self.add(sdf::FieldKey::Custom, sdf::Value::Bool(custom));
    }

    /// Set the `colorSpace` token.
    pub fn set_color_space(&mut self, color_space: impl Into<String>) {
        self.add(sdf::FieldKey::ColorSpace, sdf::Value::Token(color_space.into()));
    }

    /// Set the `allowedTokens` array.
    pub fn set_allowed_tokens<I, S>(&mut self, tokens: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let tokens: Vec<String> = tokens.into_iter().map(Into::into).collect();
        self.add(sdf::FieldKey::AllowedTokens, sdf::Value::TokenVec(tokens));
    }

    /// Set the `connectionPaths` (explicit list op, replacing any prior).
    pub fn set_connection_paths<I>(&mut self, paths: I)
    where
        I: IntoIterator<Item = sdf::Path>,
    {
        let paths: Vec<sdf::Path> = paths.into_iter().collect();
        self.add(
            sdf::FieldKey::ConnectionPaths,
            sdf::Value::PathListOp(sdf::PathListOp::explicit(paths)),
        );
    }

    /// Append a single connection path. Returns `true` if the spec was
    /// mutated, `false` when the path was already present.
    ///
    /// `prepend = true` joins the prepended-items list (the new path
    /// composes stronger than weaker layers); `prepend = false` joins
    /// the appended-items list (weaker than prepends, but still
    /// composes with weaker-layer opinions). When the existing op is
    /// `explicit`, the path is added to whichever side `prepend`
    /// selects without flipping the op out of explicit mode. A
    /// pre-existing non-`PathListOp` value is overwritten — debug
    /// builds assert.
    pub fn add_connection_path(&mut self, path: sdf::Path, prepend: bool) -> bool {
        match self.get_mut(sdf::FieldKey::ConnectionPaths.as_str()) {
            Some(sdf::Value::PathListOp(op)) => {
                // Re-adding a previously deleted target must first clear the
                // delete bucket; otherwise the newly authored connection can
                // still be removed during list-op application.
                let mut changed = remove_path(&mut op.deleted_items, &path);
                if op.iter().any(|p| p == &path) {
                    return changed;
                }
                if op.explicit {
                    // Stay explicit; honour `prepend` to control position.
                    if prepend {
                        op.explicit_items.insert(0, path);
                    } else {
                        op.explicit_items.push(path);
                    }
                } else if prepend {
                    op.prepended_items.push(path);
                } else {
                    op.appended_items.push(path);
                }
                changed = true;
                changed
            }
            Some(other) => {
                debug_assert!(false, "connectionPaths field is not a sdf::PathListOp (got {other:?})");
                let op = if prepend {
                    sdf::PathListOp::prepended([path])
                } else {
                    sdf::PathListOp::appended([path])
                };
                self.add(sdf::FieldKey::ConnectionPaths, sdf::Value::PathListOp(op));
                true
            }
            None => {
                // Default to a non-explicit list op so the new path composes
                // with weaker-layer opinions, matching C++ `UsdAttribute::AddConnection`.
                let op = if prepend {
                    sdf::PathListOp::prepended([path])
                } else {
                    sdf::PathListOp::appended([path])
                };
                self.add(sdf::FieldKey::ConnectionPaths, sdf::Value::PathListOp(op));
                true
            }
        }
    }

    /// Remove a single connection path. Returns `true` if it was present.
    pub fn remove_connection_path(&mut self, path: &sdf::Path) -> bool {
        if let Some(sdf::Value::PathListOp(op)) = self.get_mut(sdf::FieldKey::ConnectionPaths.as_str()) {
            return remove_path(&mut op.explicit_items, path)
                | remove_path(&mut op.added_items, path)
                | remove_path(&mut op.prepended_items, path)
                | remove_path(&mut op.appended_items, path);
        }
        false
    }

    /// Author a removal for a connection path. Local contributions are
    /// stripped first; non-explicit list ops also get a delete opinion so
    /// weaker-layer contributions stay removed in the composed result.
    pub fn delete_connection_path(&mut self, path: &sdf::Path) -> bool {
        match self.get_mut(sdf::FieldKey::ConnectionPaths.as_str()) {
            Some(sdf::Value::PathListOp(op)) => {
                let removed = remove_path(&mut op.explicit_items, path)
                    | remove_path(&mut op.added_items, path)
                    | remove_path(&mut op.prepended_items, path)
                    | remove_path(&mut op.appended_items, path);
                if op.explicit || op.deleted_items.iter().any(|p| p == path) {
                    return removed;
                }
                op.deleted_items.push(path.clone());
                true
            }
            Some(other) => {
                debug_assert!(false, "connectionPaths field is not a sdf::PathListOp (got {other:?})");
                self.add(
                    sdf::FieldKey::ConnectionPaths,
                    sdf::Value::PathListOp(sdf::PathListOp::deleted([path.clone()])),
                );
                true
            }
            None => {
                self.add(
                    sdf::FieldKey::ConnectionPaths,
                    sdf::Value::PathListOp(sdf::PathListOp::deleted([path.clone()])),
                );
                true
            }
        }
    }

    /// Clear all authored `connectionPaths`. Returns `true` if an
    /// opinion was actually removed.
    pub fn clear_connection_paths(&mut self) -> bool {
        self.remove(sdf::FieldKey::ConnectionPaths.as_str()).is_some()
    }
}

fn upsert_time_sample(map: &mut Vec<(f64, sdf::Value)>, time: f64, value: sdf::Value) {
    // `total_cmp` provides a deterministic total ordering over `f64`,
    // including NaN and signed zero. `partial_cmp` would return `None` for
    // NaN, which (with `unwrap_or(Equal)`) collapses NaN keys with every
    // existing sample and silently corrupts the sorted invariant.
    match map.binary_search_by(|(t, _)| t.total_cmp(&time)) {
        Ok(idx) => map[idx].1 = value,
        Err(idx) => map.insert(idx, (time, value)),
    }
}

/// Typed view of a relationship [`Spec`]. Parallel to C++ `SdfRelationshipSpec`.
///
/// The default borrow mode is read-only. [`RelationshipSpecMut`] aliases this
/// same wrapper with an exclusive borrow, so it has both read and write methods.
#[derive(Debug)]
pub struct RelationshipSpec<'a, B = &'a Spec> {
    spec: B,
    _marker: PhantomData<&'a Spec>,
}

/// Mutable typed view of a relationship [`Spec`]. Parallel to C++ `SdfRelationshipSpec`.
pub type RelationshipSpecMut<'a> = RelationshipSpec<'a, &'a mut Spec>;

impl<'a, B> RelationshipSpec<'a, B> {
    fn new(spec: B) -> Self {
        Self {
            spec,
            _marker: PhantomData,
        }
    }
}

impl<'a, B> Deref for RelationshipSpec<'a, B>
where
    B: Deref<Target = Spec>,
{
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.spec.deref()
    }
}

impl<'a, B> DerefMut for RelationshipSpec<'a, B>
where
    B: DerefMut<Target = Spec>,
{
    fn deref_mut(&mut self) -> &mut Spec {
        self.spec.deref_mut()
    }
}

impl<'a, B> RelationshipSpec<'a, B>
where
    B: Deref<Target = Spec>,
{
    /// Authored `targetPaths` list op, if present.
    pub fn target_path_list(&self) -> Option<&sdf::PathListOp> {
        match self.get(sdf::FieldKey::TargetPaths.as_str())? {
            sdf::Value::PathListOp(op) => Some(op),
            _ => None,
        }
    }

    /// Whether the relationship is `custom`.
    pub fn is_custom(&self) -> bool {
        match self.get(sdf::FieldKey::Custom.as_str()) {
            Some(sdf::Value::Bool(b)) => *b,
            _ => false,
        }
    }

    /// Relationship variability. Defaults to [`sdf::Variability::Varying`].
    pub fn variability(&self) -> sdf::Variability {
        match self.get(sdf::FieldKey::Variability.as_str()) {
            Some(sdf::Value::Variability(v)) => *v,
            _ => sdf::Variability::Varying,
        }
    }
}

impl<'a, B> RelationshipSpec<'a, B>
where
    B: DerefMut<Target = Spec>,
{
    /// Replace `targetPaths` with the given list.
    pub fn set_target_paths<I>(&mut self, paths: I)
    where
        I: IntoIterator<Item = sdf::Path>,
    {
        let paths: Vec<sdf::Path> = paths.into_iter().collect();
        self.add(
            sdf::FieldKey::TargetPaths,
            sdf::Value::PathListOp(sdf::PathListOp::explicit(paths)),
        );
    }

    /// Append a single target path. No-op if already present. A pre-existing
    /// value of a non-`sdf::PathListOp` variant is overwritten — debug builds assert.
    pub fn add_target(&mut self, path: sdf::Path) {
        match self.get_mut(sdf::FieldKey::TargetPaths.as_str()) {
            Some(sdf::Value::PathListOp(op)) => {
                if !op.iter().any(|p| p == &path) {
                    if op.explicit {
                        op.explicit_items.push(path);
                    } else {
                        op.added_items.push(path);
                    }
                }
            }
            Some(other) => {
                debug_assert!(false, "targetPaths field is not a sdf::PathListOp (got {other:?})");
                self.add(
                    sdf::FieldKey::TargetPaths,
                    sdf::Value::PathListOp(sdf::PathListOp::explicit([path])),
                );
            }
            None => {
                self.add(
                    sdf::FieldKey::TargetPaths,
                    sdf::Value::PathListOp(sdf::PathListOp::explicit([path])),
                );
            }
        }
    }

    /// Remove a single target path. Returns `true` if the path was present.
    pub fn remove_target(&mut self, path: &sdf::Path) -> bool {
        if let Some(sdf::Value::PathListOp(op)) = self.get_mut(sdf::FieldKey::TargetPaths.as_str()) {
            return remove_path(&mut op.explicit_items, path)
                | remove_path(&mut op.added_items, path)
                | remove_path(&mut op.prepended_items, path)
                | remove_path(&mut op.appended_items, path);
        }
        false
    }

    /// Set the `custom` flag.
    pub fn set_custom(&mut self, custom: bool) {
        self.add(sdf::FieldKey::Custom, sdf::Value::Bool(custom));
    }
}

fn remove_path(paths: &mut Vec<sdf::Path>, path: &sdf::Path) -> bool {
    let Some(idx) = paths.iter().position(|p| p == path) else {
        return false;
    };
    paths.remove(idx);
    true
}

/// Typed view of the layer's root pseudo-spec. Parallel to C++
/// `SdfPseudoRootSpec`; carries layer-wide metadata (`defaultPrim`,
/// `subLayers`, time codes, etc.).
///
/// The default borrow mode is read-only. [`PseudoRootSpecMut`] aliases this
/// same wrapper with an exclusive borrow, so it has both read and write methods.
#[derive(Debug)]
pub struct PseudoRootSpec<'a, B = &'a Spec> {
    spec: B,
    _marker: PhantomData<&'a Spec>,
}

/// Mutable typed view of the layer's root pseudo-spec. Parallel to C++ `SdfPseudoRootSpec`.
pub type PseudoRootSpecMut<'a> = PseudoRootSpec<'a, &'a mut Spec>;

impl<'a, B> PseudoRootSpec<'a, B> {
    fn new(spec: B) -> Self {
        Self {
            spec,
            _marker: PhantomData,
        }
    }
}

impl<'a, B> Deref for PseudoRootSpec<'a, B>
where
    B: Deref<Target = Spec>,
{
    type Target = Spec;
    fn deref(&self) -> &Spec {
        self.spec.deref()
    }
}

impl<'a, B> DerefMut for PseudoRootSpec<'a, B>
where
    B: DerefMut<Target = Spec>,
{
    fn deref_mut(&mut self) -> &mut Spec {
        self.spec.deref_mut()
    }
}

impl<'a, B> PseudoRootSpec<'a, B>
where
    B: Deref<Target = Spec>,
{
    /// `defaultPrim` token, if authored.
    pub fn default_prim(&self) -> Option<&str> {
        match self.get(sdf::FieldKey::DefaultPrim.as_str())? {
            sdf::Value::Token(t) => Some(t.as_str()),
            _ => None,
        }
    }

    /// Sublayer asset paths in strength order (strongest first).
    pub fn sublayers(&self) -> Option<&[String]> {
        match self.get(sdf::FieldKey::SubLayers.as_str())? {
            sdf::Value::StringVec(v) | sdf::Value::TokenVec(v) => Some(v.as_slice()),
            _ => None,
        }
    }

    /// Layer documentation string.
    pub fn documentation(&self) -> Option<&str> {
        match self.get(sdf::FieldKey::Documentation.as_str())? {
            sdf::Value::String(s) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Layer start time code.
    pub fn start_time_code(&self) -> Option<f64> {
        match self.get(sdf::FieldKey::StartTimeCode.as_str())? {
            sdf::Value::Double(v) => Some(*v),
            _ => None,
        }
    }

    /// Layer end time code.
    pub fn end_time_code(&self) -> Option<f64> {
        match self.get(sdf::FieldKey::EndTimeCode.as_str())? {
            sdf::Value::Double(v) => Some(*v),
            _ => None,
        }
    }

    /// Time codes per second.
    pub fn time_codes_per_second(&self) -> Option<f64> {
        match self.get(sdf::FieldKey::TimeCodesPerSecond.as_str())? {
            sdf::Value::Double(v) => Some(*v),
            _ => None,
        }
    }

    /// Frames per second.
    pub fn frames_per_second(&self) -> Option<f64> {
        match self.get(sdf::FieldKey::FramesPerSecond.as_str())? {
            sdf::Value::Double(v) => Some(*v),
            _ => None,
        }
    }

    /// Names of root prims in declared order.
    pub fn prim_children(&self) -> Option<&[String]> {
        match self.get(sdf::ChildrenKey::PrimChildren.as_str())? {
            sdf::Value::TokenVec(v) => Some(v.as_slice()),
            _ => None,
        }
    }
}

impl<'a, B> PseudoRootSpec<'a, B>
where
    B: DerefMut<Target = Spec>,
{
    /// Set the `defaultPrim` token without validation.
    ///
    /// This spec-tier setter writes whatever token it is given. The
    /// validating front door is [`crate::sdf::Layer::set_default_prim`],
    /// which rejects malformed values; use this method when you need to
    /// bypass that check (e.g. round-tripping spec data verbatim).
    pub fn set_default_prim(&mut self, name: impl Into<String>) {
        self.add(sdf::FieldKey::DefaultPrim, sdf::Value::Token(name.into()));
    }

    /// Replace the sublayer list with the given asset paths.
    pub fn set_sublayers<I, S>(&mut self, paths: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let paths: Vec<String> = paths.into_iter().map(Into::into).collect();
        self.add(sdf::FieldKey::SubLayers, sdf::Value::StringVec(paths));
    }

    /// Append a sublayer asset path. Duplicate entries are preserved because
    /// USD layer offsets and strength ordering make repeated sublayer arcs
    /// meaningful. Always writes the field as `sdf::Value::StringVec` so the
    /// USDA/USDC writers emit it (they match `StringVec` only); a
    /// pre-existing `TokenVec` is migrated in place.
    pub fn add_sublayer(&mut self, path: impl Into<String>) {
        let path = path.into();
        let mut paths: Vec<String> = match self.remove(sdf::FieldKey::SubLayers.as_str()) {
            Some(sdf::Value::StringVec(v)) | Some(sdf::Value::TokenVec(v)) => v,
            _ => Vec::new(),
        };
        paths.push(path);
        self.add(sdf::FieldKey::SubLayers, sdf::Value::StringVec(paths));
    }

    /// Set the layer documentation string.
    pub fn set_documentation(&mut self, doc: impl Into<String>) {
        self.add(sdf::FieldKey::Documentation, sdf::Value::String(doc.into()));
    }

    /// Set the layer start time code.
    pub fn set_start_time_code(&mut self, time: f64) {
        self.add(sdf::FieldKey::StartTimeCode, sdf::Value::Double(time));
    }

    /// Set the layer end time code.
    pub fn set_end_time_code(&mut self, time: f64) {
        self.add(sdf::FieldKey::EndTimeCode, sdf::Value::Double(time));
    }

    /// Set the time codes per second.
    pub fn set_time_codes_per_second(&mut self, rate: f64) {
        self.add(sdf::FieldKey::TimeCodesPerSecond, sdf::Value::Double(rate));
    }

    /// Set the frames per second.
    pub fn set_frames_per_second(&mut self, rate: f64) {
        self.add(sdf::FieldKey::FramesPerSecond, sdf::Value::Double(rate));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prim_mut_reads() {
        let mut spec = Spec::new(sdf::SpecType::Prim);
        let mut prim = spec.as_prim_mut().expect("prim spec");

        prim.set_type_name("Xform");
        prim.set_specifier(sdf::Specifier::Def);

        assert_eq!(prim.type_name(), Some("Xform"));
        assert_eq!(prim.specifier(), Some(sdf::Specifier::Def));
    }

    #[test]
    fn add_api_schema_prepends() -> Result<(), SpecError> {
        let mut spec = Spec::new(sdf::SpecType::Prim);
        let mut prim = spec.as_prim_mut().expect("prim spec");

        assert!(prim.add_applied_schema("MaterialBindingAPI")?);
        assert!(prim.add_applied_schema("SkelBindingAPI")?);
        assert!(!prim.add_applied_schema("MaterialBindingAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert!(!op.explicit);
        assert_eq!(
            op.prepended_items,
            vec!["MaterialBindingAPI".to_string(), "SkelBindingAPI".to_string()]
        );
        Ok(())
    }

    #[test]
    fn add_connection_path_dedups() {
        let mut spec = Spec::new(sdf::SpecType::Attribute);
        let mut attr = spec.as_attr_mut().expect("attr spec");
        let path = sdf::Path::new("/A.out").expect("path");

        assert!(attr.add_connection_path(path.clone(), false));
        // Duplicate — must not mutate, must not trip the change tracker.
        assert!(!attr.add_connection_path(path, false));
    }

    #[test]
    fn clear_connection_paths_noop() {
        let mut spec = Spec::new(sdf::SpecType::Attribute);
        let mut attr = spec.as_attr_mut().expect("attr spec");

        // Nothing authored — clear is a no-op.
        assert!(!attr.clear_connection_paths());

        attr.add_connection_path(sdf::Path::new("/A.out").expect("path"), false);
        assert!(attr.clear_connection_paths());
        assert!(!attr.clear_connection_paths());
    }

    #[test]
    fn add_api_schema_explicit() -> Result<(), SpecError> {
        let mut spec = Spec::new(sdf::SpecType::Prim);
        spec.add(
            sdf::FieldKey::ApiSchemas,
            sdf::Value::TokenListOp(sdf::TokenListOp::explicit(["ExistingAPI".to_string()])),
        );
        let mut prim = spec.as_prim_mut().expect("prim spec");

        assert!(prim.add_applied_schema("NewAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert!(op.explicit);
        assert_eq!(op.explicit_items, vec!["ExistingAPI".to_string(), "NewAPI".to_string()]);
        Ok(())
    }

    #[test]
    fn add_api_schema_keeps_add() -> Result<(), SpecError> {
        let mut spec = Spec::new(sdf::SpecType::Prim);
        spec.add(
            sdf::FieldKey::ApiSchemas,
            sdf::Value::TokenListOp(sdf::TokenListOp {
                added_items: vec!["ExistingAPI".to_string()],
                ..Default::default()
            }),
        );
        let mut prim = spec.as_prim_mut().expect("prim spec");

        assert!(!prim.add_applied_schema("ExistingAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert_eq!(op.added_items, vec!["ExistingAPI".to_string()]);
        assert!(op.prepended_items.is_empty());
        Ok(())
    }

    #[test]
    fn add_api_schema_clears_delete() -> Result<(), SpecError> {
        let mut spec = Spec::new(sdf::SpecType::Prim);
        spec.add(
            sdf::FieldKey::ApiSchemas,
            sdf::Value::TokenListOp(sdf::TokenListOp {
                deleted_items: vec!["RemovedAPI".to_string()],
                ..Default::default()
            }),
        );
        let mut prim = spec.as_prim_mut().expect("prim spec");

        assert!(prim.add_applied_schema("RemovedAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert_eq!(op.prepended_items, vec!["RemovedAPI".to_string()]);
        assert!(op.deleted_items.is_empty());
        Ok(())
    }

    /// Explicit op with the name lingering in (irrelevant) `added_items`:
    /// already_applied stays false, so the schema lands in `explicit_items`.
    #[test]
    fn add_api_schema_stale_added() -> Result<(), SpecError> {
        let mut spec = Spec::new(sdf::SpecType::Prim);
        spec.add(
            sdf::FieldKey::ApiSchemas,
            sdf::Value::TokenListOp(sdf::TokenListOp {
                explicit: true,
                added_items: vec!["StaleAPI".to_string()],
                ..Default::default()
            }),
        );
        let mut prim = spec.as_prim_mut().expect("prim spec");

        assert!(prim.add_applied_schema("StaleAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert!(op.explicit);
        assert_eq!(op.explicit_items, vec!["StaleAPI".to_string()]);
        Ok(())
    }

    /// A delete listing the same name twice is fully cleared (not just the
    /// first occurrence).
    #[test]
    fn add_api_schema_dup_delete() -> Result<(), SpecError> {
        let mut spec = Spec::new(sdf::SpecType::Prim);
        spec.add(
            sdf::FieldKey::ApiSchemas,
            sdf::Value::TokenListOp(sdf::TokenListOp {
                deleted_items: vec!["RemovedAPI".to_string(), "RemovedAPI".to_string()],
                ..Default::default()
            }),
        );
        let mut prim = spec.as_prim_mut().expect("prim spec");

        assert!(prim.add_applied_schema("RemovedAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert!(op.deleted_items.is_empty());
        assert_eq!(op.prepended_items, vec!["RemovedAPI".to_string()]);
        Ok(())
    }

    #[test]
    fn add_api_schema_rejects_wrong_type() {
        let mut spec = Spec::new(sdf::SpecType::Prim);
        spec.add(
            sdf::FieldKey::ApiSchemas,
            sdf::Value::TokenVec(vec!["ExistingAPI".to_string()]),
        );
        let mut prim = spec.as_prim_mut().expect("prim spec");

        assert!(matches!(
            prim.add_applied_schema("NewAPI"),
            Err(SpecError::FieldType {
                field: "apiSchemas",
                expected: "sdf::TokenListOp"
            })
        ));
    }

    #[test]
    fn attribute_mut_reads() {
        let mut spec = Spec::new(sdf::SpecType::Attribute);
        let mut attr = spec.as_attr_mut().expect("attribute spec");

        attr.set_default(sdf::Value::Int(42));
        attr.set_custom(true);

        assert_eq!(attr.default(), Some(&sdf::Value::Int(42)));
        assert!(attr.is_custom());
    }

    #[test]
    fn relationship_mut_reads() {
        let mut spec = Spec::new(sdf::SpecType::Relationship);
        let mut rel = spec.as_relationship_mut().expect("relationship spec");
        let target = sdf::Path::new("/Target").expect("valid path");

        rel.add_target(target.clone());

        assert_eq!(rel.target_path_list().and_then(|op| op.iter().next()), Some(&target));
    }

    #[test]
    fn pseudo_root_mut_reads() {
        let mut spec = Spec::new(sdf::SpecType::PseudoRoot);
        let mut root = spec.as_pseudo_root_mut().expect("pseudo-root spec");

        root.set_default_prim("World");

        assert_eq!(root.default_prim(), Some("World"));
    }
}
