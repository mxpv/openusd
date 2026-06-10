//! Spec handles over the [`sdf::AbstractData`] field API, plus the [`SpecData`]
//! storage record they read and write.
//!
//! [`SpecData`] is the per-path storage record — a spec type plus its fields in
//! authored order — that the in-memory [`Data`](crate::sdf::Data) backend keeps
//! (the analogue of C++ `SdfData`'s private `_SpecData`). The typed views are
//! something else entirely: thin handles holding `(data, path)` whose accessors
//! read and write through [`sdf::AbstractData::try_field`] / [`sdf::AbstractData::set_field`],
//! exactly like C++ `SdfSpec` and its subclasses, which hold `(layer, path)` and
//! carry no copy. Because they go through the abstract interface, a view works
//! on any backend, not just `Data`.
//!
//! The hierarchy mirrors C++ (`SdfSpec` → `SdfPropertySpec` → `SdfAttributeSpec`
//! / `SdfRelationshipSpec`):
//!
//! ```text
//! Spec ── PrimSpec
//!     ├── PseudoRootSpec
//!     └── PropertySpec ── AttributeSpec
//!                     └── RelationshipSpec
//! ```
//!
//! Each typed view newtype-wraps the one above it and uses `Deref`/`DerefMut`
//! so the base accessors are reachable. A view is generic over its borrow `B`
//! — `&'a dyn sdf::AbstractData` for reads (the default) or `&'a mut dyn sdf::AbstractData`
//! for writes (the `*Mut` aliases) — so one type serves both modes while the
//! generic stays out of the public surface.
//!
//! The primary entry points are the path-keyed methods on
//! [`Layer`](crate::sdf::Layer) (e.g. `Layer::create_prim`, `Layer::prim`),
//! which return these views and handle the write-side bookkeeping
//! (`primChildren` / `propertyChildren` ordering, ancestor specifiers).

use std::fmt;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use strum::{Display, EnumCount, FromRepr};

use crate::sdf;
use crate::tf;

/// An enum that specifies the type of an object.
/// Objects are entities that have fields and are addressable by path.
#[repr(u32)]
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, FromRepr, EnumCount, Display)]
pub enum SpecType {
    // The unknown type has a value of 0 so that SdfSpecType() is unknown.
    #[default]
    Unknown = 0,

    // Real concrete types
    Attribute = 1,
    Connection = 2,
    Expression = 3,
    Mapper = 4,
    MapperArg = 5,
    Prim = 6,
    PseudoRoot = 7,
    Relationship = 8,
    RelationshipTarget = 9,
    Variant = 10,
    VariantSet = 11,
}

/// Implements `Debug` for a spec-handle newtype by delegating to its inner
/// handle, so the data reference it holds is not required to be `Debug`.
macro_rules! impl_spec_debug {
    ($($ty:ident),+ $(,)?) => {$(
        impl<'a, B: Deref<Target = dyn sdf::AbstractData + 'a>> fmt::Debug for $ty<'a, B> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(&self.0, f)
            }
        }
    )+};
}

/// Per-path storage record kept by the in-memory [`Data`](crate::sdf::Data)
/// backend: a [`SpecType`](sdf::SpecType) plus the spec's fields in authored
/// order. The analogue of C++ `SdfData`'s private `_SpecData`.
///
/// This is backend storage, distinct from the [`Spec`] handle that reads and
/// writes it through the [`sdf::AbstractData`] interface. Fields are stored in
/// authored order, which is required for faithful text round-tripping.
#[derive(Debug, Clone)]
pub struct SpecData {
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

impl SpecData {
    /// Creates a new empty spec record of the given type.
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

    /// Adds a list-op field value, folding it into any existing list op of the
    /// same variant already on the spec so multiple operator statements
    /// (`prepend`/`append`/`add`/`delete`/`reorder`) for one field accumulate
    /// rather than overwrite (C++ Sdf stores one `SdfListOp` per field). A
    /// non-list-op `value`, or one of a different variant, replaces as usual.
    pub fn add_list_op(&mut self, key: impl AsRef<str>, value: sdf::Value) {
        let key = key.as_ref();
        let Some(slot) = self.get_mut(key) else {
            self.add(key, value);
            return;
        };
        use sdf::Value::*;
        match (slot, value) {
            (TokenListOp(existing), TokenListOp(incoming)) => existing.merge_op(incoming),
            (StringListOp(existing), StringListOp(incoming)) => existing.merge_op(incoming),
            (PathListOp(existing), PathListOp(incoming)) => existing.merge_op(incoming),
            (ReferenceListOp(existing), ReferenceListOp(incoming)) => existing.merge_op(incoming),
            (PayloadListOp(existing), PayloadListOp(incoming)) => existing.merge_op(incoming),
            (IntListOp(existing), IntListOp(incoming)) => existing.merge_op(incoming),
            (Int64ListOp(existing), Int64ListOp(incoming)) => existing.merge_op(incoming),
            (UIntListOp(existing), UIntListOp(incoming)) => existing.merge_op(incoming),
            (UInt64ListOp(existing), UInt64ListOp(incoming)) => existing.merge_op(incoming),
            (UnregisteredValueListOp(existing), UnregisteredValueListOp(incoming)) => existing.merge_op(incoming),
            (slot, value) => *slot = value,
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
    pub fn extend_from(&mut self, other: SpecData) {
        for (k, v) in other.fields {
            self.add(k, v);
        }
    }
}

/// Base spec handle — a `(data, path)` reference into an [`sdf::AbstractData`],
/// paralleling C++ `SdfSpec`. Field accessors read and write through the
/// abstract interface; the handle holds no copy of the spec.
///
/// `B` is the borrow: `&'a dyn sdf::AbstractData` for reads (the default) or
/// `&'a mut dyn sdf::AbstractData` for writes ([`SpecMut`]). The typed views
/// ([`PrimSpec`], [`AttributeSpec`], …) wrap this and reach its accessors
/// through `Deref`.
pub struct Spec<'a, B> {
    data: B,
    path: sdf::Path,
    _marker: PhantomData<&'a ()>,
}

impl<'a, B: Deref<Target = dyn sdf::AbstractData + 'a>> fmt::Debug for Spec<'a, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Spec")
            .field("path", &self.path)
            .field("type", &self.spec_type())
            .finish()
    }
}

impl_spec_debug!(PrimSpec, PseudoRootSpec, PropertySpec, AttributeSpec, RelationshipSpec);

/// A read-only base spec handle (`Spec` over a shared borrow).
pub type SpecRef<'a> = Spec<'a, &'a dyn sdf::AbstractData>;

/// A mutable base spec handle (`Spec` over an exclusive borrow).
pub type SpecMut<'a> = Spec<'a, &'a mut dyn sdf::AbstractData>;

impl<'a, B> Spec<'a, B> {
    pub(crate) fn wrap(data: B, path: sdf::Path) -> Self {
        Self {
            data,
            path,
            _marker: PhantomData,
        }
    }
}

impl<'a, B> Spec<'a, B>
where
    B: Deref<Target = dyn sdf::AbstractData + 'a>,
{
    /// The path this handle refers to.
    pub fn path(&self) -> &sdf::Path {
        &self.path
    }

    /// The type of the spec at this path, if any.
    pub fn spec_type(&self) -> Option<sdf::SpecType> {
        self.data.spec_type(&self.path)
    }

    /// Reads `key` as an owned value, propagating a decode failure. `Ok(None)`
    /// means the field (or spec) is unauthored; `Err` means a present field
    /// could not be decoded. Read accessors swallow the error via
    /// [`get`](Self::get); read-modify-write authoring keeps it so an
    /// undecodable field is not mistaken for "absent" and overwritten.
    pub fn field(&self, key: &str) -> anyhow::Result<Option<sdf::Value>> {
        Ok(self.data.try_field(&self.path, key)?.map(|c| c.into_owned()))
    }

    /// Reads `key` as `T`, treating a missing field, a decode failure, and a
    /// type mismatch all as `None`. The typed read accessor; `T = sdf::Value`
    /// returns the raw value. Read-modify-write authoring uses
    /// [`field`](Self::field) instead, which keeps the decode error so an
    /// undecodable field is never mistaken for absent and overwritten.
    pub fn get<T: TryFrom<sdf::Value>>(&self, key: impl AsRef<str>) -> Option<T> {
        self.field(key.as_ref()).ok().flatten()?.get()
    }

    /// Whether `key` is authored on this spec.
    pub fn has_field(&self, key: &str) -> bool {
        self.data.has_field(&self.path, key)
    }

    /// The authored field names on this spec, in authored order.
    pub fn fields(&self) -> Vec<String> {
        self.data.list_fields(&self.path).unwrap_or_default()
    }
}

impl<'a, B> Spec<'a, B>
where
    B: DerefMut<Target = dyn sdf::AbstractData + 'a>,
{
    /// Sets (or replaces) `key`.
    pub fn set(&mut self, key: impl AsRef<str>, value: impl Into<sdf::Value>) {
        self.data.set_field(&self.path, key.as_ref(), value.into());
    }

    /// Removes `key` if authored.
    pub fn erase(&mut self, key: &str) {
        self.data.erase_field(&self.path, key);
    }
}

/// Typed view of a prim spec. Parallel to C++ `SdfPrimSpec`.
///
/// Read-only over a shared borrow. [`PrimSpecMut`] aliases this same
/// handle with an exclusive borrow, so it has both read and write methods.
#[derive(derive_more::Deref, derive_more::DerefMut)]
pub struct PrimSpec<'a, B>(Spec<'a, B>);

/// Read-only typed view of a prim spec.
pub type PrimSpecRef<'a> = PrimSpec<'a, &'a dyn sdf::AbstractData>;

/// Mutable typed view of a prim spec. Parallel to C++ `SdfPrimSpec`.
pub type PrimSpecMut<'a> = PrimSpec<'a, &'a mut dyn sdf::AbstractData>;

impl<'a> PrimSpecRef<'a> {
    /// Returns a read-only view of the prim spec at `path`, or `None` if no
    /// prim spec exists there.
    pub(crate) fn get(data: &'a dyn sdf::AbstractData, path: sdf::Path) -> Option<Self> {
        matches!(data.spec_type(&path), Some(sdf::SpecType::Prim)).then(|| Self(Spec::wrap(data, path)))
    }
}

impl<'a> PrimSpecMut<'a> {
    /// Returns a mutable view of the prim spec at `path`, or `None` if no prim
    /// spec exists there.
    pub(crate) fn get(data: &'a mut dyn sdf::AbstractData, path: sdf::Path) -> Option<Self> {
        matches!(data.spec_type(&path), Some(sdf::SpecType::Prim)).then(|| Self(Spec::wrap(data, path)))
    }
}

impl<'a, B> PrimSpec<'a, B>
where
    B: Deref<Target = dyn sdf::AbstractData + 'a>,
{
    /// Authored `typeName` (e.g. `"Xform"`, `"Mesh"`). `None` if unset.
    pub fn type_name(&self) -> Option<tf::Token> {
        self.get(sdf::FieldKey::TypeName)
    }

    /// Authored `specifier` (`def`, `over`, `class`). `None` if unset.
    pub fn specifier(&self) -> Option<sdf::Specifier> {
        self.get(sdf::FieldKey::Specifier)
    }

    /// Authored `kind` metadata (e.g. `"component"`, `"group"`).
    pub fn kind(&self) -> Option<tf::Token> {
        self.get(sdf::FieldKey::Kind)
    }

    /// Authored `active` flag. `None` if unset (USD defaults to active).
    pub fn is_active(&self) -> Option<bool> {
        self.get(sdf::FieldKey::Active)
    }

    /// Authored `hidden` flag.
    pub fn is_hidden(&self) -> Option<bool> {
        self.get(sdf::FieldKey::Hidden)
    }

    /// Authored `instanceable` flag.
    pub fn is_instanceable(&self) -> Option<bool> {
        self.get(sdf::FieldKey::Instanceable)
    }

    /// Names of child prims, in declared order. `None` if unset.
    pub fn prim_children(&self) -> Option<Vec<tf::Token>> {
        self.get(sdf::ChildrenKey::PrimChildren)
    }

    /// Names of child properties, in declared order. `None` if unset.
    pub fn property_children(&self) -> Option<Vec<tf::Token>> {
        self.get(sdf::ChildrenKey::PropertyChildren)
    }

    /// Authored `apiSchemas` list op, if present.
    pub fn api_schemas(&self) -> Option<sdf::TokenListOp> {
        self.get(sdf::FieldKey::ApiSchemas)
    }
}

impl<'a, B> PrimSpec<'a, B>
where
    B: DerefMut<Target = dyn sdf::AbstractData + 'a>,
{
    /// Set the `typeName` field. An empty `name` clears the field instead
    /// of authoring `sdf::Value::Token("")` — matching the empty-string skip in
    /// [`crate::sdf::Layer::create_prim`] so the two write paths stay in
    /// lockstep.
    pub fn set_type_name(&mut self, name: impl Into<tf::Token>) {
        let name = name.into();
        if name.is_empty() {
            self.erase(sdf::FieldKey::TypeName.as_str());
        } else {
            self.set(sdf::FieldKey::TypeName.as_str(), sdf::Value::Token(name));
        }
    }

    /// Set the `specifier` field.
    pub fn set_specifier(&mut self, specifier: sdf::Specifier) {
        self.set(sdf::FieldKey::Specifier.as_str(), sdf::Value::Specifier(specifier));
    }

    /// Set the `kind` metadata.
    pub fn set_kind(&mut self, kind: impl Into<tf::Token>) {
        self.set(sdf::FieldKey::Kind.as_str(), sdf::Value::token(kind));
    }

    /// Set the `active` flag.
    pub fn set_active(&mut self, active: bool) {
        self.set(sdf::FieldKey::Active.as_str(), sdf::Value::Bool(active));
    }

    /// Set the `hidden` flag.
    pub fn set_hidden(&mut self, hidden: bool) {
        self.set(sdf::FieldKey::Hidden.as_str(), sdf::Value::Bool(hidden));
    }

    /// Set the `instanceable` flag.
    pub fn set_instanceable(&mut self, instanceable: bool) {
        self.set(sdf::FieldKey::Instanceable.as_str(), sdf::Value::Bool(instanceable));
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
        let name: tf::Token = name.into().into();
        // An undecodable `apiSchemas` must not be silently overwritten.
        let Ok(existing) = self.field(sdf::FieldKey::ApiSchemas.as_str()) else {
            return Ok(false);
        };
        match existing {
            Some(sdf::Value::TokenListOp(mut op)) => {
                let changed = add_applied_schema_to_list_op(&mut op, name);
                self.set(sdf::FieldKey::ApiSchemas.as_str(), sdf::Value::TokenListOp(op));
                Ok(changed)
            }
            Some(_) => Err(SpecError::FieldType {
                field: sdf::FieldKey::ApiSchemas.as_str(),
                expected: "sdf::TokenListOp",
            }),
            None => {
                self.set(
                    sdf::FieldKey::ApiSchemas.as_str(),
                    sdf::Value::TokenListOp(sdf::TokenListOp::prepended([name])),
                );
                Ok(true)
            }
        }
    }
}

fn add_applied_schema_to_list_op(op: &mut sdf::TokenListOp, name: tf::Token) -> bool {
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

/// Typed view of the layer's root pseudo-spec. Parallel to C++
/// `SdfPseudoRootSpec`; carries layer-wide metadata (`defaultPrim`,
/// `subLayers`, time codes, etc.).
///
/// Read-only over a shared borrow. [`PseudoRootSpecMut`] aliases this
/// same handle with an exclusive borrow, so it has both read and write methods.
#[derive(derive_more::Deref, derive_more::DerefMut)]
pub struct PseudoRootSpec<'a, B>(Spec<'a, B>);

/// Read-only typed view of the layer's root pseudo-spec.
pub type PseudoRootSpecRef<'a> = PseudoRootSpec<'a, &'a dyn sdf::AbstractData>;

/// Mutable typed view of the layer's root pseudo-spec. Parallel to C++ `SdfPseudoRootSpec`.
pub type PseudoRootSpecMut<'a> = PseudoRootSpec<'a, &'a mut dyn sdf::AbstractData>;

impl<'a> PseudoRootSpecRef<'a> {
    /// Returns a read-only view of the pseudo-root spec, or `None` if the
    /// layer has no pseudo-root spec.
    pub(crate) fn get(data: &'a dyn sdf::AbstractData) -> Option<Self> {
        let path = sdf::Path::abs_root();
        matches!(data.spec_type(&path), Some(sdf::SpecType::PseudoRoot)).then(|| Self(Spec::wrap(data, path)))
    }
}

impl<'a> PseudoRootSpecMut<'a> {
    /// Returns a mutable view of the pseudo-root spec, or `None` if the layer
    /// has no pseudo-root spec.
    pub(crate) fn get(data: &'a mut dyn sdf::AbstractData) -> Option<Self> {
        let path = sdf::Path::abs_root();
        matches!(data.spec_type(&path), Some(sdf::SpecType::PseudoRoot)).then(|| Self(Spec::wrap(data, path)))
    }
}

impl<'a, B> PseudoRootSpec<'a, B>
where
    B: Deref<Target = dyn sdf::AbstractData + 'a>,
{
    /// `defaultPrim` token, if authored.
    pub fn default_prim(&self) -> Option<tf::Token> {
        self.get(sdf::FieldKey::DefaultPrim)
    }

    /// Sublayer asset paths in strength order (strongest first).
    pub fn sublayers(&self) -> Option<Vec<String>> {
        self.get(sdf::FieldKey::SubLayers)
    }

    /// Namespace relocations authored in this layer's metadata.
    pub fn relocates(&self) -> Option<sdf::RelocateList> {
        self.get(sdf::FieldKey::LayerRelocates)
    }

    /// Layer documentation string.
    pub fn documentation(&self) -> Option<String> {
        self.get(sdf::FieldKey::Documentation)
    }

    /// Layer start time code.
    pub fn start_time_code(&self) -> Option<f64> {
        self.get(sdf::FieldKey::StartTimeCode)
    }

    /// Layer end time code.
    pub fn end_time_code(&self) -> Option<f64> {
        self.get(sdf::FieldKey::EndTimeCode)
    }

    /// Time codes per second.
    pub fn time_codes_per_second(&self) -> Option<f64> {
        self.get(sdf::FieldKey::TimeCodesPerSecond)
    }

    /// Frames per second.
    pub fn frames_per_second(&self) -> Option<f64> {
        self.get(sdf::FieldKey::FramesPerSecond)
    }

    /// Names of root prims in declared order.
    pub fn prim_children(&self) -> Option<Vec<tf::Token>> {
        self.get(sdf::ChildrenKey::PrimChildren)
    }
}

impl<'a, B> PseudoRootSpec<'a, B>
where
    B: DerefMut<Target = dyn sdf::AbstractData + 'a>,
{
    /// Set the `defaultPrim` token without validation.
    ///
    /// This spec-tier setter writes whatever token it is given. The
    /// validating front door is [`crate::sdf::Layer::set_default_prim`],
    /// which rejects malformed values; use this method when you need to
    /// bypass that check (e.g. round-tripping spec data verbatim).
    pub fn set_default_prim(&mut self, name: impl Into<tf::Token>) {
        self.set(sdf::FieldKey::DefaultPrim.as_str(), sdf::Value::token(name));
    }

    /// Replace the sublayer list with the given asset paths.
    pub fn set_sublayers<I, S>(&mut self, paths: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let paths: Vec<String> = paths.into_iter().map(Into::into).collect();
        self.set(sdf::FieldKey::SubLayers.as_str(), sdf::Value::StringVec(paths));
    }

    /// Replace this layer's namespace relocations with `relocates`.
    pub fn set_relocates(&mut self, relocates: sdf::RelocateList) {
        self.set(sdf::FieldKey::LayerRelocates.as_str(), sdf::Value::Relocates(relocates));
    }

    /// Append a sublayer asset path. Duplicate entries are preserved because
    /// USD layer offsets and strength ordering make repeated sublayer arcs
    /// meaningful. Always writes the field as `sdf::Value::StringVec` so the
    /// USDA/USDC writers emit it (they match `StringVec` only).
    pub fn add_sublayer(&mut self, path: impl Into<String>) {
        let path = path.into();
        let mut paths = self.sublayer_paths().unwrap_or_default();
        paths.push(path);
        self.set(sdf::FieldKey::SubLayers.as_str(), sdf::Value::StringVec(paths));
    }

    /// Insert a sublayer asset path and its layer offset at `pos` (clamped to
    /// the current sublayer count), keeping `subLayers` and `subLayerOffsets`
    /// index-aligned. A shorter `subLayerOffsets` is padded with
    /// [`LayerOffset::IDENTITY`](sdf::LayerOffset::IDENTITY) so the offset at
    /// every position matches its sublayer. Writes `subLayers` as
    /// `sdf::Value::StringVec` so the USDA/USDC writers emit it.
    pub fn insert_sublayer(&mut self, pos: usize, path: impl Into<String>, offset: sdf::LayerOffset) {
        let mut paths = self.sublayer_paths().unwrap_or_default();
        let mut offsets = self.sublayer_offsets(paths.len());
        let pos = pos.min(paths.len());
        paths.insert(pos, path.into());
        offsets.insert(pos, offset);
        self.set(sdf::FieldKey::SubLayers.as_str(), sdf::Value::StringVec(paths));
        self.set(
            sdf::FieldKey::SubLayerOffsets.as_str(),
            sdf::Value::LayerOffsetVec(offsets),
        );
    }

    /// Remove the first `subLayers` entry matching `path` and its aligned
    /// `subLayerOffsets` entry, returning whether anything was removed.
    pub fn remove_sublayer(&mut self, path: &str) -> bool {
        let Some(mut paths) = self.sublayer_paths() else {
            return false;
        };
        let Some(idx) = paths.iter().position(|p| p == path) else {
            return false;
        };
        let mut offsets = self.sublayer_offsets(paths.len());
        paths.remove(idx);
        offsets.remove(idx);
        self.set(sdf::FieldKey::SubLayers.as_str(), sdf::Value::StringVec(paths));
        self.set(
            sdf::FieldKey::SubLayerOffsets.as_str(),
            sdf::Value::LayerOffsetVec(offsets),
        );
        true
    }

    /// Reads and decodes the `subLayers` field (a `StringVec` of asset-path
    /// strings). `None` when unauthored or stored with an unexpected value type.
    /// Read-only: every caller rewrites the field with its own `set`, so this
    /// must not erase it (an erase-then-bail would drop a malformed value).
    fn sublayer_paths(&self) -> Option<Vec<String>> {
        self.get(sdf::FieldKey::SubLayers)
    }

    /// Reads and decodes the `subLayerOffsets` field, padded to `len` with
    /// [`LayerOffset::IDENTITY`](sdf::LayerOffset::IDENTITY) so it stays
    /// index-aligned with the sublayer paths.
    fn sublayer_offsets(&self, len: usize) -> Vec<sdf::LayerOffset> {
        let mut offsets = self
            .get::<Vec<sdf::LayerOffset>>(sdf::FieldKey::SubLayerOffsets)
            .unwrap_or_default();
        offsets.resize(len, sdf::LayerOffset::IDENTITY);
        offsets
    }

    /// Set the layer documentation string.
    pub fn set_documentation(&mut self, doc: impl Into<String>) {
        self.set(sdf::FieldKey::Documentation.as_str(), sdf::Value::String(doc.into()));
    }

    /// Set the layer start time code.
    pub fn set_start_time_code(&mut self, time: f64) {
        self.set(sdf::FieldKey::StartTimeCode.as_str(), sdf::Value::Double(time));
    }

    /// Set the layer end time code.
    pub fn set_end_time_code(&mut self, time: f64) {
        self.set(sdf::FieldKey::EndTimeCode.as_str(), sdf::Value::Double(time));
    }

    /// Set the time codes per second.
    pub fn set_time_codes_per_second(&mut self, rate: f64) {
        self.set(sdf::FieldKey::TimeCodesPerSecond.as_str(), sdf::Value::Double(rate));
    }

    /// Set the frames per second.
    pub fn set_frames_per_second(&mut self, rate: f64) {
        self.set(sdf::FieldKey::FramesPerSecond.as_str(), sdf::Value::Double(rate));
    }
}

/// Typed view shared by attributes and relationships. Parallel to C++
/// `SdfPropertySpec`; carries the `variability` / `custom` metadata common to
/// both property kinds.
///
/// [`AttributeSpec`] and [`RelationshipSpec`] wrap this, so its accessors are
/// reachable on them through `Deref`.
#[derive(derive_more::Deref, derive_more::DerefMut)]
pub struct PropertySpec<'a, B>(Spec<'a, B>);

/// Read-only typed view of a property spec.
pub type PropertySpecRef<'a> = PropertySpec<'a, &'a dyn sdf::AbstractData>;

/// Mutable typed view of a property spec. Parallel to C++ `SdfPropertySpec`.
pub type PropertySpecMut<'a> = PropertySpec<'a, &'a mut dyn sdf::AbstractData>;

impl<'a, B> PropertySpec<'a, B>
where
    B: Deref<Target = dyn sdf::AbstractData + 'a>,
{
    /// Property variability. Defaults to [`sdf::Variability::Varying`] if unset.
    pub fn variability(&self) -> sdf::Variability {
        self.get(sdf::FieldKey::Variability)
            .unwrap_or(sdf::Variability::Varying)
    }

    /// Whether the property is `custom`. Defaults to `false` if unset.
    pub fn is_custom(&self) -> bool {
        self.get(sdf::FieldKey::Custom).unwrap_or(false)
    }
}

impl<'a, B> PropertySpec<'a, B>
where
    B: DerefMut<Target = dyn sdf::AbstractData + 'a>,
{
    /// Set the `custom` flag.
    pub fn set_custom(&mut self, custom: bool) {
        self.set(sdf::FieldKey::Custom.as_str(), sdf::Value::Bool(custom));
    }
}

/// Typed view of an attribute spec. Parallel to C++ `SdfAttributeSpec`
/// (a `SdfPropertySpec`).
///
/// Read-only over a shared borrow. [`AttributeSpecMut`] aliases this
/// same handle with an exclusive borrow, so it has both read and write methods.
#[derive(derive_more::Deref, derive_more::DerefMut)]
pub struct AttributeSpec<'a, B>(PropertySpec<'a, B>);

/// Read-only typed view of an attribute spec.
pub type AttributeSpecRef<'a> = AttributeSpec<'a, &'a dyn sdf::AbstractData>;

/// Mutable typed view of an attribute spec. Parallel to C++ `SdfAttributeSpec`.
pub type AttributeSpecMut<'a> = AttributeSpec<'a, &'a mut dyn sdf::AbstractData>;

impl<'a> AttributeSpecRef<'a> {
    /// Returns a read-only view of the attribute spec at `path`, or `None` if
    /// no attribute spec exists there.
    pub(crate) fn get(data: &'a dyn sdf::AbstractData, path: sdf::Path) -> Option<Self> {
        matches!(data.spec_type(&path), Some(sdf::SpecType::Attribute))
            .then(|| Self(PropertySpec(Spec::wrap(data, path))))
    }
}

impl<'a> AttributeSpecMut<'a> {
    /// Returns a mutable view of the attribute spec at `path`, or `None` if no
    /// attribute spec exists there.
    pub(crate) fn get(data: &'a mut dyn sdf::AbstractData, path: sdf::Path) -> Option<Self> {
        matches!(data.spec_type(&path), Some(sdf::SpecType::Attribute))
            .then(|| Self(PropertySpec(Spec::wrap(data, path))))
    }
}

impl<'a, B> AttributeSpec<'a, B>
where
    B: Deref<Target = dyn sdf::AbstractData + 'a>,
{
    /// Attribute value type name (e.g. `"double"`, `"float3[]"`).
    pub fn type_name(&self) -> Option<tf::Token> {
        self.get(sdf::FieldKey::TypeName)
    }

    /// Default value, if authored.
    pub fn default(&self) -> Option<sdf::Value> {
        self.get(sdf::FieldKey::Default)
    }

    /// Time-sample map, if authored, in storage order. Samples authored
    /// through [`AttributeSpecMut::set_time_sample`] are kept sorted by time;
    /// samples loaded from a parsed layer reflect on-disk ordering.
    pub fn time_samples(&self) -> Option<Vec<(f64, sdf::Value)>> {
        self.get(sdf::FieldKey::TimeSamples)
    }

    /// Color-space token, if authored.
    pub fn color_space(&self) -> Option<tf::Token> {
        self.get(sdf::FieldKey::ColorSpace)
    }

    /// `allowedTokens` array, if authored.
    pub fn allowed_tokens(&self) -> Option<Vec<tf::Token>> {
        self.get(sdf::FieldKey::AllowedTokens)
    }

    /// Authored `connectionPaths` list op, if present.
    pub fn connection_path_list(&self) -> Option<sdf::PathListOp> {
        self.get(sdf::FieldKey::ConnectionPaths)
    }
}

impl<'a, B> AttributeSpec<'a, B>
where
    B: DerefMut<Target = dyn sdf::AbstractData + 'a>,
{
    /// Set the `default` value.
    pub fn set_default(&mut self, value: impl Into<sdf::Value>) {
        self.set(sdf::FieldKey::Default.as_str(), value.into());
    }

    /// Clear any authored `default`.
    pub fn clear_default(&mut self) {
        self.erase(sdf::FieldKey::Default.as_str());
    }

    /// Insert or replace a time sample at `time`. Samples are kept sorted
    /// by time so consumers can binary-search. A pre-existing value of a
    /// non-`TimeSamples` variant is overwritten — debug builds assert.
    pub fn set_time_sample(&mut self, time: f64, value: impl Into<sdf::Value>) {
        let value = value.into();
        // An undecodable `timeSamples` must not be silently overwritten.
        let Ok(existing) = self.field(sdf::FieldKey::TimeSamples.as_str()) else {
            return;
        };
        let mut map = match existing {
            Some(sdf::Value::TimeSamples(map)) => map,
            None => Vec::new(),
            Some(other) => {
                debug_assert!(false, "timeSamples field is not a TimeSamples (got {other:?})");
                Vec::new()
            }
        };
        upsert_time_sample(&mut map, time, value);
        self.set(sdf::FieldKey::TimeSamples.as_str(), sdf::Value::TimeSamples(map));
    }

    /// Erase the time sample at `time`. Returns `true` if a sample was removed.
    /// If this was the last sample, the `timeSamples` field is cleared entirely
    /// so the spec round-trips identically to one that never authored samples.
    pub fn erase_time_sample(&mut self, time: f64) -> bool {
        let Some(mut map) = self.time_samples() else {
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
            self.erase(sdf::FieldKey::TimeSamples.as_str());
        } else {
            self.set(sdf::FieldKey::TimeSamples.as_str(), sdf::Value::TimeSamples(map));
        }
        true
    }

    /// Set the `colorSpace` token.
    pub fn set_color_space(&mut self, color_space: impl Into<tf::Token>) {
        self.set(sdf::FieldKey::ColorSpace.as_str(), sdf::Value::token(color_space));
    }

    /// Set the `allowedTokens` array.
    pub fn set_allowed_tokens<I, S>(&mut self, tokens: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<tf::Token>,
    {
        let tokens: Vec<tf::Token> = tokens.into_iter().map(Into::into).collect();
        self.set(sdf::FieldKey::AllowedTokens.as_str(), sdf::Value::TokenVec(tokens));
    }

    /// Set the `connectionPaths` (explicit list op, replacing any prior).
    pub fn set_connection_paths<I>(&mut self, paths: I)
    where
        I: IntoIterator<Item = sdf::Path>,
    {
        let paths: Vec<sdf::Path> = paths.into_iter().collect();
        self.set(
            sdf::FieldKey::ConnectionPaths.as_str(),
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
        let key = sdf::FieldKey::ConnectionPaths.as_str();
        // An undecodable `connectionPaths` must not be silently overwritten.
        let Ok(existing) = self.field(key) else {
            return false;
        };
        match existing {
            Some(sdf::Value::PathListOp(mut op)) => {
                // Re-adding a previously deleted target must first clear the
                // delete bucket; otherwise the newly authored connection can
                // still be removed during list-op application.
                let mut changed = remove_path(&mut op.deleted_items, &path);
                if op.iter().any(|p| p == &path) {
                    if changed {
                        self.set(key, sdf::Value::PathListOp(op));
                    }
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
                self.set(key, sdf::Value::PathListOp(op));
                changed
            }
            Some(other) => {
                debug_assert!(false, "connectionPaths field is not a sdf::PathListOp (got {other:?})");
                let op = if prepend {
                    sdf::PathListOp::prepended([path])
                } else {
                    sdf::PathListOp::appended([path])
                };
                self.set(key, sdf::Value::PathListOp(op));
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
                self.set(key, sdf::Value::PathListOp(op));
                true
            }
        }
    }

    /// Remove a single connection path. Returns `true` if it was present.
    pub fn remove_connection_path(&mut self, path: &sdf::Path) -> bool {
        let key = sdf::FieldKey::ConnectionPaths.as_str();
        let Some(mut op) = self.get::<sdf::PathListOp>(key) else {
            return false;
        };
        let removed = remove_path(&mut op.explicit_items, path)
            | remove_path(&mut op.added_items, path)
            | remove_path(&mut op.prepended_items, path)
            | remove_path(&mut op.appended_items, path);
        self.set(key, sdf::Value::PathListOp(op));
        removed
    }

    /// Author a removal for a connection path. Local contributions are
    /// stripped first; non-explicit list ops also get a delete opinion so
    /// weaker-layer contributions stay removed in the composed result.
    pub fn delete_connection_path(&mut self, path: &sdf::Path) -> bool {
        let key = sdf::FieldKey::ConnectionPaths.as_str();
        // An undecodable `connectionPaths` must not be silently overwritten.
        let Ok(existing) = self.field(key) else {
            return false;
        };
        match existing {
            Some(sdf::Value::PathListOp(mut op)) => {
                let removed = remove_path(&mut op.explicit_items, path)
                    | remove_path(&mut op.added_items, path)
                    | remove_path(&mut op.prepended_items, path)
                    | remove_path(&mut op.appended_items, path);
                if op.explicit || op.deleted_items.iter().any(|p| p == path) {
                    self.set(key, sdf::Value::PathListOp(op));
                    return removed;
                }
                op.deleted_items.push(path.clone());
                self.set(key, sdf::Value::PathListOp(op));
                true
            }
            Some(other) => {
                debug_assert!(false, "connectionPaths field is not a sdf::PathListOp (got {other:?})");
                self.set(key, sdf::Value::PathListOp(sdf::PathListOp::deleted([path.clone()])));
                true
            }
            None => {
                self.set(key, sdf::Value::PathListOp(sdf::PathListOp::deleted([path.clone()])));
                true
            }
        }
    }

    /// Clear all authored `connectionPaths`. Returns `true` if an
    /// opinion was actually removed.
    pub fn clear_connection_paths(&mut self) -> bool {
        let key = sdf::FieldKey::ConnectionPaths.as_str();
        let present = self.has_field(key);
        if present {
            self.erase(key);
        }
        present
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

/// Typed view of a relationship spec. Parallel to C++ `SdfRelationshipSpec`
/// (a `SdfPropertySpec`).
///
/// Read-only over a shared borrow. [`RelationshipSpecMut`] aliases this
/// same handle with an exclusive borrow, so it has both read and write methods.
#[derive(derive_more::Deref, derive_more::DerefMut)]
pub struct RelationshipSpec<'a, B>(PropertySpec<'a, B>);

/// Read-only typed view of a relationship spec.
pub type RelationshipSpecRef<'a> = RelationshipSpec<'a, &'a dyn sdf::AbstractData>;

/// Mutable typed view of a relationship spec. Parallel to C++ `SdfRelationshipSpec`.
pub type RelationshipSpecMut<'a> = RelationshipSpec<'a, &'a mut dyn sdf::AbstractData>;

impl<'a> RelationshipSpecRef<'a> {
    /// Returns a read-only view of the relationship spec at `path`, or `None`
    /// if no relationship spec exists there.
    pub(crate) fn get(data: &'a dyn sdf::AbstractData, path: sdf::Path) -> Option<Self> {
        matches!(data.spec_type(&path), Some(sdf::SpecType::Relationship))
            .then(|| Self(PropertySpec(Spec::wrap(data, path))))
    }
}

impl<'a> RelationshipSpecMut<'a> {
    /// Returns a mutable view of the relationship spec at `path`, or `None` if
    /// no relationship spec exists there.
    pub(crate) fn get(data: &'a mut dyn sdf::AbstractData, path: sdf::Path) -> Option<Self> {
        matches!(data.spec_type(&path), Some(sdf::SpecType::Relationship))
            .then(|| Self(PropertySpec(Spec::wrap(data, path))))
    }
}

impl<'a, B> RelationshipSpec<'a, B>
where
    B: Deref<Target = dyn sdf::AbstractData + 'a>,
{
    /// Authored `targetPaths` list op, if present.
    pub fn target_path_list(&self) -> Option<sdf::PathListOp> {
        self.get(sdf::FieldKey::TargetPaths)
    }
}

impl<'a, B> RelationshipSpec<'a, B>
where
    B: DerefMut<Target = dyn sdf::AbstractData + 'a>,
{
    /// Replace `targetPaths` with the given list.
    pub fn set_target_paths<I>(&mut self, paths: I)
    where
        I: IntoIterator<Item = sdf::Path>,
    {
        let paths: Vec<sdf::Path> = paths.into_iter().collect();
        self.set(
            sdf::FieldKey::TargetPaths.as_str(),
            sdf::Value::PathListOp(sdf::PathListOp::explicit(paths)),
        );
    }

    /// Append a single target path. No-op if already present. A pre-existing
    /// value of a non-`sdf::PathListOp` variant is overwritten — debug builds assert.
    pub fn add_target(&mut self, path: sdf::Path) {
        let key = sdf::FieldKey::TargetPaths.as_str();
        // An undecodable `targetPaths` must not be silently overwritten.
        let Ok(existing) = self.field(key) else {
            return;
        };
        match existing {
            Some(sdf::Value::PathListOp(mut op)) => {
                if !op.iter().any(|p| p == &path) {
                    if op.explicit {
                        op.explicit_items.push(path);
                    } else {
                        op.added_items.push(path);
                    }
                }
                self.set(key, sdf::Value::PathListOp(op));
            }
            Some(other) => {
                debug_assert!(false, "targetPaths field is not a sdf::PathListOp (got {other:?})");
                self.set(key, sdf::Value::PathListOp(sdf::PathListOp::explicit([path])));
            }
            None => {
                self.set(key, sdf::Value::PathListOp(sdf::PathListOp::explicit([path])));
            }
        }
    }

    /// Remove a single target path, ensuring it is absent from the composed
    /// result rather than only from this layer's opinions (C++
    /// `UsdRelationship::RemoveTarget`). Delegates to [`ListOp::remove`]; when
    /// no targets are authored here yet it records a deletion so the same
    /// target from a weaker layer is suppressed. Returns `true` when an
    /// authored change was made.
    ///
    /// [`ListOp::remove`]: sdf::ListOp::remove
    pub fn remove_target(&mut self, path: &sdf::Path) -> bool {
        let key = sdf::FieldKey::TargetPaths.as_str();
        // An undecodable `targetPaths` must not be silently overwritten.
        let Ok(existing) = self.field(key) else {
            return false;
        };
        match existing {
            Some(sdf::Value::PathListOp(mut op)) => {
                let changed = op.remove(path);
                self.set(key, sdf::Value::PathListOp(op));
                changed
            }
            Some(_) => false,
            None => {
                // No authored targets here yet: record a deletion so the same
                // target from a weaker layer is suppressed through composition.
                self.set(key, sdf::Value::PathListOp(sdf::PathListOp::deleted([path.clone()])));
                true
            }
        }
    }
}

fn remove_path(paths: &mut Vec<sdf::Path>, path: &sdf::Path) -> bool {
    let Some(idx) = paths.iter().position(|p| p == path) else {
        return false;
    };
    paths.remove(idx);
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::{AbstractData, Data};

    /// Builds a [`Data`] with an empty spec of `ty` at `path` and returns both
    /// so tests can construct a typed view over the abstract data.
    fn data_with_spec(path: &str, ty: sdf::SpecType) -> (Data, sdf::Path) {
        let path = sdf::path(path).expect("valid path");
        let mut data = Data::new();
        data.create_spec(path.clone(), ty);
        (data, path)
    }

    #[test]
    fn prim_mut_reads() {
        let (mut data, path) = data_with_spec("/p", sdf::SpecType::Prim);
        let mut prim = PrimSpecMut::get(&mut data, path.clone()).expect("prim spec");

        prim.set_type_name("Xform");
        prim.set_specifier(sdf::Specifier::Def);

        assert_eq!(prim.type_name(), Some(tf::Token::from("Xform")));
        assert_eq!(prim.specifier(), Some(sdf::Specifier::Def));
    }

    #[test]
    fn add_api_schema_prepends() -> Result<(), SpecError> {
        let (mut data, path) = data_with_spec("/p", sdf::SpecType::Prim);
        let mut prim = PrimSpecMut::get(&mut data, path).expect("prim spec");

        assert!(prim.add_applied_schema("MaterialBindingAPI")?);
        assert!(prim.add_applied_schema("SkelBindingAPI")?);
        assert!(!prim.add_applied_schema("MaterialBindingAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert!(!op.explicit);
        assert_eq!(
            op.prepended_items,
            vec![tf::Token::from("MaterialBindingAPI"), tf::Token::from("SkelBindingAPI")]
        );
        Ok(())
    }

    #[test]
    fn add_connection_path_dedups() {
        let (mut data, path) = data_with_spec("/A.in", sdf::SpecType::Attribute);
        let mut attr = AttributeSpecMut::get(&mut data, path).expect("attr spec");
        let target = sdf::Path::new("/A.out").expect("path");

        assert!(attr.add_connection_path(target.clone(), false));
        // Duplicate — must not mutate, must not trip the change tracker.
        assert!(!attr.add_connection_path(target, false));
    }

    #[test]
    fn clear_connection_paths_noop() {
        let (mut data, path) = data_with_spec("/A.in", sdf::SpecType::Attribute);
        let mut attr = AttributeSpecMut::get(&mut data, path).expect("attr spec");

        // Nothing authored — clear is a no-op.
        assert!(!attr.clear_connection_paths());

        attr.add_connection_path(sdf::Path::new("/A.out").expect("path"), false);
        assert!(attr.clear_connection_paths());
        assert!(!attr.clear_connection_paths());
    }

    #[test]
    fn add_api_schema_explicit() -> Result<(), SpecError> {
        let (mut data, path) = data_with_spec("/p", sdf::SpecType::Prim);
        data.set_field(
            &path,
            sdf::FieldKey::ApiSchemas.as_str(),
            sdf::Value::TokenListOp(sdf::TokenListOp::explicit([tf::Token::from("ExistingAPI")])),
        );
        let mut prim = PrimSpecMut::get(&mut data, path).expect("prim spec");

        assert!(prim.add_applied_schema("NewAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert!(op.explicit);
        assert_eq!(
            op.explicit_items,
            vec![tf::Token::from("ExistingAPI"), tf::Token::from("NewAPI")]
        );
        Ok(())
    }

    #[test]
    fn add_api_schema_keeps_add() -> Result<(), SpecError> {
        let (mut data, path) = data_with_spec("/p", sdf::SpecType::Prim);
        data.set_field(
            &path,
            sdf::FieldKey::ApiSchemas.as_str(),
            sdf::Value::TokenListOp(sdf::TokenListOp {
                added_items: vec![tf::Token::from("ExistingAPI")],
                ..Default::default()
            }),
        );
        let mut prim = PrimSpecMut::get(&mut data, path).expect("prim spec");

        assert!(!prim.add_applied_schema("ExistingAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert_eq!(op.added_items, vec![tf::Token::from("ExistingAPI")]);
        assert!(op.prepended_items.is_empty());
        Ok(())
    }

    #[test]
    fn add_api_schema_clears_delete() -> Result<(), SpecError> {
        let (mut data, path) = data_with_spec("/p", sdf::SpecType::Prim);
        data.set_field(
            &path,
            sdf::FieldKey::ApiSchemas.as_str(),
            sdf::Value::TokenListOp(sdf::TokenListOp {
                deleted_items: vec![tf::Token::from("RemovedAPI")],
                ..Default::default()
            }),
        );
        let mut prim = PrimSpecMut::get(&mut data, path).expect("prim spec");

        assert!(prim.add_applied_schema("RemovedAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert_eq!(op.prepended_items, vec![tf::Token::from("RemovedAPI")]);
        assert!(op.deleted_items.is_empty());
        Ok(())
    }

    /// Explicit op with the name lingering in (irrelevant) `added_items`:
    /// already_applied stays false, so the schema lands in `explicit_items`.
    #[test]
    fn add_api_schema_stale_added() -> Result<(), SpecError> {
        let (mut data, path) = data_with_spec("/p", sdf::SpecType::Prim);
        data.set_field(
            &path,
            sdf::FieldKey::ApiSchemas.as_str(),
            sdf::Value::TokenListOp(sdf::TokenListOp {
                explicit: true,
                added_items: vec![tf::Token::from("StaleAPI")],
                ..Default::default()
            }),
        );
        let mut prim = PrimSpecMut::get(&mut data, path).expect("prim spec");

        assert!(prim.add_applied_schema("StaleAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert!(op.explicit);
        assert_eq!(op.explicit_items, vec![tf::Token::from("StaleAPI")]);
        Ok(())
    }

    /// A delete listing the same name twice is fully cleared (not just the
    /// first occurrence).
    #[test]
    fn add_api_schema_dup_delete() -> Result<(), SpecError> {
        let (mut data, path) = data_with_spec("/p", sdf::SpecType::Prim);
        data.set_field(
            &path,
            sdf::FieldKey::ApiSchemas.as_str(),
            sdf::Value::TokenListOp(sdf::TokenListOp {
                deleted_items: vec![tf::Token::from("RemovedAPI"), tf::Token::from("RemovedAPI")],
                ..Default::default()
            }),
        );
        let mut prim = PrimSpecMut::get(&mut data, path).expect("prim spec");

        assert!(prim.add_applied_schema("RemovedAPI")?);

        let op = prim.api_schemas().expect("apiSchemas");
        assert!(op.deleted_items.is_empty());
        assert_eq!(op.prepended_items, vec![tf::Token::from("RemovedAPI")]);
        Ok(())
    }

    #[test]
    fn add_api_schema_rejects_wrong_type() {
        let (mut data, path) = data_with_spec("/p", sdf::SpecType::Prim);
        data.set_field(
            &path,
            sdf::FieldKey::ApiSchemas.as_str(),
            sdf::Value::token_vec(["ExistingAPI"]),
        );
        let mut prim = PrimSpecMut::get(&mut data, path).expect("prim spec");

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
        let (mut data, path) = data_with_spec("/A.x", sdf::SpecType::Attribute);
        let mut attr = AttributeSpecMut::get(&mut data, path).expect("attribute spec");

        attr.set_default(sdf::Value::Int(42));
        attr.set_custom(true);

        assert_eq!(attr.default(), Some(sdf::Value::Int(42)));
        assert!(attr.is_custom());
    }

    #[test]
    fn relationship_mut_reads() {
        let (mut data, path) = data_with_spec("/A.rel", sdf::SpecType::Relationship);
        let mut rel = RelationshipSpecMut::get(&mut data, path).expect("relationship spec");
        let target = sdf::Path::new("/Target").expect("valid path");

        rel.add_target(target.clone());

        assert_eq!(
            rel.target_path_list().and_then(|op| op.iter().next().cloned()),
            Some(target)
        );
    }

    #[test]
    fn remove_target_suppresses_weaker() {
        // Removing a target from a relationship with no local targets must
        // author a deletion (not no-op), so a target authored in a weaker
        // layer is suppressed through composition.
        let (mut data, path) = data_with_spec("/A.rel", sdf::SpecType::Relationship);
        let mut rel = RelationshipSpecMut::get(&mut data, path).expect("relationship spec");
        let target = sdf::Path::new("/Target").expect("valid path");
        assert!(rel.remove_target(&target));

        let stronger = rel.target_path_list().expect("target list op");
        assert!(stronger.deleted_items.contains(&target));

        // A weaker layer adds /Target and /Keep; composition drops /Target.
        let weaker = sdf::PathListOp::explicit([target.clone(), sdf::Path::new("/Keep").unwrap()]);
        let composed: Vec<_> = stronger.combined_with(&weaker).iter().cloned().collect();
        assert_eq!(composed, vec![sdf::Path::new("/Keep").unwrap()]);
    }

    #[test]
    fn remove_target_explicit_drops_entry() {
        // In explicit mode the explicit list is the whole value, so removal
        // just drops the entry without authoring a deletion.
        let (mut data, path) = data_with_spec("/A.rel", sdf::SpecType::Relationship);
        let mut rel = RelationshipSpecMut::get(&mut data, path).expect("relationship spec");
        let a = sdf::Path::new("/A").unwrap();
        let b = sdf::Path::new("/B").unwrap();
        rel.add_target(a.clone());
        rel.add_target(b.clone());
        assert!(rel.remove_target(&a));

        let op = rel.target_path_list().expect("target list op");
        assert!(op.explicit);
        assert!(op.deleted_items.is_empty());
        assert_eq!(op.iter().cloned().collect::<Vec<_>>(), vec![b]);
    }

    #[test]
    fn remove_target_reports_change() {
        // A non-explicit op that adds /X while /X is already deleted: removal
        // still mutates added_items, so it must report a change so relationship
        // change tracking emits an entry.
        let x = sdf::Path::new("/X").unwrap();
        let mut op = sdf::PathListOp::added([x.clone()]);
        op.deleted_items.push(x.clone());
        let (mut data, path) = data_with_spec("/A.rel", sdf::SpecType::Relationship);
        data.set_field(&path, sdf::FieldKey::TargetPaths.as_str(), sdf::Value::PathListOp(op));

        let mut rel = RelationshipSpecMut::get(&mut data, path).expect("relationship spec");
        assert!(rel.remove_target(&x));
        let op = rel.target_path_list().expect("target list op");
        assert!(op.added_items.is_empty());
        assert!(op.deleted_items.contains(&x));
    }

    #[test]
    fn pseudo_root_mut_reads() {
        let mut data = Data::new();
        data.create_spec(sdf::Path::abs_root(), sdf::SpecType::PseudoRoot);
        let mut root = PseudoRootSpecMut::get(&mut data).expect("pseudo-root spec");

        root.set_default_prim("World");

        assert_eq!(root.default_prim(), Some(tf::Token::from("World")));
    }

    #[test]
    fn insert_sublayer_aligns_offsets() {
        let mut data = Data::new();
        data.create_spec(sdf::Path::abs_root(), sdf::SpecType::PseudoRoot);
        let mut root = PseudoRootSpecMut::get(&mut data).expect("pseudo-root spec");

        // Seed an existing sublayer with no authored offset, then insert ahead
        // of it: the prior entry must be padded to identity so offsets stay
        // index-aligned with paths.
        root.set_sublayers(["b.usda"]);
        root.insert_sublayer(0, "a.usda", sdf::LayerOffset::new(10.0, 1.0));

        assert_eq!(root.sublayers(), Some(vec!["a.usda".to_string(), "b.usda".to_string()]));
        let offsets = root
            .field(sdf::FieldKey::SubLayerOffsets.as_str())
            .ok()
            .flatten()
            .expect("offsets authored")
            .try_as_layer_offset_vec()
            .expect("layer-offset vec");
        assert_eq!(
            offsets,
            vec![sdf::LayerOffset::new(10.0, 1.0), sdf::LayerOffset::IDENTITY]
        );
    }

    #[test]
    fn remove_sublayer_drops_aligned() {
        let mut data = Data::new();
        data.create_spec(sdf::Path::abs_root(), sdf::SpecType::PseudoRoot);
        let mut root = PseudoRootSpecMut::get(&mut data).expect("pseudo-root spec");
        root.insert_sublayer(0, "a.usda", sdf::LayerOffset::new(10.0, 1.0));
        root.insert_sublayer(1, "b.usda", sdf::LayerOffset::IDENTITY);

        assert!(root.remove_sublayer("a.usda"));
        assert!(!root.remove_sublayer("missing.usda"));

        assert_eq!(root.sublayers(), Some(vec!["b.usda".to_string()]));
        let offsets = root
            .field(sdf::FieldKey::SubLayerOffsets.as_str())
            .ok()
            .flatten()
            .expect("offsets authored")
            .try_as_layer_offset_vec()
            .expect("layer-offset vec");
        assert_eq!(offsets, vec![sdf::LayerOffset::IDENTITY]);
    }
}
