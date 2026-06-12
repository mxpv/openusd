//! A single scene-description layer (the Rust equivalent of C++ `SdfLayer`):
//! identity + a backing [`AbstractData`] wrapped in a recording [`EditProxy`].
//! Spec authoring lives on the views ([`PrimSpec::new`](super::PrimSpec::new)
//! and friends); the layer records every edit into a [`ChangeList`].
//!
//! Cross-layer composition concerns (resolving sublayers, references,
//! payloads) live separately in [`crate::layer`].

use std::io::Cursor;
use std::sync::atomic::{AtomicU64, Ordering};

use anyhow::{Context, Result};

use super::schema::{ChildrenKey, FieldKey};
use super::{
    AbstractData, AttributeSpecMut, AttributeSpecRef, ChangeList, Data, EditProxy, LayerData, Path, PrimSpecMut,
    PrimSpecRef, PseudoRootSpecMut, PseudoRootSpecRef, RelationshipSpecMut, RelationshipSpecRef, RelocateList,
    SpecData, SpecError, SpecType, Value,
};

/// Prefix marking an anonymous layer identifier (`anon:<n>:<tag>`), the single
/// source of truth shared by minting and [`Layer::is_anonymous`].
const ANONYMOUS_PREFIX: &str = "anon:";

/// Monotonic source of unique anonymous-layer identifiers (the `<n>` in
/// `anon:<n>:<tag>`). Process-global so that anonymous layers created anywhere
/// in the process never collide.
static ANONYMOUS_COUNTER: AtomicU64 = AtomicU64::new(0);

/// A single loaded layer in the composition.
pub struct Layer {
    /// Resolved, canonical identifier for this layer.
    pub identifier: String,
    /// The parsed scene description data, wrapped in an [`EditProxy`] so every
    /// mutation is recorded into a [`ChangeList`]. Private so external callers
    /// reach it only through [`data`](Self::data) / [`data_mut`](Self::data_mut),
    /// keeping recording — and the authoring API's bookkeeping invariants
    /// (`primChildren`, `propertyChildren`, ancestor specifiers, …) — in force.
    data: EditProxy,
}

impl Layer {
    /// Construct a layer from a resolved identifier and a backing data store.
    /// Crate-private — external callers should use [`Layer::new_anonymous`]
    /// for blank in-memory layers, or [`crate::layer::Collector`] for layers
    /// loaded from disk.
    pub(crate) fn new(identifier: impl Into<String>, data: LayerData) -> Self {
        Self {
            identifier: identifier.into(),
            data: EditProxy::new(data),
        }
    }

    /// Borrow the underlying [`AbstractData`] backend for read-only inspection.
    pub fn data(&self) -> &dyn AbstractData {
        self.data.inner()
    }

    /// Borrow the layer's backing data as a mutable [`AbstractData`] for
    /// authoring, returning the recording [`EditProxy`] so every write is
    /// captured in the layer's [`ChangeList`].
    pub fn data_mut(&mut self) -> &mut dyn AbstractData {
        &mut self.data
    }

    /// Drain the changes recorded since the last call into `out` (appending),
    /// leaving the layer's recording buffer empty. Reuses `out`'s allocation
    /// across edits — a stage drains into one scratch [`ChangeList`] this way to
    /// feed composition invalidation without a per-op allocation.
    pub fn drain_changes(&mut self, out: &mut ChangeList) {
        self.data.take(out);
    }

    /// Whether the layer has recorded any change since the last drain. Mirrors
    /// C++ `SdfLayer::IsDirty`.
    pub fn is_dirty(&self) -> bool {
        self.data.is_dirty()
    }

    /// Discard any changes recorded since the last drain without applying them.
    /// Used to drop a partial record after an authoring call fails midway.
    pub fn discard_changes(&mut self) {
        self.data.clear();
    }

    /// The layer's resolved, canonical identifier.
    pub fn identifier(&self) -> &str {
        &self.identifier
    }
}

impl Layer {
    /// Write this layer to `filename`, choosing the format from the filename's
    /// extension (C++ `SdfLayer::Export`). This writes a copy; the layer's own
    /// identifier is unchanged.
    ///
    /// `.usda` writes text, `.usdc` writes the binary crate, `.usd` writes
    /// binary (the C++ `USD_WRITE_NEW_USD_FILES_AS_BINARY` default), and
    /// `.usdz` writes an archive wrapping one crate-encoded layer. The reader
    /// auto-detects the format regardless of extension, so text written to a
    /// `.usd` path still reads back correctly.
    pub fn export(&self, filename: impl AsRef<str>) -> Result<()> {
        let filename = filename.as_ref();
        let ext = std::path::Path::new(filename)
            .extension()
            .and_then(|e| e.to_str())
            .unwrap_or_default();
        let format = super::find_by_extension(ext).ok_or_else(|| match ext {
            "" => anyhow::anyhow!("layer path {filename} has no extension; cannot choose format"),
            other => anyhow::anyhow!("unsupported layer extension {other:?} (expected usda/usdc/usd/usdz)"),
        })?;
        if !format.caps().can_write() {
            anyhow::bail!("file format {} does not support writing", format.format_id());
        }
        let mut file = std::fs::File::create(filename).with_context(|| format!("failed to create {filename}"))?;
        format.write(self.data(), &mut file)
    }

    /// Serialize this layer to a `usda` text string (C++ `ExportToString`).
    ///
    /// Always emits text, the canonical human-readable form, regardless of the
    /// layer's on-disk format. Named to avoid confusion with the infallible
    /// [`ToString::to_string`].
    pub fn export_to_string(&self) -> Result<String> {
        let format = super::find_by_id("usda").expect("usda is a built-in format");
        let mut buf = Cursor::new(Vec::new());
        format.write(self.data(), &mut buf)?;
        String::from_utf8(buf.into_inner()).context("usda writer produced invalid UTF-8")
    }

    /// Write this layer to its own [`identifier`](Self::identifier), choosing
    /// the format from the identifier's extension (C++ `SdfLayer::Save`).
    ///
    /// The identifier must be an absolute filesystem path — the form
    /// [`Collector`](crate::layer::Collector) produces for loaded layers.
    /// Anonymous layers ([`is_anonymous`](Self::is_anonymous)) and layers whose
    /// identifier is a relative path or a non-filesystem asset identifier (e.g.
    /// `scheme://…`) have no persistent location here; save them with
    /// [`export`](Self::export) and an explicit destination instead.
    pub fn save(&self) -> Result<()> {
        anyhow::ensure!(!self.is_anonymous(), "cannot save anonymous layer {}", self.identifier);
        let path = std::path::Path::new(&self.identifier);
        anyhow::ensure!(
            path.is_absolute(),
            "cannot save layer {}: identifier is not an absolute file path; use Layer::export(path) to choose a destination",
            self.identifier
        );
        // Saving overwrites the layer's own file in place, so the format must
        // support in-place editing — unlike `export`, which only writes a copy.
        // A package format (usdz) is writable as a fresh archive but not
        // editable in place: a loaded package's other assets (textures, sibling
        // layers) are not held by the layer, so saving over it would discard
        // them. An unknown extension is left for `export` to reject.
        let ext = path.extension().and_then(|e| e.to_str()).unwrap_or_default();
        if let Some(format) = super::find_by_extension(ext) {
            anyhow::ensure!(
                format.caps().can_edit(),
                "cannot save layer {} in place: the {} format is not editable; use Layer::export(path) to write a new copy",
                self.identifier,
                format.format_id()
            );
        }
        // TODO(layer-registry): save writes to `identifier` as a literal
        // filesystem path. A layer loaded through a custom resolver may carry a
        // logical identifier (e.g. `scheme://…`); save should resolve it through
        // the owning resolver and write via a resolver write API. The
        // absolute-path guard above refuses such identifiers for now.
        // TODO(layer-registry): save re-selects the format from the identifier's
        // extension, so a textual `.usd` layer is rewritten as binary. Once the
        // load path records the FileFormat a layer was read with (C++
        // `_fileFormat`), save should reuse it to preserve the original encoding.
        self.export(&self.identifier)
    }
}

/// Errors raised by [`Layer`]'s authoring methods.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum AuthoringError {
    /// The target spec rejected an edit.
    #[error(transparent)]
    Spec(#[from] SpecError),

    /// The given path is not valid for the requested authoring operation.
    /// Prim authoring requires an absolute, non-root, non-property path;
    /// property authoring requires a property path.
    #[error("path {path} is not valid here: {reason}")]
    InvalidPath {
        /// The offending path.
        path: Path,
        /// A short, human-readable reason describing what was expected.
        reason: &'static str,
    },
}

/// Identity, persistence, and typed-view lookups. Spec authoring lives on the
/// views themselves ([`PrimSpec::new`](crate::sdf::PrimSpec::new) and friends,
/// mirroring C++ `Sdf*Spec::New`); they write through [`Layer::data_mut`], so
/// the layer's [`EditProxy`] records every edit.
///
/// The typed-view lookups ([`Layer::prim`], [`Layer::attribute`],
/// [`Layer::relationship`], [`Layer::pseudo_root`]) operate through the
/// [`AbstractData`] field interface, so they work uniformly on any backend —
/// in-memory [`Data`] or a file-loaded reader — matching C++
/// `SdfLayer::GetPrimAtPath`.
impl Layer {
    /// Create a blank in-memory writable layer with a unique anonymous
    /// identifier of the form `anon:<n>:<tag>`, mirroring C++
    /// `SdfLayer::CreateAnonymous`. `tag` is a human-readable hint, not an
    /// address: two calls with the same tag get distinct identifiers, so
    /// independent anonymous layers never alias (see [`Layer::is_anonymous`]).
    ///
    /// The layer's pseudo-root spec is pre-populated so layer-level metadata
    /// (`defaultPrim`, `subLayers`, time codes, …) can be authored via
    /// [`Layer::pseudo_root_mut`] immediately.
    pub fn new_anonymous(tag: impl std::fmt::Display) -> Self {
        let n = ANONYMOUS_COUNTER.fetch_add(1, Ordering::Relaxed);
        Self::new_in_memory(format!("{ANONYMOUS_PREFIX}{n}:{tag}"))
    }

    /// Create a blank in-memory writable layer with the given verbatim
    /// identifier and a pre-populated pseudo-root spec. Backs
    /// [`new_anonymous`](Self::new_anonymous) and, within the crate, composes
    /// layers whose identifiers must match an authored `subLayers` entry.
    pub(crate) fn new_in_memory(identifier: impl Into<String>) -> Self {
        let mut data = Data::new();
        data.create_spec(Path::abs_root(), SpecType::PseudoRoot);
        Self::new(identifier, Box::new(data))
    }

    /// Whether this layer's identifier is anonymous (the `anon:` prefix minted
    /// by [`new_anonymous`](Self::new_anonymous)). Mirrors C++
    /// `SdfLayer::IsAnonymous`; an anonymous layer has no asset-resolvable
    /// location.
    pub fn is_anonymous(&self) -> bool {
        self.identifier.starts_with(ANONYMOUS_PREFIX)
    }

    /// Look up a prim spec at `path`. Returns `None` if no spec exists or the
    /// spec is not a prim.
    pub fn prim(&self, path: impl Into<Path>) -> Option<PrimSpecRef<'_>> {
        PrimSpecRef::get(self.data(), path.into())
    }

    /// Mutably look up a prim spec at `path`.
    pub fn prim_mut(&mut self, path: impl Into<Path>) -> Option<PrimSpecMut<'_>> {
        PrimSpecMut::get(self.data_mut(), path.into())
    }

    /// Look up an attribute spec at a property path.
    pub fn attribute(&self, path: impl Into<Path>) -> Option<AttributeSpecRef<'_>> {
        AttributeSpecRef::get(self.data(), path.into())
    }

    /// Mutably look up an attribute spec at a property path.
    pub fn attribute_mut(&mut self, path: impl Into<Path>) -> Option<AttributeSpecMut<'_>> {
        AttributeSpecMut::get(self.data_mut(), path.into())
    }

    /// Look up a relationship spec at a property path.
    pub fn relationship(&self, path: impl Into<Path>) -> Option<RelationshipSpecRef<'_>> {
        RelationshipSpecRef::get(self.data(), path.into())
    }

    /// Mutably look up a relationship spec at a property path.
    pub fn relationship_mut(&mut self, path: impl Into<Path>) -> Option<RelationshipSpecMut<'_>> {
        RelationshipSpecMut::get(self.data_mut(), path.into())
    }

    /// View this layer's root pseudo-spec, which carries layer-wide metadata
    /// (`defaultPrim`, `subLayers`, time codes, …).
    pub fn pseudo_root(&self) -> Option<PseudoRootSpecRef<'_>> {
        PseudoRootSpecRef::get(self.data())
    }

    /// Set the layer's `defaultPrim` metadata to `name`.
    ///
    /// `name` must be a USD identifier or nested prim path (without leading
    /// `/`). Modern OpenUSD (≥ 23.05) allows `defaultPrim` to address a
    /// nested prim such as `"World/Char"`; both shapes are accepted here so
    /// the write contract matches the read path in
    /// [`crate::pcp::IndexCache::default_prim`].
    ///
    /// Mirrors C++ `SdfLayer::SetDefaultPrim`.
    ///
    /// Note: [`crate::sdf::PseudoRootSpecMut::set_default_prim`] writes the
    /// raw token without validation — that is the spec-tier escape hatch.
    /// This Layer-tier method is the validating front door.
    pub fn set_default_prim(&mut self, name: impl Into<String>) -> Result<(), AuthoringError> {
        let name = name.into();
        if name.is_empty() || name.starts_with('/') || Path::new(&format!("/{name}")).is_err() {
            return Err(AuthoringError::InvalidPath {
                path: Path::abs_root(),
                reason: "defaultPrim must be a relative prim identifier or nested prim path",
            });
        }
        self.pseudo_root_mut()?.set_default_prim(name);
        Ok(())
    }

    /// Remove the layer's `defaultPrim` metadata. Mirrors C++
    /// `SdfLayer::ClearDefaultPrim`. No-op when no pseudo-root spec exists
    /// (clearing what isn't there must not materialize state).
    pub fn clear_default_prim(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::DefaultPrim)
    }

    /// The list of namespace relocations authored in this layer's metadata,
    /// or an empty list when none are authored. Mirrors C++
    /// `SdfLayer::GetRelocates`. Reads through the backing [`AbstractData`], so
    /// it works on both in-memory and file-loaded layers.
    pub fn relocates(&self) -> RelocateList {
        self.pseudo_root().and_then(|root| root.relocates()).unwrap_or_default()
    }

    /// Whether this layer's metadata carries any `relocates` opinion, including
    /// an explicit empty list (an opinion that *there should be no* relocates).
    /// Mirrors C++ `SdfLayer::HasRelocates`.
    pub fn has_relocates(&self) -> bool {
        self.has_root_field(FieldKey::LayerRelocates)
    }

    /// Set this layer's entire list of namespace relocations to `relocates`.
    /// An empty list authors an explicit "no relocates" opinion (see
    /// [`Layer::has_relocates`]); use [`Layer::clear_relocates`] to remove the
    /// opinion entirely. Mirrors C++ `SdfLayer::SetRelocates`.
    pub fn set_relocates(&mut self, relocates: RelocateList) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_relocates(relocates);
        Ok(())
    }

    /// Clear this layer's `relocates` opinion from its metadata. Mirrors C++
    /// `SdfLayer::ClearRelocates`. No-op when no pseudo-root spec exists.
    pub fn clear_relocates(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::LayerRelocates)
    }

    /// The layer's `startTimeCode`, or `0.0` when unauthored. Mirrors C++
    /// `SdfLayer::GetStartTimeCode`.
    pub fn start_time_code(&self) -> f64 {
        self.pseudo_root()
            .and_then(|root| root.start_time_code())
            .unwrap_or(0.0)
    }

    /// Set the layer's `startTimeCode`. Mirrors C++ `SdfLayer::SetStartTimeCode`.
    pub fn set_start_time_code(&mut self, time: f64) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_start_time_code(time);
        Ok(())
    }

    /// Whether this layer authors a `startTimeCode` opinion. Mirrors C++
    /// `SdfLayer::HasStartTimeCode`.
    pub fn has_start_time_code(&self) -> bool {
        self.has_root_field(FieldKey::StartTimeCode)
    }

    /// Clear this layer's `startTimeCode` opinion. Mirrors C++
    /// `SdfLayer::ClearStartTimeCode`. No-op when no pseudo-root spec exists.
    pub fn clear_start_time_code(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::StartTimeCode)
    }

    /// The layer's `endTimeCode`, or `0.0` when unauthored. Mirrors C++
    /// `SdfLayer::GetEndTimeCode`.
    pub fn end_time_code(&self) -> f64 {
        self.pseudo_root().and_then(|root| root.end_time_code()).unwrap_or(0.0)
    }

    /// Set the layer's `endTimeCode`. Mirrors C++ `SdfLayer::SetEndTimeCode`.
    pub fn set_end_time_code(&mut self, time: f64) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_end_time_code(time);
        Ok(())
    }

    /// Whether this layer authors an `endTimeCode` opinion. Mirrors C++
    /// `SdfLayer::HasEndTimeCode`.
    pub fn has_end_time_code(&self) -> bool {
        self.has_root_field(FieldKey::EndTimeCode)
    }

    /// Clear this layer's `endTimeCode` opinion. Mirrors C++
    /// `SdfLayer::ClearEndTimeCode`. No-op when no pseudo-root spec exists.
    pub fn clear_end_time_code(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::EndTimeCode)
    }

    /// The layer's `timeCodesPerSecond`. Falls back to the authored
    /// `framesPerSecond`, then to `24.0`, when unauthored. Mirrors C++
    /// `SdfLayer::GetTimeCodesPerSecond`.
    pub fn time_codes_per_second(&self) -> f64 {
        let root = self.pseudo_root();
        root.as_ref()
            .and_then(|root| root.time_codes_per_second())
            .or_else(|| root.as_ref().and_then(|root| root.frames_per_second()))
            .unwrap_or(24.0)
    }

    /// Set the layer's `timeCodesPerSecond`. Mirrors C++
    /// `SdfLayer::SetTimeCodesPerSecond`.
    pub fn set_time_codes_per_second(&mut self, rate: f64) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_time_codes_per_second(rate);
        Ok(())
    }

    /// Whether this layer authors a `timeCodesPerSecond` opinion. Mirrors C++
    /// `SdfLayer::HasTimeCodesPerSecond`.
    pub fn has_time_codes_per_second(&self) -> bool {
        self.has_root_field(FieldKey::TimeCodesPerSecond)
    }

    /// Clear this layer's `timeCodesPerSecond` opinion. Mirrors C++
    /// `SdfLayer::ClearTimeCodesPerSecond`. No-op when no pseudo-root spec exists.
    pub fn clear_time_codes_per_second(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::TimeCodesPerSecond)
    }

    /// The layer's `framesPerSecond`, or `24.0` when unauthored. Mirrors C++
    /// `SdfLayer::GetFramesPerSecond`.
    pub fn frames_per_second(&self) -> f64 {
        self.pseudo_root()
            .and_then(|root| root.frames_per_second())
            .unwrap_or(24.0)
    }

    /// Set the layer's `framesPerSecond`. Mirrors C++
    /// `SdfLayer::SetFramesPerSecond`.
    pub fn set_frames_per_second(&mut self, rate: f64) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_frames_per_second(rate);
        Ok(())
    }

    /// Whether this layer authors a `framesPerSecond` opinion. Mirrors C++
    /// `SdfLayer::HasFramesPerSecond`.
    pub fn has_frames_per_second(&self) -> bool {
        self.has_root_field(FieldKey::FramesPerSecond)
    }

    /// Clear this layer's `framesPerSecond` opinion. Mirrors C++
    /// `SdfLayer::ClearFramesPerSecond`. No-op when no pseudo-root spec exists.
    pub fn clear_frames_per_second(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::FramesPerSecond)
    }

    /// The layer's `framePrecision`, or `3` when unauthored. Mirrors C++
    /// `SdfLayer::GetFramePrecision`.
    pub fn frame_precision(&self) -> i32 {
        self.pseudo_root().and_then(|root| root.frame_precision()).unwrap_or(3)
    }

    /// Set the layer's `framePrecision`. Mirrors C++
    /// `SdfLayer::SetFramePrecision`.
    pub fn set_frame_precision(&mut self, precision: i32) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_frame_precision(precision);
        Ok(())
    }

    /// Whether this layer authors a `framePrecision` opinion. Mirrors C++
    /// `SdfLayer::HasFramePrecision`.
    pub fn has_frame_precision(&self) -> bool {
        self.has_root_field(FieldKey::FramePrecision)
    }

    /// Clear this layer's `framePrecision` opinion. Mirrors C++
    /// `SdfLayer::ClearFramePrecision`. No-op when no pseudo-root spec exists.
    pub fn clear_frame_precision(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::FramePrecision)
    }

    /// Remove the spec at `path` together with its entire namespace subtree,
    /// and unregister the leaf from its parent's child list.
    ///
    /// `path` must be a prim or prim-property path. Every spec at or below
    /// `path` is erased; a missing parent or child list is simply nothing to
    /// detach. This is the single-layer mechanical half of a namespace delete:
    /// it does not touch relationship targets or attribute connections that
    /// point at `path` because Sdf does not track backpointers.
    pub fn remove_spec_subtree(&mut self, path: &Path) -> Result<(), AuthoringError> {
        let (parent, child_key, child_name) = child_registration(path)?;

        remove_from_token_vec(&mut self.data, &parent, child_key, &child_name)?;
        for p in subtree_paths(&self.data, path) {
            self.data.erase_spec(&p);
        }
        Ok(())
    }

    /// Move the spec subtree rooted at `old` to `new` within this layer,
    /// rebuilding the destination parent chain as `over`s when needed and
    /// updating both parents' child lists. Handles rename and reparent
    /// uniformly.
    ///
    /// `old` and `new` must be the same kind, either both prim paths or both
    /// prim-property paths. The destination must not already exist, and it must
    /// not be the source or a descendant of it. Like
    /// [`remove_spec_subtree`](Self::remove_spec_subtree), this is the
    /// mechanical single-layer half; target and connection fixup is the caller's
    /// responsibility.
    pub fn move_spec_subtree(&mut self, old: &Path, new: &Path) -> Result<(), AuthoringError> {
        let (old_parent, old_key, old_name) = child_registration(old)?;
        let (new_parent, new_key, new_name) = child_registration(new)?;

        let invalid_new = |reason: &'static str| AuthoringError::InvalidPath {
            path: new.clone(),
            reason,
        };
        if old.is_property_path() != new.is_property_path() {
            return Err(invalid_new("source and destination are different namespace kinds"));
        }
        if new.has_prefix(old) {
            return Err(invalid_new("destination is the source or a descendant of it"));
        }
        if self.data.spec_type(old).is_none() {
            return Err(AuthoringError::InvalidPath {
                path: old.clone(),
                reason: "no spec to move at the source path",
            });
        }
        if self.data.has_spec(new) {
            return Err(invalid_new("an object already exists at the destination"));
        }

        if new_parent.is_abs_root() {
            self.pseudo_root_mut()?;
        } else {
            PrimSpecMut::over(self.data_mut(), new_parent.clone())?;
        }

        let mut moved = Vec::new();
        for old_path in subtree_paths(&self.data, old) {
            let new_path = old_path
                .replace_prefix(old, new)
                .expect("subtree path must be at or below the source path");
            let spec = spec_data(&self.data, &old_path)?;
            moved.push((old_path, new_path, spec));
        }

        for (old_path, _, _) in &moved {
            self.data.erase_spec(old_path);
        }
        for (_, new_path, spec) in moved {
            self.data.create_spec(new_path.clone(), spec.ty);
            for (field, value) in spec.fields {
                self.data.set_field(&new_path, &field, value);
            }
        }

        remove_from_token_vec(&mut self.data, &old_parent, old_key, &old_name)?;
        add_to_token_vec(&mut self.data, &new_parent, new_key, &new_name)?;

        Ok(())
    }

    /// Whether the pseudo-root spec authors `key`, including an explicit
    /// opinion that carries an "empty"/default value.
    fn has_root_field(&self, key: FieldKey) -> bool {
        self.data.has_field(&Path::abs_root(), key.as_str())
    }

    /// Remove a metadata field from the pseudo-root spec, if that spec exists.
    /// No-op otherwise — clearing what isn't there must not materialize state.
    fn clear_root_field(&mut self, key: FieldKey) -> Result<(), AuthoringError> {
        // `erase_field` is a no-op when the pseudo-root spec is absent.
        self.data.erase_field(&Path::abs_root(), key.as_str());
        Ok(())
    }

    /// Mutably view this layer's root pseudo-spec. The spec is created on
    /// first access if missing.
    pub fn pseudo_root_mut(&mut self) -> Result<PseudoRootSpecMut<'_>, AuthoringError> {
        let root = Path::abs_root();
        match self.data.spec_type(&root) {
            Some(SpecType::PseudoRoot) => {}
            Some(_) => {
                return Err(AuthoringError::InvalidPath {
                    path: root,
                    reason: "root spec exists with non-PseudoRoot SpecType",
                })
            }
            None => self.data.create_spec(root, SpecType::PseudoRoot),
        }
        Ok(PseudoRootSpecMut::get(self.data_mut()).expect("just ensured a pseudo-root spec"))
    }
}

/// Resolve the parent path, child-list key, and child name that register
/// `path`'s leaf on its parent. Supports prim and prim-property leaves;
/// variant-selection leaves and the pseudo-root are outside namespace-edit
/// scope.
fn child_registration(path: &Path) -> Result<(Path, ChildrenKey, String), AuthoringError> {
    let invalid = |reason: &'static str| AuthoringError::InvalidPath {
        path: path.clone(),
        reason,
    };
    if let Some((prim, prop)) = path.split_property() {
        return Ok((prim, ChildrenKey::PropertyChildren, prop.to_owned()));
    }
    match path.last_element() {
        Some(super::PathElement::Prim(name)) => {
            let parent = path.parent().ok_or_else(|| invalid("prim path has no parent"))?;
            Ok((parent, ChildrenKey::PrimChildren, name.to_owned()))
        }
        Some(super::PathElement::Variant { .. }) => Err(invalid("variant-selection paths are not supported")),
        Some(super::PathElement::Property(_)) => unreachable!("property paths are handled by split_property above"),
        None => Err(invalid("cannot namespace-edit the pseudo-root")),
    }
}

/// Remove `name` from a child-list field, dropping the field when it becomes
/// empty. An absent parent or field is a no-op; a present non-token child list
/// is invalid layer bookkeeping and is reported.
fn remove_from_token_vec(
    data: &mut dyn AbstractData,
    owner_path: &Path,
    key: ChildrenKey,
    name: &str,
) -> Result<(), AuthoringError> {
    let value = data
        .try_field(owner_path, key.as_str())
        .map_err(|_| AuthoringError::InvalidPath {
            path: owner_path.clone(),
            reason: "child-list field could not be read",
        })?
        .map(std::borrow::Cow::into_owned);
    match value {
        Some(Value::TokenVec(mut v)) => {
            v.retain(|n| n != name);
            if v.is_empty() {
                data.erase_field(owner_path, key.as_str());
            } else {
                data.set_field(owner_path, key.as_str(), Value::TokenVec(v));
            }
        }
        Some(_) => {
            return Err(AuthoringError::InvalidPath {
                path: owner_path.clone(),
                reason: "child-list field exists with non-TokenVec value",
            });
        }
        None => {}
    }
    Ok(())
}

/// Insert `name` into a child-list field, creating the field if absent.
fn add_to_token_vec(
    data: &mut dyn AbstractData,
    owner_path: &Path,
    key: ChildrenKey,
    name: &str,
) -> Result<(), AuthoringError> {
    let value = data
        .try_field(owner_path, key.as_str())
        .map_err(|_| AuthoringError::InvalidPath {
            path: owner_path.clone(),
            reason: "child-list field could not be read",
        })?
        .map(std::borrow::Cow::into_owned);
    match value {
        Some(Value::TokenVec(mut v)) => {
            if !v.iter().any(|n| n == name) {
                v.push(name.into());
                data.set_field(owner_path, key.as_str(), Value::TokenVec(v));
            }
        }
        Some(_) => {
            return Err(AuthoringError::InvalidPath {
                path: owner_path.clone(),
                reason: "child-list field exists with non-TokenVec value",
            });
        }
        None => data.set_field(owner_path, key.as_str(), Value::TokenVec(vec![name.into()])),
    }
    Ok(())
}

/// Every authored path at or below `prefix`, including `prefix` itself, ordered
/// parent-before-child.
fn subtree_paths(data: &dyn AbstractData, prefix: &Path) -> Vec<Path> {
    let mut paths: Vec<Path> = data.spec_paths().into_iter().filter(|p| p.has_prefix(prefix)).collect();
    paths.sort_by_key(Path::element_count);
    paths
}

/// Copy one spec record out of an abstract backend.
fn spec_data(data: &dyn AbstractData, path: &Path) -> Result<SpecData, AuthoringError> {
    let ty = data.spec_type(path).ok_or_else(|| AuthoringError::InvalidPath {
        path: path.clone(),
        reason: "no spec at path",
    })?;
    let mut spec = SpecData::new(ty);
    if let Some(fields) = data.list_fields(path) {
        for field in fields {
            let value = data
                .try_field(path, &field)
                .map_err(|_| AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "field could not be read",
                })?
                .ok_or_else(|| AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "listed field was not authored",
                })?
                .into_owned();
            spec.add(field, value);
        }
    }
    Ok(spec)
}

impl std::fmt::Debug for Layer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Layer")
            .field("identifier", &self.identifier)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::{path, Specifier, Variability};

    /// Read a child-list field as a `Vec<String>`; absent means empty.
    fn children(layer: &Layer, prim: &str, key: ChildrenKey) -> Vec<String> {
        match layer.data().try_field(&path(prim).unwrap(), key.as_str()).unwrap() {
            Some(cow) => match cow.as_ref() {
                Value::TokenVec(v) => v.iter().map(ToString::to_string).collect(),
                other => panic!("{} is not a TokenVec: {other:?}", key.as_str()),
            },
            None => Vec::new(),
        }
    }

    /// `/A` → `/A/B` → `/A/B/C`, plus `/A/B.radius`.
    fn namespace_scene() -> Layer {
        let mut layer = Layer::new_anonymous("anon.usda");
        PrimSpecMut::new(layer.data_mut(), "/A", Specifier::Def, "Xform").unwrap();
        PrimSpecMut::new(layer.data_mut(), "/A/B", Specifier::Def, "Xform").unwrap();
        PrimSpecMut::new(layer.data_mut(), "/A/B/C", Specifier::Def, "Sphere").unwrap();
        AttributeSpecMut::new(layer.data_mut(), "/A/B.radius", "double", Variability::Varying, false).unwrap();
        layer
    }

    /// `new_anonymous` mints a unique `anon:<n>:<tag>` identifier each call, so
    /// two layers given the same tag never alias; `is_anonymous` recognizes them
    /// while a verbatim `new_in_memory` layer is not anonymous.
    #[test]
    fn anonymous_identifiers_unique() {
        let a = Layer::new_anonymous("scene.usda");
        let b = Layer::new_anonymous("scene.usda");
        assert_ne!(a.identifier(), b.identifier());
        assert!(a.identifier().ends_with(":scene.usda"));
        assert!(a.is_anonymous() && b.is_anonymous());
        assert!(!Layer::new_in_memory("scene.usda").is_anonymous());
    }

    /// `set_relocates` / `relocates` round-trip the authored pairs, and the
    /// pairs land under the pseudo-root's `layerRelocates` field.
    #[test]
    fn relocates_round_trip() {
        let mut layer = Layer::new_anonymous("test.usda");
        assert!(!layer.has_relocates());
        assert!(layer.relocates().is_empty());

        let pairs = vec![
            (Path::from("/Rig/Model"), Path::from("/Group/Model")),
            (Path::from("/Rig/Dead"), Path::from("")),
        ];
        layer.set_relocates(pairs.clone()).expect("in-memory layer is writable");

        assert!(layer.has_relocates());
        assert_eq!(layer.relocates(), pairs);
    }

    /// An explicit empty list is still an opinion (`HasRelocates` is true), while
    /// `clear_relocates` removes the opinion entirely.
    #[test]
    fn empty_opinion_vs_cleared() {
        let mut layer = Layer::new_anonymous("test.usda");

        layer.set_relocates(RelocateList::new()).expect("writable");
        assert!(layer.has_relocates());
        assert!(layer.relocates().is_empty());

        layer.clear_relocates().expect("writable");
        assert!(!layer.has_relocates());
        assert!(layer.relocates().is_empty());
    }

    /// The five time-code fields round-trip through set/get and report the
    /// documented unauthored defaults before any opinion is written.
    #[test]
    fn time_code_round_trip() {
        let mut layer = Layer::new_anonymous("test.usda");
        assert!(!layer.has_start_time_code());
        assert_eq!(layer.start_time_code(), 0.0);
        assert_eq!(layer.end_time_code(), 0.0);
        assert_eq!(layer.frame_precision(), 3);

        layer.set_start_time_code(1.0).expect("writable");
        layer.set_end_time_code(48.0).expect("writable");
        layer.set_frame_precision(6).expect("writable");

        assert!(layer.has_start_time_code());
        assert_eq!(layer.start_time_code(), 1.0);
        assert_eq!(layer.end_time_code(), 48.0);
        assert_eq!(layer.frame_precision(), 6);
    }

    /// `timeCodesPerSecond` falls back to the authored `framesPerSecond`, then
    /// to `24.0`, when no `timeCodesPerSecond` opinion is authored.
    #[test]
    fn tcps_fps_fallback() {
        let mut layer = Layer::new_anonymous("test.usda");
        assert_eq!(layer.time_codes_per_second(), 24.0);
        assert_eq!(layer.frames_per_second(), 24.0);

        layer.set_frames_per_second(30.0).expect("writable");
        assert_eq!(layer.time_codes_per_second(), 30.0);

        layer.set_time_codes_per_second(48.0).expect("writable");
        assert_eq!(layer.time_codes_per_second(), 48.0);
    }

    /// `clear_*` removes the opinion so `has_*` reports false and the getter
    /// returns the unauthored default again.
    #[test]
    fn clear_time_code() {
        let mut layer = Layer::new_anonymous("test.usda");
        layer.set_start_time_code(5.0).expect("writable");
        assert!(layer.has_start_time_code());

        layer.clear_start_time_code().expect("writable");
        assert!(!layer.has_start_time_code());
        assert_eq!(layer.start_time_code(), 0.0);
    }

    #[test]
    fn remove_prim_subtree() {
        let mut layer = namespace_scene();
        layer.remove_spec_subtree(&path("/A/B").unwrap()).unwrap();

        assert!(!layer.data().has_spec(&path("/A/B").unwrap()));
        assert!(!layer.data().has_spec(&path("/A/B/C").unwrap()));
        assert!(!layer.data().has_spec(&path("/A/B.radius").unwrap()));
        assert!(layer.data().has_spec(&path("/A").unwrap()));
        assert!(children(&layer, "/A", ChildrenKey::PrimChildren).is_empty());
    }

    #[test]
    fn remove_property() {
        let mut layer = namespace_scene();
        layer.remove_spec_subtree(&path("/A/B.radius").unwrap()).unwrap();

        assert!(!layer.data().has_spec(&path("/A/B.radius").unwrap()));
        assert!(layer.data().has_spec(&path("/A/B").unwrap()));
        assert!(layer.data().has_spec(&path("/A/B/C").unwrap()));
        assert!(children(&layer, "/A/B", ChildrenKey::PropertyChildren).is_empty());
    }

    #[test]
    fn rename_prim_subtree() {
        let mut layer = namespace_scene();
        layer
            .move_spec_subtree(&path("/A/B").unwrap(), &path("/A/Bee").unwrap())
            .unwrap();

        assert!(!layer.data().has_spec(&path("/A/B").unwrap()));
        assert!(layer.data().has_spec(&path("/A/Bee/C").unwrap()));
        assert!(layer.data().has_spec(&path("/A/Bee.radius").unwrap()));
        assert_eq!(
            layer
                .data()
                .try_field(&path("/A/Bee/C").unwrap(), FieldKey::TypeName.as_str())
                .unwrap()
                .unwrap()
                .as_ref(),
            &Value::Token("Sphere".into())
        );
        assert_eq!(
            children(&layer, "/A", ChildrenKey::PrimChildren),
            vec!["Bee".to_string()]
        );
    }

    #[test]
    fn reparent_prim() {
        let mut layer = namespace_scene();
        PrimSpecMut::new(layer.data_mut(), "/X", Specifier::Def, "Xform").unwrap();
        layer
            .move_spec_subtree(&path("/A/B").unwrap(), &path("/X/B").unwrap())
            .unwrap();

        assert!(layer.data().has_spec(&path("/X/B/C").unwrap()));
        assert!(!layer.data().has_spec(&path("/A/B").unwrap()));
        assert!(children(&layer, "/A", ChildrenKey::PrimChildren).is_empty());
        assert_eq!(children(&layer, "/X", ChildrenKey::PrimChildren), vec!["B".to_string()]);
    }

    #[test]
    fn reparent_scaffolds_parent() {
        let mut layer = namespace_scene();
        layer
            .move_spec_subtree(&path("/A/B").unwrap(), &path("/New/B").unwrap())
            .unwrap();

        assert!(layer.data().has_spec(&path("/New/B/C").unwrap()));
        assert_eq!(
            layer
                .data()
                .try_field(&path("/New").unwrap(), FieldKey::Specifier.as_str())
                .unwrap()
                .unwrap()
                .as_ref(),
            &Value::Specifier(Specifier::Over)
        );
        assert_eq!(
            children(&layer, "/New", ChildrenKey::PrimChildren),
            vec!["B".to_string()]
        );
    }

    #[test]
    fn rename_property() {
        let mut layer = namespace_scene();
        layer
            .move_spec_subtree(&path("/A/B.radius").unwrap(), &path("/A/B.size").unwrap())
            .unwrap();

        assert!(!layer.data().has_spec(&path("/A/B.radius").unwrap()));
        assert!(layer.data().has_spec(&path("/A/B.size").unwrap()));
        assert_eq!(
            children(&layer, "/A/B", ChildrenKey::PropertyChildren),
            vec!["size".to_string()]
        );
        assert_eq!(
            layer
                .data()
                .try_field(&path("/A/B.size").unwrap(), FieldKey::TypeName.as_str())
                .unwrap()
                .unwrap()
                .as_ref(),
            &Value::Token("double".into())
        );
    }

    #[test]
    fn move_rejects_bad_targets() {
        let mut layer = namespace_scene();
        PrimSpecMut::new(layer.data_mut(), "/A/D", Specifier::Def, "Xform").unwrap();

        assert!(layer
            .move_spec_subtree(&path("/A/B").unwrap(), &path("/A/D").unwrap())
            .is_err());
        assert!(layer
            .move_spec_subtree(&path("/A/B").unwrap(), &path("/A/B/Inner").unwrap())
            .is_err());
        assert!(layer
            .move_spec_subtree(&path("/A/B").unwrap(), &path("/A.attr").unwrap())
            .is_err());
    }
}
