//! A single scene-description layer (the Rust equivalent of C++ `SdfLayer`):
//! identity + a backing [`AbstractData`] wrapped in a recording [`EditProxy`].
//! Spec authoring lives on the views ([`PrimSpec::new`](super::PrimSpec::new)
//! and friends); each edit is recorded into a [`ChangeList`] and applied
//! write-through to the backend, unless wrapped in a [`Transaction::new`],
//! which stages the edits in a copy-on-write overlay and commits or rolls them
//! back as one atomic transaction.
//!
//! Cross-layer composition concerns (resolving sublayers, references,
//! payloads) live separately in [`crate::layer`].

use std::io::Cursor;
use std::sync::atomic::{AtomicU64, Ordering};

use anyhow::{Context, Result};

use super::schema::FieldKey;
use super::{
    AbstractData, AttributeSpecMut, AttributeSpecRef, ChangeList, CowData, Data, DataError, EditProxy, LayerData, Path,
    PrimSpecMut, PrimSpecRef, PseudoRootSpecMut, PseudoRootSpecRef, RelationshipSpecMut, RelationshipSpecRef,
    RelocateList, SpecError, SpecType,
};

/// Prefix marking an anonymous layer identifier (`anon:<n>:<tag>`), the single
/// source of truth shared by minting and [`Layer::is_anonymous`].
const ANONYMOUS_PREFIX: &str = "anon:";

/// Monotonic source of unique anonymous-layer identifiers (the `<n>` in
/// `anon:<n>:<tag>`). Process-global so that anonymous layers created anywhere
/// in the process never collide.
static ANONYMOUS_COUNTER: AtomicU64 = AtomicU64::new(0);

/// An atomic copy-on-write transaction over a [`Layer`], created by
/// [`Transaction::new`]. Edits authored through the guard (it derefs to the
/// `Layer`) stage in the layer's overlay; [`commit`](Self::commit) flushes them
/// to the backend and returns the recorded [`ChangeList`], while dropping the
/// guard without committing rolls them back — so an error or panic
/// mid-transaction cannot strand the layer in overlay mode with orphaned staged
/// edits.
///
/// The building block several layers share to apply a namespace edit
/// all-or-nothing: open a transaction on each, stage into all, and commit them
/// only once every layer has authored cleanly (dropping the rest to roll back
/// on the first failure).
///
/// Derefs to the [`Layer`] under transaction, so it is authored through (and
/// read from) directly — reads see the staged-over-base state, with an edit
/// staged earlier in the same transaction already visible.
#[derive(derive_more::Deref, derive_more::DerefMut)]
pub struct Transaction<'a> {
    #[deref(forward)]
    #[deref_mut(forward)]
    layer: &'a mut Layer,
    committed: bool,
}

impl<'a> Transaction<'a> {
    /// Open an atomic copy-on-write transaction on `layer`: its subsequent
    /// writes stage in an overlay rather than reaching the backend until
    /// [`commit`](Self::commit) (or roll back when the guard is dropped). The
    /// `&mut Layer` borrow the guard holds prevents a second transaction on the
    /// same layer for its lifetime.
    ///
    /// The sole entry point for atomic edits; this is an associated function
    /// (not a `Layer` method) so it is not reachable through the guard's own
    /// `Deref<Target = Layer>`, which would otherwise let a transaction nest on
    /// an already-transacting layer. The assertion backs that up against the
    /// remaining deref-coercion path (`Transaction::new(&mut tx)`); a nested
    /// commit would flush the shared overlay and the outer guard could no longer
    /// roll back, so this is a hard panic rather than a debug-only check.
    pub fn new(layer: &'a mut Layer) -> Self {
        assert!(!layer.overlay, "Transaction::new on a layer already in a transaction");
        layer.overlay = true;
        Self {
            layer,
            committed: false,
        }
    }

    /// Flush the staged edits into the backend and return the recorded change
    /// list for composition invalidation, leaving overlay mode.
    pub fn commit(mut self) -> ChangeList {
        self.layer.data.commit();
        let mut changes = ChangeList::new();
        self.layer.data.base_mut().take(&mut changes);
        self.layer.overlay = false;
        self.committed = true;
        changes
    }
}

impl Drop for Transaction<'_> {
    fn drop(&mut self) {
        if !self.committed {
            self.layer.data.rollback();
            self.layer.overlay = false;
        }
    }
}

/// A single loaded layer in the composition.
pub struct Layer {
    /// Resolved, canonical identifier for this layer.
    pub identifier: String,
    /// The parsed scene description data: a recording [`EditProxy`] over the
    /// backend, wrapped in a copy-on-write [`CowData`] staging layer. The proxy
    /// sits under the overlay, so every write is recorded whether it stages
    /// (inside a [`Transaction`]) or writes through (outside
    /// one). Private
    /// so external callers reach it only through [`data`](Self::data) /
    /// [`data_mut`](Self::data_mut), keeping recording — and the authoring API's
    /// bookkeeping invariants (`primChildren`, `propertyChildren`, ancestor
    /// specifiers, …) — in force.
    data: CowData<EditProxy<LayerData>>,
    /// Whether overlay mode is on — set for the duration of a
    /// [`Transaction`]. Off (the default),
    /// [`data_mut`](Self::data_mut) writes through to the backend directly
    /// (still recorded); on, it routes through the overlay so the edits stage
    /// for atomic commit or rollback.
    overlay: bool,
}

impl Layer {
    /// Construct a layer from a resolved identifier and a backing data store.
    /// Crate-private — external callers should use [`Layer::new_anonymous`]
    /// for blank in-memory layers, or [`crate::layer::Collector`] for layers
    /// loaded from disk.
    pub(crate) fn new(identifier: impl Into<String>, data: LayerData) -> Self {
        Self {
            identifier: identifier.into(),
            data: CowData::new(EditProxy::new(data)),
            overlay: false,
        }
    }

    /// Borrow the layer's data as a read-only [`AbstractData`]. Reads see the
    /// staged-over-base view, so uncommitted edits made inside a
    /// [`Transaction`] are visible.
    pub fn data(&self) -> &dyn AbstractData {
        &self.data
    }

    /// Borrow the layer's backing data as a mutable [`AbstractData`] for
    /// authoring. Inside a [`Transaction`] this routes through
    /// the staging overlay; outside one it writes through to the backend
    /// directly — applied immediately. Either way the write passes through the
    /// recording [`EditProxy`] and is captured in the [`ChangeList`].
    pub fn data_mut(&mut self) -> &mut dyn AbstractData {
        if self.overlay {
            &mut self.data
        } else {
            self.data.base_mut()
        }
    }

    /// Whether the layer has been modified since it was loaded or last
    /// committed — either edits staged in an open transaction, or write-through
    /// edits recorded by the proxy. Mirrors C++ `SdfLayer::IsDirty`.
    pub fn is_dirty(&self) -> bool {
        !self.data.is_empty() || self.data.base().is_dirty()
    }

    /// Drop the layer's pending change record (and any staged overlay) without
    /// applying composition invalidation. Called when a layer joins a stage:
    /// its content is composed fresh by the layer-stack recompose, so a record
    /// left by prior write-through edits is redundant — and, if left in place,
    /// would be drained by (and mis-attributed to) the first transaction the
    /// stage later runs on the layer.
    pub(crate) fn discard_changes(&mut self) {
        self.data.rollback();
        self.data.base_mut().clear();
    }

    /// Remove the spec at `path` from this layer. Removing a prim also erases
    /// its descendant specs, and the leaf name is dropped from the owning prim's
    /// child-name list. Returns `Ok(true)` when a spec was present and removed,
    /// or an [`AuthoringError`] when the owning prim's child list cannot be read.
    ///
    /// The recording [`EditProxy`] captures each erase so composition can
    /// invalidate.
    pub fn remove_spec(&mut self, path: &Path) -> Result<bool, AuthoringError> {
        super::spec::remove_spec(self.data_mut(), path)
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

    /// Reading a field from the source data failed (e.g. a lazy backend could
    /// not decode an authored value while copying it).
    #[error(transparent)]
    Data(#[from] DataError),

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

    /// Whether the pseudo-root spec authors `key`, including an explicit
    /// opinion that carries an "empty"/default value.
    fn has_root_field(&self, key: FieldKey) -> bool {
        self.data.has_field(&Path::abs_root(), key.as_str())
    }

    /// Remove a metadata field from the pseudo-root spec, if that spec exists.
    /// No-op otherwise — clearing what isn't there must not materialize state.
    fn clear_root_field(&mut self, key: FieldKey) -> Result<(), AuthoringError> {
        // `erase_field` is a no-op when the pseudo-root spec is absent.
        self.data_mut().erase_field(&Path::abs_root(), key.as_str());
        Ok(())
    }

    /// Mutably view this layer's root pseudo-spec. The spec is created on
    /// first access if missing.
    pub fn pseudo_root_mut(&mut self) -> Result<PseudoRootSpecMut<'_>, AuthoringError> {
        let root = Path::abs_root();
        match self.data().spec_type(&root) {
            Some(SpecType::PseudoRoot) => {}
            Some(_) => {
                return Err(AuthoringError::InvalidPath {
                    path: root,
                    reason: "root spec exists with non-PseudoRoot SpecType",
                })
            }
            None => self.data_mut().create_spec(root, SpecType::PseudoRoot),
        }
        Ok(PseudoRootSpecMut::get(self.data_mut()).expect("just ensured a pseudo-root spec"))
    }
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

    /// A direct edit (outside a transaction) is write-through: applied
    /// immediately and visible, with no transaction to commit.
    #[test]
    fn direct_edit_is_write_through() {
        use crate::sdf::{PrimSpec, Specifier};
        let mut layer = Layer::new_anonymous("test.usda");
        PrimSpec::new(layer.data_mut(), "/World", Specifier::Def, "Xform").expect("authored");
        assert!(layer.prim(Path::from("/World")).is_some());
        assert!(layer.is_dirty());
    }

    /// A committed transaction lands its edits in the backend and returns the
    /// recorded `ChangeList`.
    #[test]
    fn transaction_commits() {
        use crate::sdf::{PrimSpec, Specifier};
        let mut layer = Layer::new_anonymous("test.usda");
        let mut tx = Transaction::new(&mut layer);
        PrimSpec::new(tx.data_mut(), "/World", Specifier::Def, "Xform").expect("authored");
        let changes = tx.commit();
        assert!(!changes.is_empty());
        assert!(layer.prim(Path::from("/World")).is_some());
    }

    /// Dropping a transaction without committing rolls every staged edit back,
    /// leaving no trace in the backend.
    #[test]
    fn transaction_rolls_back() {
        use crate::sdf::{PrimSpec, Specifier};
        let mut layer = Layer::new_anonymous("test.usda");
        {
            let mut tx = Transaction::new(&mut layer);
            PrimSpec::new(tx.data_mut(), "/A", Specifier::Def, "Xform").expect("authored");
            // Drop `tx` without committing.
        }
        assert!(layer.prim(Path::from("/A")).is_none(), "the staged edit rolled back");
        assert!(!layer.is_dirty(), "no staged edits or recorded changes remain");
    }

    /// A panic mid-transaction unwinds cleanly: the guard drops the staged edits
    /// and closes overlay mode, so the layer is reusable afterwards rather than
    /// stuck in overlay mode with orphaned staged edits.
    #[test]
    fn transaction_recovers_on_panic() {
        use crate::sdf::{PrimSpec, Specifier};
        use std::panic::{catch_unwind, AssertUnwindSafe};

        let mut layer = Layer::new_anonymous("test.usda");
        let panicked = catch_unwind(AssertUnwindSafe(|| {
            let mut tx = Transaction::new(&mut layer);
            PrimSpec::new(tx.data_mut(), "/A", Specifier::Def, "Xform").expect("authored");
            panic!("boom");
        }));
        assert!(panicked.is_err(), "the panic propagates");
        assert!(layer.prim(Path::from("/A")).is_none(), "the staged edit rolled back");
        assert!(!layer.is_dirty(), "no staged edits or recorded changes remain");

        // The layer is still usable afterwards.
        let mut tx = Transaction::new(&mut layer);
        PrimSpec::new(tx.data_mut(), "/B", Specifier::Def, "Xform").expect("authored");
        let changes = tx.commit();
        assert!(!changes.is_empty());
        assert!(layer.prim(Path::from("/B")).is_some());
    }

    /// Opening a transaction on a layer already in one is rejected — the only
    /// remaining nesting path is `Transaction::new(&mut tx)` through the guard's
    /// `DerefMut`, which the assertion catches.
    #[test]
    #[should_panic(expected = "already in a transaction")]
    fn nested_transaction_panics() {
        let mut layer = Layer::new_anonymous("test.usda");
        let mut tx = Transaction::new(&mut layer);
        let _nested = Transaction::new(&mut tx);
    }

    /// `discard_changes` drops the pending change record (so a later transaction
    /// can't drain it) while leaving the write-through content in the backend.
    #[test]
    fn discard_changes_keeps_content() {
        use crate::sdf::{PrimSpec, Specifier};

        let mut layer = Layer::new_anonymous("test.usda");
        PrimSpec::new(layer.data_mut(), "/World", Specifier::Def, "Xform").expect("authored");
        assert!(layer.is_dirty());

        layer.discard_changes();
        assert!(!layer.is_dirty(), "the pending record is dropped");
        assert!(
            layer.prim(Path::from("/World")).is_some(),
            "the authored content survives"
        );
    }

    /// Authoring layer metadata directly (no `Stage`, so no transaction) on a
    /// backend that lacks a pseudo-root spec writes through to the backend, so a
    /// follow-up read sees it. Outside a transaction `data_mut` targets the
    /// backend directly, materializing the pseudo-root there.
    #[test]
    fn metadata_on_rootless_backend() {
        let root = Path::abs_root();
        let default_prim = FieldKey::DefaultPrim.as_str();

        let mut layer = Layer::new("rootless.usda", Box::new(Data::new()));
        layer
            .set_default_prim("World")
            .expect("authors the pseudo-root write-through");
        assert!(layer.data().has_field(&root, default_prim));

        layer.clear_default_prim().expect("clears write-through");
        assert!(!layer.data().has_field(&root, default_prim));
    }
}
