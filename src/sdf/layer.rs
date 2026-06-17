//! A single scene-description layer (the Rust equivalent of C++ `SdfLayer`):
//! identity plus a backing [`AbstractData`] under a copy-on-write [`CowData`]
//! staging overlay.
//!
//! # Editing
//!
//! A layer is mutated only through [`Layer::edit`] (one layer) or [`edit_layers`]
//! (several at once, atomically): the closure authors through a [`LayerEdit`]
//! view — [`PrimSpec::new`](super::PrimSpec::new) and friends write through
//! [`LayerEdit::data_mut`] — and the whole batch commits when the closure returns
//! `Ok`, or rolls back on its error or a panic. Committing drains the overlay into
//! the backend and yields the derived [`ChangeList`] for composition
//! invalidation. [`dry_run_layers`] runs the same staging but always discards it,
//! to check an edit applies without keeping it. Reads merge staged-over-base, so
//! an in-progress edit is visible to reads inside its closure.
//!
//! # Why copy-on-write
//!
//! Staging is the primitive that makes three things the editing pipeline relies on
//! cheap and correct (the alternative is to edit the backend immediately and track
//! changes as they happen):
//!
//! - Net-effect change records. A composition invalidation should reflect the
//!   final state of an edit, not the churn along the way. Because the overlay holds
//!   the net staged state, the [`ChangeList`] derived from it at commit reflects
//!   only that final result: a field set twice records once, and a spec created
//!   then deleted within one edit records nothing — never the in-between steps an
//!   immediate-edit log would carry.
//! - Old and new values side by side. At commit the pristine base and the staged
//!   overlay both exist, so a forward log (the new values) and an inverse log (the
//!   old values, for undo) fall out directly from the diff — no need to snapshot
//!   the old value at each mutation before it is overwritten.
//! - All-or-nothing edits. A multi-step edit — or a multi-layer one, where a
//!   namespace edit must apply across several layers together — either commits
//!   whole or rolls back whole. Rolling back is just dropping the overlay, so
//!   abandoning a half-built or vetoed edit costs nothing and leaves no partial
//!   state behind.
//!
//! Cross-layer composition concerns (resolving sublayers, references, payloads)
//! live separately in [`crate::layer`].

use std::collections::HashMap;
use std::io::Cursor;
use std::sync::atomic::{AtomicU64, Ordering};

use anyhow::{Context, Result};

use super::schema::FieldKey;
use super::{
    sink, AbstractData, AttributeSpecMut, AttributeSpecRef, ChangeList, CowData, Data, DataError, LayerData, Patch,
    Path, PrimSpecMut, PrimSpecRef, PseudoRootSpecMut, PseudoRootSpecRef, RelationshipSpecMut, RelationshipSpecRef,
    RelocateList, SpecError, SpecType,
};

/// A [`sink::Id`] for a [`LayerSink`] installed on a [`Layer`].
pub type LayerSinkId = sink::Id<dyn LayerSink>;

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
    /// The parsed scene description data, under a copy-on-write [`CowData`]
    /// staging overlay. Every authoring write stages in the overlay; committing an
    /// edit derives the composition record and drains the overlay into the backend.
    /// Private so external callers reach it only through [`data`](Self::data) for
    /// reads or a [`LayerEdit`] for authoring, keeping the authoring API's
    /// bookkeeping invariants (`primChildren`, `propertyChildren`, ancestor
    /// specifiers, …) in force.
    data: CowData<LayerData>,
    /// The change record for the edit in progress, derived from the overlay at
    /// commit and handed to the layer's sinks. Owned and refilled in place each
    /// commit (reusing its buffer) rather than reallocated; empty between edits.
    changes: ChangeList,
    /// Per-layer change sinks fired at the commit seam — the low tier of the
    /// change pipeline, where a stage installs an aggregator so it stays in sync
    /// with any edit. Empty by default.
    sinks: sink::Set<dyn LayerSink>,
}

impl Layer {
    /// Construct a layer from a resolved identifier and a backing data store.
    /// Crate-private — external callers should use [`Layer::new_anonymous`]
    /// for blank in-memory layers, or [`crate::layer::Collector`] for layers
    /// loaded from disk.
    pub(crate) fn new(identifier: impl Into<String>, data: LayerData) -> Self {
        Self {
            identifier: identifier.into(),
            data: CowData::new(data),
            changes: ChangeList::new(),
            sinks: sink::Set::default(),
        }
    }

    /// Install a [`LayerSink`] fired at this layer's commit seam, returning its
    /// [`LayerSinkId`] for a later [`remove_sink`](Self::remove_sink). Any
    /// editor of this layer — a stage, the namespace editor, raw authoring —
    /// fires the sink, so an external observer sees every committed edit. A bare
    /// `Fn(&str, &ChangeList)` closure is a `LayerSink`, so this takes either a
    /// full sink type or a closure observer.
    pub fn add_sink<S: LayerSink + 'static>(&mut self, sink: S) -> LayerSinkId {
        self.sinks.add(Box::new(sink))
    }

    /// Remove the layer sink with `id`; a no-op if it was already removed.
    pub fn remove_sink(&mut self, id: LayerSinkId) {
        self.sinks.remove(id);
    }

    /// Borrow the layer's data as a read-only [`AbstractData`]. Reads see the
    /// staged-over-base view, so edits staged but not yet flushed are visible.
    pub fn data(&self) -> &dyn AbstractData {
        &self.data
    }

    /// Discard the layer's staged (uncommitted) edits, restoring the backend to
    /// its last-committed state. Already-committed content is unaffected. Private:
    /// staging and committing are driven only through [`edit`](Self::edit) /
    /// [`edit_layers`], which roll back automatically on failure, so a caller
    /// never sequences a rollback by hand.
    fn rollback(&mut self) {
        self.data.rollback();
    }

    /// Author a batch of edits as one atomic unit: run `f` against the layer's
    /// [`LayerEdit`] view, then commit on success, or roll back on `f`'s error, a
    /// sink veto, or a panic. Returns whether the edit produced a composition
    /// change. This is the only way to mutate a layer — the commit is the closing
    /// brace, not a separate call a caller can omit — so an edit is never left
    /// staged-but-uncommitted. The single-layer case of [`edit_layers`]; mirrors
    /// C++ scene description committing through `Sdf_ChangeManager`.
    ///
    /// Panics if called re-entrantly on the same layer.
    ///
    /// # Example
    ///
    /// ```
    /// use openusd::sdf::{self, PrimSpec, Specifier};
    ///
    /// let mut layer = sdf::Layer::new_anonymous("example.usda");
    /// // On success the batch commits and the change record is returned.
    /// layer
    ///     .edit(|l| {
    ///         PrimSpec::new(l.data_mut(), "/World", Specifier::Def, "Xform")?;
    ///         Ok(())
    ///     })
    ///     .expect("authored and committed");
    /// assert!(layer.prim("/World").is_some());
    ///
    /// // If the closure returns an error, the whole batch rolls back — neither
    /// // spec below survives, because the second authoring call fails.
    /// let result = layer.edit(|l| {
    ///     PrimSpec::new(l.data_mut(), "/Good", Specifier::Def, "Xform")?;
    ///     PrimSpec::new(l.data_mut(), "/Good.prop", Specifier::Def, "Xform")?; // property path: invalid for a prim
    ///     Ok(())
    /// });
    /// assert!(result.is_err());
    /// assert!(layer.prim("/Good").is_none());
    /// ```
    pub fn edit(
        &mut self,
        f: impl FnOnce(&mut LayerEdit<'_>) -> Result<(), AuthoringError>,
    ) -> Result<bool, EditError> {
        edit_layers(&mut [self], |edits| f(&mut edits[0]).map_err(EditError::from))
    }

    /// Refill this layer's change record from the staged overlay against the
    /// still-pristine base, and offer it to each sink's
    /// [`before_commit`](LayerSink::before_commit) while the overlay is intact. A
    /// sink's rejection leaves the overlay staged for the caller to roll back. Does
    /// not touch the backend.
    fn prepare_commit(&mut self) -> Result<(), sink::Error> {
        self.changes.update(&self.data);
        if !self.changes.is_empty() && !self.sinks.is_empty() {
            let change = PendingLayerChange {
                layer_identifier: &self.identifier,
                base: &**self.data.base(),
                overlay: self.data.overlay(),
                change_list: &self.changes,
            };
            self.sinks.iter().try_for_each(|sink| sink.before_commit(&change))?;
        }
        Ok(())
    }

    /// Drain the overlay into the backend — the irreversible half of a commit,
    /// run once [`prepare_commit`](Self::prepare_commit) has accepted the edit.
    /// Returns whether the edit produced any composition change. The derived
    /// record stays in [`changes`](Self::changes) for a following
    /// [`notify_after_commit`](Self::notify_after_commit).
    fn commit_data(&mut self) -> bool {
        self.data.commit();
        !self.changes.is_empty()
    }

    /// Fire each sink's [`after_commit`](LayerSink::after_commit) with the record
    /// [`prepare_commit`](Self::prepare_commit) derived. Run only after every layer
    /// in a group has committed its data, so a panicking sink cannot strand a
    /// partially committed group.
    fn notify_after_commit(&self) {
        if !self.changes.is_empty() {
            for sink in self.sinks.iter() {
                sink.after_commit(&self.identifier, &self.changes);
            }
        }
    }

    /// Whether the layer has edits staged in its overlay but not yet committed.
    /// Mirrors C++ `SdfLayer::IsDirty` for the in-flight-edit case.
    ///
    /// Conservative about staged content: any uncommitted overlay write counts,
    /// including an idempotent edit (a field re-set to the value the base already
    /// holds) whose commit would derive no composition change.
    pub fn is_dirty(&self) -> bool {
        !self.data.is_empty()
    }

    /// Commit any staged edits into the backend to keep their content, without
    /// deriving a change record or notifying sinks. Called when a layer joins a
    /// stage: its content is composed fresh by the layer-stack recompose, so a
    /// record from prior direct edits would be redundant.
    pub(crate) fn discard_changes(&mut self) {
        self.data.commit();
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

/// An error from [`Layer::edit`]: the closure's authoring error, or a sink's
/// rejection of the staged edit.
#[derive(Debug, thiserror::Error)]
pub enum EditError {
    /// The edit closure failed to author; nothing was committed.
    #[error(transparent)]
    Author(#[from] AuthoringError),

    /// A [`LayerSink`] rejected the staged edit from its
    /// [`before_commit`](LayerSink::before_commit).
    #[error(transparent)]
    Rejected(#[from] sink::Error),
}

/// An observer of a single [`Layer`]'s committed edits — the low tier of the
/// change pipeline, fired synchronously at the layer's commit seam so a sink
/// sees every edit, by any editor, the moment it lands. A [`Stage`](crate::usd::Stage)
/// installs an aggregating sink on each layer it owns to stay in sync;
/// composition-level observation lives one tier up on the stage.
///
/// Both methods default to doing nothing, so a sink implements only the phase it
/// cares about. Sinks fire in installation order.
pub trait LayerSink {
    /// Inspect a staged edit before it commits. Returning `Err` rolls the edit
    /// back: the overlay is discarded and the error surfaces to the author. The
    /// pristine base and the staged overlay are both visible, which is what lets
    /// a sink derive an inverse (undo) record here.
    fn before_commit(&self, change: &PendingLayerChange<'_>) -> Result<(), sink::Error> {
        let _ = change;
        Ok(())
    }

    /// Observe a committed edit, after the overlay has drained into the backend.
    /// `layer` is the committing layer's identifier and `changes` the record
    /// derived from the edit.
    fn after_commit(&self, layer: &str, changes: &ChangeList) {
        let _ = (layer, changes);
    }
}

/// A bare closure is a [`LayerSink`] that only observes committed edits — the
/// ergonomic "just record commits" case, installed straight through
/// [`Layer::add_sink`] with no wrapper type. `Fn` (not `FnMut`) because a sink is
/// invoked through a shared `&self`; capture interior-mutable state to accumulate.
impl<F: Fn(&str, &ChangeList)> LayerSink for F {
    fn after_commit(&self, layer: &str, changes: &ChangeList) {
        self(layer, changes);
    }
}

/// A staged, not-yet-committed edit on one layer, handed to
/// [`LayerSink::before_commit`]: the pre-edit base, the staged overlay, and the
/// derived change record — enough for a sink to derive a forward or inverse
/// [`Edit`](crate::usd::Edit) log without committing.
pub struct PendingLayerChange<'a> {
    /// Canonical identifier of the edited layer.
    pub layer_identifier: &'a str,
    /// The layer's pre-edit values (the overlay's base).
    pub base: &'a dyn AbstractData,
    /// The staged changes keyed by path — the new values, as [`Patch`]es.
    pub overlay: &'a HashMap<Path, Patch>,
    /// The composition record derived from this layer's overlay. A sink that
    /// needs to retain it past the callback clones it ([`ChangeList`] is
    /// [`Clone`]).
    pub change_list: &'a ChangeList,
}

/// Identity, persistence, and typed-view lookups. Spec authoring lives on the
/// views themselves ([`PrimSpec::new`](crate::sdf::PrimSpec::new) and friends,
/// mirroring C++ `Sdf*Spec::New`); they write through [`LayerEdit::data_mut`], so
/// every edit stages in the layer's overlay for the next flush to record.
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
    /// [`LayerEdit::pseudo_root_mut`] immediately.
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

    /// Look up an attribute spec at a property path.
    pub fn attribute(&self, path: impl Into<Path>) -> Option<AttributeSpecRef<'_>> {
        AttributeSpecRef::get(self.data(), path.into())
    }

    /// Look up a relationship spec at a property path.
    pub fn relationship(&self, path: impl Into<Path>) -> Option<RelationshipSpecRef<'_>> {
        RelationshipSpecRef::get(self.data(), path.into())
    }

    /// View this layer's root pseudo-spec, which carries layer-wide metadata
    /// (`defaultPrim`, `subLayers`, time codes, …).
    pub fn pseudo_root(&self) -> Option<PseudoRootSpecRef<'_>> {
        PseudoRootSpecRef::get(self.data())
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

    /// The layer's `startTimeCode`, or `0.0` when unauthored. Mirrors C++
    /// `SdfLayer::GetStartTimeCode`.
    pub fn start_time_code(&self) -> f64 {
        self.pseudo_root()
            .and_then(|root| root.start_time_code())
            .unwrap_or(0.0)
    }

    /// Whether this layer authors a `startTimeCode` opinion. Mirrors C++
    /// `SdfLayer::HasStartTimeCode`.
    pub fn has_start_time_code(&self) -> bool {
        self.has_root_field(FieldKey::StartTimeCode)
    }

    /// The layer's `endTimeCode`, or `0.0` when unauthored. Mirrors C++
    /// `SdfLayer::GetEndTimeCode`.
    pub fn end_time_code(&self) -> f64 {
        self.pseudo_root().and_then(|root| root.end_time_code()).unwrap_or(0.0)
    }

    /// Whether this layer authors an `endTimeCode` opinion. Mirrors C++
    /// `SdfLayer::HasEndTimeCode`.
    pub fn has_end_time_code(&self) -> bool {
        self.has_root_field(FieldKey::EndTimeCode)
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

    /// Whether this layer authors a `timeCodesPerSecond` opinion. Mirrors C++
    /// `SdfLayer::HasTimeCodesPerSecond`.
    pub fn has_time_codes_per_second(&self) -> bool {
        self.has_root_field(FieldKey::TimeCodesPerSecond)
    }

    /// The layer's `framesPerSecond`, or `24.0` when unauthored. Mirrors C++
    /// `SdfLayer::GetFramesPerSecond`.
    pub fn frames_per_second(&self) -> f64 {
        self.pseudo_root()
            .and_then(|root| root.frames_per_second())
            .unwrap_or(24.0)
    }

    /// Whether this layer authors a `framesPerSecond` opinion. Mirrors C++
    /// `SdfLayer::HasFramesPerSecond`.
    pub fn has_frames_per_second(&self) -> bool {
        self.has_root_field(FieldKey::FramesPerSecond)
    }

    /// The layer's `framePrecision`, or `3` when unauthored. Mirrors C++
    /// `SdfLayer::GetFramePrecision`.
    pub fn frame_precision(&self) -> i32 {
        self.pseudo_root().and_then(|root| root.frame_precision()).unwrap_or(3)
    }

    /// Whether this layer authors a `framePrecision` opinion. Mirrors C++
    /// `SdfLayer::HasFramePrecision`.
    pub fn has_frame_precision(&self) -> bool {
        self.has_root_field(FieldKey::FramePrecision)
    }

    /// Whether the pseudo-root spec authors `key`, including an explicit
    /// opinion that carries an "empty"/default value.
    fn has_root_field(&self, key: FieldKey) -> bool {
        self.data.has_field(&Path::abs_root(), key.as_str())
    }
}

/// The authoring view of a [`Layer`] handed to an [`edit`](Layer::edit) /
/// [`edit_layers`] closure — the only surface through which a layer is mutated.
///
/// Derefs to the [`Layer`] for reads, and exposes the layer's authoring
/// operations directly. A layer's `commit` and `rollback` are deliberately absent:
/// the edit commits when the closure returns and rolls back on its error or a
/// panic, so an edit can never be left staged-but-uncommitted, and a multi-layer
/// edit stays atomic across its layers.
pub struct LayerEdit<'a> {
    layer: &'a mut Layer,
}

impl std::ops::Deref for LayerEdit<'_> {
    type Target = Layer;

    fn deref(&self) -> &Layer {
        &*self.layer
    }
}

impl LayerEdit<'_> {
    /// Borrow the layer's backing data mutably for authoring; the write stages in
    /// the copy-on-write overlay and commits with the enclosing edit. The typed
    /// spec constructors ([`PrimSpec::new`](crate::sdf::PrimSpec::new) and friends)
    /// write through this.
    pub fn data_mut(&mut self) -> &mut dyn AbstractData {
        &mut self.layer.data
    }

    /// Remove the spec at `path`. Removing a prim also erases its descendant specs
    /// and drops the leaf name from the owning prim's child-name list. Returns
    /// `Ok(true)` when a spec was present and removed.
    pub fn remove_spec(&mut self, path: &Path) -> Result<bool, AuthoringError> {
        super::spec::remove_spec(self.data_mut(), path)
    }

    /// Mutably look up the prim spec at `path`.
    pub fn prim_mut(&mut self, path: impl Into<Path>) -> Option<PrimSpecMut<'_>> {
        PrimSpecMut::get(self.data_mut(), path.into())
    }

    /// Mutably look up the attribute spec at a property path.
    pub fn attribute_mut(&mut self, path: impl Into<Path>) -> Option<AttributeSpecMut<'_>> {
        AttributeSpecMut::get(self.data_mut(), path.into())
    }

    /// Mutably look up the relationship spec at a property path.
    pub fn relationship_mut(&mut self, path: impl Into<Path>) -> Option<RelationshipSpecMut<'_>> {
        RelationshipSpecMut::get(self.data_mut(), path.into())
    }

    /// Mutably view the root pseudo-spec, which carries layer-wide metadata
    /// (`defaultPrim`, `subLayers`, time codes, …). The spec is created on first
    /// access if missing.
    pub fn pseudo_root_mut(&mut self) -> Result<PseudoRootSpecMut<'_>, AuthoringError> {
        let root = Path::abs_root();
        match self.layer.data().spec_type(&root) {
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

    /// Set the layer's `defaultPrim` metadata to `name`, a USD identifier or
    /// nested prim path without a leading `/` (e.g. `"World/Char"`). Mirrors C++
    /// `SdfLayer::SetDefaultPrim`, validating the name; the spec-tier
    /// [`PseudoRootSpecMut::set_default_prim`] is the unvalidated escape hatch.
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

    /// Remove the layer's `defaultPrim` metadata. No-op when no pseudo-root spec
    /// exists.
    pub fn clear_default_prim(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::DefaultPrim)
    }

    /// Set the layer's entire list of namespace relocations. An empty list authors
    /// an explicit "no relocates" opinion; use [`clear_relocates`](Self::clear_relocates)
    /// to remove the opinion entirely.
    pub fn set_relocates(&mut self, relocates: RelocateList) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_relocates(relocates);
        Ok(())
    }

    /// Clear the layer's `relocates` opinion. No-op when no pseudo-root spec exists.
    pub fn clear_relocates(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::LayerRelocates)
    }

    /// Set the layer's `startTimeCode`.
    pub fn set_start_time_code(&mut self, time: f64) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_start_time_code(time);
        Ok(())
    }

    /// Clear the layer's `startTimeCode` opinion. No-op when no pseudo-root spec exists.
    pub fn clear_start_time_code(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::StartTimeCode)
    }

    /// Set the layer's `endTimeCode`.
    pub fn set_end_time_code(&mut self, time: f64) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_end_time_code(time);
        Ok(())
    }

    /// Clear the layer's `endTimeCode` opinion. No-op when no pseudo-root spec exists.
    pub fn clear_end_time_code(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::EndTimeCode)
    }

    /// Set the layer's `timeCodesPerSecond`.
    pub fn set_time_codes_per_second(&mut self, rate: f64) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_time_codes_per_second(rate);
        Ok(())
    }

    /// Clear the layer's `timeCodesPerSecond` opinion. No-op when no pseudo-root spec exists.
    pub fn clear_time_codes_per_second(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::TimeCodesPerSecond)
    }

    /// Set the layer's `framesPerSecond`.
    pub fn set_frames_per_second(&mut self, rate: f64) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_frames_per_second(rate);
        Ok(())
    }

    /// Clear the layer's `framesPerSecond` opinion. No-op when no pseudo-root spec exists.
    pub fn clear_frames_per_second(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::FramesPerSecond)
    }

    /// Set the layer's `framePrecision`.
    pub fn set_frame_precision(&mut self, precision: i32) -> Result<(), AuthoringError> {
        self.pseudo_root_mut()?.set_frame_precision(precision);
        Ok(())
    }

    /// Clear the layer's `framePrecision` opinion. No-op when no pseudo-root spec exists.
    pub fn clear_frame_precision(&mut self) -> Result<(), AuthoringError> {
        self.clear_root_field(FieldKey::FramePrecision)
    }

    /// Remove a metadata field from the pseudo-root spec, if that spec exists. No-op
    /// otherwise — clearing what isn't there must not materialize state.
    fn clear_root_field(&mut self, key: FieldKey) -> Result<(), AuthoringError> {
        // `erase_field` is a no-op when the pseudo-root spec is absent.
        self.data_mut().erase_field(&Path::abs_root(), key.as_str());
        Ok(())
    }
}

impl std::fmt::Debug for Layer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Layer")
            .field("identifier", &self.identifier)
            .finish_non_exhaustive()
    }
}

/// Author across several layers as one atomic transaction: run `f` to stage
/// edits into every layer through its [`LayerEdit`] view, then commit them
/// together. Commit is two-phase — every layer's
/// [`before_commit`](LayerSink::before_commit) runs first, and only once all
/// accept does any layer's overlay drain into its backend — so a single vetoing
/// sink, an authoring error from `f`, or a panic rolls every layer back, leaving
/// none partially applied. Returns whether any layer's edit produced a
/// composition change. Each committed layer fires its sinks, so the change records
/// reach a stage through its aggregator rather than through this return.
///
/// [`Layer::edit`] is the single-layer case of this.
pub fn edit_layers<E: From<sink::Error>>(
    layers: &mut [&mut Layer],
    f: impl FnOnce(&mut [LayerEdit<'_>]) -> Result<(), E>,
) -> Result<bool, E> {
    let mut guard = GroupEditGuard {
        layers,
        committed: false,
    };
    {
        let mut edits: Vec<LayerEdit<'_>> = guard.layers.iter_mut().map(|layer| LayerEdit { layer }).collect();
        f(&mut edits)?;
        // `edits` drops at the block end, releasing the per-layer borrows for the
        // commit phase below.
    }
    // Phase 1: refill each layer's record and offer it to that layer's
    // `before_commit`; a veto aborts before any layer commits.
    for layer in guard.layers.iter_mut() {
        layer.prepare_commit()?;
    }
    // Phase 2: every layer accepted, so drain each overlay into its backend. Commit
    // all layers before notifying any, so the whole group's data lands even if a
    // later `after_commit` panics.
    let mut changed = false;
    for layer in guard.layers.iter_mut() {
        changed |= layer.commit_data();
    }
    // The group is committed, so the guard's drop leaves every overlay in place.
    guard.committed = true;
    // Phase 3: deliver each layer's `after_commit`. A panic here interrupts only
    // notification — the group's data is already committed.
    for layer in guard.layers.iter() {
        layer.notify_after_commit();
    }
    Ok(changed)
}

/// Stage edits across `layers` to verify they apply, then discard them all — the
/// dry-run counterpart of [`edit_layers`]. Returns `f`'s authoring result while
/// committing nothing and firing no sink, so a caller can check that an edit is
/// valid (e.g. a namespace edit's `can_apply`) without mutating the layers or
/// notifying observers.
pub fn dry_run_layers<E>(
    layers: &mut [&mut Layer],
    f: impl FnOnce(&mut [LayerEdit<'_>]) -> Result<(), E>,
) -> Result<(), E> {
    // `committed` stays false, so the guard rolls every layer back on the way out,
    // whether `f` succeeds or fails — a dry run leaves no staged state behind.
    let guard = GroupEditGuard {
        layers,
        committed: false,
    };
    let mut edits: Vec<LayerEdit<'_>> = guard.layers.iter_mut().map(|layer| LayerEdit { layer }).collect();
    f(&mut edits)
}

/// Rolls every layer in an [`edit_layers`] group back unless the group commits —
/// on an authoring error, a sink veto, or a panic — so a failed multi-layer edit
/// strands no layer with a half-applied overlay.
struct GroupEditGuard<'a, 'b> {
    layers: &'b mut [&'a mut Layer],
    committed: bool,
}

impl Drop for GroupEditGuard<'_, '_> {
    fn drop(&mut self) {
        if self.committed {
            return;
        }
        for layer in self.layers.iter_mut() {
            layer.rollback();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Author through the layer's `edit` API and commit, for tests that build a
    /// layer's content or metadata directly.
    fn edit_layer(layer: &mut Layer, f: impl FnOnce(&mut LayerEdit<'_>)) {
        layer
            .edit(|e| {
                f(e);
                Ok(())
            })
            .expect("authored");
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
        edit_layer(&mut layer, |e| {
            e.set_relocates(pairs.clone()).unwrap();
        });

        assert!(layer.has_relocates());
        assert_eq!(layer.relocates(), pairs);
    }

    /// An explicit empty list is still an opinion (`HasRelocates` is true), while
    /// `clear_relocates` removes the opinion entirely.
    #[test]
    fn empty_opinion_vs_cleared() {
        let mut layer = Layer::new_anonymous("test.usda");

        edit_layer(&mut layer, |e| {
            e.set_relocates(RelocateList::new()).unwrap();
        });
        assert!(layer.has_relocates());
        assert!(layer.relocates().is_empty());

        edit_layer(&mut layer, |e| {
            e.clear_relocates().unwrap();
        });
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

        edit_layer(&mut layer, |e| {
            e.set_start_time_code(1.0).unwrap();
            e.set_end_time_code(48.0).unwrap();
            e.set_frame_precision(6).unwrap();
        });

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

        edit_layer(&mut layer, |e| {
            e.set_frames_per_second(30.0).unwrap();
        });
        assert_eq!(layer.time_codes_per_second(), 30.0);

        edit_layer(&mut layer, |e| {
            e.set_time_codes_per_second(48.0).unwrap();
        });
        assert_eq!(layer.time_codes_per_second(), 48.0);
    }

    /// `clear_*` removes the opinion so `has_*` reports false and the getter
    /// returns the unauthored default again.
    #[test]
    fn clear_time_code() {
        let mut layer = Layer::new_anonymous("test.usda");
        edit_layer(&mut layer, |e| {
            e.set_start_time_code(5.0).unwrap();
        });
        assert!(layer.has_start_time_code());

        edit_layer(&mut layer, |e| {
            e.clear_start_time_code().unwrap();
        });
        assert!(!layer.has_start_time_code());
        assert_eq!(layer.start_time_code(), 0.0);
    }

    /// `edit` commits the batch and returns the recorded `ChangeList`.
    #[test]
    fn edit_commits() {
        use crate::sdf::{PrimSpec, Specifier};
        let mut layer = Layer::new_anonymous("test.usda");
        let changed = layer
            .edit(|l| {
                PrimSpec::new(l.data_mut(), "/World", Specifier::Def, "Xform")?;
                Ok(())
            })
            .expect("no error or veto");
        assert!(changed);
        assert!(layer.prim(Path::from("/World")).is_some());
    }

    /// `edit` rolls the batch back when the closure returns an error, leaving the
    /// layer untouched and reusable.
    #[test]
    fn edit_rolls_back_on_error() {
        use crate::sdf::{PrimSpec, Specifier};
        let mut layer = Layer::new_anonymous("test.usda");
        let result: Result<bool, EditError> = layer.edit(|l| {
            PrimSpec::new(l.data_mut(), "/A", Specifier::Def, "Xform")?;
            Err(AuthoringError::InvalidPath {
                path: Path::abs_root(),
                reason: "test",
            })
        });
        assert!(result.is_err());
        assert!(layer.prim(Path::from("/A")).is_none(), "the staged edit rolled back");
        assert!(!layer.is_dirty());
    }

    /// A panic mid-`edit` unwinds cleanly: the guard rolls the staged edits back,
    /// so the layer is reusable afterwards.
    #[test]
    fn edit_recovers_on_panic() {
        use crate::sdf::{PrimSpec, Specifier};
        use std::panic::{catch_unwind, AssertUnwindSafe};

        let mut layer = Layer::new_anonymous("test.usda");
        let panicked = catch_unwind(AssertUnwindSafe(|| {
            let _: Result<bool, EditError> = layer.edit(|l| {
                PrimSpec::new(l.data_mut(), "/A", Specifier::Def, "Xform").expect("authored");
                panic!("boom");
            });
        }));
        assert!(panicked.is_err(), "the panic propagates");
        assert!(layer.prim(Path::from("/A")).is_none(), "the staged edit rolled back");
        assert!(!layer.is_dirty(), "no staged edits or recorded changes remain");

        // The layer is still usable afterwards.
        let changed = layer
            .edit(|l| {
                PrimSpec::new(l.data_mut(), "/B", Specifier::Def, "Xform")?;
                Ok(())
            })
            .expect("no error");
        assert!(changed);
        assert!(layer.prim(Path::from("/B")).is_some());
    }

    /// A panicking `after_commit` cannot strand a partially committed group:
    /// `edit_layers` commits every layer's data before notifying any sink, so both
    /// layers land even when one's `after_commit` unwinds.
    #[test]
    fn group_commit_atomic_on_panic() {
        use crate::sdf::{PrimSpec, Specifier};
        use std::panic::{catch_unwind, AssertUnwindSafe};

        let mut a = Layer::new_anonymous("a.usda");
        let mut b = Layer::new_anonymous("b.usda");
        a.add_sink(|_: &str, _: &ChangeList| panic!("boom"));

        let panicked = catch_unwind(AssertUnwindSafe(|| {
            let _ = edit_layers(&mut [&mut a, &mut b], |edits| {
                PrimSpec::new(edits[0].data_mut(), "/A", Specifier::Def, "Xform").expect("authored a");
                PrimSpec::new(edits[1].data_mut(), "/B", Specifier::Def, "Xform").expect("authored b");
                Ok::<(), EditError>(())
            });
        }));
        assert!(panicked.is_err(), "the after_commit panic propagates");
        assert!(
            a.prim(Path::from("/A")).is_some(),
            "layer a committed despite the panic"
        );
        assert!(
            b.prim(Path::from("/B")).is_some(),
            "layer b committed despite the panic"
        );
    }

    /// `discard_changes` keeps committed content in the backend and leaves the
    /// layer non-dirty, so a layer joining a stage is composed fresh with no stale
    /// change record.
    #[test]
    fn discard_changes_keeps_content() {
        use crate::sdf::{PrimSpec, Specifier};

        let mut layer = Layer::new_anonymous("test.usda");
        edit_layer(&mut layer, |e| {
            PrimSpec::new(e.data_mut(), "/World", Specifier::Def, "Xform").unwrap();
        });

        layer.discard_changes();
        assert!(!layer.is_dirty());
        assert!(
            layer.prim(Path::from("/World")).is_some(),
            "the authored content survives"
        );
    }

    /// Authoring layer metadata on a backend that lacks a pseudo-root spec
    /// materializes the pseudo-root, so a follow-up read sees the field; clearing
    /// the opinion removes it again.
    #[test]
    fn metadata_on_rootless_backend() {
        let root = Path::abs_root();
        let default_prim = FieldKey::DefaultPrim.as_str();

        let mut layer = Layer::new("rootless.usda", Box::new(Data::new()));
        edit_layer(&mut layer, |e| {
            e.set_default_prim("World").unwrap();
        });
        assert!(layer.data().has_field(&root, default_prim));

        edit_layer(&mut layer, |e| {
            e.clear_default_prim().unwrap();
        });
        assert!(!layer.data().has_field(&root, default_prim));
    }

    /// A recording [`LayerSink`] for the tests below.
    #[derive(Default)]
    struct Recorder {
        before: std::cell::Cell<u32>,
        after: std::cell::Cell<u32>,
        veto: bool,
    }

    impl LayerSink for std::rc::Rc<Recorder> {
        fn before_commit(&self, _change: &PendingLayerChange<'_>) -> Result<(), sink::Error> {
            self.before.set(self.before.get() + 1);
            if self.veto {
                return Err(sink::Error::new("vetoed"));
            }
            Ok(())
        }
        fn after_commit(&self, _layer: &str, _changes: &ChangeList) {
            self.after.set(self.after.get() + 1);
        }
    }

    /// A committed edit fires the layer sink's `before_commit` then
    /// `after_commit` once, with the edit landed.
    #[test]
    fn layer_sink_fires() {
        use crate::sdf::{PrimSpec, Specifier};
        let mut layer = Layer::new_anonymous("test.usda");
        let rec = std::rc::Rc::new(Recorder::default());
        layer.add_sink(rec.clone());

        layer
            .edit(|l| {
                PrimSpec::new(l.data_mut(), "/World", Specifier::Def, "Xform")?;
                Ok(())
            })
            .expect("sink accepts");

        assert_eq!((rec.before.get(), rec.after.get()), (1, 1));
        assert!(layer.prim(Path::from("/World")).is_some());
    }

    /// A `before_commit` rejection rolls the edit back: `after_commit` never
    /// fires and the backend is untouched.
    #[test]
    fn layer_sink_veto_rolls_back() {
        use crate::sdf::{PrimSpec, Specifier};
        let mut layer = Layer::new_anonymous("test.usda");
        let rec = std::rc::Rc::new(Recorder {
            veto: true,
            ..Default::default()
        });
        layer.add_sink(rec.clone());

        let result = layer.edit(|l| {
            PrimSpec::new(l.data_mut(), "/World", Specifier::Def, "Xform")?;
            Ok(())
        });
        assert!(matches!(result, Err(EditError::Rejected(_))), "the sink vetoes");

        assert_eq!((rec.before.get(), rec.after.get()), (1, 0), "after_commit never fired");
        assert!(layer.prim(Path::from("/World")).is_none(), "the edit rolled back");
        assert!(!layer.is_dirty());
    }

    /// A removed sink no longer fires.
    #[test]
    fn layer_sink_removed() {
        use crate::sdf::{PrimSpec, Specifier};
        let mut layer = Layer::new_anonymous("test.usda");
        let rec = std::rc::Rc::new(Recorder::default());
        let id = layer.add_sink(rec.clone());
        layer.remove_sink(id);

        layer
            .edit(|l| {
                PrimSpec::new(l.data_mut(), "/World", Specifier::Def, "Xform")?;
                Ok(())
            })
            .expect("no sink");
        assert_eq!((rec.before.get(), rec.after.get()), (0, 0));
    }
}
