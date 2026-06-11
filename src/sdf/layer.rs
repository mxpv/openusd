//! A single scene-description layer (the Rust equivalent of C++ `SdfLayer`):
//! identity + a backing [`AbstractData`] wrapped in a recording [`EditProxy`].
//! Spec authoring lives on the views ([`PrimSpec::new`](super::PrimSpec::new)
//! and friends); the layer records every edit into a [`ChangeList`].
//!
//! Cross-layer composition concerns (resolving sublayers, references,
//! payloads) live separately in [`crate::layer`].

use std::io::Cursor;
use std::sync::atomic::{AtomicU64, Ordering};

use anyhow::Result;

use super::schema::FieldKey;
use super::{
    AbstractData, AttributeSpecMut, AttributeSpecRef, ChangeList, Data, EditProxy, LayerData, Path, PrimSpecMut,
    PrimSpecRef, PseudoRootSpecMut, PseudoRootSpecRef, RelationshipSpecMut, RelationshipSpecRef, RelocateList,
    SpecError, SpecType,
};
use crate::{usda, usdc};

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

    /// Drain the changes recorded since the last call, leaving the layer's
    /// recording buffer empty. `Stage` calls this after each authoring op to
    /// feed composition invalidation.
    pub fn take_changes(&mut self) -> ChangeList {
        let mut changes = ChangeList::new();
        self.data.take(&mut changes);
        changes
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

/// Persistent format for a saved layer.
///
/// Used by [`Layer::save_as`] and [`LayerFormat::from_extension`] to make
/// the writer's format choice explicit. For `.usd` — which the AOUSD Core
/// Spec permits to be either text (§16.2) or binary (§16.3) — this lets the
/// caller pick.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LayerFormat {
    /// Text format (`.usda`).
    Usda,
    /// Binary crate format (`.usdc`).
    Usdc,
    /// Archive/package format (`.usdz`).
    Usdz,
}

impl LayerFormat {
    /// Infer the most likely format from a file extension.
    ///
    /// `.usda` → [`LayerFormat::Usda`], `.usdc` → [`LayerFormat::Usdc`],
    /// `.usdz` → [`LayerFormat::Usdz`]. The ambiguous `.usd` extension defaults
    /// to [`LayerFormat::Usdc`], matching the C++ reference implementation
    /// (`USD_WRITE_NEW_USD_FILES_AS_BINARY=true`). Unknown or missing
    /// extensions return `None`.
    pub fn from_extension(ext: &str) -> Option<Self> {
        match ext.to_ascii_lowercase().as_str() {
            "usda" => Some(Self::Usda),
            "usdc" | "usd" => Some(Self::Usdc),
            "usdz" => Some(Self::Usdz),
            _ => None,
        }
    }
}

impl Layer {
    /// Save the layer to disk, dispatching on the destination's extension.
    ///
    /// - `.usda` → text writer
    /// - `.usdc` → binary crate writer
    /// - `.usd` → binary crate writer (see below)
    /// - `.usdz` → archive containing one `.usdc` entry named after the layer's
    ///   final path component (with the extension swapped to `.usdc`)
    ///
    /// # `.usd` format choice
    ///
    /// Per the AOUSD Core Specification, `.usd` is valid for **either** text
    /// (§16.2: "stored with the .usda or .usd extension") **or** binary
    /// (§16.3: "represented with the .usdc or .usd extension"). The reader
    /// side auto-detects via magic-byte sniffing.
    ///
    /// `save()` defaults to binary for `.usd`, matching Pixar's C++ USD default
    /// (`USD_WRITE_NEW_USD_FILES_AS_BINARY=true`). To force a specific format
    /// — for example, to save text to a `.usd` path — use [`Layer::save_as`].
    pub fn save(&self, path: impl AsRef<std::path::Path>) -> Result<()> {
        let path = path.as_ref();
        let ext = path.extension().and_then(|e| e.to_str()).unwrap_or_default();
        let format = LayerFormat::from_extension(ext).ok_or_else(|| match ext {
            "" => anyhow::anyhow!("layer path {} has no extension; cannot choose format", path.display()),
            other => anyhow::anyhow!("unsupported layer extension {other:?} for save (expected usda/usdc/usd/usdz)"),
        })?;
        self.save_as(path, format)
    }

    /// Save the layer to disk using an explicit format.
    ///
    /// Unlike [`Layer::save`], the destination path's extension is not
    /// consulted — the writer strictly uses `format`. This is the path for:
    ///
    /// - Writing text to a `.usd` file: `save_as(path, LayerFormat::Usda)`
    /// - Writing binary to a `.usd` file (explicit, not just default):
    ///   `save_as(path, LayerFormat::Usdc)`
    /// - Emitting an atypical extension in general.
    ///
    /// Note that the reader's magic-byte auto-detection will still read the
    /// result correctly regardless of the filename extension.
    pub fn save_as(&self, path: impl AsRef<std::path::Path>, format: LayerFormat) -> Result<()> {
        let path = path.as_ref();
        match format {
            LayerFormat::Usda => usda::TextWriter::write_to_file(self.data(), path),
            LayerFormat::Usdc => usdc::CrateWriter::write_to_file(self.data(), path),
            LayerFormat::Usdz => {
                let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("layer");
                let mut buf = Vec::new();
                usdc::CrateWriter::write(self.data(), &mut Cursor::new(&mut buf))?;
                let mut archive = crate::usdz::ArchiveWriter::create(path)?;
                archive.add_layer(&format!("{stem}.usdc"), &buf)?;
                archive.finish()?;
                Ok(())
            }
        }
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
        self.data
            .has_field(&Path::abs_root(), FieldKey::LayerRelocates.as_str())
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
}
