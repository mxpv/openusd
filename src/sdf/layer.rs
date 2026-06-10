//! A single scene-description layer (the Rust equivalent of C++ `SdfLayer`):
//! identity + a backing [`AbstractData`] + an authoring surface that mirrors
//! `SdfLayer::CreatePrimSpec` and friends.
//!
//! Cross-layer composition concerns (resolving sublayers, references,
//! payloads) live separately in [`crate::layer`].

use std::borrow::Cow;
use std::io::Cursor;
use std::sync::atomic::{AtomicU64, Ordering};

use anyhow::Result;

use super::schema::{ChildrenKey, FieldKey};
use super::{
    AbstractData, AttributeSpecMut, AttributeSpecRef, Data, LayerData, Path, PathComponent, PrimSpecMut, PrimSpecRef,
    PseudoRootSpecMut, PseudoRootSpecRef, RelationshipSpecMut, RelationshipSpecRef, RelocateList, SpecError, SpecType,
    Specifier, Value, Variability,
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
    /// The parsed scene description data. Private so external
    /// callers cannot swap the backing box or write to it directly,
    /// bypassing the authoring API's bookkeeping invariants
    /// (`primChildren`, `propertyChildren`, ancestor specifiers, …).
    data: LayerData,
}

impl Layer {
    /// Construct a layer from a resolved identifier and a backing data store.
    /// Crate-private — external callers should use [`Layer::new_anonymous`]
    /// for blank in-memory layers, or [`crate::layer::Collector`] for layers
    /// loaded from disk.
    pub(crate) fn new(identifier: impl Into<String>, data: LayerData) -> Self {
        Self {
            identifier: identifier.into(),
            data,
        }
    }

    /// Borrow the underlying [`AbstractData`] backend for read-only inspection.
    /// Callers that need typed views should prefer [`Layer::prim`] /
    /// [`Layer::attribute`] / etc.
    pub fn data(&self) -> &dyn AbstractData {
        self.data.as_ref()
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
            LayerFormat::Usda => usda::TextWriter::write_to_file(self.data.as_ref(), path),
            LayerFormat::Usdc => usdc::CrateWriter::write_to_file(self.data.as_ref(), path),
            LayerFormat::Usdz => {
                let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("layer");
                let mut buf = Vec::new();
                usdc::CrateWriter::write(self.data.as_ref(), &mut Cursor::new(&mut buf))?;
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

/// Authoring methods. Mirrors `SdfLayer`'s authoring surface:
/// [`Layer::create_prim`], [`Layer::override_prim`], [`Layer::create_attribute`],
/// and [`Layer::create_relationship`] parallel `SdfCreatePrimInLayer` /
/// `SdfAttributeSpec::New` / `SdfRelationshipSpec::New`. `primChildren` and
/// `propertyChildren` ordering is maintained automatically: ancestor prim specs
/// are auto-created as `over` when missing.
///
/// The typed-view lookups ([`Layer::prim`], [`Layer::attribute`],
/// [`Layer::relationship`], [`Layer::pseudo_root`]) and all authoring operate
/// through the [`AbstractData`] field interface, so they work uniformly on any
/// backend — in-memory [`Data`] or a file-loaded reader — matching C++
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

    /// Create or upgrade a prim spec at `path` with the given specifier and
    /// `typeName`. Any missing ancestor specs are created as `over` and the
    /// parent's `primChildren` is updated.
    ///
    /// An empty `type_name` leaves `typeName` unauthored, matching C++
    /// `SdfCreatePrimInLayer` followed by a no-op `SetTypeName(TfToken())`.
    /// Mirrors C++ `SdfCreatePrimInLayer` + `SetSpecifier` + `SetTypeName`.
    pub fn create_prim(
        &mut self,
        path: impl Into<Path>,
        specifier: Specifier,
        type_name: impl Into<String>,
    ) -> Result<PrimSpecMut<'_>, AuthoringError> {
        let path: Path = path.into();
        let type_name: String = type_name.into();

        require_prim_leaf(&path)?;
        let data = self.data_mut();
        ensure_prim_chain(data, &path)?;

        data.set_field(&path, FieldKey::Specifier.as_str(), Value::Specifier(specifier));
        if !type_name.is_empty() {
            data.set_field(&path, FieldKey::TypeName.as_str(), Value::token(type_name));
        }

        Ok(PrimSpecMut::get(data, path).expect("ensure_prim_chain created a prim spec"))
    }

    /// Ensure a prim spec exists at `path` with specifier `over`. Existing
    /// `def` / `class` specs are left as-is; this only creates missing ones.
    /// Ancestor specs are auto-created as `over` as well.
    ///
    /// Mirrors C++ `UsdStage::OverridePrim` semantics at the layer tier.
    pub fn override_prim(&mut self, path: impl Into<Path>) -> Result<PrimSpecMut<'_>, AuthoringError> {
        let path: Path = path.into();

        require_prim_leaf(&path)?;
        let data = self.data_mut();
        ensure_prim_chain(data, &path)?;

        Ok(PrimSpecMut::get(data, path).expect("ensure_prim_chain created a prim spec"))
    }

    /// Ensure an `over` prim spec exists at `path` (and for every missing
    /// ancestor), returning the paths that were newly created so the caller can
    /// record [`ChangeList::add_inert_prims`](crate::sdf::ChangeList::add_inert_prims)
    /// entries for them. Equivalent to [`override_prim`](Self::override_prim)
    /// paired with [`missing_prim_chain_inclusive`](Self::missing_prim_chain_inclusive),
    /// computed before the specs exist.
    pub fn ensure_prim_over(&mut self, path: impl Into<Path>) -> Result<Vec<Path>, AuthoringError> {
        let path: Path = path.into();
        let created = self.missing_prim_chain_inclusive(&path);
        self.override_prim(path)?;
        Ok(created)
    }

    /// Create an attribute spec at `path` (a property path like
    /// `/World/Mesh.points`). The owning prim is auto-created as `over` if
    /// missing, and the prim's `propertyChildren` is updated.
    ///
    /// `typeName` and `variability` are construction parameters (matching
    /// C++ `SdfAttributeSpec::New`); there is no post-hoc setter for either.
    pub fn create_attribute(
        &mut self,
        path: impl Into<Path>,
        type_name: impl Into<String>,
        variability: Variability,
        custom: bool,
    ) -> Result<AttributeSpecMut<'_>, AuthoringError> {
        let path: Path = path.into();
        let type_name: String = type_name.into();

        let (prim_path, property_name) = split_property_path(&path)?;
        let data = self.data_mut();
        require_spec_type_or_absent(data, &path, SpecType::Attribute)?;
        validate_token_vec(data, &prim_path, ChildrenKey::PropertyChildren)?;
        ensure_prim_chain(data, &prim_path)?;

        add_to_token_vec(data, &prim_path, ChildrenKey::PropertyChildren, &property_name)?;

        if !data.has_spec(&path) {
            data.create_spec(path.clone(), SpecType::Attribute);
        }

        data.set_field(&path, FieldKey::TypeName.as_str(), Value::token(type_name));

        if variability != Variability::Varying {
            data.set_field(&path, FieldKey::Variability.as_str(), Value::Variability(variability));
        } else {
            data.erase_field(&path, FieldKey::Variability.as_str());
        }

        if custom {
            data.set_field(&path, FieldKey::Custom.as_str(), Value::Bool(true));
        } else {
            data.erase_field(&path, FieldKey::Custom.as_str());
        }

        Ok(AttributeSpecMut::get(data, path).expect("type guaranteed by require_spec_type_or_absent"))
    }

    /// Create a relationship spec at `path`. The owning prim is auto-created
    /// as `over` if missing, and the prim's `propertyChildren` is updated.
    ///
    /// `variability` and `custom` are construction parameters, matching C++
    /// `SdfCreateRelationshipInLayer`.
    pub fn create_relationship(
        &mut self,
        path: impl Into<Path>,
        variability: Variability,
        custom: bool,
    ) -> Result<RelationshipSpecMut<'_>, AuthoringError> {
        let path: Path = path.into();

        let (prim_path, property_name) = split_property_path(&path)?;
        let data = self.data_mut();
        require_spec_type_or_absent(data, &path, SpecType::Relationship)?;
        validate_token_vec(data, &prim_path, ChildrenKey::PropertyChildren)?;
        ensure_prim_chain(data, &prim_path)?;

        add_to_token_vec(data, &prim_path, ChildrenKey::PropertyChildren, &property_name)?;

        if !data.has_spec(&path) {
            data.create_spec(path.clone(), SpecType::Relationship);
        }

        if variability != Variability::Varying {
            data.set_field(&path, FieldKey::Variability.as_str(), Value::Variability(variability));
        } else {
            data.erase_field(&path, FieldKey::Variability.as_str());
        }

        if custom {
            data.set_field(&path, FieldKey::Custom.as_str(), Value::Bool(true));
        } else {
            data.erase_field(&path, FieldKey::Custom.as_str());
        }

        Ok(RelationshipSpecMut::get(data, path).expect("type guaranteed by require_spec_type_or_absent"))
    }

    /// Look up a prim spec at `path`. Returns `None` if no spec exists or the
    /// spec is not a prim.
    pub fn prim(&self, path: impl Into<Path>) -> Option<PrimSpecRef<'_>> {
        PrimSpecRef::get(self.data.as_ref(), path.into())
    }

    /// Mutably look up a prim spec at `path`.
    pub fn prim_mut(&mut self, path: impl Into<Path>) -> Option<PrimSpecMut<'_>> {
        PrimSpecMut::get(self.data.as_mut(), path.into())
    }

    /// Look up an attribute spec at a property path.
    pub fn attribute(&self, path: impl Into<Path>) -> Option<AttributeSpecRef<'_>> {
        AttributeSpecRef::get(self.data.as_ref(), path.into())
    }

    /// Mutably look up an attribute spec at a property path.
    pub fn attribute_mut(&mut self, path: impl Into<Path>) -> Option<AttributeSpecMut<'_>> {
        AttributeSpecMut::get(self.data.as_mut(), path.into())
    }

    /// Look up a relationship spec at a property path.
    pub fn relationship(&self, path: impl Into<Path>) -> Option<RelationshipSpecRef<'_>> {
        RelationshipSpecRef::get(self.data.as_ref(), path.into())
    }

    /// Mutably look up a relationship spec at a property path.
    pub fn relationship_mut(&mut self, path: impl Into<Path>) -> Option<RelationshipSpecMut<'_>> {
        RelationshipSpecMut::get(self.data.as_mut(), path.into())
    }

    /// View this layer's root pseudo-spec, which carries layer-wide metadata
    /// (`defaultPrim`, `subLayers`, time codes, …).
    pub fn pseudo_root(&self) -> Option<PseudoRootSpecRef<'_>> {
        PseudoRootSpecRef::get(self.data.as_ref())
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

    /// Paths along `target`'s namespace chain (strict ancestors, root → leaf,
    /// excluding `/`) that lack a spec on this layer and will therefore be
    /// auto-created as `over` specs when authoring at `target` via
    /// [`Layer::create_prim`] / [`Layer::override_prim`].
    ///
    /// Surfaces the same set of paths [`ensure_prim_chain`] (private) would
    /// touch, so authoring callers can record cache-invalidation entries
    /// for each auto-created ancestor without re-deriving the walk.
    pub fn missing_prim_ancestors(&self, target: &Path) -> Vec<Path> {
        match target.parent() {
            Some(p) => self.missing_prim_chain_inclusive(&p),
            None => Vec::new(),
        }
    }

    /// `target` itself plus all its ancestors (root → leaf, excluding `/`)
    /// that lack a spec on this layer. Mirrors the set
    /// [`Layer::create_attribute`] / [`Layer::create_relationship`] will
    /// auto-create — the owning prim may itself be missing, in which case
    /// both the leaf and its ancestors get over specs.
    pub fn missing_prim_chain_inclusive(&self, target: &Path) -> Vec<Path> {
        // `namespace_chain` mirrors exactly what `ensure_prim_chain` will
        // create, including variant set / variant scaffolding for variant
        // paths. An unparseable target yields no entries — the subsequent
        // authoring call surfaces the error.
        namespace_chain(target)
            .map(|chain| {
                chain
                    .into_iter()
                    .map(|elem| elem.path)
                    .filter(|p| !self.data.has_spec(p))
                    .collect()
            })
            .unwrap_or_default()
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
        Ok(PseudoRootSpecMut::get(self.data.as_mut()).expect("just ensured a pseudo-root spec"))
    }

    /// Borrow the layer's backing data as a mutable [`AbstractData`] for
    /// authoring. Every backend is writable (the field-level write API lives on
    /// the trait), so this is infallible — used by higher-level authoring
    /// helpers (e.g. [`crate::usd::Prim`]) to reach the write surface.
    pub(crate) fn data_mut(&mut self) -> &mut dyn AbstractData {
        self.data.as_mut()
    }
}

impl std::fmt::Debug for Layer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Layer")
            .field("identifier", &self.identifier)
            .finish_non_exhaustive()
    }
}

// =========================================================================
// Authoring helpers
// =========================================================================

/// Ensure prim specs exist for every ancestor of `target` and for `target`
/// itself, creating missing ones as `over`. Updates each parent's
/// `primChildren` to include the next name along the chain. Idempotent.
/// `target` must be an absolute, non-root, non-property prim path;
/// callers should validate via [`require_prim_path`] first.
///
/// Errors with [`AuthoringError::InvalidPath`] if any ancestor or `target`
/// path already holds a spec of a non-prim type — stamping `primChildren`
/// onto an Attribute or Relationship spec would corrupt the layer.
//
// TODO(perf): the Stage tier rebuilds this chain per authoring op —
// `missing_prim_ancestors` / `missing_prim_chain_inclusive` walk
// `namespace_chain` to report auto-created ancestors, then `create_*` walk it
// again here. The chain is independent of the layer mutation, so it could be
// built once and threaded through (e.g. `create_*` could accept a prevalidated
// chain) instead of re-parsing the path two or three times per write.
fn ensure_prim_chain(data: &mut dyn AbstractData, target: &Path) -> Result<(), AuthoringError> {
    let chain = namespace_chain(target)?;
    let abs_root = Path::abs_root();

    // The first element's parent is the pseudo-root; if a spec already sits
    // there it must be a `PseudoRoot`, or `primChildren` would be stamped onto
    // the wrong spec type below.
    if let Some(existing) = data.spec_type(&abs_root) {
        if existing != SpecType::PseudoRoot {
            return Err(AuthoringError::InvalidPath {
                path: abs_root,
                reason: "root spec exists with a non-PseudoRoot SpecType",
            });
        }
    }

    // The parent of each element is positional: the preceding element, or the
    // pseudo-root for the first.
    let parent_of = |i: usize| if i == 0 { &abs_root } else { &chain[i - 1].path };

    // First pass: every existing spec along the chain must already hold the
    // SpecType the chain expects, and every child-list field must be a
    // `TokenVec` (or absent). Stamping `primChildren` onto an Attribute, or a
    // variant set onto a non-prim, would corrupt the layer.
    for (i, elem) in chain.iter().enumerate() {
        if let Some(existing) = data.spec_type(&elem.path) {
            if existing != elem.spec_type {
                return Err(AuthoringError::InvalidPath {
                    path: elem.path.clone(),
                    reason: "spec exists with an incompatible SpecType",
                });
            }
        }
        validate_token_vec(data, parent_of(i), elem.child_key)?;
    }

    // Materialize the pseudo-root so the first element's parent is present;
    // every other element's parent is itself an earlier element in the chain.
    if data.spec_type(&abs_root).is_none() {
        data.create_spec(abs_root.clone(), SpecType::PseudoRoot);
    }

    // Second pass: register each child name on its parent and create the spec.
    for (i, elem) in chain.iter().enumerate() {
        add_to_token_vec(data, parent_of(i), elem.child_key, &elem.child_name)?;

        if data.spec_type(&elem.path).is_none() {
            data.create_spec(elem.path.clone(), elem.spec_type);
            // Only prim specs carry a specifier; variant set / variant specs
            // are pure scaffolding.
            if elem.spec_type == SpecType::Prim {
                data.set_field(
                    &elem.path,
                    FieldKey::Specifier.as_str(),
                    Value::Specifier(Specifier::Over),
                );
            }
        }
    }
    Ok(())
}

/// One spec on the namespace chain from the pseudo-root down to an authoring
/// target, in root → leaf order. A variant selection `{set=sel}` expands into
/// two elements: the variant set spec (`/Prim{set=}`) registered under the
/// owning prim's `variantSetChildren`, then the variant spec (`/Prim{set=sel}`)
/// registered under the variant set's `variantChildren`.
///
/// The parent is positional — every element's parent is the preceding element
/// (or the pseudo-root for the first), so it isn't stored. `child_name` is kept
/// because it is not recoverable from `path` for variant elements
/// (`/Prim{set=}.name()` is `Prim{set=}`, not the set name `set`).
struct ChainElement {
    /// Path of the spec to ensure.
    path: Path,
    /// Spec type to create at `path` if absent.
    spec_type: SpecType,
    /// Child-list field on the parent that records `child_name`.
    child_key: ChildrenKey,
    /// Name to register in the parent's child list.
    child_name: String,
}

/// Validate that `target` is an authorable prim path and invoke `emit` for
/// each of its components ([`Path::components`]) in root → leaf order.
///
/// Adds the authoring rules on top of the shared prim-path grammar: `target`
/// must be absolute, non-root, and non-property, every prim name and variant
/// set / selection must be a USD identifier, and the whole path must parse (no
/// malformed tail). Both [`require_prim_path`] (validate only, no allocation)
/// and [`namespace_chain`] (build the spec chain) drive this, so they cannot
/// drift apart.
fn parse_prim_path(target: &Path, mut emit: impl FnMut(PathComponent<'_>)) -> Result<(), AuthoringError> {
    let invalid = |reason: &'static str| AuthoringError::InvalidPath {
        path: target.clone(),
        reason,
    };
    if !target.is_abs() || target.is_abs_root() {
        return Err(invalid("expected absolute non-root prim path"));
    }
    if target.is_property_path() {
        return Err(invalid("expected prim path, got property path"));
    }

    let mut components = target.components();
    for component in components.by_ref() {
        match component {
            PathComponent::Prim(name) => {
                if !Path::is_valid_identifier(name) {
                    return Err(invalid("prim path component is not a USD identifier"));
                }
            }
            PathComponent::Variant { set, selection } => {
                if !Path::is_valid_identifier(set) {
                    return Err(invalid("variant set name is not a USD identifier"));
                }
                if selection.is_empty() || !Path::is_valid_identifier(selection) {
                    return Err(invalid("variant selection is not a USD identifier"));
                }
            }
        }
        emit(component);
    }
    if !components.remainder().is_empty() {
        return Err(invalid("malformed prim path"));
    }
    Ok(())
}

/// Decompose `target` — a prim path that may contain `{set=sel}` variant
/// selections — into the ordered chain of specs that must exist for it to be
/// authorable. Validation and grammar live in [`parse_prim_path`].
fn namespace_chain(target: &Path) -> Result<Vec<ChainElement>, AuthoringError> {
    let mut elems = Vec::new();
    let mut cursor = Path::abs_root();

    parse_prim_path(target, |component| match component {
        PathComponent::Prim(name) => {
            let path = cursor.append_path(name).expect("name validated as an identifier");
            elems.push(ChainElement {
                path: path.clone(),
                spec_type: SpecType::Prim,
                child_key: ChildrenKey::PrimChildren,
                child_name: name.to_owned(),
            });
            cursor = path;
        }
        PathComponent::Variant { set, selection } => {
            elems.push(ChainElement {
                path: cursor.append_variant_selection(set, ""),
                spec_type: SpecType::VariantSet,
                child_key: ChildrenKey::VariantSetChildren,
                child_name: set.to_owned(),
            });
            let variant_path = cursor.append_variant_selection(set, selection);
            elems.push(ChainElement {
                path: variant_path.clone(),
                spec_type: SpecType::Variant,
                child_key: ChildrenKey::VariantChildren,
                child_name: selection.to_owned(),
            });
            cursor = variant_path;
        }
    })?;
    Ok(elems)
}

/// Insert `name` into the `TokenVec` field at `key` on the spec at `owner_path`,
/// creating the field if absent. No-op if the name is already present.
///
// TODO(perf): this clones the parent's whole child-name `TokenVec` per insert
// (read-into-owned → push → write back), so registering N siblings is O(N^2).
// An in-place `AbstractData` append hook (default clone-set, overridden by
// `Data` to `spec_mut` + `Vec::push`) would make each registration O(1).
fn add_to_token_vec(
    data: &mut dyn AbstractData,
    owner_path: &Path,
    key: ChildrenKey,
    name: &str,
) -> Result<(), AuthoringError> {
    // A decode error must surface, not be mistaken for an absent field — the
    // `None` arm overwrites, which would silently drop an undecodable child
    // list on a lazy backend.
    let existing = read_child_field(data, owner_path, key)?;
    match existing {
        Some(Value::TokenVec(mut v)) => {
            if !v.iter().any(|n| *n == name) {
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
        None => {
            data.set_field(owner_path, key.as_str(), Value::TokenVec(vec![name.into()]));
        }
    }
    Ok(())
}

/// Verify that an authored child-list field is either absent or a `TokenVec`.
fn validate_token_vec(data: &dyn AbstractData, path: &Path, key: ChildrenKey) -> Result<(), AuthoringError> {
    match read_child_field(data, path, key)? {
        Some(value) if !matches!(value, Value::TokenVec(_)) => Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "child-list field exists with non-TokenVec value",
        }),
        _ => Ok(()),
    }
}

/// Read a child-list field as an owned [`Value`], surfacing a decode failure as
/// an [`AuthoringError`] rather than swallowing it to "absent".
fn read_child_field(data: &dyn AbstractData, path: &Path, key: ChildrenKey) -> Result<Option<Value>, AuthoringError> {
    let value = data
        .try_get(path, key.as_str())
        .map_err(|_| AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "child-list field could not be read",
        })?;
    Ok(value.map(Cow::into_owned))
}

/// Verify that `path` either holds no spec or holds one of type `expected`.
fn require_spec_type_or_absent(data: &dyn AbstractData, path: &Path, expected: SpecType) -> Result<(), AuthoringError> {
    match data.spec_type(path) {
        Some(existing) if existing != expected => Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "spec exists with the wrong SpecType",
        }),
        _ => Ok(()),
    }
}

/// Validate that `path` is an absolute, non-root, non-property path suitable
/// for prim authoring. Each prim component must be a USD identifier, optionally
/// carrying `{set=sel}` variant selections whose set and selection names are
/// themselves identifiers. Shares [`parse_prim_path`] with [`namespace_chain`]
/// so the accepted grammar stays in lock-step, but allocates nothing — it
/// drives the parser with a no-op rather than building the spec chain.
fn require_prim_path(path: &Path) -> Result<(), AuthoringError> {
    parse_prim_path(path, |_| {})
}

/// Reject a target whose leaf is a variant selection (e.g. `/Prim{set=sel}`).
///
/// Such a path identifies a variant spec, not a prim, so `create_prim` /
/// `override_prim` cannot author a `PrimSpec` there. (Properties and children
/// *inside* a variant — `/Prim{set=sel}.attr`, `/Prim{set=sel}child` — remain
/// valid; only the bare variant selection as the leaf is rejected.)
fn require_prim_leaf(path: &Path) -> Result<(), AuthoringError> {
    if path.is_prim_variant_selection_path() {
        return Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "expected a prim path, but the leaf is a variant selection",
        });
    }
    Ok(())
}

/// Split a property path like `/World/Mesh.points` into `(/World/Mesh,
/// "points")`. Returns an error if `path` is not an absolute property path
/// whose owning prim portion is itself a valid prim path.
fn split_property_path(path: &Path) -> Result<(Path, String), AuthoringError> {
    let (prim_path, suffix) = path.split_property().ok_or(AuthoringError::InvalidPath {
        path: path.clone(),
        reason: "expected property path",
    })?;
    // Owning prim must be an absolute, non-root, non-property path — guards
    // against relative roots ("A.foo"), root-level properties ("/.foo"), and
    // paths whose `prim_path()` returned a structurally invalid string.
    require_prim_path(&prim_path)?;
    // Property names are colon-separated identifiers — reject target/connection
    // brackets, embedded dots, and other syntax that would round-trip as garbage.
    if !suffix.split(':').all(Path::is_valid_identifier) {
        return Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "property name must be a colon-separated identifier",
        });
    }
    Ok((prim_path, suffix.to_owned()))
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
