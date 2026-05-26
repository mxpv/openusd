//! A single scene-description layer (the Rust equivalent of C++ `SdfLayer`):
//! identity + a backing [`AbstractData`] + an authoring surface that mirrors
//! `SdfLayer::CreatePrimSpec` and friends.
//!
//! Cross-layer composition concerns (resolving sublayers, references,
//! payloads) live separately in [`crate::layer`].

use std::io::Cursor;

use anyhow::Result;

use super::schema::{ChildrenKey, FieldKey};
use super::{
    AbstractData, AttributeSpec, AttributeSpecMut, Data, LayerData, Path, PrimSpec, PrimSpecMut, PseudoRootSpec,
    PseudoRootSpecMut, RelationshipSpec, RelationshipSpecMut, Spec, SpecType, Specifier, Value, Variability,
};
use crate::{usda, usdc};

/// A single loaded layer in the composition.
pub struct Layer {
    /// Resolved, canonical identifier for this layer.
    pub identifier: String,
    /// The parsed scene description data. Kept crate-private so external
    /// callers cannot swap the backing box or write to it directly,
    /// bypassing the authoring API's bookkeeping invariants
    /// (`primChildren`, `propertyChildren`, ancestor specifiers, …).
    pub(crate) data: LayerData,
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
    /// The layer's backend is not an in-memory [`Data`] store. Layers loaded
    /// from files via [`crate::layer::Collector`] are read-only.
    #[error("layer {identifier} is read-only; authoring is not supported")]
    ReadOnly {
        /// The layer's resolved identifier.
        identifier: String,
    },

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

/// Authoring methods. These require the layer's backend to be a writable
/// in-memory [`Data`] store (created via [`Layer::new_anonymous`]).
/// File-loaded layers return [`AuthoringError::ReadOnly`].
///
/// Mirrors `SdfLayer`'s authoring surface: [`Layer::create_prim`],
/// [`Layer::override_prim`], [`Layer::create_attr`], and
/// [`Layer::create_relationship`] parallel `SdfCreatePrimInLayer` /
/// `SdfAttributeSpec::New` / `SdfRelationshipSpec::New`. `primChildren`
/// and `propertyChildren` ordering is maintained automatically: ancestor
/// prim specs are auto-created as `over` when missing.
///
/// # Reading file-loaded layers
///
/// The typed-view lookups ([`Layer::prim`], [`Layer::attribute`],
/// [`Layer::relationship`], [`Layer::pseudo_root`]) currently borrow an
/// underlying [`Data`] directly. Layers loaded by `usda::TextReader` or
/// `usdc::CrateData` keep their own internal spec storage and do not yet
/// expose a `Data` view, so the lookup methods return `None` on file-loaded
/// layers. Use [`crate::stage::Stage`]'s path-keyed query API for inspection
/// in the meantime.
//
// TODO: materialize `TextReader` / `CrateData` into `Data` (or expose one via
// `AbstractData::as_data`) so the typed views work uniformly across in-memory
// and file-loaded layers, matching C++ `SdfLayer::GetPrimAtPath`.
impl Layer {
    /// Create a blank in-memory writable layer with the given identifier.
    ///
    /// The layer's pseudo-root spec is pre-populated so layer-level metadata
    /// (`defaultPrim`, `subLayers`, time codes, …) can be authored via
    /// [`Layer::pseudo_root_mut`] immediately.
    pub fn new_anonymous(identifier: impl Into<String>) -> Self {
        let mut data = Data::new();
        data.create_spec(Path::abs_root(), SpecType::PseudoRoot);
        Self::new(identifier, Box::new(data))
    }

    /// Create or upgrade a prim spec at `path` with the given specifier and
    /// `typeName`. Any missing ancestor specs are created as `over` and the
    /// parent's `primChildren` is updated.
    ///
    /// Mirrors C++ `SdfCreatePrimInLayer` + `SetSpecifier` + `SetTypeName`.
    pub fn create_prim(
        &mut self,
        path: impl Into<Path>,
        specifier: Specifier,
        type_name: impl Into<String>,
    ) -> Result<PrimSpecMut<'_>, AuthoringError> {
        let path: Path = path.into();
        let type_name: String = type_name.into();

        require_prim_path(&path)?;
        let data = self.writable_data_mut()?;
        ensure_prim_chain(data, &path)?;

        let spec = data.spec_mut(&path).expect("just ensured");
        spec.add(FieldKey::Specifier, Value::Specifier(specifier));
        spec.add(FieldKey::TypeName, Value::Token(type_name));

        Ok(spec.as_prim_mut().expect("type guaranteed by ensure_prim_chain"))
    }

    /// Ensure a prim spec exists at `path` with specifier `over`. Existing
    /// `def` / `class` specs are left as-is; this only creates missing ones.
    /// Ancestor specs are auto-created as `over` as well.
    ///
    /// Mirrors C++ `UsdStage::OverridePrim` semantics at the layer tier.
    pub fn override_prim(&mut self, path: impl Into<Path>) -> Result<PrimSpecMut<'_>, AuthoringError> {
        let path: Path = path.into();

        require_prim_path(&path)?;
        let data = self.writable_data_mut()?;
        ensure_prim_chain(data, &path)?;

        let spec = data.spec_mut(&path).expect("just ensured");
        Ok(spec.as_prim_mut().expect("type guaranteed by ensure_prim_chain"))
    }

    /// Create an attribute spec at `path` (a property path like
    /// `/World/Mesh.points`). The owning prim is auto-created as `over` if
    /// missing, and the prim's `propertyChildren` is updated.
    ///
    /// `typeName` and `variability` are construction parameters (matching
    /// C++ `SdfAttributeSpec::New`); there is no post-hoc setter for either.
    pub fn create_attr(
        &mut self,
        path: impl Into<Path>,
        type_name: impl Into<String>,
        variability: Variability,
        custom: bool,
    ) -> Result<AttributeSpecMut<'_>, AuthoringError> {
        let path: Path = path.into();
        let type_name: String = type_name.into();

        let (prim_path, property_name) = split_property_path(&path)?;
        let data = self.writable_data_mut()?;
        require_spec_type_or_absent(data, &path, SpecType::Attribute)?;
        validate_token_vec(data, &prim_path, ChildrenKey::PropertyChildren)?;
        ensure_prim_chain(data, &prim_path)?;

        add_to_token_vec(
            data.spec_mut(&prim_path).expect("ensure_prim_chain created it"),
            &prim_path,
            ChildrenKey::PropertyChildren,
            &property_name,
        )?;

        if !data.has_spec(&path) {
            data.create_spec(path.clone(), SpecType::Attribute);
        }
        let spec = data.spec_mut(&path).expect("just ensured");
        spec.add(FieldKey::TypeName, Value::Token(type_name));
        if variability != Variability::Varying {
            spec.add(FieldKey::Variability, Value::Variability(variability));
        } else {
            spec.remove(FieldKey::Variability.as_str());
        }
        if custom {
            spec.add(FieldKey::Custom, Value::Bool(true));
        } else {
            spec.remove(FieldKey::Custom.as_str());
        }

        Ok(spec
            .as_attr_mut()
            .expect("type guaranteed by require_spec_type_or_absent"))
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
        let data = self.writable_data_mut()?;
        require_spec_type_or_absent(data, &path, SpecType::Relationship)?;
        validate_token_vec(data, &prim_path, ChildrenKey::PropertyChildren)?;
        ensure_prim_chain(data, &prim_path)?;

        add_to_token_vec(
            data.spec_mut(&prim_path).expect("ensure_prim_chain created it"),
            &prim_path,
            ChildrenKey::PropertyChildren,
            &property_name,
        )?;

        if !data.has_spec(&path) {
            data.create_spec(path.clone(), SpecType::Relationship);
        }
        let spec = data.spec_mut(&path).expect("just ensured");
        if variability != Variability::Varying {
            spec.add(FieldKey::Variability, Value::Variability(variability));
        } else {
            spec.remove(FieldKey::Variability.as_str());
        }
        if custom {
            spec.add(FieldKey::Custom, Value::Bool(true));
        } else {
            spec.remove(FieldKey::Custom.as_str());
        }

        Ok(spec
            .as_relationship_mut()
            .expect("type guaranteed by require_spec_type_or_absent"))
    }

    /// Look up a prim spec at `path`. Returns `None` if no spec exists, the
    /// spec is not a prim, or the backend is not in-memory writable.
    pub fn prim(&self, path: impl Into<Path>) -> Option<PrimSpec<'_>> {
        let path: Path = path.into();
        self.data.as_data()?.spec(&path)?.as_prim()
    }

    /// Mutably look up a prim spec at `path`.
    pub fn prim_mut(&mut self, path: impl Into<Path>) -> Option<PrimSpecMut<'_>> {
        let path: Path = path.into();
        self.data.as_data_mut()?.spec_mut(&path)?.as_prim_mut()
    }

    /// Look up an attribute spec at a property path.
    pub fn attribute(&self, path: impl Into<Path>) -> Option<AttributeSpec<'_>> {
        let path: Path = path.into();
        self.data.as_data()?.spec(&path)?.as_attr()
    }

    /// Mutably look up an attribute spec at a property path.
    pub fn attribute_mut(&mut self, path: impl Into<Path>) -> Option<AttributeSpecMut<'_>> {
        let path: Path = path.into();
        self.data.as_data_mut()?.spec_mut(&path)?.as_attr_mut()
    }

    /// Look up a relationship spec at a property path.
    pub fn relationship(&self, path: impl Into<Path>) -> Option<RelationshipSpec<'_>> {
        let path: Path = path.into();
        self.data.as_data()?.spec(&path)?.as_relationship()
    }

    /// Mutably look up a relationship spec at a property path.
    pub fn relationship_mut(&mut self, path: impl Into<Path>) -> Option<RelationshipSpecMut<'_>> {
        let path: Path = path.into();
        self.data.as_data_mut()?.spec_mut(&path)?.as_relationship_mut()
    }

    /// View this layer's root pseudo-spec, which carries layer-wide metadata
    /// (`defaultPrim`, `subLayers`, time codes, …).
    pub fn pseudo_root(&self) -> Option<PseudoRootSpec<'_>> {
        self.data.as_data()?.spec(&Path::abs_root())?.as_pseudo_root()
    }

    /// Mutably view this layer's root pseudo-spec. The spec is created on
    /// first access if missing. Returns [`AuthoringError::ReadOnly`] for
    /// file-loaded layers.
    pub fn pseudo_root_mut(&mut self) -> Result<PseudoRootSpecMut<'_>, AuthoringError> {
        let data = self.writable_data_mut()?;
        let root = Path::abs_root();
        match data.spec_type(&root) {
            Some(SpecType::PseudoRoot) => {}
            Some(_) => {
                return Err(AuthoringError::InvalidPath {
                    path: root,
                    reason: "root spec exists with non-PseudoRoot SpecType",
                })
            }
            None => {
                data.create_spec(root.clone(), SpecType::PseudoRoot);
            }
        }
        Ok(data
            .spec_mut(&root)
            .expect("just ensured")
            .as_pseudo_root_mut()
            .expect("type guaranteed above"))
    }

    fn writable_data_mut(&mut self) -> Result<&mut Data, AuthoringError> {
        let identifier = self.identifier.clone();
        self.data.as_data_mut().ok_or(AuthoringError::ReadOnly { identifier })
    }
}

impl std::fmt::Debug for Layer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Layer")
            .field("identifier", &self.identifier)
            .finish_non_exhaustive()
    }
}

/// `Layer` forwards every [`AbstractData`] method to its backing storage so
/// `&Layer` can stand in wherever `&dyn AbstractData` was used. Mirrors C++
/// `SdfLayer : SdfAbstractData`.
impl AbstractData for Layer {
    fn has_spec(&self, path: &Path) -> bool {
        self.data.has_spec(path)
    }

    fn has_field(&self, path: &Path, field: &str) -> bool {
        self.data.has_field(path, field)
    }

    fn spec_type(&self, path: &Path) -> Option<SpecType> {
        self.data.spec_type(path)
    }

    fn try_get(&self, path: &Path, field: &str) -> Result<Option<std::borrow::Cow<'_, Value>>> {
        self.data.try_get(path, field)
    }

    fn list(&self, path: &Path) -> Option<Vec<String>> {
        self.data.list(path)
    }

    fn paths(&self) -> Vec<Path> {
        self.data.paths()
    }

    fn as_data(&self) -> Option<&Data> {
        self.data.as_data()
    }

    fn as_data_mut(&mut self) -> Option<&mut Data> {
        None
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
fn ensure_prim_chain(data: &mut Data, target: &Path) -> Result<(), AuthoringError> {
    let mut chain: Vec<Path> = Vec::new();
    let mut cursor: Path = target.clone();
    while !cursor.is_abs_root() {
        chain.push(cursor.clone());
        cursor = cursor.parent().expect("non-root has a parent (validated upstream)");
    }
    chain.reverse(); // root → leaf

    for (i, child) in chain.iter().enumerate() {
        let parent_path = if i == 0 { Path::abs_root() } else { chain[i - 1].clone() };
        let parent_ty = if parent_path.is_abs_root() {
            SpecType::PseudoRoot
        } else {
            SpecType::Prim
        };

        if let Some(existing) = data.spec_type(&parent_path) {
            if existing != parent_ty {
                return Err(AuthoringError::InvalidPath {
                    path: parent_path,
                    reason: "ancestor spec exists with non-prim SpecType",
                });
            }
        }
        validate_token_vec(data, &parent_path, ChildrenKey::PrimChildren)?;

        if let Some(existing) = data.spec_type(child) {
            if existing != SpecType::Prim {
                return Err(AuthoringError::InvalidPath {
                    path: child.clone(),
                    reason: "spec exists with non-prim SpecType",
                });
            }
        }
    }

    for (i, child) in chain.iter().enumerate() {
        let parent_path = if i == 0 { Path::abs_root() } else { chain[i - 1].clone() };
        let child_name = child.name().expect("non-root has a name").to_owned();

        let parent_ty = if parent_path.is_abs_root() {
            SpecType::PseudoRoot
        } else {
            SpecType::Prim
        };
        if data.spec_type(&parent_path).is_none() {
            data.create_spec(parent_path.clone(), parent_ty);
        }

        let parent_spec = data.spec_mut(&parent_path).expect("just ensured");
        add_to_token_vec(parent_spec, &parent_path, ChildrenKey::PrimChildren, &child_name)?;

        if data.spec_type(child).is_none() {
            let spec = data.create_spec(child.clone(), SpecType::Prim);
            spec.add(FieldKey::Specifier, Value::Specifier(Specifier::Over));
        }
    }
    Ok(())
}

/// Insert `name` into the `TokenVec` field at `key` on `spec`, creating the
/// field if absent. No-op if the name is already present.
fn add_to_token_vec(spec: &mut Spec, owner_path: &Path, key: ChildrenKey, name: &str) -> Result<(), AuthoringError> {
    match spec.get_mut(key.as_str()) {
        Some(Value::TokenVec(v)) => {
            if !v.iter().any(|n| n == name) {
                v.push(name.to_owned());
            }
        }
        Some(_) => {
            return Err(AuthoringError::InvalidPath {
                path: owner_path.clone(),
                reason: "child-list field exists with non-TokenVec value",
            });
        }
        None => {
            spec.add(key, Value::TokenVec(vec![name.to_owned()]));
        }
    }
    Ok(())
}

/// Verify that an authored child-list field is either absent or a `TokenVec`.
fn validate_token_vec(data: &Data, path: &Path, key: ChildrenKey) -> Result<(), AuthoringError> {
    match data.spec(path).and_then(|spec| spec.get(key.as_str())) {
        Some(Value::TokenVec(_)) | None => Ok(()),
        Some(_) => Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "child-list field exists with non-TokenVec value",
        }),
    }
}

/// Verify that `path` either holds no spec or holds one of type `expected`.
fn require_spec_type_or_absent(data: &Data, path: &Path, expected: SpecType) -> Result<(), AuthoringError> {
    match data.spec_type(path) {
        Some(existing) if existing != expected => Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "spec exists with the wrong SpecType",
        }),
        _ => Ok(()),
    }
}

/// Validate that `path` is an absolute, non-root, non-property path suitable
/// for prim authoring — every `/`-separated component must be a USD identifier
/// (no brackets, variant-selection segments, or stray dots).
fn require_prim_path(path: &Path) -> Result<(), AuthoringError> {
    if !path.is_abs() || path.is_abs_root() {
        return Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "expected absolute non-root prim path",
        });
    }
    if path.is_property_path() {
        return Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "expected prim path, got property path",
        });
    }
    for segment in path.as_str()[1..].split('/') {
        if !Path::is_valid_identifier(segment) {
            return Err(AuthoringError::InvalidPath {
                path: path.clone(),
                reason: "prim path component is not a USD identifier",
            });
        }
    }
    Ok(())
}

/// Split a property path like `/World/Mesh.points` into `(/World/Mesh,
/// "points")`. Returns an error if `path` is not an absolute property path
/// whose owning prim portion is itself a valid prim path.
fn split_property_path(path: &Path) -> Result<(Path, String), AuthoringError> {
    if !path.is_property_path() {
        return Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "expected property path",
        });
    }
    let prim_path = path.prim_path();
    // Owning prim must be an absolute, non-root, non-property path — guards
    // against relative roots ("A.foo"), root-level properties ("/.foo"), and
    // paths whose `prim_path()` returned a structurally invalid string.
    require_prim_path(&prim_path)?;
    let suffix = path
        .as_str()
        .strip_prefix(prim_path.as_str())
        .and_then(|t| t.strip_prefix('.'))
        .ok_or(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "malformed property path",
        })?;
    // Property names are colon-separated identifiers — reject target/connection
    // brackets, embedded dots, and other syntax that would round-trip as garbage.
    if suffix.is_empty() || !suffix.split(':').all(Path::is_valid_identifier) {
        return Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "property name must be a colon-separated identifier",
        });
    }
    Ok((prim_path, suffix.to_owned()))
}
