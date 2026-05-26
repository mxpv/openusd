//! Layer stack collection.
//!
//! Given a root USD file, [`Collector`] uses an [`ar::Resolver`] to recursively
//! resolve and load every layer the stage depends on — following sublayers,
//! references, and payloads across files and formats (`.usda`, `.usdc`, `.usd`,
//! `.usdz`). The result is a [`Vec`] of [`Layer`]s, each wrapping a parsed
//! [`AbstractData`] with its resolved identity. Cycles are detected and
//! skipped automatically.

use std::collections::{HashMap, HashSet};
use std::io::Cursor;

use anyhow::{bail, Context, Result};

use crate::ar::{self, Resolver};
use crate::expr;
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{self, AbstractData, LayerData, Path, Value};
use crate::{usda, usdc, usdz};

/// The kind of layer dependency that triggered a composition error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DependencyKind {
    /// A sublayer declared on the layer's pseudo-root.
    SubLayer,
    /// A reference arc on a prim.
    Reference,
    /// A payload arc on a prim.
    Payload,
}

impl std::fmt::Display for DependencyKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SubLayer => write!(f, "sublayer"),
            Self::Reference => write!(f, "reference"),
            Self::Payload => write!(f, "payload"),
        }
    }
}

/// An error encountered during layer collection that may be recoverable.
///
/// When opening a stage, some errors (such as missing referenced files) can be
/// tolerated so that the stage is partially constructed. A callback provided via
/// [`StageBuilder::on_error`](crate::stage::StageBuilder::on_error) receives
/// these errors and decides whether to continue or abort.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// An asset path could not be resolved to a physical location.
    #[error(
        "failed to resolve {kind} asset: {asset_path} (referenced by {referencing_layer}{})",
        "prim_path.as_ref().map(|p| format!(\" at {p}\")).unwrap_or_default()"
    )]
    UnresolvedAsset {
        /// The asset path that could not be resolved.
        asset_path: String,
        /// The layer that declared this dependency.
        referencing_layer: String,
        /// What kind of composition arc declared this dependency.
        kind: DependencyKind,
        /// The prim that declared this arc (`None` for sublayers).
        prim_path: Option<Path>,
    },
}

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
    /// Borrow the underlying [`AbstractData`] backend for read-only inspection.
    /// Callers that need typed views should prefer [`Layer::prim`] /
    /// [`Layer::attr`] / etc.
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
    fn new(identifier: impl Into<String>, data: LayerData) -> Self {
        Self {
            identifier: identifier.into(),
            data,
        }
    }

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
    /// The layer's backend is not an in-memory [`sdf::Data`] store. Layers
    /// loaded from files via [`Collector`] are read-only.
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
/// in-memory [`sdf::Data`] store (created via [`Layer::new_anonymous`]).
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
/// The typed-view lookups ([`Layer::prim`], [`Layer::attr`],
/// [`Layer::relationship`], [`Layer::pseudo_root`]) currently borrow an
/// underlying [`sdf::Data`] directly. Layers loaded by `usda::TextReader` or
/// `usdc::CrateData` keep their own internal spec storage and do not yet
/// expose an `sdf::Data` view, so the lookup methods return `None` on
/// file-loaded layers. Use [`crate::stage::Stage`]'s path-keyed query API
/// for inspection in the meantime.
//
// TODO: materialize `TextReader` / `CrateData` into `sdf::Data` (or expose
// one via `AbstractData::as_data`) so the typed views work uniformly across
// in-memory and file-loaded layers, matching C++ `SdfLayer::GetPrimAtPath`.
impl Layer {
    /// Create a blank in-memory writable layer with the given identifier.
    ///
    /// The layer's pseudo-root spec is pre-populated so layer-level metadata
    /// (`defaultPrim`, `subLayers`, time codes, …) can be authored via
    /// [`Layer::pseudo_root_mut`] immediately.
    pub fn new_anonymous(identifier: impl Into<String>) -> Self {
        let mut data = sdf::Data::new();
        data.create_spec(Path::abs_root(), sdf::SpecType::PseudoRoot);
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
        specifier: sdf::Specifier,
        type_name: impl Into<String>,
    ) -> Result<sdf::PrimSpecMut<'_>, AuthoringError> {
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
    pub fn override_prim(&mut self, path: impl Into<Path>) -> Result<sdf::PrimSpecMut<'_>, AuthoringError> {
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
        variability: sdf::Variability,
        custom: bool,
    ) -> Result<sdf::AttributeSpecMut<'_>, AuthoringError> {
        let path: Path = path.into();
        let type_name: String = type_name.into();

        let (prim_path, property_name) = split_property_path(&path)?;
        let data = self.writable_data_mut()?;
        require_spec_type_or_absent(data, &path, sdf::SpecType::Attribute)?;
        validate_token_vec(data, &prim_path, ChildrenKey::PropertyChildren)?;
        ensure_prim_chain(data, &prim_path)?;

        add_to_token_vec(
            data.spec_mut(&prim_path).expect("ensure_prim_chain created it"),
            &prim_path,
            ChildrenKey::PropertyChildren,
            &property_name,
        )?;

        if !data.has_spec(&path) {
            data.create_spec(path.clone(), sdf::SpecType::Attribute);
        }
        let spec = data.spec_mut(&path).expect("just ensured");
        spec.add(FieldKey::TypeName, Value::Token(type_name));
        if variability != sdf::Variability::Varying {
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
        variability: sdf::Variability,
        custom: bool,
    ) -> Result<sdf::RelationshipSpecMut<'_>, AuthoringError> {
        let path: Path = path.into();

        let (prim_path, property_name) = split_property_path(&path)?;
        let data = self.writable_data_mut()?;
        require_spec_type_or_absent(data, &path, sdf::SpecType::Relationship)?;
        validate_token_vec(data, &prim_path, ChildrenKey::PropertyChildren)?;
        ensure_prim_chain(data, &prim_path)?;

        add_to_token_vec(
            data.spec_mut(&prim_path).expect("ensure_prim_chain created it"),
            &prim_path,
            ChildrenKey::PropertyChildren,
            &property_name,
        )?;

        if !data.has_spec(&path) {
            data.create_spec(path.clone(), sdf::SpecType::Relationship);
        }
        let spec = data.spec_mut(&path).expect("just ensured");
        if variability != sdf::Variability::Varying {
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
    pub fn prim(&self, path: impl Into<Path>) -> Option<sdf::PrimSpec<'_>> {
        let path: Path = path.into();
        self.data.as_data()?.spec(&path)?.as_prim()
    }

    /// Mutably look up a prim spec at `path`.
    pub fn prim_mut(&mut self, path: impl Into<Path>) -> Option<sdf::PrimSpecMut<'_>> {
        let path: Path = path.into();
        self.data.as_data_mut()?.spec_mut(&path)?.as_prim_mut()
    }

    /// Look up an attribute spec at a property path.
    pub fn attr(&self, path: impl Into<Path>) -> Option<sdf::AttributeSpec<'_>> {
        let path: Path = path.into();
        self.data.as_data()?.spec(&path)?.as_attr()
    }

    /// Mutably look up an attribute spec at a property path.
    pub fn attr_mut(&mut self, path: impl Into<Path>) -> Option<sdf::AttributeSpecMut<'_>> {
        let path: Path = path.into();
        self.data.as_data_mut()?.spec_mut(&path)?.as_attr_mut()
    }

    /// Look up a relationship spec at a property path.
    pub fn relationship(&self, path: impl Into<Path>) -> Option<sdf::RelationshipSpec<'_>> {
        let path: Path = path.into();
        self.data.as_data()?.spec(&path)?.as_relationship()
    }

    /// Mutably look up a relationship spec at a property path.
    pub fn relationship_mut(&mut self, path: impl Into<Path>) -> Option<sdf::RelationshipSpecMut<'_>> {
        let path: Path = path.into();
        self.data.as_data_mut()?.spec_mut(&path)?.as_relationship_mut()
    }

    /// View this layer's root pseudo-spec, which carries layer-wide metadata
    /// (`defaultPrim`, `subLayers`, time codes, …).
    pub fn pseudo_root(&self) -> Option<sdf::PseudoRootSpec<'_>> {
        self.data.as_data()?.spec(&Path::abs_root())?.as_pseudo_root()
    }

    /// Mutably view this layer's root pseudo-spec. The spec is created on
    /// first access if missing. Returns [`AuthoringError::ReadOnly`] for
    /// file-loaded layers.
    pub fn pseudo_root_mut(&mut self) -> Result<sdf::PseudoRootSpecMut<'_>, AuthoringError> {
        let data = self.writable_data_mut()?;
        let root = Path::abs_root();
        match data.spec_type(&root) {
            Some(sdf::SpecType::PseudoRoot) => {}
            Some(_) => {
                return Err(AuthoringError::InvalidPath {
                    path: root,
                    reason: "root spec exists with non-PseudoRoot SpecType",
                })
            }
            None => {
                data.create_spec(root.clone(), sdf::SpecType::PseudoRoot);
            }
        }
        Ok(data
            .spec_mut(&root)
            .expect("just ensured")
            .as_pseudo_root_mut()
            .expect("type guaranteed above"))
    }

    fn writable_data_mut(&mut self) -> Result<&mut sdf::Data, AuthoringError> {
        let identifier = self.identifier.clone();
        self.data.as_data_mut().ok_or(AuthoringError::ReadOnly { identifier })
    }
}

/// Ensure prim specs exist for every ancestor of `target` and for `target`
/// itself, creating missing ones as `over`. Updates each parent's
/// `primChildren` to include the next name along the chain. Idempotent.
/// `target` must be an absolute, non-root, non-property prim path;
/// callers should validate via [`require_prim_path`] first.
///
/// Errors with [`AuthoringError::InvalidPath`] if any ancestor or `target`
/// path already holds a spec of a non-prim type — stamping `primChildren`
/// onto an Attribute or Relationship spec would corrupt the layer.
fn ensure_prim_chain(data: &mut sdf::Data, target: &Path) -> Result<(), AuthoringError> {
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
            sdf::SpecType::PseudoRoot
        } else {
            sdf::SpecType::Prim
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
            if existing != sdf::SpecType::Prim {
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
            sdf::SpecType::PseudoRoot
        } else {
            sdf::SpecType::Prim
        };
        match data.spec_type(&parent_path) {
            Some(_) => {}
            None => {
                data.create_spec(parent_path.clone(), parent_ty);
            }
        }

        let parent_spec = data.spec_mut(&parent_path).expect("just ensured");
        add_to_token_vec(parent_spec, &parent_path, ChildrenKey::PrimChildren, &child_name)?;

        match data.spec_type(child) {
            Some(_) => {}
            None => {
                let spec = data.create_spec(child.clone(), sdf::SpecType::Prim);
                spec.add(FieldKey::Specifier, Value::Specifier(sdf::Specifier::Over));
            }
        }
    }
    Ok(())
}

/// Insert `name` into the `TokenVec` field at `key` on `spec`, creating the
/// field if absent. No-op if the name is already present.
fn add_to_token_vec(
    spec: &mut sdf::Spec,
    owner_path: &Path,
    key: ChildrenKey,
    name: &str,
) -> Result<(), AuthoringError> {
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
fn validate_token_vec(data: &sdf::Data, path: &Path, key: ChildrenKey) -> Result<(), AuthoringError> {
    match data.spec(path).and_then(|spec| spec.get(key.as_str())) {
        Some(Value::TokenVec(_)) | None => Ok(()),
        Some(_) => Err(AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "child-list field exists with non-TokenVec value",
        }),
    }
}

/// Verify that `path` either holds no spec or holds one of type `expected`.
fn require_spec_type_or_absent(data: &sdf::Data, path: &Path, expected: sdf::SpecType) -> Result<(), AuthoringError> {
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

impl std::fmt::Debug for Layer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Layer")
            .field("identifier", &self.identifier)
            .finish_non_exhaustive()
    }
}

/// A dependency discovered while walking a layer's scene graph.
struct Dependency {
    /// The asset path to resolve.
    asset_path: String,
    /// What kind of composition arc declared this dependency.
    kind: DependencyKind,
    /// The prim that declared this arc (`None` for sublayers).
    prim_path: Option<Path>,
}

struct CollectionContext<'a> {
    load_payloads: bool,
    include_prim_dependency: Option<&'a dyn Fn(&Path) -> bool>,
    on_error: &'a dyn Fn(Error) -> Result<()>,
}

impl<'a> CollectionContext<'a> {
    fn with_filter(&self, include_prim_dependency: Option<&'a dyn Fn(&Path) -> bool>) -> Self {
        Self {
            load_payloads: self.load_payloads,
            include_prim_dependency,
            on_error: self.on_error,
        }
    }
}

type StrictErrorHandler = fn(Error) -> Result<()>;

fn strict_error(e: Error) -> Result<()> {
    bail!("{e}")
}

/// Builder for collecting a root layer and all layers it depends on.
pub struct Collector<'a, R: Resolver, E: Fn(Error) -> Result<()> = StrictErrorHandler> {
    resolver: &'a R,
    load_payloads: bool,
    include_prim_dependency: Option<&'a dyn Fn(&Path) -> bool>,
    on_error: E,
}

impl<'a, R: Resolver> Collector<'a, R, StrictErrorHandler> {
    /// Creates a collector that errors on any unresolvable dependency and
    /// follows payload arcs. Use [`Collector::on_error`] or
    /// [`Collector::load_payloads`] to override.
    pub fn new(resolver: &'a R) -> Self {
        Self {
            resolver,
            load_payloads: true,
            include_prim_dependency: None,
            on_error: strict_error,
        }
    }
}

impl<'a, R: Resolver, E: Fn(Error) -> Result<()>> Collector<'a, R, E> {
    /// Controls whether payload dependencies are followed.
    ///
    /// When `load_payloads` is `false`, payload arcs are left as authored
    /// metadata but their target layers are not loaded during collection.
    pub fn load_payloads(mut self, load_payloads: bool) -> Self {
        self.load_payloads = load_payloads;
        self
    }

    /// Sets a callback for recoverable layer collection errors.
    ///
    /// The callback decides whether to continue (`Ok(())`) or abort (`Err(...)`)
    /// for each recoverable error encountered.
    pub fn on_error<E2: Fn(Error) -> Result<()>>(self, on_error: E2) -> Collector<'a, R, E2> {
        Collector {
            resolver: self.resolver,
            load_payloads: self.load_payloads,
            include_prim_dependency: self.include_prim_dependency,
            on_error,
        }
    }

    /// Skips reference/payload dependencies whose authoring prim path fails
    /// `include`. Used by `StageBuilder` to honor `StagePopulationMask` during
    /// root-layer-stack collection so culled-subtree dependencies aren't
    /// resolved or loaded. Crate-internal pending a public design.
    pub(crate) fn prim_dependency_filter(mut self, include: &'a dyn Fn(&Path) -> bool) -> Self {
        self.include_prim_dependency = Some(include);
        self
    }

    /// Opens a root layer and recursively collects all referenced layers.
    ///
    /// Returns a [`Vec<Layer>`] with the root (strongest) layer first.
    pub fn collect(&self, root_path: &str) -> Result<Vec<Layer>> {
        let mut layers = Vec::new();
        let mut visited = HashSet::new();
        let context = CollectionContext {
            load_payloads: self.load_payloads,
            include_prim_dependency: self.include_prim_dependency,
            on_error: &self.on_error,
        };

        collect_recursive(self.resolver, root_path, None, &context, &mut layers, &mut visited)?;

        // Layers are collected in post-order (leaves first), reverse so root is first.
        layers.reverse();

        Ok(layers)
    }
}

/// Recursive layer collector.
fn collect_recursive(
    resolver: &impl Resolver,
    asset_path: &str,
    anchor: Option<&ar::ResolvedPath>,
    context: &CollectionContext<'_>,
    layers: &mut Vec<Layer>,
    visited: &mut HashSet<String>,
) -> Result<()> {
    // Create an anchored identifier so relative paths resolve correctly.
    let identifier = resolver.create_identifier(asset_path, anchor);

    // Skip already-visited layers to avoid cycles.
    if visited.contains(&identifier) {
        return Ok(());
    }

    // Resolve using the anchored identifier (which is absolute).
    // Root layer (no anchor) must always resolve — missing root is a hard error.
    let resolved = resolver
        .resolve(&identifier)
        .with_context(|| format!("failed to resolve asset path: {asset_path}"))?;

    visited.insert(identifier.clone());

    // Load and parse the layer.
    let data = open_layer(resolver, &resolved)?;

    // Read expression variables from this layer's pseudo-root.
    let expr_vars = read_expression_variables(data.as_ref())?;

    // Collect typed dependencies from this layer.
    let deps = collect_dependencies(data.as_ref(), context.load_payloads)?;

    let is_usdz = resolved.extension().and_then(|e| e.to_str()) == Some("usdz");

    for dep in deps {
        if let (Some(include), Some(prim_path)) = (context.include_prim_dependency, dep.prim_path.as_ref()) {
            if !include(prim_path) {
                continue;
            }
        }

        // Evaluate expression-valued asset paths.
        let dep_asset = resolve_expression(&dep.asset_path, &expr_vars)?;

        if is_usdz {
            bail!(
                "cross-file references within USDZ archives are not yet supported: {}",
                resolved
            );
        }

        // Check if this dependency resolves before recursing.
        let dep_id = resolver.create_identifier(&dep_asset, Some(&resolved));
        if !visited.contains(&dep_id) && resolver.resolve(&dep_id).is_none() {
            (context.on_error)(Error::UnresolvedAsset {
                asset_path: dep_asset,
                referencing_layer: identifier.clone(),
                kind: dep.kind,
                prim_path: dep.prim_path,
            })?;
            visited.insert(dep_id);
            continue;
        }

        // References and payloads enter a new layer's namespace, so the
        // caller's prim-path filter (rooted in the originating namespace) no
        // longer applies. Sublayers share the parent's namespace and keep it.
        let child_filter = match dep.kind {
            DependencyKind::SubLayer => context.include_prim_dependency,
            DependencyKind::Reference | DependencyKind::Payload => None,
        };
        collect_recursive(
            resolver,
            &dep_asset,
            Some(&resolved),
            &context.with_filter(child_filter),
            layers,
            visited,
        )?;
    }

    layers.push(Layer::new(identifier, data));

    Ok(())
}

/// Collects typed dependencies from sublayers, references, and optionally
/// payloads in a layer.
fn collect_dependencies(data: &dyn AbstractData, load_payloads: bool) -> Result<Vec<Dependency>> {
    let mut deps = Vec::new();

    let root = Path::abs_root();

    // Sublayers (layer-level).
    if let Some(value) = data.try_get(&root, FieldKey::SubLayers.as_str())? {
        if let Value::StringVec(sub_paths) = value.into_owned() {
            for asset_path in sub_paths {
                deps.push(Dependency {
                    asset_path,
                    kind: DependencyKind::SubLayer,
                    prim_path: None,
                });
            }
        }
    }

    // Walk the prim hierarchy to find references and payloads.
    let prim_paths = collect_prim_paths(data)?;
    for prim_path in &prim_paths {
        // References.
        if let Some(value) = data.try_get(prim_path, FieldKey::References.as_str())? {
            if let Value::ReferenceListOp(list_op) = value.as_ref() {
                for r in list_op.iter().filter(|r| !r.asset_path.is_empty()) {
                    deps.push(Dependency {
                        asset_path: r.asset_path.clone(),
                        kind: DependencyKind::Reference,
                        prim_path: Some(prim_path.clone()),
                    });
                }
            }
        }

        if load_payloads {
            // Payloads.
            if let Some(value) = data.try_get(prim_path, FieldKey::Payload.as_str())? {
                match value.as_ref() {
                    Value::Payload(p) if !p.asset_path.is_empty() => {
                        deps.push(Dependency {
                            asset_path: p.asset_path.clone(),
                            kind: DependencyKind::Payload,
                            prim_path: Some(prim_path.clone()),
                        });
                    }
                    Value::PayloadListOp(list_op) => {
                        for p in list_op.iter().filter(|p| !p.asset_path.is_empty()) {
                            deps.push(Dependency {
                                asset_path: p.asset_path.clone(),
                                kind: DependencyKind::Payload,
                                prim_path: Some(prim_path.clone()),
                            });
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    Ok(deps)
}

/// Collects all prim and variant spec paths by walking `primChildren`,
/// `variantSetChildren`, and `variantChildren` hierarchies.
fn collect_prim_paths(data: &dyn AbstractData) -> Result<Vec<Path>> {
    let mut result = Vec::new();
    let mut queue = vec![Path::abs_root()];

    while let Some(path) = queue.pop() {
        if !data.has_spec(&path) {
            continue;
        }

        // Skip the pseudo-root itself but process its children.
        if path != Path::abs_root() {
            result.push(path.clone());
        }

        // Regular prim children.
        if let Some(value) = data.try_get(&path, ChildrenKey::PrimChildren.as_str())? {
            if let Value::TokenVec(children) = value.into_owned() {
                for name in children.iter().rev() {
                    if let Ok(child) = path.append_path(name.as_str()) {
                        queue.push(child);
                    }
                }
            }
        }

        // Variant set children (e.g. /Prim -> /Prim{setName=}).
        if let Some(value) = data.try_get(&path, ChildrenKey::VariantSetChildren.as_str())? {
            if let Value::TokenVec(set_names) = value.into_owned() {
                for set_name in &set_names {
                    // Variant children within each set (e.g. /Prim{setName=selA}).
                    let set_path = path.append_variant_selection(set_name, "");
                    if let Some(value) = data.try_get(&set_path, ChildrenKey::VariantChildren.as_str())? {
                        if let Value::TokenVec(variant_names) = value.into_owned() {
                            for variant_name in &variant_names {
                                let variant_path = path.append_variant_selection(set_name, variant_name);
                                queue.push(variant_path);
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(result)
}

/// Opens a single layer from a resolved path, auto-detecting the format.
///
/// Supports `.usda` (text), `.usdc` (binary), `.usd` (auto-detected via magic
/// bytes), and `.usdz` (archive — reads the first layer). Returns the parsed
/// data as a boxed [`AbstractData`].
pub fn open_layer(resolver: &impl Resolver, resolved: &ar::ResolvedPath) -> Result<LayerData> {
    let ext = resolved.extension().and_then(|e| e.to_str()).unwrap_or_default();

    let mut asset = resolver.open_asset(resolved)?;
    let bytes = asset.read_all()?;

    if ext == "usdz" {
        let mut archive = usdz::Archive::from_reader(Cursor::new(bytes)).context("failed to open USDZ archive")?;
        return archive
            .read_first_layer()
            .context("failed to read first layer from USDZ archive");
    }

    // For .usd files, sniff magic bytes to detect binary vs text format.
    let is_binary = ext == "usdc" || (ext == "usd" && bytes.starts_with(usdc::MAGIC));

    if is_binary {
        let data = usdc::CrateData::open(Cursor::new(bytes), true).context("failed to parse USDC layer")?;
        Ok(Box::new(data))
    } else {
        let content = String::from_utf8(bytes).context("layer is not valid UTF-8")?;
        let mut parser = usda::parser::Parser::new(&content);
        let data = parser.parse().context("failed to parse USDA layer")?;
        Ok(Box::new(usda::TextReader::from_data(data)))
    }
}

/// Reads `expressionVariables` from the layer's pseudo-root, if present.
fn read_expression_variables(data: &dyn AbstractData) -> Result<HashMap<String, Value>> {
    let root = Path::abs_root();
    if let Some(value) = data.try_get(&root, FieldKey::ExpressionVariables.as_str())? {
        if let Value::Dictionary(dict) = value.into_owned() {
            return Ok(dict);
        }
    }
    Ok(HashMap::new())
}

/// Evaluates an expression-valued asset path, or passes it through unchanged.
fn resolve_expression(path: &str, vars: &HashMap<String, Value>) -> Result<String> {
    if expr::is_expression(path) {
        let expression = expr::Expr::parse(path).with_context(|| format!("failed to parse expression: {path}"))?;
        let result = expression
            .eval(vars)
            .with_context(|| format!("failed to evaluate expression: {path}"))?;
        match result {
            Value::String(s) => Ok(s),
            other => bail!("expression must evaluate to a string, got: {other:?}"),
        }
    } else {
        Ok(path.to_string())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;
    use crate::ar::DefaultResolver;

    const VENDOR_COMPOSITION: &str = "vendor/usd-wg-assets/test_assets/foundation/stage_composition";

    fn manifest_dir() -> String {
        std::env::var("CARGO_MANIFEST_DIR").unwrap()
    }

    fn composition_path(relative: &str) -> String {
        format!("{}/{}/{}", manifest_dir(), VENDOR_COMPOSITION, relative)
    }

    fn fixture_path(relative: &str) -> String {
        format!("{}/fixtures/{}", manifest_dir(), relative)
    }

    // -----------------------------------------------------------------------
    // Expression evaluation
    // -----------------------------------------------------------------------

    #[test]
    fn expression_sublayer() -> Result<()> {
        let path = fixture_path("expr_sublayer.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 expression-resolved sublayer");
        assert!(layers[0].identifier.contains("expr_sublayer.usda"));
        assert!(layers[1].identifier.contains("expr_sublayer_target.usda"));
        Ok(())
    }

    #[test]
    fn expression_reference() -> Result<()> {
        let path = fixture_path("expr_reference.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 expression-resolved reference");
        assert!(layers[1].identifier.contains("expr_sublayer_target.usda"));
        Ok(())
    }

    #[test]
    fn expression_asset_path() -> Result<()> {
        let path = fixture_path("expr_asset_path.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 expression-resolved reference");
        assert!(layers[0].identifier.contains("expr_asset_path.usda"));
        assert!(layers[1]
            .identifier
            .replace('\\', "/")
            .contains("expr_assets/extraAssets.usda"));
        Ok(())
    }

    #[test]
    fn expression_payload() -> Result<()> {
        let path = fixture_path("expr_payload.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 expression-resolved payload");
        assert!(layers[1].identifier.contains("expr_sublayer_target.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Sublayers
    // -----------------------------------------------------------------------

    #[test]
    fn sublayer_same_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_same_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 sublayer");
        assert!(layers[0].identifier.contains("sublayer_same_folder.usda"));
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_child_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_child_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_parent_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // References
    // -----------------------------------------------------------------------

    #[test]
    fn reference_same_folder() -> Result<()> {
        let path = composition_path("references/reference_same_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 referenced layer");
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn reference_child_folder() -> Result<()> {
        let path = composition_path("references/reference_child_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn reference_parent_folder() -> Result<()> {
        let path = composition_path("references/reference_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Payloads
    // -----------------------------------------------------------------------

    #[test]
    fn payload_same_folder() -> Result<()> {
        let path = composition_path("payload/payload_same_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 payload layer");
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn skip_payloads() -> Result<()> {
        let resolver = DefaultResolver::new();

        let path = composition_path("payload/payload_same_folder.usda");
        let layers = Collector::new(&resolver)
            .load_payloads(false)
            .on_error(|_| Ok(()))
            .collect(&path)?;
        assert_eq!(layers.len(), 1);
        assert!(layers[0].identifier.contains("payload_same_folder.usda"));

        let errors = RefCell::new(0);
        let path = composition_path("payload/payload_invalid.usda");
        let layers = Collector::new(&resolver)
            .load_payloads(false)
            .on_error(|_| {
                *errors.borrow_mut() += 1;
                Ok(())
            })
            .collect(&path)?;
        assert_eq!(layers.len(), 1);
        assert_eq!(*errors.borrow(), 0);
        Ok(())
    }

    #[test]
    fn payload_child_folder() -> Result<()> {
        let path = composition_path("payload/payload_child_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn payload_parent_folder() -> Result<()> {
        let path = composition_path("payload/payload_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Multi-level composition
    // -----------------------------------------------------------------------

    #[test]
    fn teapot_multi_level() -> Result<()> {
        let path = format!("{}/vendor/usd-wg-assets/full_assets/Teapot/Teapot.usd", manifest_dir());
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        // Teapot.usd -> payload Teapot_Payload.usd -> sublayer Teapot_Materials.usd
        assert!(layers.len() >= 3, "expected at least 3 layers, got {}", layers.len());

        assert!(layers[0].identifier.contains("Teapot.usd"));

        let ids = layers.iter().map(|l| l.identifier.as_str()).collect::<Vec<_>>();
        assert!(ids.iter().any(|id| id.contains("Teapot_Payload")));
        assert!(ids.iter().any(|id| id.contains("Teapot_Materials")));

        Ok(())
    }

    // -----------------------------------------------------------------------
    // Error handling
    // -----------------------------------------------------------------------

    /// Default handler errors on unresolvable dependencies (backward compat).
    #[test]
    fn strict_errors_on_missing_reference() {
        let path = composition_path("references/reference_invalid.usda");
        let resolver = DefaultResolver::new();
        assert!(Collector::new(&resolver).collect(&path).is_err());
    }

    /// Custom handler receives correct error details for each dependency kind.
    #[test]
    fn handler_receives_error() -> Result<()> {
        let resolver = DefaultResolver::new();
        let errors = RefCell::new(Vec::new());

        let path = composition_path("references/reference_invalid.usda");
        Collector::new(&resolver)
            .on_error(|e| {
                errors.borrow_mut().push(e);
                Ok(())
            })
            .collect(&path)?;

        let path = composition_path("payload/payload_invalid.usda");
        Collector::new(&resolver)
            .on_error(|e| {
                errors.borrow_mut().push(e);
                Ok(())
            })
            .collect(&path)?;

        let path = composition_path("subLayer/sublayer_invalid.usda");
        Collector::new(&resolver)
            .on_error(|e| {
                errors.borrow_mut().push(e);
                Ok(())
            })
            .collect(&path)?;

        let errors = errors.into_inner();
        assert_eq!(errors.len(), 3);

        let Error::UnresolvedAsset {
            kind, ref prim_path, ..
        } = errors[0];
        assert_eq!(kind, DependencyKind::Reference);
        assert_eq!(prim_path.as_ref().unwrap().as_str(), "/World/invalid_reference");

        let Error::UnresolvedAsset {
            kind, ref prim_path, ..
        } = errors[1];
        assert_eq!(kind, DependencyKind::Payload);
        assert_eq!(prim_path.as_ref().unwrap().as_str(), "/World/invalid_payload");

        let Error::UnresolvedAsset {
            kind, ref prim_path, ..
        } = errors[2];
        assert_eq!(kind, DependencyKind::SubLayer);
        assert!(prim_path.is_none());

        Ok(())
    }

    /// Handler that ignores all errors allows partial layer collection.
    #[test]
    fn handler_can_ignore_errors() -> Result<()> {
        let path = composition_path("references/reference_invalid.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).on_error(|_| Ok(())).collect(&path)?;

        // Root layer loads despite the missing reference.
        assert_eq!(layers.len(), 1);
        assert!(layers[0].identifier.contains("reference_invalid.usda"));
        Ok(())
    }

    #[test]
    fn filter_skips_dependency() -> Result<()> {
        let path = composition_path("references/reference_invalid.usda");
        let resolver = DefaultResolver::new();
        let errors = RefCell::new(0);
        let include = |path: &Path| path.as_str() == "/World/cube";
        let layers = Collector::new(&resolver)
            .prim_dependency_filter(&include)
            .on_error(|_| {
                *errors.borrow_mut() += 1;
                Ok(())
            })
            .collect(&path)?;

        assert_eq!(layers.len(), 1);
        assert_eq!(*errors.borrow(), 0);
        assert!(layers[0].identifier.contains("reference_invalid.usda"));
        Ok(())
    }

    #[test]
    fn save_dispatches_on_extension() -> Result<()> {
        use crate::sdf::{self, SpecType, Value};

        let mut data = sdf::Data::new();
        let root = sdf::Path::abs_root();
        let ps = data.create_spec(root, SpecType::PseudoRoot);
        ps.add("primChildren", Value::TokenVec(vec!["Foo".into()]));
        let foo = sdf::path("/Foo")?;
        let sp = data.create_spec(foo, SpecType::Prim);
        sp.add("specifier", Value::Specifier(sdf::Specifier::Def));
        sp.add("typeName", Value::Token("Xform".into()));

        let layer = Layer::new("test://layer", Box::new(data));
        let dir = tempfile::tempdir()?;

        let usda_path = dir.path().join("layer-save.usda");
        let usdc_path = dir.path().join("layer-save.usdc");
        let usdz_path = dir.path().join("layer-save.usdz");

        layer.save(&usda_path)?;
        layer.save(&usdc_path)?;
        layer.save(&usdz_path)?;

        assert!(std::fs::metadata(&usda_path)?.len() > 0);
        assert!(std::fs::metadata(&usdc_path)?.len() > 0);
        assert!(std::fs::metadata(&usdz_path)?.len() > 0);

        // The usdz should contain an entry we can read back.
        let archive = crate::usdz::Archive::open(&usdz_path)?;
        let name = archive.first_layer_name().expect("usdz has a layer");
        assert!(name.ends_with(".usdc"));
        Ok(())
    }

    #[test]
    fn save_as_usd_writes_binary_and_roundtrips() -> Result<()> {
        use crate::sdf::{self, SpecType, Value};

        let mut data = sdf::Data::new();
        let root = sdf::Path::abs_root();
        let ps = data.create_spec(root, SpecType::PseudoRoot);
        ps.add("primChildren", Value::TokenVec(vec!["Bar".into()]));
        let bar = sdf::path("/Bar")?;
        let sp = data.create_spec(bar.clone(), SpecType::Prim);
        sp.add("specifier", Value::Specifier(sdf::Specifier::Def));
        sp.add("typeName", Value::Token("Cube".into()));

        let layer = Layer::new("test://layer-usd", Box::new(data));
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("layer-save.usd");
        layer.save(&path)?;

        // Writer chose binary for `.usd` — first bytes must be the USDC magic.
        let bytes = std::fs::read(&path)?;
        assert!(
            bytes.starts_with(crate::usdc::MAGIC),
            "writer should emit binary for .usd, got magic {:?}",
            &bytes[..crate::usdc::MAGIC.len().min(bytes.len())],
        );

        // Reader's magic-byte auto-detection must accept it.
        let resolver = DefaultResolver::new();
        let resolved = resolver.resolve(path.to_str().unwrap()).unwrap();
        let round = open_layer(&resolver, &resolved)?;
        assert_eq!(round.spec_type(&bar), Some(SpecType::Prim));
        assert_eq!(
            round.get(&bar, "typeName").unwrap().into_owned(),
            Value::Token("Cube".into())
        );
        Ok(())
    }

    #[test]
    fn save_rejects_unknown_extension() {
        use crate::sdf::{self, SpecType};
        let mut data = sdf::Data::new();
        data.create_spec(sdf::Path::abs_root(), SpecType::PseudoRoot);
        let layer = Layer::new("test://layer", Box::new(data));
        let err = layer.save("/tmp/openusd-bad.xyz").unwrap_err();
        assert!(err.to_string().contains("unsupported"));
    }

    /// Per spec §16.2, `.usd` is a valid extension for text layers. Verify we
    /// can force-write text to a `.usd` file and the reader correctly
    /// auto-detects it as text via the absence of the USDC magic.
    #[test]
    fn save_as_forces_text_to_usd_extension() -> Result<()> {
        use crate::sdf::{self, SpecType, Value};

        let mut data = sdf::Data::new();
        let root = sdf::Path::abs_root();
        let ps = data.create_spec(root, SpecType::PseudoRoot);
        ps.add("primChildren", Value::TokenVec(vec!["Text".into()]));
        let prim = sdf::path("/Text")?;
        let sp = data.create_spec(prim.clone(), SpecType::Prim);
        sp.add("specifier", Value::Specifier(sdf::Specifier::Def));
        sp.add("typeName", Value::Token("Xform".into()));

        let layer = Layer::new("test://text-as-usd", Box::new(data));
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("text-as-usd.usd");
        layer.save_as(&path, LayerFormat::Usda)?;

        // Emitted bytes must NOT start with the binary magic — they're text.
        let bytes = std::fs::read(&path)?;
        assert!(
            !bytes.starts_with(crate::usdc::MAGIC),
            "save_as(Usda) should produce text, but output begins with USDC magic",
        );
        assert!(bytes.starts_with(b"#usda"), "text output must start with #usda header");

        // Reader auto-detect (magic-byte sniff) accepts it as text.
        let resolver = DefaultResolver::new();
        let resolved = resolver.resolve(path.to_str().unwrap()).unwrap();
        let round = open_layer(&resolver, &resolved)?;
        assert_eq!(round.spec_type(&prim), Some(SpecType::Prim));
        assert_eq!(
            round.get(&prim, "typeName").unwrap().into_owned(),
            Value::Token("Xform".into())
        );
        Ok(())
    }

    #[test]
    fn layer_format_from_extension_matches_spec() {
        assert_eq!(LayerFormat::from_extension("usda"), Some(LayerFormat::Usda));
        assert_eq!(LayerFormat::from_extension("usdc"), Some(LayerFormat::Usdc));
        assert_eq!(LayerFormat::from_extension("usd"), Some(LayerFormat::Usdc));
        assert_eq!(LayerFormat::from_extension("USDA"), Some(LayerFormat::Usda));
        assert_eq!(LayerFormat::from_extension("usdz"), Some(LayerFormat::Usdz));
        assert_eq!(LayerFormat::from_extension("xyz"), None);
        assert_eq!(LayerFormat::from_extension(""), None);
    }

    // -----------------------------------------------------------------------
    // Authoring API
    // -----------------------------------------------------------------------

    #[test]
    fn create_prim_basic() -> Result<()> {
        let mut layer = Layer::new_anonymous("anon.usda");
        let mut prim = layer.create_prim("/World", sdf::Specifier::Def, "Xform")?;
        prim.set_kind("group");

        let world = layer.prim("/World").expect("prim authored");
        assert_eq!(world.type_name(), Some("Xform"));
        assert_eq!(world.specifier(), Some(sdf::Specifier::Def));
        assert_eq!(world.kind(), Some("group"));
        Ok(())
    }

    #[test]
    fn auto_ancestor_chain() -> Result<()> {
        let mut layer = Layer::new_anonymous("anon.usda");
        layer.create_prim("/A/B/C", sdf::Specifier::Def, "Mesh")?;

        // Leaf is Def; ancestors are Over.
        assert_eq!(
            layer.prim("/A/B/C").and_then(|p| p.specifier()),
            Some(sdf::Specifier::Def)
        );
        assert_eq!(
            layer.prim("/A/B").and_then(|p| p.specifier()),
            Some(sdf::Specifier::Over)
        );
        assert_eq!(layer.prim("/A").and_then(|p| p.specifier()), Some(sdf::Specifier::Over));
        Ok(())
    }

    #[test]
    fn prim_children() -> Result<()> {
        let mut layer = Layer::new_anonymous("anon.usda");
        layer.create_prim("/World", sdf::Specifier::Def, "Xform")?;
        layer.create_prim("/World/Mesh", sdf::Specifier::Def, "Mesh")?;
        layer.create_prim("/World/Cube", sdf::Specifier::Def, "Cube")?;

        let root = layer.pseudo_root().expect("pseudo-root present");
        assert_eq!(root.prim_children(), Some(["World".to_string()].as_slice()));

        let world = layer.prim("/World").expect("prim");
        assert_eq!(
            world.prim_children(),
            Some(["Mesh".to_string(), "Cube".to_string()].as_slice())
        );
        Ok(())
    }

    #[test]
    fn property_children() -> Result<()> {
        let mut layer = Layer::new_anonymous("anon.usda");
        layer.create_prim("/Mesh", sdf::Specifier::Def, "Mesh")?;
        layer.create_attr("/Mesh.points", "point3f[]", sdf::Variability::Varying, false)?;
        layer.create_attr("/Mesh.normals", "normal3f[]", sdf::Variability::Varying, false)?;
        layer.create_relationship("/Mesh.material:binding", sdf::Variability::Varying, false)?;

        let mesh = layer.prim("/Mesh").expect("prim");
        assert_eq!(
            mesh.property_children(),
            Some(
                [
                    "points".to_string(),
                    "normals".to_string(),
                    "material:binding".to_string()
                ]
                .as_slice()
            )
        );
        Ok(())
    }

    #[test]
    fn relationship_variability() -> Result<()> {
        let mut layer = Layer::new_anonymous("anon.usda");
        layer.create_relationship("/Mesh.material:binding", sdf::Variability::Uniform, false)?;

        let rel = layer.relationship("/Mesh.material:binding").expect("relationship");
        assert_eq!(rel.variability(), sdf::Variability::Uniform);

        layer.create_relationship("/Mesh.material:binding", sdf::Variability::Varying, false)?;
        let rel = layer.relationship("/Mesh.material:binding").expect("relationship");
        assert_eq!(rel.variability(), sdf::Variability::Varying);
        assert!(rel.get(FieldKey::Variability.as_str()).is_none());
        Ok(())
    }

    #[test]
    fn bad_prim_children_errors() {
        let mut layer = Layer::new_anonymous("anon.usda");
        layer
            .data
            .as_data_mut()
            .unwrap()
            .spec_mut(&Path::abs_root())
            .unwrap()
            .add(ChildrenKey::PrimChildren, Value::String("bad".into()));

        let err = layer.create_prim("/A", sdf::Specifier::Def, "Xform").unwrap_err();
        assert!(matches!(err, AuthoringError::InvalidPath { .. }));

        let root = layer
            .data
            .as_data()
            .unwrap()
            .spec(&Path::abs_root())
            .expect("pseudo-root present");
        assert!(matches!(
            root.get(ChildrenKey::PrimChildren.as_str()),
            Some(Value::String(value)) if value == "bad"
        ));
    }

    #[test]
    fn bad_property_children_errors() -> Result<()> {
        let mut layer = Layer::new_anonymous("anon.usda");
        layer.create_prim("/Mesh", sdf::Specifier::Def, "Mesh")?;
        layer
            .data
            .as_data_mut()
            .unwrap()
            .spec_mut(&sdf::path("/Mesh").unwrap())
            .unwrap()
            .add(ChildrenKey::PropertyChildren, Value::String("bad".into()));

        let err = layer
            .create_relationship("/Mesh.material:binding", sdf::Variability::Varying, false)
            .unwrap_err();
        assert!(matches!(err, AuthoringError::InvalidPath { .. }));

        let data = layer.data.as_data().unwrap();
        assert!(data.spec(&sdf::path("/Mesh.material:binding").unwrap()).is_none());
        let mesh = data.spec(&sdf::path("/Mesh").unwrap()).expect("prim present");
        assert!(matches!(
            mesh.get(ChildrenKey::PropertyChildren.as_str()),
            Some(Value::String(value)) if value == "bad"
        ));
        Ok(())
    }

    #[test]
    fn attr_samples() -> Result<()> {
        let mut layer = Layer::new_anonymous("anon.usda");
        layer.create_prim("/Sphere", sdf::Specifier::Def, "Sphere")?;

        let mut radius = layer.create_attr("/Sphere.radius", "double", sdf::Variability::Varying, false)?;
        radius.set_default(Value::Double(2.5));
        radius.set_time_sample(0.0, Value::Double(1.0));
        radius.set_time_sample(10.0, Value::Double(3.0));
        // Out-of-order insert lands in sorted position.
        radius.set_time_sample(5.0, Value::Double(2.0));

        let read = layer.attr("/Sphere.radius").expect("attr");
        assert_eq!(read.type_name(), Some("double"));
        assert_eq!(read.default(), Some(&Value::Double(2.5)));
        let samples = read.time_samples().expect("samples authored");
        let times: Vec<f64> = samples.iter().map(|(t, _)| *t).collect();
        assert_eq!(times, vec![0.0, 5.0, 10.0]);
        Ok(())
    }

    #[test]
    fn wrong_ancestor_type() {
        let mut layer = Layer::new_anonymous("anon.usda");
        // Plant a non-Prim spec at a prim-shaped path through the public data API.
        layer
            .data
            .as_data_mut()
            .unwrap()
            .create_spec(sdf::path("/A").unwrap(), sdf::SpecType::Attribute);

        let err = layer.create_prim("/A/B", sdf::Specifier::Def, "Xform").unwrap_err();
        assert!(matches!(err, AuthoringError::InvalidPath { .. }));
        let err = layer
            .create_attr("/A.x", "double", sdf::Variability::Varying, false)
            .unwrap_err();
        assert!(matches!(err, AuthoringError::InvalidPath { .. }));
    }

    #[test]
    fn failed_prim_chain_creation_is_atomic() {
        let mut layer = Layer::new_anonymous("anon.usda");
        let bad_child = sdf::path("/A/B").unwrap();
        layer
            .data
            .as_data_mut()
            .unwrap()
            .create_spec(bad_child, sdf::SpecType::Attribute);

        let err = layer.create_prim("/A/B", sdf::Specifier::Def, "Xform").unwrap_err();
        assert!(matches!(err, AuthoringError::InvalidPath { .. }));

        let data = layer.data.as_data().unwrap();
        assert!(data.spec(&sdf::path("/A").unwrap()).is_none());
        let root = data.spec(&Path::abs_root()).expect("pseudo-root present");
        assert!(root.get(ChildrenKey::PrimChildren.as_str()).is_none());
    }

    #[test]
    fn nan_time_sample() -> Result<()> {
        let mut layer = Layer::new_anonymous("anon.usda");
        layer.create_prim("/Sphere", sdf::Specifier::Def, "Sphere")?;
        let mut r = layer.create_attr("/Sphere.radius", "double", sdf::Variability::Varying, false)?;

        r.set_time_sample(1.0, Value::Double(1.0));
        r.set_time_sample(f64::NAN, Value::Double(99.0));
        r.set_time_sample(2.0, Value::Double(2.0));
        // NaN does not collide with finite samples — both finite values survive.
        let samples = layer.attr("/Sphere.radius").unwrap().time_samples().unwrap().to_vec();
        let finite: Vec<f64> = samples.iter().map(|(t, _)| *t).filter(|t| t.is_finite()).collect();
        assert_eq!(finite, vec![1.0, 2.0]);

        // erase_time_sample(NaN) can find the NaN entry via total_cmp.
        assert!(layer.attr_mut("/Sphere.radius").unwrap().erase_time_sample(f64::NAN));
        let times: Vec<f64> = layer
            .attr("/Sphere.radius")
            .unwrap()
            .time_samples()
            .unwrap()
            .iter()
            .map(|(t, _)| *t)
            .collect();
        assert_eq!(times, vec![1.0, 2.0]);
        Ok(())
    }

    #[test]
    fn override_prim() -> Result<()> {
        let mut layer = Layer::new_anonymous("anon.usda");
        layer.override_prim("/A/B")?;

        assert_eq!(layer.prim("/A").and_then(|p| p.specifier()), Some(sdf::Specifier::Over));
        assert_eq!(
            layer.prim("/A/B").and_then(|p| p.specifier()),
            Some(sdf::Specifier::Over)
        );

        // override_prim on an existing def leaves the specifier untouched.
        layer.create_prim("/Defined", sdf::Specifier::Def, "Xform")?;
        layer.override_prim("/Defined")?;
        assert_eq!(
            layer.prim("/Defined").and_then(|p| p.specifier()),
            Some(sdf::Specifier::Def)
        );
        Ok(())
    }

    #[test]
    fn pseudo_root_metadata() -> Result<()> {
        let mut layer = Layer::new_anonymous("anon.usda");
        {
            let mut root = layer.pseudo_root_mut().expect("writable");
            root.set_default_prim("World");
            root.set_documentation("auto-generated");
            root.set_start_time_code(1.0);
            root.set_end_time_code(24.0);
            root.add_sublayer("./over.usda");
            root.add_sublayer("./over.usda");
        }
        let root = layer.pseudo_root().expect("present");
        assert_eq!(root.default_prim(), Some("World"));
        assert_eq!(root.documentation(), Some("auto-generated"));
        assert_eq!(root.start_time_code(), Some(1.0));
        assert_eq!(root.end_time_code(), Some(24.0));
        assert_eq!(
            root.sublayers(),
            Some(["./over.usda".to_string(), "./over.usda".to_string()].as_slice())
        );
        Ok(())
    }

    #[test]
    fn read_only_layer() {
        // A layer wrapping an empty Data via the public AbstractData trait but
        // *without* the writable hook would normally come from a file reader.
        // We simulate by wrapping a custom no-op AbstractData.
        struct ReadOnly;
        impl AbstractData for ReadOnly {
            fn has_spec(&self, _: &Path) -> bool {
                false
            }
            fn has_field(&self, _: &Path, _: &str) -> bool {
                false
            }
            fn spec_type(&self, _: &Path) -> Option<sdf::SpecType> {
                None
            }
            fn try_get(&self, _: &Path, _: &str) -> Result<Option<std::borrow::Cow<'_, Value>>> {
                Ok(None)
            }
            fn list(&self, _: &Path) -> Option<Vec<String>> {
                None
            }
            fn paths(&self) -> Vec<Path> {
                Vec::new()
            }
        }

        let mut layer = Layer::new("file.usda", Box::new(ReadOnly));
        let err = layer.create_prim("/World", sdf::Specifier::Def, "Xform").unwrap_err();
        assert!(matches!(err, AuthoringError::ReadOnly { .. }));
    }

    #[test]
    fn invalid_paths() {
        let mut layer = Layer::new_anonymous("anon.usda");
        assert!(matches!(
            layer.create_prim("/", sdf::Specifier::Def, "Xform").unwrap_err(),
            AuthoringError::InvalidPath { .. }
        ));
        assert!(matches!(
            layer.create_prim("/A.foo", sdf::Specifier::Def, "Xform").unwrap_err(),
            AuthoringError::InvalidPath { .. }
        ));
        assert!(matches!(
            layer
                .create_attr("/A", "double", sdf::Variability::Varying, false)
                .unwrap_err(),
            AuthoringError::InvalidPath { .. }
        ));
        // Relative property paths must error, not panic in ensure_prim_chain.
        assert!(matches!(
            layer
                .create_attr("A.foo", "double", sdf::Variability::Varying, false)
                .unwrap_err(),
            AuthoringError::InvalidPath { .. }
        ));
        assert!(matches!(
            layer
                .create_relationship("A.foo", sdf::Variability::Varying, false)
                .unwrap_err(),
            AuthoringError::InvalidPath { .. }
        ));
        // Root-level property paths (`/.foo`) must also error, not panic.
        assert!(matches!(
            layer
                .create_attr("/.foo", "double", sdf::Variability::Varying, false)
                .unwrap_err(),
            AuthoringError::InvalidPath { .. }
        ));
        // Target-bracket property paths slip past `is_property_path` because the
        // tail after the last `.` is alphanumeric — split_property_path must reject them.
        assert!(matches!(
            layer
                .create_attr("/A.rel[/Target].attr", "double", sdf::Variability::Varying, false)
                .unwrap_err(),
            AuthoringError::InvalidPath { .. }
        ));
        // Variant-selection segments aren't USD identifiers — reject them in prim paths.
        assert!(matches!(
            layer
                .create_prim("/A{x=y}/B", sdf::Specifier::Def, "Xform")
                .unwrap_err(),
            AuthoringError::InvalidPath { .. }
        ));
    }

    #[test]
    fn usda_roundtrip() -> Result<()> {
        let mut layer = Layer::new_anonymous("scene.usda");
        layer.pseudo_root_mut().unwrap().set_default_prim("World");
        layer.create_prim("/World", sdf::Specifier::Def, "Xform")?;
        let mut sphere = layer.create_prim("/World/Sphere", sdf::Specifier::Def, "Sphere")?;
        sphere.set_kind("component");
        let mut radius = layer.create_attr("/World/Sphere.radius", "double", sdf::Variability::Varying, false)?;
        radius.set_default(Value::Double(1.5));
        let material = sdf::path("/World/Material")?;
        layer.create_prim(&material, sdf::Specifier::Def, "Material")?;
        let mut binding =
            layer.create_relationship("/World/Sphere.material:binding", sdf::Variability::Varying, false)?;
        binding.add_target(material.clone());
        let mut surface = layer.create_attr(
            "/World/Sphere.inputs:surface",
            "token",
            sdf::Variability::Varying,
            false,
        )?;
        surface.set_connection_paths([sdf::path("/World/Material.outputs:surface")?]);

        let tmp = std::env::temp_dir().join("openusd_authoring_roundtrip.usda");
        layer.save_as(&tmp, LayerFormat::Usda)?;

        let parsed = usda::TextReader::read(&tmp)?;
        assert_eq!(parsed.spec_type(&sdf::path("/World")?), Some(sdf::SpecType::Prim));
        assert_eq!(
            parsed.spec_type(&sdf::path("/World/Sphere")?),
            Some(sdf::SpecType::Prim)
        );
        assert_eq!(
            parsed.spec_type(&sdf::path("/World/Sphere.radius")?),
            Some(sdf::SpecType::Attribute)
        );
        assert_eq!(
            parsed
                .get(&sdf::Path::abs_root(), FieldKey::DefaultPrim.as_str())?
                .into_owned(),
            Value::Token("World".into())
        );
        match parsed
            .get(
                &sdf::path("/World/Sphere.material:binding")?,
                FieldKey::TargetPaths.as_str(),
            )?
            .into_owned()
        {
            Value::PathListOp(op) => {
                assert!(op.explicit);
                assert_eq!(op.explicit_items, vec![material]);
            }
            other => panic!("expected relationship targets as PathListOp, got {other:?}"),
        }
        match parsed
            .get(
                &sdf::path("/World/Sphere.inputs:surface")?,
                FieldKey::ConnectionPaths.as_str(),
            )?
            .into_owned()
        {
            Value::PathListOp(op) => {
                assert!(op.explicit);
                assert_eq!(op.explicit_items, vec![sdf::path("/World/Material.outputs:surface")?]);
            }
            other => panic!("expected connection paths as PathListOp, got {other:?}"),
        }
        let _ = std::fs::remove_file(&tmp);
        Ok(())
    }
}
