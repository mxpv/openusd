//! Layer loading and the format registry.
//!
//! [`LayerRegistry`] owns the [`ar::Resolver`] and load policy a stage opens
//! layers with, and dispatches through the built-in format set
//! ([`find_by_extension`](LayerRegistry::find_by_extension) /
//! [`find_by_id`](LayerRegistry::find_by_id)) to the
//! [`FileFormat`](super::FileFormat) claiming each layer's extension. It is the
//! Rust seam for C++ `Sdf_LayerRegistry` and `SdfFileFormat::FindByExtension`:
//! it holds the layers [`find_or_open`](LayerRegistry::find_or_open) opens,
//! one per identifier, shared through [`sdf::LayerHandle`]s. Custom format
//! registration grows here too.
//!
//! References and payloads are not followed here. Composition opens each
//! reference/payload target layer on demand when it reaches the arc (see
//! [`crate::pcp`]), so an un-visited subtree never loads its layers. Only the
//! sublayer stack is opened eagerly, since a layer's sublayers contribute
//! opinions to its own namespace and so must be present whenever the layer is
//! (spec 10.3.1.1).

use std::borrow::Cow;
use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::io;
use std::rc::{Rc, Weak};
use std::sync::Arc;
use std::time::SystemTime;

use crate::sdf::{self, expr};
use crate::usda::UsdaFileFormat;
use crate::usdc::UsdcFileFormat;
use crate::usdz::UsdzFileFormat;
use crate::{ar, vt};

static USDA: UsdaFileFormat = UsdaFileFormat;
static USDC: UsdcFileFormat = UsdcFileFormat;
static USDZ: UsdzFileFormat = UsdzFileFormat;

/// The built-in formats, in lookup order — the Rust analog of C++
/// `SdfFileFormat`'s static plugin set. Custom formats will register alongside
/// these on a [`LayerRegistry`] in the future; today the set is fixed.
static DEFAULT_FORMATS: &[&dyn sdf::FileFormat] = &[&USDA, &USDC, &USDZ];

/// An error encountered while opening a layer's sublayer stack that may be
/// recoverable.
///
/// A missing sublayer can be tolerated so loading continues; the `on_error`
/// callback passed to [`LayerRegistry::open_stack`] configures that policy.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum Error {
    /// A sublayer asset path could not be resolved to a physical location.
    #[error("failed to resolve sublayer asset: {asset_path} (referenced by {referencing_layer})")]
    UnresolvedAsset {
        /// The sublayer asset path that could not be resolved.
        asset_path: String,
        /// The layer that declared the sublayer.
        referencing_layer: String,
    },

    /// A sublayer resolved to a physical location but could not be read or
    /// parsed. Only the bad sublayer is dropped; the layer that declared it (and
    /// the rest of the stack) still loads, matching C++ `SdfLayer`, which opens
    /// the parent and reports the unreadable sublayer.
    #[error("failed to read sublayer asset: {asset_path} (referenced by {referencing_layer})")]
    UnreadableAsset {
        /// The sublayer asset path that resolved but could not be read.
        asset_path: String,
        /// The layer that declared the sublayer.
        referencing_layer: String,
        /// The underlying read or parse error, shared with the stage's record
        /// of the failure.
        #[source]
        source: Arc<LoadError>,
    },

    /// An expression-valued (`${VAR}`) sublayer path failed to evaluate, so the
    /// entry selects nothing and only this sublayer is dropped. Converts to the
    /// same composition diagnostic the layer graph regenerates for the entry on
    /// each stack rebuild, so the two report one failure identically.
    #[error("invalid sublayer expression {expression} in {referencing_layer}: {reason}")]
    InvalidExpression {
        /// The raw, unevaluated backtick expression.
        expression: String,
        /// The layer that declared the sublayer.
        referencing_layer: String,
        /// The evaluator's errors, joined.
        reason: String,
    },
}

/// Operational failure that aborts a registry load.
///
/// Recoverable per-sublayer problems are reported as [`Error`] values through
/// the caller's `on_error` handler and never travel through this type.
#[derive(Debug, thiserror::Error)]
pub(crate) enum LoadError {
    /// The asset did not resolve to a physical location.
    #[error("failed to resolve asset path: {asset_path}")]
    Unresolved {
        /// The asset path that did not resolve.
        asset_path: String,
    },

    /// No registered file format claims the resolved location.
    #[error("no file format registered for {resolved}")]
    UnsupportedFormat {
        /// The resolved location.
        resolved: String,
    },

    /// The chosen format failed to read the asset.
    #[error(transparent)]
    Format(#[from] sdf::FormatError),

    /// Reading a field out of an opened layer's data failed.
    #[error(transparent)]
    Data(#[from] sdf::DataError),

    /// The caller's `on_error` handler declined to recover from a sublayer
    /// load failure, aborting the load with it.
    #[error(transparent)]
    Rejected(#[from] Error),

    /// The registry refused to hold a layer it read, or its layers were in use.
    #[error(transparent)]
    Layer(#[from] sdf::LayerError),
}

/// Projects a load failure onto the public [`crate::Error`]: resolution and
/// format-dispatch failures map to the root variants that name them, layer
/// read failures convert transparently, and a rejected sublayer failure rides
/// whole — Display and typed source intact — as a decode failure of the stack
/// being loaded.
impl From<LoadError> for crate::Error {
    fn from(error: LoadError) -> Self {
        match error {
            LoadError::Unresolved { asset_path } => crate::Error::UnresolvedAsset(asset_path),
            LoadError::UnsupportedFormat { resolved } => crate::Error::UnsupportedFormat(resolved),
            LoadError::Format(error) => error.into(),
            LoadError::Data(error) => error.into(),
            LoadError::Rejected(error) => crate::Error::Format(sdf::FormatError::Decode(Box::new(error))),
            LoadError::Layer(error) => error.into(),
        }
    }
}

/// Owns layer loading for a stage: the [`ar::Resolver`] that finds and opens
/// layers, the built-in format set, and whether payload arcs are expanded.
///
/// The `pcp::LayerGraph` holds one and opens reference and payload targets on
/// demand through it. The resolver is private: every path that resolves and
/// reads a layer is a method here, and the registry stands in as the
/// [`ar::Resolver`] it fronts where one is asked for, with the identifier
/// rules below applied. This is the Rust analog of C++ `Sdf_LayerRegistry`,
/// less custom format registration.
///
/// The registry also holds layers, one per identifier, shared through
/// [`sdf::LayerHandle`]s: [`find_or_open`](Self::find_or_open) returns the
/// layer already open at an identifier, unsaved edits included, and opens it
/// only when none is (C++ `SdfLayer::FindOrOpen`). Cloning the registry shares
/// its resolver and the layers it holds. Every stage opened on the registry
/// holds its layers here, so stages on one registry share each layer and see
/// each other's edits.
///
/// A layer stays held while any handle to it exists. Once its last handle
/// drops, it is freed at the next [`sweep`](Self::sweep), or at once when no
/// handle into the registry remains. The registry itself refers to its layers
/// weakly, as C++ `Sdf_LayerRegistry` does. A registry kept by a layer it
/// holds, as that layer's resolver, therefore does not keep the layer alive.
/// An edit through one handle borrows the registry's layers whole, so it
/// conflicts with any other access to them (see [`sdf::LayerHandle`]).
#[derive(Clone)]
pub struct LayerRegistry {
    resolver: Rc<dyn ar::Resolver>,
    /// The store of the layers handles share, shared by every clone of the
    /// registry. Weak: the handles own the store, and the registry starts a
    /// new one when it next holds a layer after the last handle has dropped.
    store: Rc<Cell<Weak<sdf::LayerStore>>>,
}

/// Where a [`LayerRegistry`] lookup of an asset path ends.
enum Located {
    /// At a layer open in the registry.
    Open(sdf::LayerHandle),
    /// At a location no open layer was read from.
    Closed {
        /// The canonical identifier the path names.
        identifier: String,
        /// The location it resolves to.
        resolved: ar::ResolvedPath,
    },
    /// Nowhere: the path does not resolve, or names an anonymous layer that
    /// is not open.
    Unresolved,
}

/// A layer as the registry reads it: its canonical identifier,
/// the location it resolved to, and its parsed data, ahead of the
/// [`sdf::Layer`] or sublayer walk built from it.
pub(crate) struct PreparedLayer {
    /// The layer's canonical identifier.
    pub identifier: String,
    /// Where the layer was found.
    pub resolved: ar::ResolvedPath,
    /// The layer's data.
    pub data: sdf::LayerData,
    /// The format the data was read in, or `None` for data that was never
    /// read in one (a layer built in memory).
    pub format: Option<&'static dyn sdf::FileFormat>,
    /// When the asset was modified, taken before its content was read, so a
    /// change made while it was read is not mistaken for the content read.
    pub modified: sdf::layer::AssetTime,
}

/// A layer a load reached, with the identifier the load asked for it under.
/// That is another spelling of the layer's own identifier when the registry
/// held the file under the layer's, so the graph can record it as an alias.
pub(crate) struct LoadedLayer {
    /// The identifier the load asked for.
    pub(crate) identifier: String,
    /// The layer, which the registry holds.
    pub(crate) handle: sdf::LayerHandle,
}

/// What the caller of a stack open has of a layer the open reaches, by
/// canonical identifier.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Presence {
    /// The caller does not hold it: the open reads and emits it.
    Absent,
    /// The caller holds it: the open does not emit it, and walks it again only
    /// in a reload.
    Held,
    /// The caller leaves it out: the open does not read a sublayer it
    /// excludes, and reads and emits an excluded root without walking below
    /// it.
    Excluded,
}

impl From<sdf::LayerHandle> for LoadedLayer {
    /// The layer `handle` names, asked for under its own identifier.
    fn from(handle: sdf::LayerHandle) -> Self {
        Self {
            identifier: handle.identifier().to_owned(),
            handle,
        }
    }
}

/// The registry as the resolver it fronts. An identifier passes the
/// registry's own rules (`create_identifier`, `in_memory_identifier`,
/// `is_context_dependent_path`); every other call reaches the resolver as it
/// is.
impl ar::Resolver for LayerRegistry {
    fn create_identifier(&self, asset_path: &str, anchor: Option<&ar::ResolvedPath>) -> String {
        LayerRegistry::create_identifier(self, asset_path, anchor)
    }

    fn resolve(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
        LayerRegistry::resolve(self, asset_path)
    }

    fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
        self.resolver.resolve_for_new_asset(asset_path)
    }

    fn open_asset(&self, resolved_path: &ar::ResolvedPath) -> io::Result<Box<dyn ar::Asset>> {
        LayerRegistry::open_asset(self, resolved_path)
    }

    fn extension<'a>(&self, asset_path: &'a str) -> &'a str {
        self.resolver.extension(asset_path)
    }

    fn is_context_dependent_path(&self, asset_path: &str) -> bool {
        LayerRegistry::is_context_dependent_path(self, asset_path)
    }

    fn in_memory_identifier<'a>(&self, asset_path: &'a str) -> Cow<'a, str> {
        LayerRegistry::in_memory_identifier(self, asset_path)
    }

    fn asset_info(&self, asset_path: &str, resolved_path: &ar::ResolvedPath) -> ar::AssetInfo {
        self.resolver.asset_info(asset_path, resolved_path)
    }

    fn modification_timestamp(&self, asset_path: &str, resolved_path: &ar::ResolvedPath) -> Option<SystemTime> {
        self.resolver.modification_timestamp(asset_path, resolved_path)
    }

    fn identity(&self) -> String {
        LayerRegistry::identity(self)
    }

    fn cache_id(&self) -> Option<u64> {
        self.resolver.cache_id()
    }
}

impl Default for LayerRegistry {
    /// A registry over the filesystem [`DefaultResolver`](ar::DefaultResolver)
    /// and the built-in formats — what [`Stage::builder`](crate::usd::Stage)
    /// uses unless a registry is configured.
    fn default() -> Self {
        Self::new(Box::new(ar::DefaultResolver::new()))
    }
}

impl LayerRegistry {
    /// A registry resolving asset paths through `resolver`.
    pub fn new(resolver: Box<dyn ar::Resolver>) -> Self {
        Self {
            resolver: Rc::from(resolver),
            store: Rc::default(),
        }
    }

    /// The layer open in this registry at `asset_path`, if any, unsaved edits
    /// included (C++ `SdfLayer::Find`). The path is canonicalized first, as
    /// [`find_or_open`](Self::find_or_open) does, and a layer read from the
    /// file it resolves to under another identifier is found too. Fails with
    /// [`LayerError::Busy`](sdf::LayerError::Busy) when called from inside an
    /// edit on this registry.
    pub fn find(&self, asset_path: &str) -> Result<Option<sdf::LayerHandle>, sdf::LayerError> {
        Ok(match self.locate(self.create_identifier(asset_path, None))? {
            Located::Open(handle) => Some(handle),
            Located::Closed { .. } | Located::Unresolved => None,
        })
    }

    /// The layer open in this registry at `asset_path`, or else that layer read
    /// and held here, or `None` when the path does not resolve (C++
    /// `SdfLayer::FindOrOpen`). A layer already open is returned as it is, with
    /// any edits not yet saved; a changed file is read again only by a reload.
    /// Only the layer itself is opened: the sublayers, references and payloads
    /// it declares stay the asset paths it authored. Fails with
    /// [`LayerError::Busy`](sdf::LayerError::Busy), before reading anything,
    /// when it would have to open a layer from inside an edit on this registry,
    /// or from a resolver a stage calls while it reads the registry's layers.
    pub fn find_or_open(&self, asset_path: &str) -> crate::Result<Option<sdf::LayerHandle>> {
        let _scope = ar::CacheScope::begin();
        let identifier = self.create_identifier(asset_path, None);
        Ok(self.find_or_read(&identifier)?.map(|layer| layer.handle))
    }

    /// Where the canonical `identifier` leads: to a layer open here under it
    /// or read from the location it resolves to, or to that location, or
    /// nowhere. An anonymous layer is found by identifier only.
    fn locate(&self, identifier: String) -> Result<Located, sdf::LayerError> {
        let store = self.held();
        if let Some(store) = &store
            && let Some(handle) = store.find(&identifier, None)?
        {
            return Ok(Located::Open(handle));
        }
        if sdf::Layer::is_anonymous_identifier(&identifier) {
            return Ok(Located::Unresolved);
        }
        let Some(resolved) = self.resolve_layer(&identifier) else {
            return Ok(Located::Unresolved);
        };
        if let Some(store) = &store
            && let Some(handle) = store.find(&identifier, resolved.to_str())?
        {
            return Ok(Located::Open(handle));
        }
        Ok(Located::Closed { identifier, resolved })
    }

    /// The store, while any handle keeps it.
    fn held(&self) -> Option<Rc<sdf::LayerStore>> {
        let weak = self.store.take();
        let store = weak.upgrade();
        self.store.set(weak);
        store
    }

    /// Fails with [`LayerError::Busy`](sdf::LayerError::Busy) while a
    /// composition read or an edit holds the registry's layers. A load that
    /// joins its layers to a stage checks first, as the stage subscribes to
    /// each layer, held already or not.
    fn ensure_writable(&self) -> Result<(), sdf::LayerError> {
        self.held().map_or(Ok(()), |store| store.ensure_writable())
    }

    /// The store, started anew when no handle keeps one.
    pub(crate) fn store(&self) -> Rc<sdf::LayerStore> {
        self.held().unwrap_or_else(|| {
            let store = Rc::default();
            self.store.set(Rc::downgrade(&store));
            store
        })
    }

    /// Hold `layer` here, where [`find`](Self::find) returns it, and return a
    /// handle to it. Any edit it has staged is committed, without notifying its
    /// sinks, and the registry's resolver anchors, reads and saves it from then
    /// on, as it does a layer the registry reads. Fails, handing the layer back
    /// in the [`sdf::AdoptError`], with
    /// [`LayerError::Duplicate`](sdf::LayerError::Duplicate) when a layer with
    /// its identifier, or read from its file, is already open here, and with
    /// [`LayerError::Busy`](sdf::LayerError::Busy) from inside an edit on this
    /// registry, or from a resolver a stage calls while it reads the registry's
    /// layers.
    pub fn adopt(&self, mut layer: sdf::Layer) -> Result<sdf::LayerHandle, sdf::AdoptError> {
        layer.set_resolver(Rc::clone(&self.resolver));
        self.store().insert(layer)
    }

    /// Free the layers whose last handle has dropped. A dropped handle leaves
    /// its layer in memory until a sweep, which
    /// [`find_or_open`](Self::find_or_open) and [`adopt`](Self::adopt) run
    /// before they add a layer, unless it was the last handle into the
    /// registry, which frees every layer it held. A no-op while an edit on this
    /// registry is in progress, while a resolver a stage calls as it reads the
    /// registry's layers runs, or while a stage on it holds its composition
    /// borrowed or is delivering its notifications, the end of which sweeps.
    pub fn sweep(&self) {
        if let Some(store) = self.held() {
            store.sweep();
        }
    }

    /// Canonicalizes `asset_path` into a stable identifier, anchoring a relative
    /// path against `anchor` (C++ `ArResolver::CreateIdentifier`). Interning a
    /// layer by a path the caller names and keying the muted set call it
    /// directly; a path a layer authors is anchored by
    /// [`sdf::absolute_path_at`], which calls it with the registry as the
    /// resolver. The underlying [`ar::Resolver`] stays private.
    ///
    /// An anonymous layer identifier is its own canonical id: it names no
    /// asset-resolvable location, so it passes through unchanged (C++
    /// `SdfLayer::_GetCanonicalLayerId` / `ArResolver::CreateIdentifier`).
    /// Anchoring it against a layer would corrupt it into a bogus path that no
    /// interned layer matches.
    pub(crate) fn create_identifier(&self, asset_path: &str, anchor: Option<&ar::ResolvedPath>) -> String {
        if sdf::Layer::is_anonymous_identifier(asset_path) {
            return asset_path.to_string();
        }
        self.resolver.create_identifier(asset_path, anchor)
    }

    /// The identifier an in-memory layer is interned under when `asset_path`
    /// names it, by the resolver's
    /// [`in_memory_identifier`](ar::Resolver::in_memory_identifier). An
    /// anonymous layer identifier is its own, as it is for
    /// [`create_identifier`](Self::create_identifier).
    pub(crate) fn in_memory_identifier<'a>(&self, asset_path: &'a str) -> Cow<'a, str> {
        if sdf::Layer::is_anonymous_identifier(asset_path) {
            return Cow::Borrowed(asset_path);
        }
        self.resolver.in_memory_identifier(asset_path)
    }

    /// Whether the resolver calls `asset_path`
    /// [context dependent](ar::Resolver::is_context_dependent_path). An
    /// anonymous layer identifier never is: it names the one layer.
    pub(crate) fn is_context_dependent_path(&self, asset_path: &str) -> bool {
        !sdf::Layer::is_anonymous_identifier(asset_path) && self.resolver.is_context_dependent_path(asset_path)
    }

    /// Resolves an asset identifier to a physical location, or `None` if it does
    /// not exist.
    pub(crate) fn resolve(&self, identifier: &str) -> Option<ar::ResolvedPath> {
        self.resolver.resolve(identifier)
    }

    /// Opens the asset at a [`resolve`](Self::resolve)d location for reading.
    pub(crate) fn open_asset(&self, resolved: &ar::ResolvedPath) -> io::Result<Box<dyn ar::Asset>> {
        self.resolver.open_asset(resolved)
    }

    /// Resolves the layer the composition graph should open at `identifier`.
    ///
    /// This is [`resolve`](Self::resolve) deferred to the selected format's
    /// [`resolve_layer`](sdf::FileFormat::resolve_layer): a package
    /// (`pkg.usdz`) resolves to its default — first — packaged layer
    /// (`pkg.usdz[root.usd]`), so it composes as an ordinary layer stack and
    /// the sublayers and references authored inside it anchor in-package, while
    /// an ordinary format keeps the resolved location. Generic
    /// [`resolve`](Self::resolve) stays package-agnostic for asset-value
    /// resolution and the resolvability probe, which want the package path
    /// itself rather than a layer inside it. A resolved location no registered
    /// format claims passes through unchanged, so [`read`](Self::read) reports
    /// the missing format.
    ///
    /// The format is chosen by extension alone — unlike [`read`](Self::read),
    /// which content-sniffs the ambiguous `.usd`. That is sound because every
    /// `.usd` claimant keeps the identity default, so which one is picked does
    /// not change the real path; a future `.usd` format with a non-identity
    /// `resolve_layer` would need the content sniff here too.
    pub(crate) fn resolve_layer(&self, identifier: &str) -> Option<ar::ResolvedPath> {
        Self::resolve_layer_with(self.resolver.as_ref(), identifier)
    }

    /// [`resolve_layer`](Self::resolve_layer) through `resolver`.
    pub(crate) fn resolve_layer_with(resolver: &dyn ar::Resolver, identifier: &str) -> Option<ar::ResolvedPath> {
        let resolved = resolver.resolve(identifier)?;
        match Self::find_by_extension(&resolved.extension()) {
            Some(format) => format.resolve_layer(resolver, &resolved),
            None => Some(resolved),
        }
    }

    /// The resolver's [`identity`](ar::Resolver::identity) token — the
    /// configuration the stack's asset paths resolve under.
    pub(crate) fn identity(&self) -> String {
        self.resolver.identity()
    }

    /// Decodes `bytes` as a layer, choosing the registered format whose
    /// [`matches_content`](sdf::FileFormat::matches_content) claims what they
    /// begin with (C++ `SdfFileFormat::CanRead`).
    ///
    /// This is the door for layer bytes that never came from an asset — a layer
    /// compiled into a program, or one a host hands over — where there is no
    /// extension to dispatch on. Content is therefore the only evidence, and
    /// bytes no format recognizes are
    /// [`Unrecognized`](sdf::FormatError::Unrecognized) rather than guessed at.
    /// A package has no content signature, so a `.usdz` is read from its asset
    /// rather than from bytes. `source_name` names their origin, for
    /// diagnostics that quote a location.
    ///
    /// Returns the data with the format that read it.
    pub fn read_bytes(
        bytes: ar::AssetBuffer,
        source_name: &str,
    ) -> Result<(sdf::LayerData, &'static dyn sdf::FileFormat), sdf::FormatError> {
        let format = DEFAULT_FORMATS
            .iter()
            .copied()
            .find(|format| format.matches_content(&bytes))
            .ok_or_else(|| sdf::FormatError::Unrecognized(source_name.into()))?;
        Ok((format.read_bytes(bytes, source_name)?, format))
    }

    /// Find the format claiming `ext` (without the leading dot, case-insensitive),
    /// e.g. `"usda"` or `"usd"`. C++ `SdfFileFormat::FindByExtension`.
    pub fn find_by_extension(ext: &str) -> Option<&'static dyn sdf::FileFormat> {
        DEFAULT_FORMATS
            .iter()
            .copied()
            .find(|f| f.extensions().iter().any(|e| e.eq_ignore_ascii_case(ext)))
    }

    /// The format that writes a layer at `filename`, chosen by its extension:
    /// [`find_by_extension`](Self::find_by_extension) narrowed to a format
    /// that can write, with the error an export reports otherwise.
    pub(crate) fn export_format(filename: &str) -> Result<&'static dyn sdf::FileFormat, sdf::ExportError> {
        let ext = ar::extension(filename);
        let format = Self::find_by_extension(ext).ok_or_else(|| match ext {
            "" => sdf::ExportError::NoExtension {
                filename: filename.to_owned(),
            },
            other => sdf::ExportError::UnsupportedExtension {
                extension: other.to_owned(),
            },
        })?;
        if !format.caps().can_write() {
            return Err(sdf::ExportError::NotWritable {
                format: format.format_id(),
            });
        }
        Ok(format)
    }

    /// Find the format with the given [`format_id`](sdf::FileFormat::format_id),
    /// e.g. `"usdc"`. C++ `SdfFileFormat::FindById`.
    pub fn find_by_id(id: &str) -> Option<&'static dyn sdf::FileFormat> {
        DEFAULT_FORMATS.iter().copied().find(|f| f.format_id() == id)
    }

    /// The layer the registry holds under the canonical `identifier` or read
    /// from the file it resolves to, unsaved edits included, or else that layer
    /// read and held from then on, or `None` when it does not resolve. Fails
    /// with [`LayerError::Busy`](sdf::LayerError::Busy), before reading
    /// anything, when it would have to hold a layer from inside a composition
    /// read or an edit on this registry.
    pub(crate) fn find_or_read(&self, identifier: &str) -> Result<Option<LoadedLayer>, LoadError> {
        let _scope = ar::CacheScope::begin();
        let handle = match self.locate(identifier.to_owned())? {
            Located::Open(handle) => handle,
            Located::Closed { identifier, resolved } => {
                self.ensure_writable()?;
                let layer = self.read_layer(&identifier, resolved)?;
                self.store().insert(layer).map_err(|refused| refused.error)?
            }
            Located::Unresolved => return Ok(None),
        };
        Ok(Some(LoadedLayer {
            identifier: identifier.to_owned(),
            handle,
        }))
    }

    /// Opens the layer at `identifier` as an [`sdf::Layer`] anchored at the
    /// location it resolved to, which for a package is its default packaged
    /// layer, or `None` when it does not resolve. The registry does not hold it.
    pub(crate) fn open_layer(&self, identifier: &str) -> Result<Option<sdf::Layer>, LoadError> {
        let _scope = ar::CacheScope::begin();
        let Some(resolved) = self.resolve_layer(identifier) else {
            return Ok(None);
        };
        self.read_layer(identifier, resolved).map(Some)
    }

    /// The layer at `identifier`, which resolved to `resolved`, read from its
    /// asset.
    pub(crate) fn read_layer(&self, identifier: &str, resolved: ar::ResolvedPath) -> Result<sdf::Layer, LoadError> {
        // TODO(perf): one more stat of the file per layer read; the asset the
        // read opens could carry its modification time.
        let modified = sdf::layer::asset_time(self.resolver.as_ref(), identifier, &resolved);
        let prepared = Self::read(self.resolver.as_ref(), identifier.to_owned(), resolved, modified)?;
        Ok(sdf::Layer::new_resolved(prepared, Rc::clone(&self.resolver)))
    }

    /// The layer at `asset_path`, the one the registry holds or else one read
    /// and held from then on, without opening
    /// its sublayers: the shallow read the stage root stack needs to compose
    /// its root and session layers' own expression variables into one context
    /// before either region's sublayer subtree is collected. The layer is then
    /// handed to [`open_prepared_stack`](Self::open_prepared_stack), and a
    /// sublayer walk that reaches it finds it held, so the layer is parsed
    /// once at open. A path that does not resolve, the empty path
    /// among them, is [`Unresolved`](LoadError::Unresolved); a read failure
    /// propagates.
    pub(crate) fn prepare_root(&self, asset_path: &str) -> Result<LoadedLayer, LoadError> {
        self.ensure_writable()?;
        let identifier = self.create_identifier(asset_path, None);
        let unresolved = || LoadError::Unresolved {
            asset_path: asset_path.to_owned(),
        };
        if identifier.is_empty() {
            return Err(unresolved());
        }
        self.find_or_read(&identifier)?.ok_or_else(unresolved)
    }

    /// Opens the layer at `identifier` — a canonical identifier, as
    /// [`create_identifier`](Self::create_identifier) produces — together with
    /// its sublayer stack, root (strongest) layer first. Taking the identifier
    /// rather than an asset path keeps a search-path identifier (`lib/x.usda`,
    /// resolved through the search directories) from being re-anchored here.
    ///
    /// Following stops at references and payloads: composition opens those target
    /// layers on demand when it reaches the arc, so an un-visited subtree never
    /// loads them. Only `subLayers` edges are walked, since a layer's sublayer
    /// stack contributes opinions to its own namespace and so must be present
    /// whenever the layer is (spec 10.3.1.1). `presence` reports what the
    /// caller has of a layer (by canonical identifier), so a sublayer shared
    /// with the graph is neither re-read nor re-emitted, and one the caller
    /// excludes is not read.
    ///
    /// A root that does not resolve returns `Ok(None)`; one that resolves but
    /// cannot be read propagates as `Err` — the caller decides how to frame
    /// each. A sublayer that fails to resolve, or that resolves but cannot be
    /// read, is routed to `on_error` and skipped, so one bad sublayer never
    /// fails the whole stack (C++ `SdfLayer` opens the root and reports the bad
    /// sublayer).
    ///
    /// `ancestor_expr_vars` are the overrides the stack that brought the layer
    /// in supplies (the session root's own variables for the stage root stack, a
    /// reference/payload arc's composed set for a target). They overlay the root
    /// layer's own `expressionVariables` — the overrides win — to form the one
    /// context the whole stack resolves its expression-valued `subLayers` paths
    /// against (C++ `PcpExpressionVariables`). Sublayers of the root contribute no
    /// variables, so the context is fixed for the whole walk.
    ///
    /// With `reload`, an already-interned root and its held sublayers are
    /// walked again, as the registry holds them, but not re-emitted. A re-open
    /// under a new expression-variable context then loads the `${VAR}`
    /// sublayers that context resolves, including ones nested below a literal
    /// sublayer, which a first, variable-free open left unresolved. The caller
    /// only reloads for that case.
    ///
    /// The loader reports every load failure raw (a missing or unreadable
    /// sublayer, at whatever site reaches it). Whether such a failure is a
    /// stage diagnostic depends on composition reachability (a failure under a
    /// muted branch contributes nothing), which the composition layer decides
    /// once the muted-aware graph exists (see
    /// [`Stage`](crate::usd::Stage)'s construction).
    pub(crate) fn open_stack(
        &self,
        identifier: &str,
        ancestor_expr_vars: &HashMap<String, vt::Value>,
        reload: bool,
        on_error: &dyn Fn(Error) -> Result<(), Error>,
        presence: &dyn Fn(&str) -> Presence,
    ) -> Result<Option<Vec<LoadedLayer>>, LoadError> {
        self.ensure_writable()?;
        if identifier.is_empty() {
            return Ok(None);
        }
        self.find_or_read(identifier)?
            .map(|root| self.open_prepared_stack(root, ancestor_expr_vars, reload, on_error, presence))
            .transpose()
    }

    /// [`open_stack`](Self::open_stack) from a root layer
    /// [`prepare_root`](Self::prepare_root) holds.
    pub(crate) fn open_prepared_stack(
        &self,
        root: LoadedLayer,
        ancestor_expr_vars: &HashMap<String, vt::Value>,
        reload: bool,
        on_error: &dyn Fn(Error) -> Result<(), Error>,
        presence: &dyn Fn(&str) -> Presence,
    ) -> Result<Vec<LoadedLayer>, LoadError> {
        let mut layers = Vec::new();
        let mut visited = HashSet::from([root.identifier.clone()]);

        // The whole stack resolves its `${VAR}` sublayers against one context (C++
        // `PcpExpressionVariables`): the root layer's own `expressionVariables`
        // overlaid by the inherited overrides. Sublayers contribute nothing, so it
        // is fixed for the walk.
        let stack_vars = root
            .handle
            .read(|layer| expr::stack_variables(layer.data(), ancestor_expr_vars))??;

        self.open_sublayers(root, &stack_vars, reload, on_error, presence, &mut visited, &mut layers)?;
        Ok(layers)
    }

    /// Opens the layer at `identifier` — the canonical identifier a composed
    /// stack's `subLayers` entry resolved to — together with its own sublayer
    /// subtree, strongest first, for a layer joining an already-composed stack
    /// on demand (a `SublayerDemand` in [`crate::pcp`]).
    ///
    /// Unlike [`open_stack`](Self::open_stack), which treats its asset as a new
    /// stack root and composes that layer's own `expressionVariables` into the
    /// context, the subtree opened here joins the enclosing stack, so
    /// `stack_vars` — that stack's composed variables — resolve the whole walk
    /// unchanged: a sublayer contributes no variables (C++
    /// `PcpExpressionVariables`).
    ///
    /// Like [`open_stack`](Self::open_stack), this is a pure loader that knows
    /// nothing of who demanded the layer: a root that does not resolve returns
    /// `Ok(None)` and one that resolves but cannot be read propagates as
    /// `Err`, leaving the caller — who knows the referring layer and authored
    /// entry — to frame the diagnostic. A failure nested inside the subtree is
    /// skipped; it surfaces once the tree is wired into its stack, whose
    /// recompose re-derives the failing entry as its own demand.
    pub(crate) fn open_sublayer_tree(
        &self,
        identifier: &str,
        stack_vars: &HashMap<String, vt::Value>,
        presence: &dyn Fn(&str) -> Presence,
    ) -> Result<Option<Vec<LoadedLayer>>, LoadError> {
        self.ensure_writable()?;
        let Some(layer) = self.find_or_read(identifier)? else {
            return Ok(None);
        };
        let mut layers = Vec::new();
        let mut visited = HashSet::from([identifier.to_string()]);
        self.open_sublayers(
            layer,
            stack_vars,
            false,
            &|_| Ok(()),
            presence,
            &mut visited,
            &mut layers,
        )?;
        Ok(Some(layers))
    }

    /// Reads the layer `identifier` resolved to at `resolved` through
    /// `resolver`, dispatching to the registered format for its extension.
    /// The `.usd` extension is the one ambiguous case — binary crate or text —
    /// so it reads the bytes once and lets [`read_bytes`](Self::read_bytes)
    /// choose by content. C++ `SdfFileFormat::FindByExtension` + `CanRead`.
    /// `modified` is the asset's modification time, taken before the read.
    pub(crate) fn read(
        resolver: &dyn ar::Resolver,
        identifier: String,
        resolved: ar::ResolvedPath,
        modified: sdf::layer::AssetTime,
    ) -> Result<PreparedLayer, LoadError> {
        let ext = resolved.extension();
        let (data, format) = if ext.eq_ignore_ascii_case("usd") {
            let bytes = resolver
                .open_asset(&resolved)
                .and_then(|asset| asset.into_buffer())
                .map_err(sdf::FormatError::from)?;
            Self::read_bytes(bytes, &resolved.to_string())?
        } else {
            let format = Self::find_by_extension(&ext).ok_or_else(|| LoadError::UnsupportedFormat {
                resolved: resolved.to_string(),
            })?;
            (format.read(resolver, &resolved)?, format)
        };
        Ok(PreparedLayer {
            identifier,
            resolved,
            data,
            format: Some(format),
            modified,
        })
    }

    /// Emits an already-read layer and recursively opens its sublayers.
    ///
    /// `layer` is read by the caller (the root in
    /// [`open_prepared_stack`](Self::open_prepared_stack), each sublayer in
    /// the loop below) so a sublayer's read failure is routed to `on_error`
    /// while the root's propagates.
    ///
    /// `stack_vars` is the one context the whole stack resolves against (the root
    /// layer's own `expressionVariables` overlaid by the inherited overrides,
    /// computed once in [`open_prepared_stack`](Self::open_prepared_stack)).
    /// This layer's own `expressionVariables` do not contribute — only the
    /// stack root's do (C++ `PcpExpressionVariables`) — so it is passed down
    /// unchanged.
    #[allow(clippy::too_many_arguments)]
    fn open_sublayers(
        &self,
        layer: LoadedLayer,
        stack_vars: &HashMap<String, vt::Value>,
        reload: bool,
        on_error: &dyn Fn(Error) -> Result<(), Error>,
        presence: &dyn Fn(&str) -> Presence,
        visited: &mut HashSet<String>,
        layers: &mut Vec<LoadedLayer>,
    ) -> Result<(), LoadError> {
        let anchor = layer.handle.anchor_location().cloned();
        let identifier = layer.identifier.clone();
        let held = presence(&identifier);
        // An excluded layer reaches here only as the root of the open, which the
        // caller asked for: it is emitted, and nothing beneath it is walked.
        if held == Presence::Excluded {
            layers.push(layer);
            return Ok(());
        }
        let sub_paths = layer.handle.read(|layer| Self::sublayer_paths(layer.data()))?;

        // Emit this layer ahead of its sublayers so the collected stack is
        // strongest-first: a layer overrides the layers it sublayers, and earlier
        // entries in a `subLayers` list override later ones (spec 10.3.1.1). In a
        // reload pass an already-interned layer is re-walked (to reach a `${VAR}`
        // sublayer the new context now resolves) but not re-emitted.
        if held == Presence::Absent {
            layers.push(layer);
        }

        // Failed sublayer identifiers already reported for *this* layer, so a layer
        // that authors the same missing/unreadable sublayer twice reports it once.
        // Kept per referrer (not shared with the pass-wide `visited`) so a failure
        // suppressed here never hides the same sublayer's diagnostic at another,
        // active referrer.
        let mut failed: HashSet<String> = HashSet::new();

        // Sublayers (and references) reached from inside a `.usdz` resolve
        // in-package: a package root is anchored to its first layer, so this
        // layer's `resolved` is already package-relative and its sublayer paths
        // anchor against it the same way any other layer's do.
        //
        // TODO(rayon): each sublayer's resolve and read is independent of its
        // siblings'; only the emission order and the `visited` / `failed`
        // bookkeeping are sequential.
        for sub_path in sub_paths {
            // Evaluate an expression-valued sublayer path. An unevaluable
            // expression drops only this sublayer — like an unresolved or
            // unreadable one — rather than failing the whole stack open. It has no
            // resolved identifier to key on, so it deduplicates per referrer by its
            // authored path, keeping the three load-failure branches consistent. An
            // expression evaluating to `None` contributes no sublayer and no error
            // (C++ skips it silently).
            let sub_asset = if expr::is_expression(&sub_path) {
                let evaluated = expr::evaluate_string(&sub_path, stack_vars);
                match evaluated.value {
                    Some(evaluated) => evaluated,
                    None if evaluated.errors.is_empty() => continue,
                    None => {
                        if failed.insert(sub_path.clone()) {
                            on_error(Error::InvalidExpression {
                                expression: sub_path,
                                referencing_layer: identifier.clone(),
                                reason: evaluated.errors.join("; "),
                            })?;
                        }
                        continue;
                    }
                }
            } else {
                sub_path
            };

            let sub_id = sdf::absolute_path_at(self, anchor.as_ref(), &sub_asset);
            // A sublayer already opened this pass is skipped, and so is one the
            // caller excludes. One the caller holds is skipped too, except in a
            // reload pass, where it is re-walked to reach the `${VAR}` sublayers
            // the new context now resolves below it (it is not re-emitted; see
            // the push above). A failure this layer already reported is skipped
            // too. An empty/degenerate identifier falls through to the resolve
            // below as `UnresolvedAsset`.
            let skipped = match presence(&sub_id) {
                Presence::Absent => false,
                Presence::Held => !reload,
                Presence::Excluded => true,
            };
            if skipped || visited.contains(&sub_id) || failed.contains(&sub_id) {
                continue;
            }
            // Find or read the sublayer. A missing one is a raw load failure reported at
            // this referencing site. It is a leaf (no subtree to walk), so it is not
            // added to the pass-wide `visited`: each referencing layer records its own
            // edge, so a shared missing layer reached from several layers is reported
            // once per referrer and the composition layer can suppress by referrer.
            // A resolved-but-unreadable one is a raw load failure like a missing one,
            // reported at this referencing site and, being a leaf, left out of
            // `visited` (dropping only this layer; the root's read failure propagated
            // from `open_stack`).
            let sublayer = match self.find_or_read(&sub_id) {
                Ok(Some(sublayer)) => sublayer,
                Ok(None) => {
                    on_error(Error::UnresolvedAsset {
                        asset_path: sub_asset,
                        referencing_layer: identifier.clone(),
                    })?;
                    failed.insert(sub_id);
                    continue;
                }
                // A borrow conflict is not the sublayer's failure: the load fails.
                Err(LoadError::Layer(sdf::LayerError::Busy)) => return Err(sdf::LayerError::Busy.into()),
                Err(reason) => {
                    on_error(Error::UnreadableAsset {
                        asset_path: sub_asset,
                        referencing_layer: identifier.clone(),
                        source: Arc::new(reason),
                    })?;
                    failed.insert(sub_id);
                    continue;
                }
            };
            // A readable layer is interned and its subtree walked once; claim it in
            // `visited` before recursing so a diamond or cycle does not re-emit it.
            visited.insert(sub_id);

            self.open_sublayers(sublayer, stack_vars, reload, on_error, presence, visited, layers)?;
        }

        Ok(())
    }

    /// A layer's `subLayers` asset paths (empty when it declares none).
    pub(crate) fn sublayer_paths(data: &dyn sdf::AbstractData) -> Vec<String> {
        sdf::PseudoRootSpecRef::get(data)
            .and_then(|root| root.sublayers())
            .unwrap_or_default()
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::Result;
    use crate::sdf::FileFormatCaps;

    /// `layer` held in `store`, or the live layer already carrying its
    /// identifier or real path, which a fixture repeating a layer collapses
    /// onto. It is asked for under `layer`'s identifier.
    pub(crate) fn hold(store: &Rc<sdf::LayerStore>, layer: sdf::Layer) -> LoadedLayer {
        let identifier = layer.identifier().to_owned();
        let handle = match store.insert(layer) {
            Ok(handle) => handle,
            Err(refused) => store
                .find(refused.layer.identifier(), Some(refused.layer.real_path()))
                .expect("the store is free")
                .expect("a refused duplicate is held"),
        };
        LoadedLayer { identifier, handle }
    }

    /// A registry over a filesystem resolver, with the count of the assets it
    /// has opened.
    pub(crate) fn counting_registry() -> (LayerRegistry, Rc<Cell<usize>>) {
        let opens = Rc::new(Cell::new(0));
        let count = Rc::clone(&opens);
        let resolver = HookResolver::new(move |_| count.set(count.get() + 1));
        (LayerRegistry::new(Box::new(resolver)), opens)
    }

    /// A filesystem resolver that calls its hooks before opening each asset
    /// and before identifying each asset path: user code a layer load, or a
    /// sublayer's resolution, runs.
    pub(crate) struct HookResolver {
        inner: ar::DefaultResolver,
        hook: Box<dyn Fn(&ar::ResolvedPath)>,
        identify: Box<dyn Fn(&str)>,
    }

    impl HookResolver {
        /// A resolver calling `hook` with each asset's resolved path before
        /// opening it.
        pub(crate) fn new(hook: impl Fn(&ar::ResolvedPath) + 'static) -> Self {
            Self {
                inner: ar::DefaultResolver::new(),
                hook: Box::new(hook),
                identify: Box::new(|_| {}),
            }
        }

        /// The resolver calling `identify` with each asset path before
        /// creating its identifier.
        pub(crate) fn on_identify(self, identify: impl Fn(&str) + 'static) -> Self {
            Self {
                identify: Box::new(identify),
                ..self
            }
        }
    }

    impl ar::Resolver for HookResolver {
        fn create_identifier(&self, asset_path: &str, anchor: Option<&ar::ResolvedPath>) -> String {
            (self.identify)(asset_path);
            self.inner.create_identifier(asset_path, anchor)
        }

        fn resolve(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
            self.inner.resolve(asset_path)
        }

        fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
            self.inner.resolve_for_new_asset(asset_path)
        }

        fn open_asset(&self, resolved_path: &ar::ResolvedPath) -> io::Result<Box<dyn ar::Asset>> {
            (self.hook)(resolved_path);
            self.inner.open_asset(resolved_path)
        }
    }

    /// Opens a root layer and the full transitive closure of its sublayers,
    /// references, and payloads — the layer set a fully-composed (and fully-
    /// traversed) stage would have loaded on demand.
    ///
    /// The `pcp` composition tests build a fully-resolved layer graph from this
    /// without the stage's on-demand load loop; eager arc following lives only
    /// here, off the production path.
    pub(crate) fn collect_with_arcs(registry: &LayerRegistry, root_path: &str) -> Result<Vec<sdf::Layer>, LoadError> {
        let mut layers = Vec::new();
        let mut visited = HashSet::new();
        collect_with_arcs_in(registry, root_path, None, &HashMap::new(), &mut layers, &mut visited)?;
        layers.reverse();
        Ok(layers)
    }

    fn collect_with_arcs_in(
        registry: &LayerRegistry,
        asset_path: &str,
        anchor: Option<&ar::ResolvedPath>,
        ancestor_expr_vars: &HashMap<String, vt::Value>,
        layers: &mut Vec<sdf::Layer>,
        visited: &mut HashSet<String>,
    ) -> Result<(), LoadError> {
        let identifier = sdf::absolute_path_at(registry, anchor, asset_path);
        if identifier.is_empty() || visited.contains(&identifier) {
            return Ok(());
        }
        let Some(resolved) = registry.resolve_layer(&identifier) else {
            return Ok(());
        };
        visited.insert(identifier.clone());
        let modified = sdf::layer::AssetTime::Unknown;
        let layer = LayerRegistry::read(registry.resolver.as_ref(), identifier, resolved, modified)?;
        let (data, resolved) = (layer.data.as_ref(), &layer.resolved);
        // Resolve this layer's arc/sublayer paths against its stack context (root
        // own overlaid by the inherited overrides). This eager test closure loads a
        // superset of what any one stack references; the `LayerGraph` re-derives the
        // actual per-stack membership with the same stack-level context, so a layer
        // reached here that no stack includes is simply an unused node.
        let stack_vars = expr::stack_variables(data, ancestor_expr_vars)?;
        for dep in arc_dependencies(data)? {
            // An unevaluable dependency loads nothing, mirroring the graph's
            // drop-the-edge handling.
            let Some(dep_asset) = expr::evaluate_string(&dep, &stack_vars).value else {
                continue;
            };
            collect_with_arcs_in(registry, &dep_asset, Some(resolved), &stack_vars, layers, visited)?;
        }
        layers.push(sdf::Layer::new_resolved(layer, Rc::clone(&registry.resolver)));
        Ok(())
    }

    /// Every sublayer, reference, and payload asset path authored in a layer.
    fn arc_dependencies(data: &dyn sdf::AbstractData) -> Result<Vec<String>, sdf::DataError> {
        let mut deps = LayerRegistry::sublayer_paths(data);
        let mut queue = vec![sdf::Path::abs_root()];
        while let Some(path) = queue.pop() {
            if !data.has_spec(&path) {
                continue;
            }
            if let Some(value) = data.try_field(&path, sdf::FieldKey::References.as_str())?
                && let vt::Value::ReferenceListOp(list_op) = value.as_ref()
            {
                deps.extend(
                    list_op
                        .iter()
                        .filter(|r| !r.asset_path.is_empty())
                        .map(|r| r.asset_path.clone()),
                );
            }
            if let Some(value) = data.try_field(&path, sdf::FieldKey::Payload.as_str())? {
                match value.as_ref() {
                    vt::Value::Payload(p) if !p.asset_path.is_empty() => deps.push(p.asset_path.clone()),
                    vt::Value::PayloadListOp(list_op) => {
                        deps.extend(
                            list_op
                                .iter()
                                .filter(|p| !p.asset_path.is_empty())
                                .map(|p| p.asset_path.clone()),
                        );
                    }
                    _ => {}
                }
            }
            if let Some(value) = data.try_field(&path, sdf::ChildrenKey::PrimChildren.as_str())?
                && let vt::Value::TokenVec(children) = value.into_owned()
            {
                for name in children.iter().rev() {
                    if let Ok(child) = path.append_path(name.as_str()) {
                        queue.push(child);
                    }
                }
            }
            if let Some(value) = data.try_field(&path, sdf::ChildrenKey::VariantSetChildren.as_str())?
                && let vt::Value::TokenVec(set_names) = value.into_owned()
            {
                for set_name in &set_names {
                    // An invalid authored set or variant name cannot address
                    // variant storage; there is nothing to visit under it.
                    let Ok(set_path) = path.append_variant_selection(set_name, "") else {
                        continue;
                    };
                    if let Some(value) = data.try_field(&set_path, sdf::ChildrenKey::VariantChildren.as_str())?
                        && let vt::Value::TokenVec(variant_names) = value.into_owned()
                    {
                        for variant_name in &variant_names {
                            if let Ok(variant_path) = path.append_variant_selection(set_name, variant_name) {
                                queue.push(variant_path);
                            }
                        }
                    }
                }
            }
        }
        Ok(deps)
    }

    const VENDOR_COMPOSITION: &str = concat!(
        env!("CARGO_WORKSPACE_DIR"),
        "vendor/usd-wg-assets/test_assets/foundation/stage_composition"
    );

    fn manifest_dir() -> String {
        std::env::var("CARGO_MANIFEST_DIR").unwrap()
    }

    fn composition_path(relative: &str) -> String {
        format!("{VENDOR_COMPOSITION}/{relative}")
    }

    fn fixture_path(relative: &str) -> String {
        format!("{}/fixtures/{}", manifest_dir(), relative)
    }

    /// A registry over the default filesystem resolver.
    fn registry() -> LayerRegistry {
        LayerRegistry::default()
    }

    /// Bytes are dispatched by what they begin with: the crate magic, the
    /// `usda` header, and nothing else. A guess would decode one format's
    /// bytes as another's and report that format's parse error.
    #[test]
    fn content_picks_format() {
        let text = LayerRegistry::read_bytes(
            b"#usda 1.0
"
            .as_slice()
            .into(),
            "text",
        )
        .expect("text is recognized");
        assert!(text.0.has_spec(&sdf::Path::abs_root()));
        assert_eq!(text.1.format_id(), "usda");

        let unknown = LayerRegistry::read_bytes(b"nothing claims this".as_slice().into(), "mystery");
        assert!(
            matches!(unknown, Err(sdf::FormatError::Unrecognized(_))),
            "unrecognized bytes are refused rather than guessed at"
        );

        // The lexer skips whitespace before the cookie, so detection must too.
        let indented = LayerRegistry::read_bytes(b"\n#usda 1.0\n".as_slice().into(), "indented");
        assert!(indented.is_ok(), "a layer opening with a blank line is still text");
    }

    /// Opens a root layer and its sublayer stack, erroring on a missing sublayer
    /// or an unresolvable root.
    fn open_stack(path: &str) -> Result<Vec<LoadedLayer>> {
        let registry = registry();
        let identifier = registry.create_identifier(path, None);
        Ok(registry
            .open_stack(&identifier, &HashMap::new(), false, &Err, &|_| Presence::Absent)?
            .expect("root did not resolve"))
    }

    #[test]
    fn lookup_by_extension() {
        assert_eq!(LayerRegistry::find_by_extension("usda").unwrap().format_id(), "usda");
        assert_eq!(LayerRegistry::find_by_extension("usdc").unwrap().format_id(), "usdc");
        assert_eq!(LayerRegistry::find_by_extension("usd").unwrap().format_id(), "usdc");
        assert_eq!(LayerRegistry::find_by_extension("USDA").unwrap().format_id(), "usda");
        assert_eq!(LayerRegistry::find_by_extension("usdz").unwrap().format_id(), "usdz");
        assert!(LayerRegistry::find_by_extension("xyz").is_none());
        assert!(LayerRegistry::find_by_extension("").is_none());
    }

    #[test]
    fn lookup_by_id() {
        assert_eq!(
            LayerRegistry::find_by_id("usdc").unwrap().extensions(),
            &["usdc", "usd"]
        );
        assert!(LayerRegistry::find_by_id("usd").is_none());
    }

    #[test]
    fn builtin_capabilities() {
        for id in ["usda", "usdc"] {
            let caps = LayerRegistry::find_by_id(id).unwrap().caps();
            assert_eq!(caps, FileFormatCaps::all(), "{id} should read, write, and edit");
        }
        // usdz is a package format: writable as a new archive, but not editable
        // (savable) in place.
        let usdz = LayerRegistry::find_by_id("usdz").unwrap().caps();
        assert!(usdz.can_read() && usdz.can_write());
        assert!(!usdz.can_edit(), "usdz should not be editable in place");
    }

    // References and payloads are not followed here — composition opens those
    // targets on demand — so loading walks only the root and its sublayer stack.
    // The binary-`.usd` content-sniff round-trip is covered by
    // `sdf::layer::tests::export_usd_writes_binary`.

    #[test]
    fn expression_sublayer() -> Result<()> {
        let layers = open_stack(&fixture_path("expr_sublayer.usda"))?;
        assert_eq!(layers.len(), 2, "root + 1 expression-resolved sublayer");
        assert!(layers[0].identifier.contains("expr_sublayer.usda"));
        assert!(layers[1].identifier.contains("expr_sublayer_target.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_same_folder() -> Result<()> {
        let layers = open_stack(&composition_path("subLayer/sublayer_same_folder.usda"))?;
        assert_eq!(layers.len(), 2, "root + 1 sublayer");
        assert!(layers[0].identifier.contains("sublayer_same_folder.usda"));
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_child_folder() -> Result<()> {
        let layers = open_stack(&composition_path("subLayer/sublayer_child_folder.usda"))?;
        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_parent_folder() -> Result<()> {
        let layers = open_stack(&composition_path("subLayer/sublayer_parent_folder.usda"))?;
        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    /// A reference target is not opened by the loader; only the root and its
    /// sublayers load. (Composition opens the reference on demand.)
    #[test]
    fn reference_not_followed() -> Result<()> {
        let layers = open_stack(&composition_path("references/reference_same_folder.usda"))?;
        assert_eq!(layers.len(), 1, "only the root; the reference is composed lazily");
        assert!(layers[0].identifier.contains("reference_same_folder.usda"));
        Ok(())
    }

    /// Sibling sublayers load in authored order, strongest first (spec 10.3.1.1):
    /// a layer overrides the layers it sublayers, and an earlier `subLayers` entry
    /// overrides a later one. Guards against reversing sibling subtrees.
    #[test]
    fn sublayer_sibling_order() -> Result<()> {
        let root = format!(
            "{}vendor/usd-wg-assets/test_assets/RelationshipEncapsulationTests/SublayeredInternalReferenceTest.usda",
            env!("CARGO_WORKSPACE_DIR")
        );
        let names: Vec<String> = open_stack(&root)?.iter().map(|l| l.identifier.clone()).collect();
        assert_eq!(names.len(), 4, "root + 3 sublayers");
        assert!(names[0].contains("SublayeredInternalReferenceTest.usda"));
        assert!(names[1].contains("Environment.usda"));
        assert!(names[2].contains("hardware.shading.usda"));
        assert!(names[3].contains("hardware.modeling.usda"));
        Ok(())
    }

    /// The default handler errors on an unresolvable sublayer.
    #[test]
    fn strict_errors_on_missing_sublayer() {
        assert!(open_stack(&composition_path("subLayer/sublayer_invalid.usda")).is_err());
    }

    /// A custom handler receives the missing sublayer's asset path.
    #[test]
    fn handler_receives_sublayer_error() -> Result<()> {
        let errors = std::cell::RefCell::new(Vec::new());
        let registry = registry();
        let layers = registry
            .open_stack(
                &registry.create_identifier(&composition_path("subLayer/sublayer_invalid.usda"), None),
                &HashMap::new(),
                false,
                &|e| {
                    errors.borrow_mut().push(e);
                    Ok(())
                },
                &|_| Presence::Absent,
            )?
            .expect("root resolves");

        // The root still loads despite the missing sublayer.
        assert_eq!(layers.len(), 1);
        assert!(layers[0].identifier.contains("sublayer_invalid.usda"));

        let errors = errors.into_inner();
        assert_eq!(errors.len(), 1);
        let Error::UnresolvedAsset { referencing_layer, .. } = &errors[0] else {
            panic!("expected UnresolvedAsset, got {:?}", errors[0]);
        };
        assert!(referencing_layer.contains("sublayer_invalid.usda"));
        Ok(())
    }
}
