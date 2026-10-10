//! Asset resolution framework.
//!
//! USD layers reference external assets through asset paths — the `@...@` syntax in
//! `.usda` files. These paths appear in sublayers, references, payloads, and asset-valued
//! attributes. An asset path is a logical identifier that may be relative, absolute, or
//! use package-relative notation (`Model.usdz[Geom.usd]`).
//!
//! This module resolves those logical paths to physical locations that can be opened
//! and read. It corresponds to the C++ Ar (Asset Resolution) module:
//! <https://openusd.org/dev/api/ar_page_front.html>
//!
//! The [`Resolver`] trait defines the resolution interface. The [`DefaultResolver`]
//! provides a filesystem-based implementation that searches configurable directories
//! for matching files. Custom resolvers can map asset paths to databases, cloud storage,
//! or other backends.
//!
//! # Example
//!
//! ```no_run
//! use openusd::ar::{DefaultResolver, Resolver};
//!
//! let resolver = DefaultResolver::new();
//! if let Some(resolved) = resolver.resolve("model.usda") {
//!     let mut asset = resolver.open_asset(&resolved).unwrap();
//!     let data = asset.read_all().unwrap();
//! }
//! ```

use std::any::{Any, TypeId};
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fmt;
use std::fs;
use std::io::{self, Read, Seek};
use std::marker::PhantomData;
use std::ops::{Deref, Range};
use std::path::{Component, Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use crate::{tf, usdz};

/// A resolved asset path representing the physical location of an asset.
///
/// This is a newtype around a [`PathBuf`] that distinguishes resolved paths
/// from unresolved asset path strings. An empty resolved path indicates
/// that the asset could not be found.
///
/// Implements [`Deref<Target = Path>`] for transparent access to [`Path`] methods.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResolvedPath(PathBuf);

impl ResolvedPath {
    /// Creates a new resolved path.
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self(path.into())
    }

    /// Returns `true` if the resolved path is empty (resolution failed).
    pub fn is_empty(&self) -> bool {
        self.0.as_os_str().is_empty()
    }

    /// The file extension (without the leading dot), lowercased, or `""` when
    /// there is none or it is not valid UTF-8. Lowercased so a caller can match a
    /// format case-insensitively — `resolved.extension() == "usdz"` — the way the
    /// format registry's `find_by_extension` does, without juggling `OsStr`.
    pub(crate) fn extension(&self) -> String {
        extension(&self.0.to_string_lossy()).to_ascii_lowercase()
    }
}

impl Deref for ResolvedPath {
    type Target = Path;

    fn deref(&self) -> &Path {
        &self.0
    }
}

impl fmt::Display for ResolvedPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.display())
    }
}

impl AsRef<Path> for ResolvedPath {
    fn as_ref(&self) -> &Path {
        self
    }
}

/// Metadata about a resolved asset.
#[derive(Debug, Default, Clone)]
pub struct AssetInfo {
    /// Version of the asset, if known.
    pub version: String,
    /// Display name for the asset.
    pub asset_name: String,
    /// Repository path, if the asset is managed by a version control system.
    pub repo_path: String,
    /// Additional resolver-specific metadata.
    pub resolver_info: HashMap<String, String>,
}

/// Readable asset handle returned by [`Resolver::open_asset`].
///
/// This trait abstracts over the underlying storage mechanism (filesystem,
/// in-memory buffer, archive entry, etc.) and provides random-access reading.
pub trait Asset: Read + Seek + Send {
    /// Returns the total size of the asset in bytes.
    fn size(&self) -> io::Result<u64>;

    /// Reads the entire asset into a byte buffer.
    fn read_all(&mut self) -> io::Result<Vec<u8>> {
        let mut buf = Vec::with_capacity(usize::try_from(self.size()?).unwrap_or(0));
        self.read_to_end(&mut buf)?;
        Ok(buf)
    }

    /// Returns a shared view of the complete asset without consuming it,
    /// or `None` if the asset must be read into a buffer (C++
    /// `ArAsset::GetBuffer`).
    ///
    /// The view starts at offset zero and matches the bytes exposed through
    /// [`Read`] and [`Seek`] for the asset's lifetime.
    fn shared_buffer(&self) -> Option<SharedBuffer> {
        None
    }

    /// The complete asset as a buffer, consuming the asset: the view
    /// [`shared_buffer`](Self::shared_buffer) returns when it returns one,
    /// otherwise what [`read_all`](Self::read_all) reads. An asset that owns
    /// its buffer hands it over.
    fn into_buffer(mut self: Box<Self>) -> io::Result<AssetBuffer> {
        match self.shared_buffer() {
            Some(view) => Ok(AssetBuffer::Shared(view)),
            None => self.read_all().map(AssetBuffer::Owned),
        }
    }
}

/// The bytes a layer decodes from: an asset's complete contents, as
/// [`Asset::into_buffer`] yields them, or bytes that never were an asset,
/// compiled into the program or handed over by a host. They live as long as
/// the layer because a decoder may keep reading them: the crate format
/// indexes into the buffer in place, while the text format copies out what
/// it keeps.
#[derive(Debug, Clone)]
pub enum AssetBuffer {
    /// Bytes the caller owns outright.
    Owned(Vec<u8>),
    /// A view of bytes somebody else holds: a buffer a host resolver keeps,
    /// bytes compiled into the program, or a mapped file.
    Shared(SharedBuffer),
}

impl AssetBuffer {
    /// This buffer as a view, sharing its bytes from then on: an `Owned`
    /// buffer becomes the source of a view over all of it, without copying,
    /// and a `Shared` one is returned as it is.
    pub fn into_shared(self) -> SharedBuffer {
        match self {
            AssetBuffer::Owned(bytes) => SharedBuffer::new(bytes),
            AssetBuffer::Shared(view) => view,
        }
    }
}

impl Deref for AssetBuffer {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        match self {
            AssetBuffer::Owned(bytes) => bytes,
            AssetBuffer::Shared(view) => view,
        }
    }
}

impl AsRef<[u8]> for AssetBuffer {
    fn as_ref(&self) -> &[u8] {
        self
    }
}

/// Bytes compiled into the program are shared as they are.
impl From<&'static [u8]> for AssetBuffer {
    fn from(bytes: &'static [u8]) -> Self {
        AssetBuffer::Shared(SharedBuffer::new(bytes))
    }
}

impl From<Vec<u8>> for AssetBuffer {
    fn from(bytes: Vec<u8>) -> Self {
        AssetBuffer::Owned(bytes)
    }
}

impl From<Arc<[u8]>> for AssetBuffer {
    fn from(bytes: Arc<[u8]>) -> Self {
        AssetBuffer::Shared(SharedBuffer::new(bytes))
    }
}

impl From<SharedBuffer> for AssetBuffer {
    fn from(view: SharedBuffer) -> Self {
        AssetBuffer::Shared(view)
    }
}

/// A view of bytes a [`SharedSource`] holds: the range of the source it
/// covers, which it never outgrows. A clone shares the source, and
/// [`slice`](Self::slice) narrows the range without copying. A package entry
/// is therefore a view of its package, and a layer's bytes a view of its
/// asset.
///
/// A source's bytes have a fixed length and fixed contents for as long as
/// any view of it lives. The sources are a sealed set that each guarantee
/// that on their own, which keeps the range recorded here within the source
/// and a view from ever reading past it.
#[derive(Clone)]
pub struct SharedBuffer {
    source: Arc<dyn SharedSource>,
    range: Range<usize>,
}

impl SharedBuffer {
    /// A view of the whole of `source`.
    pub fn new(source: impl SharedSource + 'static) -> Self {
        let len = source.bytes().len();
        SharedBuffer {
            source: Arc::new(source),
            range: 0..len,
        }
    }

    /// The view of `range` within this view, sharing the source, or `None`
    /// when `range` reaches past it.
    pub fn slice(&self, range: Range<usize>) -> Option<SharedBuffer> {
        self.get(range.clone())?;
        Some(SharedBuffer {
            source: Arc::clone(&self.source),
            range: self.range.start + range.start..self.range.start + range.end,
        })
    }

    /// Tells the source how `range` of this view is about to be read. The
    /// part of `range` past the view is left out. Advice is a hint: a
    /// source that takes none ignores it, and it changes no bytes.
    pub fn advise(&self, range: Range<usize>, advice: Advice) {
        let end = range.end.min(self.len());
        if range.start < end {
            self.source
                .advise(self.range.start + range.start..self.range.start + end, advice);
        }
    }

    /// Whether the view is of a file mapping, as against bytes held in
    /// memory.
    pub fn is_mapping(&self) -> bool {
        self.source.is_mapping()
    }
}

/// How a range of shared bytes is about to be read, for a source that can
/// prepare for it (C++ `ArchMemAdvice`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Advice {
    /// No particular pattern, the platform's default.
    Normal,
    /// Reads at scattered offsets, which reading ahead does not serve.
    Random,
    /// The whole range, soon.
    WillNeed,
}

impl Deref for SharedBuffer {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        &self.source.bytes()[self.range.clone()]
    }
}

impl AsRef<[u8]> for SharedBuffer {
    fn as_ref(&self) -> &[u8] {
        self
    }
}

impl fmt::Debug for SharedBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SharedBuffer")
            .field("range", &self.range)
            .field("source_len", &self.source.bytes().len())
            .finish()
    }
}

/// The backing a [`SharedBuffer`] views: bytes whose length and contents
/// are fixed for as long as the source lives. The trait is sealed since every
/// view relies on that promise; the sources are `&'static [u8]`, `Vec<u8>`,
/// `Arc<[u8]>` and, with the `mmap` feature, a read-only file mapping, whose
/// promise is the one [`DefaultResolver::map_files`] has its caller make.
pub trait SharedSource: sealed::Sealed + Send + Sync {
    /// The whole of the source's bytes.
    fn bytes(&self) -> &[u8];

    /// Takes `advice` about how `range` of the bytes is about to be read.
    /// A source held in memory has nothing to prepare.
    fn advise(&self, _range: Range<usize>, _advice: Advice) {}

    /// Whether the source is a file mapping.
    fn is_mapping(&self) -> bool {
        false
    }
}

impl SharedSource for &'static [u8] {
    fn bytes(&self) -> &[u8] {
        self
    }
}

impl SharedSource for Vec<u8> {
    fn bytes(&self) -> &[u8] {
        self
    }
}

impl SharedSource for Arc<[u8]> {
    fn bytes(&self) -> &[u8] {
        self
    }
}

#[cfg(feature = "mmap")]
impl SharedSource for memmap2::Mmap {
    fn bytes(&self) -> &[u8] {
        self
    }

    /// Passes the advice to the platform where it takes any (`madvise` on
    /// Unix). C++ `ArchMemAdvise` likewise does nothing on Windows.
    ///
    /// TODO(perf): `PrefetchVirtualMemory` is the Windows call that would
    /// serve [`Advice::WillNeed`]; it needs a measurement on a cold file to
    /// say what it buys.
    #[cfg_attr(not(unix), allow(unused_variables))]
    fn advise(&self, range: Range<usize>, advice: Advice) {
        #[cfg(unix)]
        {
            let advice = match advice {
                Advice::Normal => memmap2::Advice::Normal,
                Advice::Random => memmap2::Advice::Random,
                Advice::WillNeed => memmap2::Advice::WillNeed,
            };
            // A hint the platform refuses costs nothing but the hint.
            let _ = self.advise_range(advice, range.start, range.len());
        }
    }

    fn is_mapping(&self) -> bool {
        true
    }
}

mod sealed {
    use std::sync::Arc;

    pub trait Sealed {}

    impl Sealed for &'static [u8] {}
    impl Sealed for Vec<u8> {}
    impl Sealed for Arc<[u8]> {}
    #[cfg(feature = "mmap")]
    impl Sealed for memmap2::Mmap {}
}

impl Asset for fs::File {
    fn size(&self) -> io::Result<u64> {
        self.metadata().map(|m| m.len())
    }
}

impl Asset for io::Cursor<Vec<u8>> {
    fn size(&self) -> io::Result<u64> {
        Ok(self.get_ref().len() as u64)
    }

    /// Hands the buffer over.
    fn into_buffer(self: Box<Self>) -> io::Result<AssetBuffer> {
        Ok(AssetBuffer::Owned(self.into_inner()))
    }
}

/// An asset over a buffer already in hand, as a package entry, a mapped file
/// or the bytes a host keeps in memory are served.
impl Asset for io::Cursor<AssetBuffer> {
    fn size(&self) -> io::Result<u64> {
        Ok(self.get_ref().len() as u64)
    }

    fn shared_buffer(&self) -> Option<SharedBuffer> {
        match self.get_ref() {
            AssetBuffer::Shared(view) => Some(view.clone()),
            AssetBuffer::Owned(_) => None,
        }
    }

    /// Hands the buffer over.
    fn into_buffer(self: Box<Self>) -> io::Result<AssetBuffer> {
        Ok(self.into_inner())
    }
}

/// Interface for resolving asset paths to physical locations.
///
/// Implementations of this trait map logical asset paths (as authored in USD
/// layers) to resolved paths that can be opened and read. The default
/// implementation, [`DefaultResolver`], performs filesystem-based resolution
/// with configurable search paths.
///
/// # Correspondence
///
/// This trait corresponds to `ArResolver` in the C++ USD API:
/// <https://openusd.org/dev/api/class_ar_resolver.html>
pub trait Resolver {
    /// Canonicalizes an asset path into a stable identifier.
    ///
    /// The `anchor` path, if provided, is used to resolve relative paths.
    /// Two asset paths that refer to the same asset must produce the same identifier.
    fn create_identifier(&self, asset_path: &str, anchor: Option<&ResolvedPath>) -> String;

    /// Resolves an asset path to a physical location.
    ///
    /// Returns [`Some`] with the resolved path if the asset exists,
    /// or [`None`] if the asset cannot be found.
    fn resolve(&self, asset_path: &str) -> Option<ResolvedPath>;

    /// Resolves an asset path for creating a new asset.
    ///
    /// Unlike [`resolve`](Resolver::resolve), the asset need not exist yet.
    fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ResolvedPath>;

    /// Opens a resolved asset for reading.
    fn open_asset(&self, resolved_path: &ResolvedPath) -> io::Result<Box<dyn Asset>>;

    /// Returns the file extension of the given asset path (without the leading
    /// dot), the innermost packaged path's for a package-relative one.
    fn get_extension<'a>(&self, asset_path: &'a str) -> &'a str {
        extension(asset_path)
    }

    /// Whether the asset `asset_path` names depends on more than the path
    /// itself, such as the directories a search consults or what exists
    /// beside the layer that authors it (C++
    /// `ArResolver::IsContextDependentPath`). An identifier made from such a
    /// path can change while the path stays the same.
    ///
    /// The base trait answers `false`: every identifier is stable. A
    /// resolver that wraps another forwards this to it, or the wrapped
    /// resolver's context-dependent paths are taken for stable ones.
    fn is_context_dependent_path(&self, _asset_path: &str) -> bool {
        false
    }

    /// The identifier an in-memory layer is interned under when `asset_path`
    /// names it. A layer that was never read from an asset has no location
    /// to anchor against, so this is the one spelling it is found by.
    ///
    /// It differs from [`create_identifier`](Self::create_identifier) with
    /// no anchor, which names a location: [`DefaultResolver`] places a
    /// relative path under the working directory there.
    ///
    /// The base trait returns `asset_path` as written, so `./sub.usda` and
    /// `sub.usda` are two identifiers. A resolver whose paths have segments
    /// overrides this to give equivalent spellings one identifier, and a
    /// resolver that wraps another forwards this to it.
    fn in_memory_identifier<'a>(&self, asset_path: &'a str) -> Cow<'a, str> {
        Cow::Borrowed(asset_path)
    }

    /// Returns metadata about a resolved asset.
    fn get_asset_info(&self, _asset_path: &str, _resolved_path: &ResolvedPath) -> AssetInfo {
        AssetInfo::default()
    }

    /// Returns the modification timestamp of a resolved asset.
    fn get_modification_timestamp(&self, _asset_path: &str, resolved_path: &ResolvedPath) -> Option<SystemTime> {
        fs::metadata(&**resolved_path).and_then(|m| m.modified()).ok()
    }

    /// A stable token identifying this resolver's configuration, used as the
    /// resolver component of a composed stack's
    /// [`LayerStackIdentifier`](crate::pcp::LayerStackIdentifier).
    ///
    /// Two resolvers that resolve every asset path identically must return the
    /// same token, and two that may resolve some path differently must return
    /// different tokens — so two stages opened under different resolver
    /// configurations are distinguished (the cross-stage edit-target guard).
    ///
    /// The base trait reports an empty token, meaning "indistinguishable from
    /// any other unconfigured resolver". Any implementation whose resolution can
    /// differ from another's — a different backend, or configuration such as
    /// search paths, a base URL, or a repository revision — must override this
    /// to render that distinguishing identity; otherwise it collides with the
    /// empty default and the guard treats the two as the same composition input.
    /// It is read once per stage, so computing it on demand is fine.
    fn identity(&self) -> String {
        String::new()
    }

    /// An id unique to this resolver among every resolver the process has
    /// made, under which a [`CacheScope`] keeps what was opened through it,
    /// or `None` for a resolver nothing is cached for.
    ///
    /// A cache keyed by it never answers one resolver with what another
    /// opened, whatever the two have in common. A resolver that forwards
    /// to another may answer with that one's id.
    fn cache_id(&self) -> Option<u64> {
        None
    }
}

/// A cache scope (C++ `ArResolverScopedCache`): a span, on one thread,
/// over which work that asks for the same asset several times keeps what
/// it opened, such as a package's directory. The scope ends when the guard
/// drops.
///
/// A scope begun while another is open on the thread shares that scope's
/// cache: an operation holds one without asking whether its caller does.
/// A scope belongs to the thread that began it and the guard stays on that
/// thread; [`handle`](Self::handle) gives the cache for a scope on another
/// thread to share.
pub struct CacheScope {
    handle: CacheHandle,
    /// Keeps the guard on its thread.
    thread: PhantomData<*const ()>,
}

impl CacheScope {
    /// Begins a scope on the calling thread. It shares the cache of the
    /// innermost scope open on the thread, and starts an empty one when
    /// there is none.
    pub fn begin() -> Self {
        Self::begin_shared(&Self::current().unwrap_or_default())
    }

    /// Begins a scope on the calling thread that shares `handle`'s cache,
    /// the cache of a scope open on another thread.
    ///
    /// TODO(rayon): nothing shares a cache across threads yet. A parallel
    /// load would begin each worker's scope with the handle of the scope
    /// its caller holds.
    pub fn begin_shared(handle: &CacheHandle) -> Self {
        SCOPES.with_borrow_mut(|scopes| scopes.push(handle.clone()));
        CacheScope {
            handle: handle.clone(),
            thread: PhantomData,
        }
    }

    /// The scope's cache.
    pub fn handle(&self) -> CacheHandle {
        self.handle.clone()
    }

    /// The cache of the innermost scope open on the calling thread.
    pub fn current() -> Option<CacheHandle> {
        SCOPES.with_borrow(|scopes| scopes.last().cloned())
    }
}

impl Drop for CacheScope {
    fn drop(&mut self) {
        // The innermost scope sharing this cache is the one removed: scopes
        // on one cache are interchangeable, which keeps guards dropped out
        // of the order they were begun in exact. A guard outliving its
        // thread's storage has nothing left to remove.
        let _ = SCOPES.try_with(|scopes| {
            let mut scopes = scopes.borrow_mut();
            if let Some(at) = scopes.iter().rposition(|open| Arc::ptr_eq(&open.0, &self.handle.0)) {
                scopes.remove(at);
            }
        });
    }
}

thread_local! {
    /// The caches of the scopes open on this thread, innermost last.
    static SCOPES: RefCell<Vec<CacheHandle>> = const { RefCell::new(Vec::new()) };
}

/// A cache scope's cache, by reference: clones share the one cache, and
/// the cache is released when the last of them drops.
///
/// The cache holds one value of each type asked of it. Each kind of work
/// keeps its own, such as the package cache of [`crate::usdz`].
#[derive(Clone, Default)]
pub struct CacheHandle(Arc<Mutex<HashMap<TypeId, Arc<dyn Any + Send + Sync>>>>);

impl CacheHandle {
    /// The cache of type `T` this scope keeps, made empty when first asked
    /// for.
    ///
    /// TODO(rayon): every lookup on every thread sharing the handle takes
    /// this one lock before the cache's own. A lookup only reads once the
    /// cache exists; a read lock would let them run together.
    pub fn cache<T: Any + Default + Send + Sync>(&self) -> Arc<T> {
        let mut caches = tf::lock(&self.0);
        let cache = caches
            .entry(TypeId::of::<T>())
            .or_insert_with(|| Arc::new(T::default()));
        Arc::clone(cache)
            .downcast()
            .expect("a cache is kept under its own type")
    }
}

/// Default filesystem-based asset resolver.
///
/// Resolves asset paths by searching the filesystem using a configurable
/// list of search directories. Resolution proceeds in order:
///
/// 1. If the path is absolute and the file exists, return it directly.
/// 2. Search the resolver's configured search directories.
/// 3. Search relative to the current working directory.
///
/// # Correspondence
///
/// This corresponds to `ArDefaultResolver` in the C++ USD API:
/// <https://openusd.org/dev/api/class_ar_default_resolver.html>
///
/// A file asset is read into memory unless the resolver was told to map
/// files ([`map_files`](Self::map_files)), in which case it is served from a
/// read-only memory mapping and a layer holds no copy of its file.
pub struct DefaultResolver {
    search_paths: Vec<PathBuf>,
    /// This resolver's [`cache_id`](Resolver::cache_id).
    id: u64,
    /// Whether a file asset is served from a memory mapping.
    #[cfg(feature = "mmap")]
    map_files: bool,
}

impl DefaultResolver {
    /// Creates a new default resolver with no search paths.
    pub fn new() -> Self {
        Self {
            search_paths: Vec::new(),
            id: crate::next_id(),
            #[cfg(feature = "mmap")]
            map_files: false,
        }
    }

    /// Serves every file asset from a read-only memory mapping of it. A
    /// layer then holds no copy of its file, and only the pages a read
    /// touches are loaded. An empty file, or one the platform cannot map, is
    /// read into memory.
    ///
    /// # Safety
    ///
    /// A mapped file must not be modified, by this process or any other,
    /// while anything read from it is alive: a layer, a package index, or an
    /// [`AssetBuffer`] view. The caller guarantees that for every file this
    /// resolver serves. The library upholds its half by never writing into a
    /// file it holds a view of: [`Layer::save`](crate::sdf::Layer::save)
    /// writes beside the file and renames over it, which unlinks the mapped
    /// file and leaves its bytes as they are. On Windows the mapped file is
    /// opened with write sharing denied, which keeps other handles from
    /// opening it for writing meanwhile and refuses to open a file a handle
    /// already has open for writing, and with delete sharing allowed, which
    /// lets a rename over it go through. Neither establishes the guarantee.
    /// If it is broken, a read faults the process when the file has shrunk
    /// and is undefined behaviour otherwise.
    #[cfg(feature = "mmap")]
    // Declaring the opt-in `unsafe` is what puts the promise on the caller;
    // the method itself does nothing unsafe, which is why the crate's ban on
    // unsafe code is lifted for its declaration alone.
    #[allow(unsafe_code)]
    pub unsafe fn map_files(mut self) -> Self {
        self.map_files = true;
        self
    }

    /// Creates a new default resolver with the given search paths.
    ///
    /// Each path is canonicalized to a stable spelling — relative paths are
    /// anchored to the current working directory and lexical noise (`.`
    /// components, redundant and trailing separators) is collapsed — so that
    /// directories named equivalently resolve, and render via
    /// [`identity`](Self::identity), identically.
    pub fn with_search_paths(paths: impl IntoIterator<Item = impl Into<PathBuf>>) -> Self {
        let mut resolver = Self::new();
        resolver.search_paths = paths.into_iter().map(|p| normalize_search_path(p.into())).collect();
        resolver
    }

    /// Searches for an asset by trying the path against the resolver's search
    /// directories, then the current working directory.
    fn resolve_with_search_paths(&self, asset_path: &str) -> Option<ResolvedPath> {
        let rel_path = &*host_path(asset_path)?;

        // If the path is absolute, just check existence.
        if rel_path.is_absolute() {
            return if rel_path.exists() {
                Some(ResolvedPath::new(rel_path.canonicalize().ok()?))
            } else {
                None
            };
        }

        for dir in &self.search_paths {
            let candidate = dir.join(rel_path);
            if candidate.exists() {
                return Some(ResolvedPath::new(candidate.canonicalize().ok()?));
            }
        }

        // Try relative to the current working directory.
        if let Ok(cwd) = std::env::current_dir() {
            let candidate = cwd.join(rel_path);
            if candidate.exists() {
                return Some(ResolvedPath::new(candidate.canonicalize().ok()?));
            }
        }

        None
    }
}

impl Default for DefaultResolver {
    fn default() -> Self {
        Self::new()
    }
}

impl Resolver for DefaultResolver {
    /// Anchors a relative `asset_path` against `anchor`'s directory, with the
    /// look-here-first rule of C++ `ArDefaultResolver::_CreateIdentifier`: a
    /// search path (relative, not spelled from `.` or `..`) whose anchored
    /// candidate does not exist keeps its bare normalized spelling, so
    /// resolving the identifier goes through the search directories and a
    /// `@usd/schema.usda@` sublayer is found beside any layer that names it.
    ///
    /// A relative path is read with `\` as a separator on every host, the
    /// rule C++ `ArchNormPath` applies on Windows, so a layer authored there
    /// (`@tex\stone.png@`) names the same asset everywhere. That departs
    /// from C++ in four ways:
    ///
    /// - C++ on a POSIX host keeps `\` as a file-name byte. Here a relative
    ///   asset path cannot name a file whose name contains `\`, and
    ///   `tex\stone.png` names `tex/stone.png` when both exist.
    /// - `.\sub.usda` and `..\sub.usda` are file-relative. C++
    ///   `_IsFileRelative` recognizes the `/` spellings only, so on Windows
    ///   it searches for `.\sub.usda`.
    /// - The packaged path of `pkg.usdz[tex\stone.png]` is normalized to the
    ///   entry name `tex/stone.png`. C++ leaves it as authored.
    ///
    /// - A letter and a colon open a Windows drive on every host, so
    ///   `a:b.usda` is absolute. C++ on a POSIX host reads it as a relative
    ///   path to a file of that name. A longer prefix (`ab:c.usda`) is an
    ///   ordinary file name.
    ///
    /// A path absolute for another platform (`C:\tex\a.png` or `a:b.usda` on
    /// Unix) names no location on this host and is returned unchanged.
    fn create_identifier(&self, asset_path: &str, anchor: Option<&ResolvedPath>) -> String {
        if asset_path.is_empty() {
            return String::new();
        }

        // An already package-relative asset path (`pkg.usdz[inner]`): anchor its
        // outer package path like any other path (so a relative `pkg.usdz` is
        // resolved against the anchor), then nest the inner packaged path back
        // inside the anchored package.
        if let Some((package, inner)) = split_authored_package(asset_path) {
            let anchored = self.create_identifier(&package, anchor);
            return nest_packaged_path(&anchored, &inner);
        }

        let Some(path) = host_path(asset_path) else {
            return asset_path.to_string();
        };

        // Absolute paths are their own identifier.
        if path.is_absolute() {
            return canonical_identifier(path.into_owned());
        }

        // Anchor relative paths.
        if let Some(anchor) = anchor {
            let anchor_str = anchor.to_string_lossy();
            // Anchor lives inside a package (`pkg.usdz[inner/layer.usd]`): keep
            // the reference inside the package, relative to the inner layer's
            // directory → `pkg.usdz[inner/asset.usd]`.
            if is_package_relative_path(&anchor_str)
                && let Some((package, inner)) = split_package_relative_path_inner(&anchor_str)
            {
                let inner_dir = inner.rsplit_once('/').map_or("", |(dir, _)| dir);
                let joined = join_packaged_path(inner_dir, asset_path);
                return nest_packaged_path(&package, &joined);
            }
            // Anchor IS a package file (`foo.usdz`): a relative reference from
            // the package's root layer is package-relative → `foo.usdz[asset]`.
            if anchor_str.to_ascii_lowercase().ends_with(".usdz") {
                let joined = join_packaged_path("", asset_path);
                return join_package_relative_path(&anchor_str, &joined);
            }
            if let Some(dir) = anchor.parent() {
                let anchored = dir.join(&path);
                if is_search_path(asset_path) {
                    return match anchored.canonicalize() {
                        Ok(found) => found.to_string_lossy().into_owned(),
                        Err(_) => path.to_string_lossy().into_owned(),
                    };
                }
                return canonical_identifier(anchored);
            }
        }

        // Without an anchor, resolve relative to the current working directory so
        // every identifier is stable and absolute (matching canonicalized dependencies).
        if let Ok(cwd) = std::env::current_dir() {
            return canonical_identifier(cwd.join(path));
        }

        asset_path.to_string()
    }

    fn resolve(&self, asset_path: &str) -> Option<ResolvedPath> {
        if asset_path.is_empty() {
            return None;
        }

        // A package-relative path (`pkg.usdz[inner]`) resolves its outer package
        // as a plain file, then reattaches the inner packaged path. The inner
        // entry must actually exist in the archive: a path to a missing entry is
        // unresolved, not merely unreadable, so the caller reports it as such
        // rather than as a malformed layer.
        if let Some((package, inner)) = split_authored_package(asset_path) {
            let resolved_package = self.resolve_with_search_paths(&package)?;
            let package_str = resolved_package.to_string_lossy();
            // The levels of a nested path share this call's scope when the
            // caller holds none: the outer package is opened once.
            let _scope = is_package_relative_path(&inner).then(CacheScope::begin);
            if !usdz::package_contains(self, &package_str, &inner) {
                return None;
            }
            return Some(ResolvedPath::new(join_package_relative_path(&package_str, &inner)));
        }

        self.resolve_with_search_paths(asset_path)
    }

    fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ResolvedPath> {
        if asset_path.is_empty() {
            return None;
        }

        // A new asset inside a package is placed in the new location of
        // its outer package.
        if let Some((package, inner)) = split_authored_package(asset_path) {
            let package = self.resolve_for_new_asset(&package)?;
            return Some(ResolvedPath::new(join_package_relative_path(
                &package.to_string_lossy(),
                &inner,
            )));
        }

        let path = host_path(asset_path)?;

        if path.is_absolute() {
            return Some(ResolvedPath::new(path.into_owned()));
        }

        // Resolve relative to the current working directory.
        std::env::current_dir()
            .ok()
            .map(|cwd| ResolvedPath::new(cwd.join(path)))
    }

    /// Whether `asset_path` is a search path, the one form whose identifier
    /// follows the filesystem: it stays bare until an asset appears beside
    /// the layer that authors it (C++
    /// `ArDefaultResolver::_IsContextDependentPath`).
    fn is_context_dependent_path(&self, asset_path: &str) -> bool {
        is_search_path(asset_path)
    }

    /// A relative `asset_path` in its normalized spelling (`\` read as a
    /// separator, `.` segments and repeated separators dropped), and the
    /// packaged part of a package-relative one as the entry name it reaches.
    /// So `sub\layer.usda`, `./sub/layer.usda` and `sub/layer.usda` all name
    /// the in-memory layer `sub/layer.usda`. An absolute path is returned
    /// unchanged.
    fn in_memory_identifier<'a>(&self, asset_path: &'a str) -> Cow<'a, str> {
        match split_authored_package(asset_path) {
            Some((package, inner)) => Cow::Owned(join_package_relative_path(&normalize_if_relative(&package), &inner)),
            None => normalize_if_relative(asset_path),
        }
    }

    /// Renders the canonicalized search paths as the resolver's identity token,
    /// so two `DefaultResolver`s with different search roots key distinct stacks.
    ///
    /// Each path is rendered via [`Debug`](std::fmt::Debug), which escapes
    /// losslessly — including newlines and non-UTF-8 bytes that
    /// [`to_string_lossy`](std::path::Path::to_string_lossy) would flatten — and
    /// wraps each segment in quotes. The concatenation is therefore injective:
    /// distinct path lists never collapse to the same token.
    fn identity(&self) -> String {
        self.search_paths.iter().map(|p| format!("{p:?}")).collect()
    }

    fn cache_id(&self) -> Option<u64> {
        Some(self.id)
    }

    fn open_asset(&self, resolved_path: &ResolvedPath) -> io::Result<Box<dyn Asset>> {
        let path_str = resolved_path.to_str().unwrap_or_default();

        // A package-relative path is an entry of its innermost package.
        // TODO(ar-package-resolver): the resolver reads a package through
        // `usdz::Archive` directly, so `ar` depends on the one package
        // format. C++ keeps `Ar` format-agnostic behind `ArPackageResolver`,
        // a per-extension trait the usdz resolver implements; `open_asset`
        // and `package_contains` would dispatch to it by the package's
        // extension.
        if is_package_relative_path(path_str) {
            let (package, inner) = split_package_relative_path_outer(path_str).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("invalid package-relative path: {}", resolved_path),
                )
            })?;
            // The entry's bytes are shared: a package nested here serves
            // its own entries as views of them.
            let bytes = usdz::package_entry(self, &package, &inner)?.into_shared();
            return Ok(Box::new(io::Cursor::new(AssetBuffer::Shared(bytes))));
        }

        self.open_file(resolved_path)
    }
}

impl DefaultResolver {
    /// Opens the file at `path` as an asset: over a mapping of it when the
    /// resolver maps files, over the file itself otherwise. A package is
    /// opened the same way, so its entries are views of the mapping too.
    // Without the feature there is no mapping policy to consult.
    #[cfg_attr(not(feature = "mmap"), allow(clippy::unused_self))]
    fn open_file(&self, path: &Path) -> io::Result<Box<dyn Asset>> {
        #[cfg(feature = "mmap")]
        if self.map_files {
            return open_mapped(path);
        }
        Ok(Box::new(fs::File::open(path)?))
    }
}

/// Opens the file at `path` as an asset over a read-only mapping of it, or
/// over the file itself when it is empty (Windows cannot map zero bytes) or
/// the platform cannot map it.
#[cfg(feature = "mmap")]
// Mapping a file is `unsafe` in memmap2: a file changed underneath the map is
// undefined behaviour, which no code here can rule out. The crate denies
// `unsafe_code` everywhere else; the exemption stops at this call, whose
// promise the caller of `DefaultResolver::map_files` makes.
#[allow(unsafe_code)]
fn open_mapped(path: &Path) -> io::Result<Box<dyn Asset>> {
    #[cfg(windows)]
    let file = {
        use std::os::windows::fs::OpenOptionsExt;
        // `FILE_SHARE_READ | FILE_SHARE_DELETE` from the Windows SDK: readers
        // and a rename may share the file, a writer may not, for as long as
        // the handle or a mapping made from it lives.
        fs::OpenOptions::new().read(true).share_mode(0x1 | 0x4).open(path)?
    };
    #[cfg(not(windows))]
    let file = fs::File::open(path)?;
    let Some(len) = usize::try_from(file.metadata()?.len()).ok().filter(|&len| len > 0) else {
        return Ok(Box::new(file));
    };
    // SAFETY: the mapping is read-only, and `DefaultResolver::map_files`, the
    // only way here, is `unsafe` so that its caller promises the file is not
    // modified while anything read from it is alive.
    match unsafe { memmap2::MmapOptions::new().len(len).map(&file) } {
        Ok(map) => Ok(Box::new(io::Cursor::new(AssetBuffer::Shared(SharedBuffer::new(map))))),
        Err(_) => Ok(Box::new(file)),
    }
}

/// Lexically normalizes `path`: drops `.` components (including a leading one)
/// and collapses redundant separators, with no filesystem access. `..` is
/// preserved, since collapsing it lexically could change meaning across
/// symlinks. C++ `TfNormPath` collapses it.
fn lexically_normalize(path: &Path) -> PathBuf {
    path.components().filter(|c| !matches!(c, Component::CurDir)).collect()
}

/// The characters that separate the segments of an authored asset path, on
/// every host.
const SEPARATORS: [char; 2] = ['/', '\\'];

/// Whether the authored `asset_path` is relative, as C++ `TfIsRelativePath`
/// reads it on Windows: it opens with neither a separator nor a drive, one
/// ASCII letter and a colon (`C:`). The answer is the same on every host, so
/// on Unix a file named `a:b.usda` is not reached by a relative path, while
/// `ab:c.usda` is.
fn is_relative_path(asset_path: &str) -> bool {
    let drive = matches!(asset_path.as_bytes(), [letter, b':', ..] if letter.is_ascii_alphabetic());
    !asset_path.starts_with(SEPARATORS) && !drive
}

/// Whether the authored `asset_path` is file-relative: it opens with a `.`
/// or `..` segment, so it is spelled from the directory of the layer that
/// authors it and is looked up there and nowhere else. The segment may end in
/// either separator: `.\sub.usda` is file-relative here, where C++
/// `_IsFileRelative` recognizes `./` and `../` alone.
pub(crate) fn is_file_relative_path(asset_path: &str) -> bool {
    matches!(asset_path.split(SEPARATORS).next(), Some("." | ".."))
}

/// Whether the authored `asset_path` is a search path (C++ `_IsSearchPath`):
/// relative, and not [file-relative](is_file_relative_path).
fn is_search_path(asset_path: &str) -> bool {
    is_relative_path(asset_path) && !is_file_relative_path(asset_path)
}

/// The relative `asset_path` with `/` between its segments, its `.` segments
/// dropped and its repeated or trailing separators collapsed: `tex\a.png`,
/// `./tex/a.png` and `tex//a.png` all become `tex/a.png`, as C++ `_NormPath`
/// collapses them. `..` segments stay, for the reason [`lexically_normalize`]
/// keeps them. A path already in this spelling is borrowed.
fn normalize_asset_path(asset_path: &str) -> Cow<'_, str> {
    let dropped = |segment: &str| segment.is_empty() || segment == ".";
    if !asset_path.contains('\\') && !asset_path.split('/').any(dropped) {
        return Cow::Borrowed(asset_path);
    }
    let kept: Vec<&str> = asset_path
        .split(SEPARATORS)
        .filter(|segment| !dropped(segment))
        .collect();
    Cow::Owned(kept.join("/"))
}

/// The authored `asset_path` in the spelling [`DefaultResolver`] gives it
/// before any anchoring: a relative path normalized, an absolute one as
/// written.
fn normalize_if_relative(asset_path: &str) -> Cow<'_, str> {
    if is_relative_path(asset_path) {
        normalize_asset_path(asset_path)
    } else {
        Cow::Borrowed(asset_path)
    }
}

/// The authored `asset_path` as a path on this host, or `None` for one that
/// is absolute for another platform and names no location here: `C:\tex\a.png`
/// and `\\server\share\a.png` on Unix, which the host's [`Path`] would read as
/// a single file name. A relative path comes back normalized
/// ([`normalize_asset_path`]), and one the host roots keeps its spelling.
fn host_path(asset_path: &str) -> Option<Cow<'_, Path>> {
    if is_relative_path(asset_path) {
        return Some(match normalize_asset_path(asset_path) {
            Cow::Borrowed(path) => Cow::Borrowed(Path::new(path)),
            Cow::Owned(path) => Cow::Owned(PathBuf::from(path)),
        });
    }
    let path = Path::new(asset_path);
    matches!(
        path.components().next(),
        Some(Component::Prefix(_) | Component::RootDir)
    )
    .then_some(Cow::Borrowed(path))
}

/// Renders `path` as a stable layer identifier: its filesystem-canonical
/// spelling when it resolves (collapsing equivalent spellings and following
/// symlinks), else the [`lexically_normalize`]d path.
///
/// `.` components are dropped either way, matching C++
/// [`ArResolver::CreateIdentifier`], which normalizes via `TfNormPath` without
/// touching the filesystem. So a target authored `./foo.usda` produces the same
/// identifier as `foo.usda` even when it is an in-memory layer that cannot be
/// canonicalized, and the registry's exact-identifier lookup still finds it.
///
/// [`ArResolver::CreateIdentifier`]: https://openusd.org/release/api/class_ar_resolver.html
fn canonical_identifier(path: PathBuf) -> String {
    path.canonicalize()
        .unwrap_or_else(|_| lexically_normalize(&path))
        .to_string_lossy()
        .into_owned()
}

/// Canonicalizes a search-path spelling for [`DefaultResolver`].
///
/// Relative paths are anchored to the current working directory, then lexical
/// noise is collapsed (see [`lexically_normalize`]). The result resolves
/// candidates identically to the input while giving equivalent directories one
/// canonical rendering.
fn normalize_search_path(path: PathBuf) -> PathBuf {
    let path = if path.is_relative() {
        std::env::current_dir().unwrap_or_default().join(path)
    } else {
        path
    };
    lexically_normalize(&path)
}

// ---------------------------------------------------------------------------
// Package-relative path utilities
// ---------------------------------------------------------------------------

/// Returns `true` if the path contains a package-relative component (bracket syntax).
///
/// Package-relative paths reference assets inside package files (e.g., USDZ archives)
/// using bracket notation: `Model.usdz[Geom.usd]`.
pub fn is_package_relative_path(path: &str) -> bool {
    path.contains('[') && path.ends_with(']')
}

/// Splits a package-relative path at the outermost bracket.
///
/// Returns the outer package path and the inner packaged path.
///
/// # Examples
///
/// ```
/// use openusd::ar::split_package_relative_path_outer;
///
/// let result = split_package_relative_path_outer("Model.usdz[Geom.usd]");
/// assert_eq!(result, Some(("Model.usdz".to_string(), "Geom.usd".to_string())));
///
/// let nested = split_package_relative_path_outer("Outer.usdz[Inner.usdz[Geom.usd]]");
/// assert_eq!(nested, Some(("Outer.usdz".to_string(), "Inner.usdz[Geom.usd]".to_string())));
/// ```
pub fn split_package_relative_path_outer(path: &str) -> Option<(String, String)> {
    let bracket = path.find('[')?;
    if !path.ends_with(']') {
        return None;
    }
    let outer = &path[..bracket];
    let inner = &path[bracket + 1..path.len() - 1];
    Some((outer.to_string(), inner.to_string()))
}

/// Splits a package-relative path at the innermost bracket.
///
/// Returns the outer package path (potentially still package-relative) and the
/// innermost asset path.
///
/// # Examples
///
/// ```
/// use openusd::ar::split_package_relative_path_inner;
///
/// let result = split_package_relative_path_inner("Model.usdz[Geom.usd]");
/// assert_eq!(result, Some(("Model.usdz".to_string(), "Geom.usd".to_string())));
///
/// let nested = split_package_relative_path_inner("Outer.usdz[Inner.usdz[Geom.usd]]");
/// assert_eq!(nested, Some(("Outer.usdz[Inner.usdz]".to_string(), "Geom.usd".to_string())));
/// ```
pub fn split_package_relative_path_inner(path: &str) -> Option<(String, String)> {
    if !path.ends_with(']') {
        return None;
    }

    // Find the last '[' — this starts the innermost packaged path.
    let open = path.rfind('[')?;

    // Find the matching ']' — the first ']' after the last '['.
    let close = path[open..].find(']').map(|i| open + i)?;

    let inner = &path[open + 1..close];
    // Outer is everything before the '[' plus everything after the ']'.
    let mut outer = path[..open].to_string();
    let remainder = &path[close + 1..];
    outer.push_str(remainder);

    Some((outer, inner.to_string()))
}

/// Joins a package path and an inner path into a package-relative path.
///
/// # Examples
///
/// ```
/// use openusd::ar::join_package_relative_path;
///
/// assert_eq!(
///     join_package_relative_path("Model.usdz", "Geom.usd"),
///     "Model.usdz[Geom.usd]"
/// );
/// ```
pub fn join_package_relative_path(package_path: &str, packaged_path: &str) -> String {
    format!("{}[{}]", package_path, packaged_path)
}

/// The byte range of the innermost packaged path of `path`, or of the whole
/// of `path` when it is not package-relative: the part a file extension or
/// name is read from.
fn innermost_span(path: &str) -> Range<usize> {
    if !is_package_relative_path(path) {
        return 0..path.len();
    }
    let Some(open) = path.rfind('[') else {
        return 0..path.len();
    };
    let close = path[open..].find(']').map_or(path.len(), |i| open + i);
    open + 1..close
}

/// The file extension of `path` without its leading dot, read inside the
/// innermost package bracket (C++ `ArResolver::GetExtension`), or `""` when
/// there is none.
pub(crate) fn extension(path: &str) -> &str {
    Path::new(&path[innermost_span(path)])
        .extension()
        .and_then(OsStr::to_str)
        .unwrap_or_default()
}

/// Splits `path` before its file name, read inside the innermost package
/// bracket: `pkg.usdz[dir/a.usda]` gives `("pkg.usdz[dir/", "a.usda")`, and a
/// plain path splits after its last separator.
pub(crate) fn split_file_name(path: &str) -> (&str, &str) {
    let span = innermost_span(path);
    let inner = &path[span.clone()];
    let name = inner.rfind(SEPARATORS).map_or(0, |i| i + 1);
    (&path[..span.start + name], &inner[name..])
}

/// Joins a package-internal directory with a relative reference authored inside
/// it, producing the entry name a packaged layer is stored under.
///
/// Package entry names are always `/`-separated and carry no filesystem
/// semantics, so unlike [`lexically_normalize`] this collapses `..` as well as
/// `.` and always emits forward slashes — the spelling
/// [`zip::ZipArchive::by_name`] matches against. `dir` is the directory of the
/// anchoring inner layer (empty for a layer at the package root); `rel` is the
/// relative path it references. A `..` that would climb above the package root
/// is dropped, since there is nothing above it inside the archive.
fn join_packaged_path(dir: &str, rel: &str) -> String {
    walk_packaged_path(dir, rel).0
}

/// [`join_packaged_path`] for a reference that must stay inside the package:
/// `None` when a `..` in `rel` climbs above the package root.
pub(crate) fn join_within_package(dir: &str, rel: &str) -> Option<String> {
    let (joined, climbed_out) = walk_packaged_path(dir, rel);
    (!climbed_out).then_some(joined)
}

/// The entry name `rel` reaches from the package-internal directory `dir`,
/// and whether a `..` in it climbed above the package root and was dropped.
fn walk_packaged_path(dir: &str, rel: &str) -> (String, bool) {
    let mut components: Vec<&str> = dir.split('/').filter(|c| !c.is_empty()).collect();
    let mut climbed_out = false;
    for part in rel.split(SEPARATORS) {
        match part {
            "" | "." => {}
            ".." => climbed_out |= components.pop().is_none(),
            other => components.push(other),
        }
    }
    (components.join("/"), climbed_out)
}

/// Splits the authored package-relative `asset_path` at its outermost
/// bracket into the package path as written and the packaged path as the
/// entry name it reaches, or `None` for a path that is not package-relative.
fn split_authored_package(asset_path: &str) -> Option<(String, String)> {
    let (package, inner) = split_package_relative_path_outer(asset_path)?;
    Some((package, normalize_packaged_path(&inner)))
}

/// The authored packaged path `packaged` as the entry name it reaches from a
/// package's root, each level of a nested one (`inner.usdz[tex\a.png]`)
/// normalized on its own. A level that climbs above its package's root
/// (`../a.png`) names no entry and keeps its spelling.
fn normalize_packaged_path(packaged: &str) -> String {
    let entry = |level: &str| join_within_package("", level).unwrap_or_else(|| level.to_owned());
    match split_authored_package(packaged) {
        Some((package, inner)) => join_package_relative_path(&entry(&package), &inner),
        None => entry(packaged),
    }
}

/// Attaches `leaf` as a packaged layer inside the deepest package of `base`.
///
/// For a plain `base` this is [`join_package_relative_path`]. When `base` is
/// itself package-relative — its outer package holds a nested package — the
/// `leaf` is nested into the innermost bracket so the result stays well-formed
/// (`pkg[inner[leaf]]`) rather than gaining a stray second bracket pair
/// (`pkg[inner][leaf]`), which no split or resolve step can interpret.
pub(crate) fn nest_packaged_path(base: &str, leaf: &str) -> String {
    match split_package_relative_path_outer(base) {
        Some((package, inner)) => join_package_relative_path(&package, &nest_packaged_path(&inner, leaf)),
        None => join_package_relative_path(base, leaf),
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::thread;

    use super::*;

    /// A resolver under which every asset path resolves to itself and opens
    /// to what `open` gives, standing in for the storage underneath a
    /// resolved asset.
    pub(crate) struct TestResolver<F>(pub(crate) F);

    impl<F: Fn() -> io::Result<Box<dyn Asset>>> Resolver for TestResolver<F> {
        fn create_identifier(&self, asset_path: &str, _anchor: Option<&ResolvedPath>) -> String {
            asset_path.to_string()
        }

        fn resolve(&self, asset_path: &str) -> Option<ResolvedPath> {
            Some(ResolvedPath::new(asset_path))
        }

        fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ResolvedPath> {
            Some(ResolvedPath::new(asset_path))
        }

        fn open_asset(&self, _resolved_path: &ResolvedPath) -> io::Result<Box<dyn Asset>> {
            (self.0)()
        }
    }

    // -----------------------------------------------------------------------
    // ResolvedPath
    // -----------------------------------------------------------------------

    #[test]
    fn resolved_path_empty() {
        let p = ResolvedPath::new("");
        assert!(p.is_empty());
    }

    #[test]
    fn resolved_path_display() {
        let p = ResolvedPath::new("/tmp/model.usda");
        assert_eq!(format!("{}", p), "/tmp/model.usda");
        assert!(!p.is_empty());
    }

    #[test]
    fn resolved_path_deref() {
        let p = ResolvedPath::new("some/path/model.usda");
        // The string-typed `extension` accessor, then a Path method via Deref.
        assert_eq!(p.extension(), "usda");
        assert_eq!(p.file_name().unwrap(), "model.usda");
        // The extension is lowercased for case-insensitive format matching.
        assert_eq!(ResolvedPath::new("x/Model.USDZ").extension(), "usdz");
        assert_eq!(ResolvedPath::new("x/noext").extension(), "");
    }

    #[test]
    fn resolver_identity_renders_search_paths() {
        // No search paths → empty identity (no distinguishing configuration).
        assert!(DefaultResolver::new().identity().is_empty());

        // Same search paths → equal identity; different → distinct.
        let a = DefaultResolver::with_search_paths(["/show/assets", "/lib"]);
        let b = DefaultResolver::with_search_paths(["/show/assets", "/lib"]);
        let c = DefaultResolver::with_search_paths(["/other"]);
        assert_eq!(a.identity(), b.identity());
        assert_ne!(a.identity(), c.identity());

        // Equivalent spellings canonicalize to one identity: a relative path
        // anchors to the cwd, and `.` lexical noise is collapsed.
        let cwd = std::env::current_dir().unwrap();
        let rel = DefaultResolver::with_search_paths(["assets"]);
        let abs = DefaultResolver::with_search_paths([cwd.join("assets")]);
        assert_eq!(rel.identity(), abs.identity());

        let plain = DefaultResolver::with_search_paths([cwd.join("lib")]);
        let noisy = DefaultResolver::with_search_paths([cwd.join("lib").join(".")]);
        assert_eq!(plain.identity(), noisy.identity());

        // The encoding is injective: a single path embedding a separator must
        // not collide with two distinct paths. `["a\nb"]` and `["a", "b"]` key
        // different stacks, keeping the cross-stage guard sound.
        let embedded = DefaultResolver::with_search_paths([cwd.join("a\nb")]);
        let split = DefaultResolver::with_search_paths([cwd.join("a"), cwd.join("b")]);
        assert_ne!(embedded.identity(), split.identity());
    }

    // -----------------------------------------------------------------------
    // Package-relative paths
    // -----------------------------------------------------------------------

    #[test]
    fn is_package_relative() {
        assert!(is_package_relative_path("Model.usdz[Geom.usd]"));
        assert!(is_package_relative_path("A.usdz[B.usdz[C.usd]]"));
        assert!(!is_package_relative_path("Model.usdz"));
        assert!(!is_package_relative_path("Model.usdz["));
        assert!(!is_package_relative_path("plain/path.usd"));
    }

    #[test]
    fn split_outer_simple() {
        let result = split_package_relative_path_outer("Model.usdz[Geom.usd]");
        assert_eq!(result, Some(("Model.usdz".to_string(), "Geom.usd".to_string())));
    }

    #[test]
    fn split_outer_nested() {
        let result = split_package_relative_path_outer("Outer.usdz[Inner.usdz[Geom.usd]]");
        assert_eq!(
            result,
            Some(("Outer.usdz".to_string(), "Inner.usdz[Geom.usd]".to_string()))
        );
    }

    #[test]
    fn split_inner_simple() {
        let result = split_package_relative_path_inner("Model.usdz[Geom.usd]");
        assert_eq!(result, Some(("Model.usdz".to_string(), "Geom.usd".to_string())));
    }

    #[test]
    fn split_inner_nested() {
        let result = split_package_relative_path_inner("Outer.usdz[Inner.usdz[Geom.usd]]");
        assert_eq!(
            result,
            Some(("Outer.usdz[Inner.usdz]".to_string(), "Geom.usd".to_string()))
        );
    }

    #[test]
    fn split_invalid() {
        assert_eq!(split_package_relative_path_outer("no_brackets"), None);
        assert_eq!(split_package_relative_path_inner("no_brackets"), None);
        assert_eq!(split_package_relative_path_outer("open[only"), None);
        assert_eq!(split_package_relative_path_inner("open[only"), None);
    }

    #[test]
    fn join_package_path() {
        assert_eq!(
            join_package_relative_path("Model.usdz", "Geom.usd"),
            "Model.usdz[Geom.usd]"
        );
    }

    // -----------------------------------------------------------------------
    // DefaultResolver
    // -----------------------------------------------------------------------

    #[test]
    fn resolver_empty_path() {
        let resolver = DefaultResolver::new();
        assert_eq!(resolver.resolve(""), None);
        assert_eq!(resolver.create_identifier("", None), "");
    }

    #[test]
    fn resolver_extension() {
        let resolver = DefaultResolver::new();
        assert_eq!(resolver.get_extension("model.usda"), "usda");
        assert_eq!(resolver.get_extension("archive.usdz"), "usdz");
        assert_eq!(resolver.get_extension("no_extension"), "");
        assert_eq!(resolver.get_extension("path/to/file.usdc"), "usdc");
        assert_eq!(resolver.get_extension("pkg.usdz[inner.usdz[a.usda]]"), "usda");
    }

    #[test]
    fn resolver_resolve_existing_file() {
        // Use Cargo.toml as a known existing file.
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let resolver = DefaultResolver::with_search_paths([&manifest]);

        let resolved = resolver.resolve("Cargo.toml");
        assert!(resolved.is_some());
        let resolved = resolved.unwrap();
        assert!(!resolved.is_empty());
        assert!(resolved.exists());
    }

    #[test]
    fn resolver_resolve_nonexistent() {
        let resolver = DefaultResolver::new();
        assert_eq!(resolver.resolve("nonexistent_file_12345.usda"), None);
    }

    #[test]
    fn resolver_resolve_absolute_path() {
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let abs_path = Path::new(&manifest).join("Cargo.toml");

        let resolver = DefaultResolver::new();
        let resolved = resolver.resolve(abs_path.to_str().unwrap());
        assert!(resolved.is_some());
    }

    #[test]
    fn resolver_create_identifier_absolute() {
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let abs_path = Path::new(&manifest).join("Cargo.toml");
        let abs_str = abs_path.to_str().unwrap();

        let resolver = DefaultResolver::new();
        let id = resolver.create_identifier(abs_str, None);
        assert!(!id.is_empty());
    }

    #[test]
    fn resolver_create_identifier_anchored() {
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let anchor = ResolvedPath::new(PathBuf::from(&manifest).join("src/lib.rs"));

        let resolver = DefaultResolver::new();
        let id = resolver.create_identifier("ar.rs", Some(&anchor));
        // The identifier should resolve relative to the anchor's directory.
        assert!(id.contains("ar.rs"));
    }

    /// A `.`-relative asset path that cannot be canonicalized (the target does
    /// not exist on disk, as for an in-memory layer) still has its `.` components
    /// dropped lexically, matching C++ `ArResolver::CreateIdentifier`'s
    /// `TfNormPath`. So `./sub.usda` and `sub.usda` yield the same identifier and
    /// the registry's exact-identifier lookup resolves an in-memory sublayer.
    #[test]
    fn resolver_create_identifier_dot_relative() {
        let resolver = DefaultResolver::new();
        let anchor = ResolvedPath::new(PathBuf::from("root.usda"));
        assert_eq!(
            resolver.create_identifier("./sub.usda", Some(&anchor)),
            resolver.create_identifier("sub.usda", Some(&anchor)),
            "a leading `./` normalizes away when the target cannot be canonicalized"
        );
    }

    /// A search path keeps its bare spelling when nothing sits beside the
    /// anchor, so the identifier resolves through the search directories; the
    /// same path anchors normally once a file appears beside the anchor
    /// (look-here-first), and a `./` path anchors even when missing.
    #[test]
    fn search_path_identifier_falls_back() {
        let dir = tempfile::tempdir().unwrap();
        let scene = dir.path().join("scene");
        let library = dir.path().join("library");
        fs::create_dir_all(scene.join("lib")).unwrap();
        fs::create_dir_all(library.join("lib")).unwrap();
        fs::write(scene.join("root.usda"), "#usda 1.0\n").unwrap();
        fs::write(library.join("lib").join("sub.usda"), "#usda 1.0\n").unwrap();

        let resolver = DefaultResolver::with_search_paths([&library]);
        let anchor = ResolvedPath::new(scene.join("root.usda"));

        let id = resolver.create_identifier("lib/sub.usda", Some(&anchor));
        assert_eq!(id, "lib/sub.usda", "a search path keeps its `/`-spelled bare form");
        assert_eq!(
            resolver.create_identifier("lib/./sub.usda", Some(&anchor)),
            "lib/sub.usda",
            "interior `.` segments normalize away"
        );
        let resolved = resolver.resolve(&id).expect("found through the search directory");
        assert_eq!(
            resolved.canonicalize().unwrap(),
            library.join("lib/sub.usda").canonicalize().unwrap()
        );

        // A `./` path is file-relative: it anchors even though nothing is there.
        let dot = resolver.create_identifier("./lib/sub.usda", Some(&anchor));
        assert!(Path::new(&dot).is_absolute(), "file-relative path anchored: {dot}");
        assert!(resolver.resolve(&dot).is_none());

        // Look-here-first: a file beside the anchor wins over the search path.
        fs::write(scene.join("lib").join("sub.usda"), "#usda 1.0\n").unwrap();
        let beside = resolver.create_identifier("lib/sub.usda", Some(&anchor));
        assert_eq!(
            Path::new(&beside).canonicalize().unwrap(),
            scene.join("lib/sub.usda").canonicalize().unwrap()
        );
    }

    #[test]
    fn search_path_predicate() {
        assert!(is_search_path("lib/sub.usda"));
        assert!(is_search_path("sub.usda"));
        assert!(is_search_path(r"tex\a.png"));
        assert!(!is_search_path("./sub.usda"));
        assert!(!is_search_path("../sub.usda"));
        assert!(!is_search_path("/abs/sub.usda"));
        // File-relative in either separator.
        assert!(!is_search_path(r".\sub.usda"));
        assert!(!is_search_path(r"..\sub.usda"));
        // Absolute on every host.
        for absolute in [
            r"C:\a.usda",
            "C:/a.usda",
            r"\\server\a.usda",
            r"\\?\C:\a.usda",
            "a:b.usda",
        ] {
            assert!(!is_relative_path(absolute), "{absolute}");
        }
        // Only a single letter before the colon is a drive.
        assert!(is_search_path("ab:c.usda"));
        assert!(is_search_path("1:c.usda"));
    }

    /// A relative asset path is normalized to `/` separators with its `.`
    /// segments and repeated separators dropped, on every host.
    #[test]
    fn asset_path_normalized() {
        assert_eq!(&*normalize_asset_path("./sub.usda"), "sub.usda");
        assert_eq!(&*normalize_asset_path("././sub.usda"), "sub.usda");
        assert_eq!(&*normalize_asset_path("dir/./sub.usda"), "dir/sub.usda");
        assert_eq!(&*normalize_asset_path(r"tex\stone.png"), "tex/stone.png");
        assert_eq!(&*normalize_asset_path(r".\sub.usda"), "sub.usda");
        assert_eq!(&*normalize_asset_path(r"dir\.\sub.usda"), "dir/sub.usda");
        assert_eq!(&*normalize_asset_path("a//b"), "a/b");
        assert_eq!(&*normalize_asset_path(r"..\a"), "../a");
        for unchanged in ["sub.usda", "../a", "a/../b.usda"] {
            assert!(
                matches!(normalize_asset_path(unchanged), Cow::Borrowed(path) if path == unchanged),
                "{unchanged} is borrowed as written"
            );
        }
    }

    /// The in-memory identifier of a relative path is its normalized
    /// spelling, an absolute path its own, and a packaged path is normalized
    /// level by level.
    #[test]
    fn in_memory_identifier_normalized() {
        let resolver = DefaultResolver::new();
        assert_eq!(resolver.in_memory_identifier(r".\sub\layer.usda"), "sub/layer.usda");
        assert_eq!(resolver.in_memory_identifier("/abs/./a.usda"), "/abs/./a.usda");
        assert_eq!(resolver.in_memory_identifier(r"C:\dir\a.usda"), r"C:\dir\a.usda");
        assert_eq!(
            resolver.in_memory_identifier(r"pkg\m.usdz[in.usdz[tex\a.png]]"),
            "pkg/m.usdz[in.usdz[tex/a.png]]"
        );
        assert_eq!(
            resolver.in_memory_identifier(r"C:\dir\m.usdz[tex/a.png]"),
            r"C:\dir\m.usdz[tex/a.png]"
        );
    }

    /// A `\`-spelled relative path names the asset its `/` spelling names:
    /// beside the anchor when it is there, bare when it is not, and anchored
    /// regardless when it opens with `.`.
    #[test]
    fn backslash_identifier() {
        let dir = tempfile::tempdir().unwrap();
        let anchor = ResolvedPath::new(dir.path().join("root.usda"));
        let resolver = DefaultResolver::new();

        assert_eq!(
            resolver.create_identifier(r"tex\stone.png", Some(&anchor)),
            "tex/stone.png",
            "a missing search path keeps its bare normalized spelling"
        );
        let colon = resolver.create_identifier("./ab:c.usda", Some(&anchor));
        assert!(Path::new(&colon).is_absolute(), "a longer prefix is no drive: {colon}");
        let dot = resolver.create_identifier(r".\tex\stone.png", Some(&anchor));
        assert!(Path::new(&dot).is_absolute(), "file-relative path anchored: {dot}");
        assert_eq!(dot, resolver.create_identifier("./tex/stone.png", Some(&anchor)));

        fs::create_dir(dir.path().join("tex")).unwrap();
        fs::write(dir.path().join("tex").join("stone.png"), b"png").unwrap();
        let expected = resolver.create_identifier("tex/stone.png", Some(&anchor));
        assert!(Path::new(&expected).is_absolute());
        assert_eq!(resolver.create_identifier(r"tex\stone.png", Some(&anchor)), expected);
        assert_eq!(resolver.create_identifier(r".\tex\stone.png", Some(&anchor)), expected);
    }

    #[test]
    fn backslash_search_dir() {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir(dir.path().join("tex")).unwrap();
        fs::write(dir.path().join("tex").join("stone.png"), b"png").unwrap();

        let resolver = DefaultResolver::with_search_paths([dir.path()]);
        let resolved = resolver
            .resolve(r"tex\stone.png")
            .expect("found in the search directory");
        assert_eq!(
            resolved.canonicalize().unwrap(),
            dir.path().join("tex/stone.png").canonicalize().unwrap()
        );
    }

    #[test]
    fn backslash_new_asset() {
        let resolver = DefaultResolver::new();
        let forward = resolver.resolve_for_new_asset("sub/new.usda").unwrap();
        assert!(forward.is_absolute());
        assert_eq!(resolver.resolve_for_new_asset(r"sub\new.usda").unwrap(), forward);
        assert_eq!(resolver.resolve_for_new_asset(r".\sub\new.usda").unwrap(), forward);
        assert_eq!(
            resolver.resolve_for_new_asset(r"sub\new.usdz[tex\a.png]").unwrap(),
            resolver.resolve_for_new_asset("sub/new.usdz[tex/a.png]").unwrap()
        );
    }

    /// A path absolute for another platform is its own identifier and
    /// resolves to nothing, even beside a file whose name is that path.
    #[cfg(unix)]
    #[test]
    fn foreign_absolute_unresolved() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(dir.path().join(r"C:\x\a.png"), b"png").unwrap();
        fs::write(dir.path().join("root.usda"), "#usda 1.0\n").unwrap();
        let anchor = ResolvedPath::new(dir.path().join("root.usda"));
        let resolver = DefaultResolver::with_search_paths([dir.path()]);

        for foreign in [r"C:\x\a.png", "C:/x/a.png", r"\\server\x\a.png"] {
            assert_eq!(resolver.create_identifier(foreign, Some(&anchor)), foreign);
            assert_eq!(resolver.create_identifier(foreign, None), foreign);
            assert!(resolver.resolve(foreign).is_none(), "{foreign}");
            assert!(resolver.resolve_for_new_asset(foreign).is_none(), "{foreign}");
        }
    }

    /// With a file literally named `tex\stone.png` beside `tex/stone.png`,
    /// the authored `tex\stone.png` names the latter.
    #[cfg(unix)]
    #[test]
    fn backslash_file_name_shadowed() {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir(dir.path().join("tex")).unwrap();
        fs::write(dir.path().join("tex").join("stone.png"), b"nested").unwrap();
        fs::write(dir.path().join(r"tex\stone.png"), b"literal").unwrap();
        let anchor = ResolvedPath::new(dir.path().join("root.usda"));
        let resolver = DefaultResolver::new();

        let id = resolver.create_identifier(r"tex\stone.png", Some(&anchor));
        let resolved = resolver.resolve(&id).expect("resolves");
        assert_eq!(fs::read(&*resolved).unwrap(), b"nested");
    }

    /// Each part of a package-relative path is normalized by its own rule:
    /// the package as a path beside the anchor, the packaged path as an
    /// entry name, at every level of nesting.
    #[test]
    fn backslash_package_relative() {
        let dir = tempfile::tempdir().unwrap();
        let packages = dir.path().join("packages");
        fs::create_dir(&packages).unwrap();
        let mut writer = usdz::ArchiveWriter::create(packages.join("model.usdz")).unwrap();
        writer.add_layer("root.usda", b"#usda 1.0\n").unwrap();
        writer.add_layer("tex/stone.png", b"png").unwrap();
        writer.finish().unwrap();

        let anchor = ResolvedPath::new(dir.path().join("root.usda"));
        let resolver = DefaultResolver::new();
        let package = resolver.create_identifier("packages/model.usdz", Some(&anchor));
        assert!(Path::new(&package).is_absolute());

        let id = resolver.create_identifier(r"packages\model.usdz[tex\stone.png]", Some(&anchor));
        assert_eq!(id, format!("{package}[tex/stone.png]"));
        let resolved = resolver.resolve(&id).expect("the entry is in the archive");
        assert_eq!(resolver.open_asset(&resolved).unwrap().read_all().unwrap(), b"png");
        assert!(
            resolver.resolve(&format!(r"{package}[tex\stone.png]")).is_some(),
            "the packaged path is normalized when resolving too"
        );

        assert_eq!(
            resolver.create_identifier(r"outer.usdz[inner.usdz[tex\stone.png]]", Some(&anchor)),
            "outer.usdz[inner.usdz[tex/stone.png]]",
            "a missing package keeps its bare spelling around the normalized entry"
        );
        assert!(
            resolver.resolve(&format!("{package}[../root.usda]")).is_none(),
            "a packaged path leading out of the package names no entry"
        );
        assert_eq!(
            resolver.create_identifier(r".\outer.usdz[inner.usdz[tex\stone.png]]", Some(&anchor)),
            format!(
                "{}[inner.usdz[tex/stone.png]]",
                resolver.create_identifier("./outer.usdz", Some(&anchor))
            )
        );
    }

    #[test]
    fn resolver_create_identifier_package_relative_anchored() {
        let resolver = DefaultResolver::new();
        let anchor = ResolvedPath::new(PathBuf::from("/scene/root.usda"));
        // A package-relative target anchors its outer package path to the
        // anchor's directory (not returned verbatim), then reattaches the inner
        // packaged path — the same identifier as anchoring the bare package.
        assert_eq!(
            resolver.create_identifier("model.usdz[geom.usd]", Some(&anchor)),
            join_package_relative_path(&resolver.create_identifier("model.usdz", Some(&anchor)), "geom.usd"),
        );
    }

    #[test]
    fn packaged_path_join_forward_slash() {
        // Package entry names are `/`-separated regardless of host platform, and
        // `.`/`..` collapse since there is no filesystem inside the archive.
        assert_eq!(join_packaged_path("geom", "mesh.usd"), "geom/mesh.usd");
        assert_eq!(join_packaged_path("geom", "./mesh.usd"), "geom/mesh.usd");
        assert_eq!(join_packaged_path("geom", "../tex/foo.usda"), "tex/foo.usda");
        assert_eq!(join_packaged_path("", "geom/mesh.usd"), "geom/mesh.usd");
        // A back-slash spelling is normalized to forward slashes.
        assert_eq!(join_packaged_path("geom", r"sub\mesh.usd"), "geom/sub/mesh.usd");
    }

    #[test]
    fn in_package_anchor_crosses_dirs() {
        let resolver = DefaultResolver::new();
        // A reference authored in a sub-directory layer that climbs out of it
        // resolves to a forward-slash, `..`-collapsed entry name — the spelling
        // the archive is keyed by — not a host path with separators or `..`.
        let anchor = ResolvedPath::new(PathBuf::from("pkg.usdz[geom/scene.usda]"));
        assert_eq!(
            resolver.create_identifier("../tex/foo.usda", Some(&anchor)),
            "pkg.usdz[tex/foo.usda]",
        );
    }

    #[test]
    fn nest_packaged_well_formed() {
        // A leaf nests into the innermost package rather than appending a stray
        // second bracket pair.
        assert_eq!(nest_packaged_path("pkg.usdz", "geom.usd"), "pkg.usdz[geom.usd]");
        assert_eq!(
            nest_packaged_path("pkg.usdz[model.usdz]", "geom.usd"),
            "pkg.usdz[model.usdz[geom.usd]]",
        );
        assert_eq!(
            nest_packaged_path("a.usdz[b.usdz[c.usdz]]", "d.usd"),
            "a.usdz[b.usdz[c.usdz[d.usd]]]",
        );
    }

    #[test]
    fn resolver_open_asset() {
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let resolver = DefaultResolver::with_search_paths([&manifest]);

        let resolved = resolver.resolve("Cargo.toml").unwrap();
        let mut asset = resolver.open_asset(&resolved).unwrap();

        let size = asset.size().unwrap();
        assert!(size > 0);

        let data = asset.read_all().unwrap();
        assert_eq!(data.len() as u64, size);
        assert!(String::from_utf8_lossy(&data).contains("[package]"));
    }

    #[test]
    fn resolver_modification_timestamp() {
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let resolver = DefaultResolver::with_search_paths([&manifest]);

        let resolved = resolver.resolve("Cargo.toml").unwrap();
        let ts = resolver.get_modification_timestamp("Cargo.toml", &resolved);
        assert!(ts.is_some());
    }

    #[test]
    fn resolve_for_new_asset_relative() {
        let resolver = DefaultResolver::new();
        let resolved = resolver.resolve_for_new_asset("new_file.usda");
        assert!(resolved.is_some());
        let resolved = resolved.unwrap();
        assert!(resolved.is_absolute());
    }

    // -----------------------------------------------------------------------
    // Asset impls
    // -----------------------------------------------------------------------

    #[test]
    fn cursor_asset_read() {
        let data = b"hello world".to_vec();
        let mut asset = io::Cursor::new(data.clone());

        assert_eq!(asset.size().unwrap(), 11);

        let result = asset.read_all().unwrap();
        assert_eq!(result, data);
    }

    /// Consuming a cursor asset hands its buffer over: an owned cursor moves
    /// it out and a shared one shares it. Reading the asset first leaves it
    /// intact.
    #[test]
    fn cursor_into_buffer() {
        let data = b"hello world".to_vec();
        let pointer = data.as_ptr();
        let mut asset: Box<dyn Asset> = Box::new(io::Cursor::new(data));
        assert_eq!(asset.read_all().unwrap(), b"hello world");
        assert_eq!(asset.size().unwrap(), 11);
        let AssetBuffer::Owned(moved) = asset.into_buffer().unwrap() else {
            panic!("an owned cursor moves its buffer out");
        };
        assert_eq!(moved.as_ptr(), pointer);

        let shared: Arc<[u8]> = b"hello world".to_vec().into();
        let asset: Box<dyn Asset> = Box::new(io::Cursor::new(AssetBuffer::from(shared.clone())));
        let AssetBuffer::Shared(view) = asset.into_buffer().unwrap() else {
            panic!("a shared cursor shares its buffer");
        };
        assert_eq!(view.as_ptr(), shared.as_ptr());
    }

    /// A view's bytes are the source's own, a slice of a slice composes the
    /// ranges, and a range past the view is refused.
    #[test]
    fn shared_slice() {
        let source: Arc<[u8]> = (0..32u8).collect::<Vec<_>>().into();
        let view = SharedBuffer::new(source.clone());
        assert_eq!(view.as_ptr(), source.as_ptr());
        let middle = view.slice(8..24).expect("within the view");
        assert_eq!(middle.as_ptr(), source[8..].as_ptr());
        assert_eq!(&*middle, &source[8..24]);
        let inner = middle.slice(4..8).expect("within the slice");
        assert_eq!(&*inner, &source[12..16]);
        assert!(middle.slice(8..17).is_none());
        let (start, end) = (5, 4);
        assert!(middle.slice(start..end).is_none());
        assert!(view.slice(32..32).is_some());
    }

    /// A file asset is read, and offers no view, unless the resolver maps
    /// files.
    #[test]
    fn file_asset_read() -> io::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("asset.bin");
        fs::write(&path, b"hello world")?;
        let asset = DefaultResolver::new().open_asset(&ResolvedPath::new(&path))?;
        assert!(asset.shared_buffer().is_none());
        let AssetBuffer::Owned(bytes) = asset.into_buffer()? else {
            panic!("a file asset is read");
        };
        assert_eq!(bytes, b"hello world");
        Ok(())
    }

    /// With the opt-in a file asset is a view of its mapping, as long as the
    /// file; an empty file, which cannot be mapped, is read.
    #[cfg(feature = "mmap")]
    #[test]
    // The opt-in is `unsafe` by contract, and this test, the only writer of
    // its directory, can make the promise.
    #[allow(unsafe_code)]
    fn file_asset_mapped() -> io::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("asset.bin");
        fs::write(&path, b"hello world")?;
        // SAFETY: nothing writes the files in this directory while they are
        // mapped.
        let resolver = unsafe { DefaultResolver::new().map_files() };
        let asset = resolver.open_asset(&ResolvedPath::new(&path))?;
        let view = asset.shared_buffer().expect("a mapped file offers its bytes");
        assert_eq!(view.len() as u64, fs::metadata(&path)?.len());
        assert_eq!(&*view, b"hello world");
        assert!(matches!(asset.into_buffer()?, AssetBuffer::Shared(_)));

        let empty = dir.path().join("empty.bin");
        fs::write(&empty, b"")?;
        let asset = resolver.open_asset(&ResolvedPath::new(&empty))?;
        assert!(asset.shared_buffer().is_none());
        assert!(matches!(asset.into_buffer()?, AssetBuffer::Owned(bytes) if bytes.is_empty()));
        Ok(())
    }

    /// Turning an owned buffer into a view keeps its allocation, and an
    /// in-memory asset's view is the whole asset from offset zero.
    #[test]
    fn shared_buffer_whole_asset() {
        let data = b"hello world".to_vec();
        let pointer = data.as_ptr();
        let view = AssetBuffer::Owned(data).into_shared();
        assert_eq!(view.as_ptr(), pointer);
        assert_eq!(&*view, b"hello world");

        let shared: Arc<[u8]> = b"hello world".to_vec().into();
        let mut asset = io::Cursor::new(AssetBuffer::from(shared.clone()));
        asset.seek(io::SeekFrom::Start(6)).unwrap();
        let view = asset.shared_buffer().expect("a shared cursor offers its bytes");
        asset.seek(io::SeekFrom::Start(0)).unwrap();
        assert_eq!(&*view, asset.read_all().unwrap().as_slice());

        let mut asset = io::Cursor::new(AssetBuffer::Shared(view));
        assert_eq!(
            asset.shared_buffer().expect("a view is offered").as_ptr(),
            shared.as_ptr()
        );
        assert_eq!(asset.read_all().unwrap(), b"hello world");
        assert!(
            io::Cursor::new(AssetBuffer::Owned(Vec::new()))
                .shared_buffer()
                .is_none()
        );
    }

    #[test]
    fn cursor_asset_seek() {
        let data = b"hello world".to_vec();
        let mut asset = io::Cursor::new(data);

        asset.seek(io::SeekFrom::Start(6)).unwrap();
        let mut buf = [0u8; 5];
        asset.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"world");
    }

    // Cache scopes

    /// A value a test keeps in a scope's cache.
    #[derive(Default)]
    struct Kept(Mutex<Vec<u32>>);

    /// What the scope open on this thread has kept, `None` with no scope.
    fn kept() -> Option<Vec<u32>> {
        Some(CacheScope::current()?.cache::<Kept>().0.lock().unwrap().clone())
    }

    /// Keeps `value` in the scope open on this thread.
    fn keep(value: u32) {
        let handle = CacheScope::current().expect("a scope is open");
        handle.cache::<Kept>().0.lock().unwrap().push(value);
    }

    /// A scope begun inside another shares its cache; the next scope begun
    /// with none open starts empty.
    #[test]
    fn nested_scope_shares() {
        assert_eq!(kept(), None);
        {
            let _scope = CacheScope::begin();
            keep(1);
            {
                let _nested = CacheScope::begin();
                keep(2);
            }
            assert_eq!(kept(), Some(vec![1, 2]));
        }
        assert_eq!(kept(), None);
        let _sibling = CacheScope::begin();
        assert_eq!(kept(), Some(vec![]));
    }

    /// A scope on another thread has its own cache, and shares one when it
    /// is begun with that cache's handle.
    #[test]
    fn scope_per_thread() {
        let scope = CacheScope::begin();
        keep(1);
        let handle = scope.handle();
        thread::scope(|threads| {
            let own = threads.spawn(|| {
                let _own = CacheScope::begin();
                kept()
            });
            assert_eq!(own.join().unwrap(), Some(vec![]));

            let shared = threads.spawn(|| {
                let _shared = CacheScope::begin_shared(&handle);
                keep(2);
                kept()
            });
            assert_eq!(shared.join().unwrap(), Some(vec![1, 2]));
        });
        assert_eq!(kept(), Some(vec![1, 2]));
    }

    /// Guards dropped out of the order they were begun in leave the
    /// surviving scope open, and no scope once the last is gone.
    #[test]
    fn scope_drop_order() {
        let outer = CacheScope::begin();
        let inner = CacheScope::begin();
        keep(1);
        drop(outer);
        assert_eq!(kept(), Some(vec![1]), "the surviving scope keeps the cache");
        drop(inner);
        assert_eq!(kept(), None);
    }

    /// A cache is kept by its type: two kinds of work in one scope each
    /// have their own.
    #[test]
    fn cache_per_type() {
        #[derive(Default)]
        struct Other(Mutex<u32>);

        let scope = CacheScope::begin();
        keep(1);
        *scope.handle().cache::<Other>().0.lock().unwrap() = 7;
        assert_eq!(kept(), Some(vec![1]));
        assert_eq!(*scope.handle().cache::<Other>().0.lock().unwrap(), 7);
    }

    // Advice

    /// The advice a [`Recording`] source was given, in order.
    pub(crate) type AdviceLog = Arc<Mutex<Vec<(Range<usize>, Advice)>>>;

    /// Shared bytes that record the advice they are given, standing in for
    /// a mapping.
    struct Recording {
        bytes: Vec<u8>,
        log: AdviceLog,
        mapping: bool,
    }

    impl sealed::Sealed for Recording {}

    impl SharedSource for Recording {
        fn bytes(&self) -> &[u8] {
            &self.bytes
        }

        fn advise(&self, range: Range<usize>, advice: Advice) {
            self.log.lock().unwrap().push((range, advice));
        }

        fn is_mapping(&self) -> bool {
            self.mapping
        }
    }

    /// A view of all of `bytes` over a source that records its advice and
    /// answers `mapping` when asked whether it is a file mapping, with the
    /// record. The record is shared with the source and has a second
    /// holder for as long as a view of the source lives.
    pub(crate) fn recording_source(bytes: Vec<u8>, mapping: bool) -> (SharedBuffer, AdviceLog) {
        let log = AdviceLog::default();
        let source = Recording {
            bytes,
            log: Arc::clone(&log),
            mapping,
        };
        (SharedBuffer::new(source), log)
    }

    /// Advice on a view reaches the source as the range of the source the
    /// view covers, cut off at the view's end.
    #[test]
    fn advise_translates_range() {
        let (buffer, log) = recording_source(vec![7; 100], true);
        let view = buffer.slice(10..50).expect("in range");
        view.advise(5..100, Advice::WillNeed);
        view.advise(60..70, Advice::Random);
        view.advise(0..40, Advice::Normal);
        assert_eq!(
            *log.lock().unwrap(),
            [(15..50, Advice::WillNeed), (10..50, Advice::Normal)],
            "a range wholly past the view is dropped"
        );
        assert_eq!(&*view, [7; 40]);
    }

    /// Bytes held in memory take advice and do nothing with it.
    #[test]
    fn heap_ignores_advice() {
        let buffer = SharedBuffer::new(vec![1, 2, 3]);
        buffer.advise(0..3, Advice::WillNeed);
        buffer.advise(0..3, Advice::Random);
        assert!(!buffer.is_mapping());
        assert_eq!(&*buffer, [1, 2, 3]);
    }
}
