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

use std::collections::HashMap;
use std::fmt;
use std::fs;
use std::io::{self, Read, Seek};
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

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
        let size = self.size()? as usize;
        let mut buf = Vec::with_capacity(size);
        self.read_to_end(&mut buf)?;
        Ok(buf)
    }
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

    /// Returns the file extension of the given asset path (without the leading dot).
    fn get_extension<'a>(&self, asset_path: &'a str) -> &'a str {
        Path::new(asset_path)
            .extension()
            .and_then(|e| e.to_str())
            .unwrap_or_default()
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
pub struct DefaultResolver {
    search_paths: Vec<PathBuf>,
}

impl DefaultResolver {
    /// Creates a new default resolver with no search paths.
    pub fn new() -> Self {
        Self {
            search_paths: Vec::new(),
        }
    }

    /// Creates a new default resolver with the given search paths.
    ///
    /// Each path is canonicalized to a stable spelling — relative paths are
    /// anchored to the current working directory and lexical noise (`.`
    /// components, redundant and trailing separators) is collapsed — so that
    /// directories named equivalently resolve, and render via
    /// [`identity`](Self::identity), identically.
    pub fn with_search_paths(paths: impl IntoIterator<Item = impl Into<PathBuf>>) -> Self {
        let search_paths = paths.into_iter().map(|p| normalize_search_path(p.into())).collect();
        Self { search_paths }
    }

    /// Searches for an asset by trying the path against the resolver's search
    /// directories, then the current working directory.
    fn resolve_with_search_paths(&self, asset_path: &str) -> Option<ResolvedPath> {
        let rel_path = Path::new(asset_path);

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
    fn create_identifier(&self, asset_path: &str, anchor: Option<&ResolvedPath>) -> String {
        if asset_path.is_empty() {
            return String::new();
        }

        let path = Path::new(asset_path);

        // Absolute paths are their own identifier.
        if path.is_absolute() {
            return path
                .canonicalize()
                .unwrap_or_else(|_| path.to_path_buf())
                .to_string_lossy()
                .into_owned();
        }

        // Anchor relative paths to the anchor's directory.
        if let Some(anchor) = anchor {
            if let Some(dir) = anchor.parent() {
                let anchored = dir.join(path);
                return anchored
                    .canonicalize()
                    .unwrap_or(anchored)
                    .to_string_lossy()
                    .into_owned();
            }
        }

        // Without an anchor, resolve relative to the current working directory so
        // every identifier is stable and absolute (matching canonicalized dependencies).
        if let Ok(cwd) = std::env::current_dir() {
            let joined = cwd.join(path);
            return joined.canonicalize().unwrap_or(joined).to_string_lossy().into_owned();
        }

        asset_path.to_string()
    }

    fn resolve(&self, asset_path: &str) -> Option<ResolvedPath> {
        if asset_path.is_empty() {
            return None;
        }

        // Handle package-relative paths.
        if is_package_relative_path(asset_path) {
            let (package, inner) = split_package_relative_path_outer(asset_path)?;
            let resolved_package = self.resolve(&package)?;
            // Return the resolved package with the inner path reattached.
            let package_str = resolved_package.to_str().unwrap_or_default();
            return Some(ResolvedPath::new(join_package_relative_path(package_str, &inner)));
        }

        self.resolve_with_search_paths(asset_path)
    }

    fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ResolvedPath> {
        if asset_path.is_empty() {
            return None;
        }

        let path = Path::new(asset_path);

        if path.is_absolute() {
            return Some(ResolvedPath::new(path));
        }

        // Resolve relative to the current working directory.
        std::env::current_dir()
            .ok()
            .map(|cwd| ResolvedPath::new(cwd.join(path)))
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

    fn open_asset(&self, resolved_path: &ResolvedPath) -> io::Result<Box<dyn Asset>> {
        let path_str = resolved_path.to_str().unwrap_or_default();

        // Handle package-relative paths by extracting from the archive.
        if is_package_relative_path(path_str) {
            let (package, inner) = split_package_relative_path_outer(path_str).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("invalid package-relative path: {}", resolved_path),
                )
            })?;

            let package_file = fs::File::open(&package)?;
            let mut archive = zip::ZipArchive::new(package_file).map_err(io::Error::other)?;
            let mut entry = archive.by_name(&inner).map_err(io::Error::other)?;

            let mut buffer = Vec::new();
            entry.read_to_end(&mut buffer)?;

            return Ok(Box::new(io::Cursor::new(buffer)));
        }

        let file = fs::File::open(&**resolved_path)?;
        Ok(Box::new(file))
    }
}

/// Canonicalizes a search-path spelling for [`DefaultResolver`].
///
/// Relative paths are anchored to the current working directory; lexical noise
/// (`.` components, redundant and trailing separators) is collapsed. The result
/// resolves candidates identically to the input while giving equivalent
/// directories one canonical rendering. `..` is preserved, since collapsing it
/// lexically would change meaning across symlinks.
fn normalize_search_path(path: PathBuf) -> PathBuf {
    let path = if path.is_relative() {
        std::env::current_dir().unwrap_or_default().join(path)
    } else {
        path
    };
    path.components().collect()
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

#[cfg(test)]
mod tests {
    use super::*;

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
        // Deref to Path allows calling Path methods directly.
        assert_eq!(p.extension().unwrap(), "usda");
        assert_eq!(p.file_name().unwrap(), "model.usda");
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

    #[test]
    fn cursor_asset_seek() {
        let data = b"hello world".to_vec();
        let mut asset = io::Cursor::new(data);

        asset.seek(io::SeekFrom::Start(6)).unwrap();
        let mut buf = [0u8; 5];
        asset.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"world");
    }
}
