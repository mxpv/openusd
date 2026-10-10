//! Reading a package through a resolver (C++ `Sdf_UsdzResolver`), each
//! package opened once per cache scope (C++ `Sdf_UsdzResolverCache`).

use std::cell::Cell;
use std::collections::HashMap;
use std::io;
use std::sync::{Arc, Mutex, OnceLock};

use super::{Archive, ArchiveError};
use crate::{ar, tf};

/// A package opened through a resolver: its central directory, parsed once
/// and shared by every holder (C++ `SdfZipFile` as `Sdf_UsdzResolverCache`
/// shares it).
#[derive(Clone)]
pub struct Package(Arc<Mutex<Archive>>);

impl Package {
    /// Runs `read` on the package's archive. Holders take turns, since
    /// reading an entry moves the archive's position in its asset.
    ///
    /// TODO(rayon): a reader of one entry holds the package for the whole
    /// read. Entries are independent ranges of the package: readers on
    /// several threads could each take a range under the lock and read it
    /// outside.
    pub fn with<T>(&self, read: impl FnOnce(&mut Archive) -> T) -> T {
        read(&mut tf::lock(&self.0))
    }
}

/// Why a package could not be opened, or an entry of it read. The failure
/// is shared, since a cache scope reports one failed open to every caller
/// that asks for the package within it.
#[derive(Debug, Clone, thiserror::Error)]
#[error(transparent)]
pub struct PackageError(Arc<ArchiveError>);

impl PackageError {
    /// The failure underneath.
    pub fn archive_error(&self) -> &ArchiveError {
        &self.0
    }
}

impl From<ArchiveError> for PackageError {
    fn from(error: ArchiveError) -> Self {
        PackageError(Arc::new(error))
    }
}

/// A package failure keeps the kind of the byte I/O failure underneath it
/// when there is one.
impl From<PackageError> for io::Error {
    fn from(error: PackageError) -> Self {
        io::Error::new(error.0.io_kind().unwrap_or(io::ErrorKind::Other), error)
    }
}

/// The package work done on one thread, as [`package_stats`] reports it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PackageStats {
    /// How many times a package file was asked for, found or not.
    pub opens: u64,
    /// How many times a package was opened to parse its central directory,
    /// counting each level of a package nested in another.
    pub directory_parses: u64,
    /// How many requests for a package a cache scope answered with one it
    /// had already opened.
    pub cache_hits: u64,
}

/// What a cache scope keeps for packages: each one opened within it, by
/// the resolver it was opened through and the package path it was asked for
/// by, one slot per level of nesting. A slot is filled once, by the open,
/// and holds its failure when it fails.
#[derive(Default)]
struct PackageCache {
    slots: Mutex<HashMap<u64, HashMap<String, PackageSlot>>>,
}

type PackageSlot = Arc<OnceLock<Result<Package, PackageError>>>;

/// Opens the package at `package` through `resolver`, reading only its
/// central directory. `package` is a resolved path, itself package-relative
/// for a package nested in another (`outer.usdz[inner.usdz]`), whose asset
/// the resolver serves as an entry of the package around it.
///
/// With an [`ar::CacheScope`] open on the calling thread, and a resolver
/// that names itself to caches ([`ar::Resolver::cache_id`]), the package
/// comes from the scope's cache (C++
/// `Sdf_UsdzResolverCache::FindOrOpenZipFile`): it is opened once within the
/// scope, callers that miss on it at once share the one open, and a failed
/// open is kept and reported to each of them. Otherwise it is opened for
/// this call alone.
///
/// A cached package is answered for as long as the scope is open: one
/// replaced meanwhile is still read as it was opened, and one that failed
/// to open still fails. A caller that rewrites a package ends the scope
/// first.
pub fn open_package(resolver: &dyn ar::Resolver, package: &ar::ResolvedPath) -> Result<Package, PackageError> {
    let path = package.to_string_lossy();
    let open = || -> Result<Package, PackageError> {
        count(|stats| {
            if !ar::is_package_relative_path(&path) {
                stats.opens += 1;
            }
            stats.directory_parses += 1;
        });
        // A nested package's asset is an entry of the package around it,
        // and a failure to read that one arrives wrapped as an I/O error:
        // it is reported as the package failure it is.
        let asset = resolver
            .open_asset(package)
            .map_err(|error| match error.downcast::<PackageError>() {
                Ok(outer) => outer,
                Err(error) => ArchiveError::from(error).into(),
            })?;
        Ok(Package(Arc::new(Mutex::new(Archive::from_asset(asset)?))))
    };
    let (Some(scope), Some(resolver_id)) = (ar::CacheScope::current(), resolver.cache_id()) else {
        return open();
    };
    // The slot map is locked only to find the package's slot. The open runs
    // under the slot alone. The open of a nested package, which asks the
    // resolver for the package around it, takes the map afresh.
    let cache = scope.cache::<PackageCache>();
    let slot = {
        let mut slots = tf::lock(&cache.slots);
        let of_resolver = slots.entry(resolver_id).or_default();
        match of_resolver.get(path.as_ref()) {
            Some(slot) => Arc::clone(slot),
            None => Arc::clone(of_resolver.entry(path.to_string()).or_default()),
        }
    };
    if let Some(found) = slot.get() {
        count(|stats| stats.cache_hits += 1);
        return found.clone();
    }
    slot.get_or_init(open).clone()
}

/// Whether `inner` should be treated as present in the package at `package`
/// (C++ `Sdf_UsdzResolver::Resolve`).
///
/// Reading only the archive's central directory, not its entry data, a
/// readable archive that lacks a flat entry reports it absent. A nested
/// packaged path (`inner.usdz[deep.usd]`) is checked one bracket at a time,
/// the inner package read from its entry. A package that cannot be opened
/// (an I/O error or a corrupt archive, as distinct from an absent entry) is
/// treated as present. The open that follows then reports the real error,
/// where an absent package would read as a missing asset.
pub fn package_contains(resolver: &dyn ar::Resolver, package: &str, inner: &str) -> bool {
    let Ok(found) = open_package(resolver, &ar::ResolvedPath::new(package)) else {
        return true;
    };
    let Some((nested, rest)) = ar::split_package_relative_path_outer(inner) else {
        return found.with(|archive| archive.contains(inner));
    };
    found.with(|archive| archive.contains(&nested))
        && package_contains(resolver, &ar::nest_packaged_path(package, &nested), &rest)
}

/// The bytes of the entry `inner` names in the package at `package` (C++
/// `Sdf_UsdzResolver::OpenAsset`). A nested packaged path
/// (`inner.usdz[deep.usd]`) is followed one bracket at a time from the
/// outside, as [`package_contains`] follows it, each level a view of the
/// one around it when the package shares its bytes.
pub fn package_entry(resolver: &dyn ar::Resolver, package: &str, inner: &str) -> Result<ar::AssetBuffer, PackageError> {
    match ar::split_package_relative_path_outer(inner) {
        Some((nested, rest)) => package_entry(resolver, &ar::nest_packaged_path(package, &nested), &rest),
        None => Ok(open_package(resolver, &ar::ResolvedPath::new(package))?.with(|archive| archive.entry(inner))?),
    }
}

/// The package work [`open_package`] has done on the calling thread.
pub fn package_stats() -> PackageStats {
    STATS.get()
}

/// Applies `update` to the calling thread's counts.
fn count(update: impl FnOnce(&mut PackageStats)) {
    let mut stats = STATS.get();
    update(&mut stats);
    STATS.set(stats);
}

thread_local! {
    static STATS: Cell<PackageStats> = const {
        Cell::new(PackageStats {
            opens: 0,
            directory_parses: 0,
            cache_hits: 0,
        })
    };
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::io;
    use std::path::Path;
    use std::sync::Barrier;
    use std::thread;

    use super::*;
    use crate::ar::Resolver as _;
    use crate::usd;
    use crate::usdz::tests::package;

    /// `path` as the string the resolver knows it by.
    fn canonical(path: &Path) -> String {
        path.canonicalize().unwrap().to_string_lossy().into_owned()
    }

    /// A directory holding `pkg.usdz` with the layers `a.usda` and `b.usda`,
    /// and the package's path.
    fn packaged_dir() -> (tempfile::TempDir, String) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("pkg.usdz");
        fs::write(
            &path,
            package(&[("a.usda", b"#usda 1.0\n"), ("b.usda", b"#usda 1.0\n")]),
        )
        .unwrap();
        let path = canonical(&path);
        (dir, path)
    }

    /// A directory holding `outer.usdz`, whose entry `inner.usdz` is a
    /// package holding `a.usda`, and the outer package's path.
    fn nested_dir() -> (tempfile::TempDir, String) {
        let dir = tempfile::tempdir().unwrap();
        let inner = package(&[("a.usda", b"#usda 1.0\n")]);
        let path = dir.path().join("outer.usdz");
        fs::write(&path, package(&[("root.usda", b"#usda 1.0\n"), ("inner.usdz", &inner)])).unwrap();
        let path = canonical(&path);
        (dir, path)
    }

    /// The package file opens and directory parses done on this thread.
    fn work() -> (u64, u64) {
        let stats = package_stats();
        (stats.opens, stats.directory_parses)
    }

    /// Resolves and opens the entry `name` of `package`.
    fn read_entry(resolver: &ar::DefaultResolver, package: &str, name: &str) -> io::Result<Vec<u8>> {
        let path = ar::join_package_relative_path(package, name);
        let resolved = resolver
            .resolve(&path)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        resolver.open_asset(&resolved)?.read_all()
    }

    /// Within a scope a package is opened and parsed once, whatever is asked
    /// of it; a scope begun inside shares that, and the next scope does not.
    #[test]
    fn scope_opens_once() {
        let (_dir, pkg) = packaged_dir();
        let resolver = ar::DefaultResolver::new();
        {
            let _scope = ar::CacheScope::begin();
            read_entry(&resolver, &pkg, "a.usda").unwrap();
            read_entry(&resolver, &pkg, "b.usda").unwrap();
            let missing = ar::join_package_relative_path(&pkg, "missing.usda");
            assert!(resolver.resolve(&missing).is_none());
            {
                let _nested = ar::CacheScope::begin();
                read_entry(&resolver, &pkg, "a.usda").unwrap();
            }
            assert_eq!(work(), (1, 1));
            assert!(package_stats().cache_hits > 0);
        }
        let _sibling = ar::CacheScope::begin();
        read_entry(&resolver, &pkg, "a.usda").unwrap();
        assert_eq!(work(), (2, 2));
    }

    /// With no scope held nothing is kept past a call: each request opens
    /// the package.
    #[test]
    fn no_scope_no_cache() {
        let (_dir, pkg) = packaged_dir();
        let resolver = ar::DefaultResolver::new();
        let path = ar::join_package_relative_path(&pkg, "a.usda");
        resolver.resolve(&path).unwrap();
        resolver.resolve(&path).unwrap();
        assert_eq!(work(), (2, 2));
    }

    /// A package nested in another is one file open and one parse per level.
    #[test]
    fn nested_levels_once() {
        let (_dir, outer) = nested_dir();
        let resolver = ar::DefaultResolver::new();
        let _scope = ar::CacheScope::begin();
        for _ in 0..2 {
            assert_eq!(
                read_entry(&resolver, &outer, "inner.usdz[a.usda]").unwrap(),
                b"#usda 1.0\n"
            );
        }
        read_entry(&resolver, &outer, "root.usda").unwrap();
        assert_eq!(work(), (1, 2));
    }

    /// With no scope held, a path into a nested package still opens the
    /// outer file once per call.
    #[test]
    fn nested_unscoped_opens_once() {
        let (_dir, outer) = nested_dir();
        let resolver = ar::DefaultResolver::new();
        let nested = ar::join_package_relative_path(&outer, "inner.usdz[a.usda]");
        let resolved = resolver.resolve(&nested).expect("the entry exists");
        assert_eq!(work(), (1, 2), "the resolve");
        resolver.open_asset(&resolved).unwrap();
        assert_eq!(work(), (2, 4), "the open");
    }

    /// An entry whose name holds brackets is one entry, to the open as to
    /// the resolve.
    #[test]
    fn bracketed_entry_name() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("pkg.usdz");
        fs::write(
            &path,
            package(&[("root.usda", b"#usda 1.0\n"), ("textures/tile[0].png", b"pixels")]),
        )
        .unwrap();
        let resolver = ar::DefaultResolver::new();
        assert_eq!(
            read_entry(&resolver, &canonical(&path), "textures/tile[0].png").unwrap(),
            b"pixels"
        );
    }

    /// Threads that miss on one package at once, in one cache, share a
    /// single open of it.
    #[test]
    fn concurrent_miss_one_open() {
        let (_dir, pkg) = packaged_dir();
        let resolver = ar::DefaultResolver::new();
        let scope = ar::CacheScope::begin();
        let handle = scope.handle();
        let start = Barrier::new(8);
        let opens: u64 = thread::scope(|threads| {
            let workers: Vec<_> = (0..8)
                .map(|_| {
                    threads.spawn(|| {
                        let _shared = ar::CacheScope::begin_shared(&handle);
                        start.wait();
                        read_entry(&resolver, &pkg, "a.usda").unwrap();
                        package_stats().opens
                    })
                })
                .collect();
            workers.into_iter().map(|worker| worker.join().unwrap()).sum()
        });
        assert_eq!(opens, 1);
    }

    /// A cached package answers the resolver it was opened through: another
    /// resolver, though configured the same, opens its own.
    #[test]
    fn cache_keyed_by_resolver() {
        let (_dir, pkg) = packaged_dir();
        let (first, second) = (ar::DefaultResolver::new(), ar::DefaultResolver::new());
        let _scope = ar::CacheScope::begin();
        read_entry(&first, &pkg, "a.usda").unwrap();
        read_entry(&first, &pkg, "b.usda").unwrap();
        assert_eq!(work(), (1, 1));
        read_entry(&second, &pkg, "a.usda").unwrap();
        assert_eq!(work(), (2, 2));
    }

    /// A resolver that does not name itself to caches is opened through
    /// afresh each time, scope or no scope.
    #[test]
    fn unnamed_resolver_not_cached() {
        let (_dir, pkg) = packaged_dir();
        let bytes = fs::read(&pkg).unwrap();
        let resolver = ar::tests::TestResolver(move || -> io::Result<Box<dyn ar::Asset>> {
            Ok(Box::new(io::Cursor::new(bytes.clone())))
        });
        let _scope = ar::CacheScope::begin();
        let package = ar::ResolvedPath::new(&pkg);
        for _ in 0..2 {
            assert!(
                open_package(&resolver, &package)
                    .unwrap()
                    .with(|archive| archive.contains("a.usda"))
            );
        }
        assert_eq!(work(), (2, 2));
    }

    /// A package nested in a package that cannot be read fails as a package
    /// failure, not as byte I/O.
    #[test]
    fn nested_failure_keeps_kind() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("outer.usdz");
        fs::write(&path, b"not a package").unwrap();
        let nested = ar::ResolvedPath::new(ar::join_package_relative_path(&path.to_string_lossy(), "inner.usdz"));
        let error = open_package(&ar::DefaultResolver::new(), &nested)
            .err()
            .expect("an unreadable package");
        assert!(
            !matches!(error.archive_error(), ArchiveError::Io(_)),
            "{:?}",
            error.archive_error()
        );
    }

    /// A package replaced between two scopes is read anew by the second.
    #[test]
    fn replaced_between_scopes() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("pkg.usdz");
        fs::write(&path, package(&[("a.usda", b"#usda 1.0\n# old\n")])).unwrap();
        let pkg = canonical(&path);
        let resolver = ar::DefaultResolver::new();
        {
            let _scope = ar::CacheScope::begin();
            assert_eq!(read_entry(&resolver, &pkg, "a.usda").unwrap(), b"#usda 1.0\n# old\n");
        }
        fs::write(&path, package(&[("a.usda", b"#usda 1.0\n# new\n")])).unwrap();
        let _scope = ar::CacheScope::begin();
        assert_eq!(read_entry(&resolver, &pkg, "a.usda").unwrap(), b"#usda 1.0\n# new\n");
    }

    /// A package that cannot be opened fails the same way each time it is
    /// asked for within a scope, from the one attempt, and is tried again in
    /// the next scope.
    #[test]
    fn failed_open_keeps_error() {
        let dir = tempfile::tempdir().unwrap();
        let corrupt = dir.path().join("corrupt.usdz");
        fs::write(&corrupt, b"not a package").unwrap();
        let missing = dir.path().join("missing.usdz");

        let mut attempts = 0;
        for (package, kind) in [(corrupt, io::ErrorKind::Other), (missing, io::ErrorKind::NotFound)] {
            let resolver = ar::DefaultResolver::new();
            let entry = ar::ResolvedPath::new(ar::join_package_relative_path(&package.to_string_lossy(), "a.usda"));
            let failure = |resolver: &ar::DefaultResolver| {
                let error = resolver.open_asset(&entry).err().expect("an unreadable package");
                (error.kind(), error.to_string())
            };
            let hits = package_stats().cache_hits;
            {
                let _scope = ar::CacheScope::begin();
                let first = failure(&resolver);
                assert_eq!(first.0, kind, "{}", first.1);
                assert!(!first.1.is_empty());
                assert_eq!(failure(&resolver), first);
                assert_eq!(package_stats().cache_hits, hits + 1, "one attempt serves both");
            }
            let _scope = ar::CacheScope::begin();
            failure(&resolver);
            assert_eq!(package_stats().cache_hits, hits + 1, "the next scope tries again");
            attempts += 1;
        }
        assert_eq!(attempts, 2);
    }

    /// Opening a stage on a bare package opens and parses the package once,
    /// for the default-layer lookup, the probes and the entry reads
    /// together, and a caller's scope extends that over the traversal.
    #[test]
    fn stage_opens_package_once() -> crate::Result<()> {
        let dir = tempfile::tempdir().unwrap();
        let root = b"#usda 1.0\ndef \"A\" (references = @./b.usda@</B>) {}\n";
        let leaf = b"#usda 1.0\ndef \"B\" { def \"Child\" {} }\n";
        let path = dir.path().join("pkg.usdz");
        fs::write(&path, package(&[("root.usda", root), ("b.usda", leaf)])).unwrap();
        let path = path.to_string_lossy().into_owned();

        let stage = usd::Stage::open(&path)?;
        assert_eq!(work(), (1, 1));
        drop(stage);

        let _scope = ar::CacheScope::begin();
        let stage = usd::Stage::open(&path)?;
        assert!(stage.prim("/A/Child")?.is_valid()?);
        assert_eq!(work(), (2, 2), "one more open for the second stage and its traversal");
        Ok(())
    }

    /// A package whose default layer references into a package nested in it
    /// costs one file open and one parse per level.
    #[test]
    fn stage_opens_nested_once() -> crate::Result<()> {
        let dir = tempfile::tempdir().unwrap();
        let inner = package(&[("b.usda", b"#usda 1.0\ndef \"B\" { def \"Child\" {} }\n")]);
        let root = b"#usda 1.0\ndef \"A\" (references = @./inner.usdz@</B>) {}\n";
        let path = dir.path().join("pkg.usdz");
        fs::write(&path, package(&[("root.usda", root), ("inner.usdz", &inner)])).unwrap();
        let path = path.to_string_lossy().into_owned();

        let _scope = ar::CacheScope::begin();
        let stage = usd::Stage::open(&path)?;
        assert!(stage.prim("/A/Child")?.is_valid()?);
        assert_eq!(work(), (1, 2));
        Ok(())
    }
}
