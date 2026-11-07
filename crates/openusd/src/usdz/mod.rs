//! USDZ archive format reader and writer.
//!
//! USDZ is a ZIP archive containing USD layer files (and optional adjacent
//! resources such as textures). Per the specification, archived files are
//! stored uncompressed (STORED, method 0) and aligned to a 64-byte boundary
//! so the contained data can be consumed in place without extraction.
//!
//! The reader does consume it in place: [`Archive::entry`] serves a stored
//! entry as a view of the package's bytes when the asset shares them, and
//! refuses a compressed or encrypted entry as C++ does. A view is served
//! without checking the entry's CRC32, again as C++ serves a mapped package;
//! [`Archive::verify`] checks one on request, and the bounded read a package
//! without shared bytes falls back to checks it on the way. The `deflate`
//! feature of the `zip` crate stays for `usd_utils` package rebuilding,
//! which copies entries through the ZIP reader.

mod package;
mod reader;
mod writer;

pub use package::{Package, PackageError, PackageStats, open_package, package_contains, package_entry, package_stats};
pub use reader::Archive;
pub(crate) use reader::is_layer_name;
pub use writer::ArchiveWriter;

use std::io::{self, Cursor};
use std::str;

use crate::{ar, sdf, tf, usda, usdc};

/// How deep packages may nest, each as the first entry of the one around it,
/// before the root layer they lead to is refused with
/// [`ArchiveError::NestedTooDeep`]. Reading follows the chain one recursion
/// per package, so the limit bounds the stack a crafted package can take.
pub const MAX_NESTING: usize = 32;

/// Error reading or writing a `.usdz` package ([`Archive`] /
/// [`ArchiveWriter`]).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ArchiveError {
    /// Byte I/O against the package failed.
    #[error(transparent)]
    Io(#[from] io::Error),

    /// The ZIP layer failed while reading or writing the archive.
    #[error(transparent)]
    Zip(#[from] zip::result::ZipError),

    /// A named entry could not be read from or written to the archive.
    #[error("failed to access USDZ entry {name:?}")]
    Entry {
        /// The archive-relative entry name.
        name: String,
        /// The underlying failure.
        #[source]
        source: Box<ArchiveError>,
    },

    /// The archive has no root layer: it holds no entry, or its first entry
    /// names no layer format.
    #[error("the USDZ archive has no root layer: its first entry is missing or not a USD layer")]
    NoRootLayer,

    /// The root layer sits in packages nested, each as the first entry of the
    /// one around it, deeper than [`MAX_NESTING`].
    #[error("the USDZ archive's root layer is nested in packages deeper than {MAX_NESTING}")]
    NestedTooDeep,

    /// The writer refuses an unsafe or non-portable entry name.
    #[error("USDZ entry name {name:?} {reason}")]
    InvalidEntryName {
        /// The offending entry name.
        name: String,
        /// What the name violates.
        reason: &'static str,
    },

    /// A packaged crate layer failed to decode.
    #[error(transparent)]
    Read(#[from] usdc::ReadError),

    /// A packaged text layer failed to parse.
    #[error(transparent)]
    Parse(#[from] usda::ParseError),

    /// A packaged text layer is not valid UTF-8.
    #[error("file {name:?} is not valid UTF-8")]
    Utf8 {
        /// The archive-relative entry name.
        name: String,
        /// The underlying UTF-8 failure.
        #[source]
        source: str::Utf8Error,
    },

    /// An entry is compressed, which the USDZ specification forbids: only a
    /// stored entry can be served in place.
    #[error("USDZ entry {name:?} is {method} compressed; only stored entries are read")]
    Compressed {
        /// The archive-relative entry name.
        name: String,
        /// The compression the entry uses.
        method: zip::CompressionMethod,
    },

    /// An entry is encrypted, which the USDZ specification forbids.
    #[error("USDZ entry {name:?} is encrypted; only plain entries are read")]
    Encrypted {
        /// The archive-relative entry name.
        name: String,
    },
}

impl ArchiveError {
    /// Wraps a failure with the archive-relative entry it struck.
    pub(crate) fn entry(name: impl Into<String>, source: impl Into<ArchiveError>) -> Self {
        Self::Entry {
            name: name.into(),
            source: Box::new(source.into()),
        }
    }

    /// The [`io::ErrorKind`] at the heart of a write failure, seen through
    /// the entry and ZIP wrappers, or `None` when the failure is about the
    /// data rather than the destination. Meaningful only where the sink is
    /// real storage — the write seam; on the read side the package is already
    /// in hand, so a nested I/O failure there means truncated content.
    fn io_kind(&self) -> Option<io::ErrorKind> {
        match self {
            Self::Io(error) | Self::Zip(zip::result::ZipError::Io(error)) => Some(error.kind()),
            Self::Entry { source, .. } => source.io_kind(),
            _ => None,
        }
    }
}

/// Archive package format (`.usdz`) as an [`sdf::FileFormat`], wrapping
/// [`Archive`] and [`ArchiveWriter`]. Writing wraps a single crate-encoded
/// layer.
pub struct UsdzFileFormat;

/// Name of the single inner crate entry written into a `.usdz` package.
///
/// `write` only sees the sink, not the destination filename, so the entry name
/// is fixed; reading back is name-agnostic ([`Archive::read_root`] takes
/// the first entry).
const USDZ_LAYER_NAME: &str = "layer.usdc";

impl sdf::FileFormat for UsdzFileFormat {
    fn format_id(&self) -> tf::Token {
        tf::Token::new("usdz")
    }

    fn extensions(&self) -> &[&str] {
        &["usdz"]
    }

    fn caps(&self) -> sdf::FileFormatCaps {
        // Writable as a fresh single-layer archive (`export`), but not editable
        // in place (`save`): a loaded package's other assets — textures, sibling
        // layers — are not held by the layer, so overwriting it would drop them.
        sdf::FileFormatCaps::READ | sdf::FileFormatCaps::WRITE
    }

    fn is_package(&self) -> bool {
        true
    }

    fn package_meta(&self, resolver: &dyn ar::Resolver, package: &ar::ResolvedPath) -> Option<sdf::PackageMeta> {
        let entries = open_package(resolver, package)
            .ok()?
            .with(|archive| archive.entry_names().ok())?;
        Some(sdf::PackageMeta { entries })
    }

    fn forget_package(&self, resolver: &dyn ar::Resolver, package: &str) {
        package::forget_package(resolver, package);
    }

    /// The first entry stored, of any type, as C++ reads it from the
    /// archive's local headers (`_GetFirstFileInZipFile`).
    fn package_root<'m>(&self, meta: &'m sdf::PackageMeta) -> Option<&'m str> {
        meta.entries.first().map(String::as_str)
    }

    fn resolve_layer(&self, resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Option<ar::ResolvedPath> {
        // A package is anchored to its root layer, its first entry, followed
        // into a package nested there (`pkg.usdz[inner.usdz[root.usdc]]`, C++
        // `_ExpandPackagePath`). A package nested in another
        // (`pkg.usdz[inner.usdz]`) is anchored inside the innermost bracket.
        //
        // A package that cannot be opened, or that has no root layer, is
        // anchored at that package itself, so `read` reports its zip or parse
        // error there and the asset counts as found. A chain nested deeper
        // than `MAX_NESTING` is anchored at the package resolved, whose read
        // counts the whole chain.
        //
        // Each level's central directory names its root entry. The cache
        // scope holds every level's package for this lookup, and for the
        // reads that follow when the caller's scope encloses it.
        let _scope = ar::CacheScope::begin();
        let mut package = resolved.clone();
        for _ in 0..=MAX_NESTING {
            let root = open_package(resolver, &package)
                .ok()
                .and_then(|opened| opened.with(|archive| archive.root_entry().ok().flatten()));
            let Some(root) = root else {
                return Some(package);
            };
            let nested = ar::ResolvedPath::new(ar::nest_packaged_path(&package.to_string_lossy(), &root));
            if !sdf::LayerRegistry::is_package(ar::extension(&root)) {
                return Some(nested);
            }
            package = nested;
        }
        // Past the limit, the read of the whole chain refuses it.
        Some(resolved.clone())
    }

    fn read_bytes(&self, bytes: ar::AssetBuffer, _source_name: &str) -> Result<sdf::LayerData, sdf::FormatError> {
        // A bare package has no named entry, so read its first (default) layer.
        //
        // Every failure here is a decode: the bytes are already in hand, so
        // even an I/O error comes from the cursor reading them and means the
        // package is truncated or corrupt.
        Archive::from_bytes(bytes)
            .and_then(|mut archive| archive.read_root())
            .map_err(|error| sdf::FormatError::Decode(Box::new(error)))
    }

    /// Reads the root layer of the package at `resolved` from the
    /// package [`open_package`] gives, which a cache scope shares with the
    /// lookups around this read.
    fn read(
        &self,
        resolver: &dyn ar::Resolver,
        resolved: &ar::ResolvedPath,
    ) -> Result<sdf::LayerData, sdf::FormatError> {
        // Failing to open the package's file is an I/O failure. Any failure
        // past that, an I/O error from reading the directory among them,
        // means the bytes are not a whole package.
        let package = open_package(resolver, resolved).map_err(|error| match error.archive_error() {
            ArchiveError::Io(_) => sdf::FormatError::Io(error.into()),
            _ => sdf::FormatError::Decode(Box::new(error)),
        })?;
        package
            .with(|archive| archive.read_root())
            .map_err(|error| sdf::FormatError::Decode(Box::new(error)))
    }

    fn write(&self, data: &dyn sdf::AbstractData, sink: &mut dyn sdf::WriteSeek) -> Result<(), sdf::FormatError> {
        // Package-write failures map onto the format seam: a failure that is
        // byte I/O at heart — even wrapped in an entry or ZIP layer — stays
        // `Io`, keeping its kind and carrying the archive error as its
        // source; anything else is an encode failure.
        let encode = |error: ArchiveError| match error.io_kind() {
            Some(kind) => sdf::FormatError::Io(io::Error::new(kind, error)),
            None => sdf::FormatError::Encode {
                reason: tf::error_chain(&error).into(),
            },
        };
        let mut buf = Vec::new();
        usdc::CrateWriter::write(data, &mut Cursor::new(&mut buf))?;
        let mut archive = ArchiveWriter::new(sink);
        archive.add_layer(USDZ_LAYER_NAME, &buf).map_err(encode)?;
        archive.finish().map_err(encode)?;
        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::Result;
    use crate::ar::Resolver;
    use crate::ar::tests::TestResolver;
    use crate::sdf::FileFormat;
    use crate::usd::{PrimPredicate, Stage, TimeCode};
    use crate::vt;
    use std::cell::RefCell;
    use std::fs;
    use std::io::Write;
    use std::rc::Rc;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    /// A resolver whose assets exist but cannot be opened, standing in for a
    /// storage failure underneath a resolved package.
    fn failing_resolver() -> impl ar::Resolver {
        TestResolver(|| -> io::Result<Box<dyn ar::Asset>> { Err(io::Error::from(io::ErrorKind::PermissionDenied)) })
    }

    /// An in-memory asset counting the bytes read from it.
    struct CountingAsset {
        inner: Cursor<Vec<u8>>,
        read: Arc<AtomicUsize>,
    }

    impl io::Read for CountingAsset {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let count = self.inner.read(buf)?;
            self.read.fetch_add(count, Ordering::Relaxed);
            Ok(count)
        }
    }

    impl io::Seek for CountingAsset {
        fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
            self.inner.seek(pos)
        }
    }

    impl ar::Asset for CountingAsset {
        fn size(&self) -> io::Result<u64> {
            self.inner.size()
        }
    }

    /// A sink whose first write fails, standing in for a storage failure
    /// underneath the archive writer. Later writes are swallowed, so the
    /// `ZipWriter` drop can finalize quietly after the failure aborts the
    /// caller (the zip crate warns on stderr when that finalize fails too).
    struct FailingSink {
        tripped: bool,
    }

    impl io::Write for FailingSink {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            if self.tripped {
                return Ok(buf.len());
            }
            self.tripped = true;
            Err(io::Error::from(io::ErrorKind::BrokenPipe))
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    impl io::Seek for FailingSink {
        fn seek(&mut self, _pos: io::SeekFrom) -> io::Result<u64> {
            Ok(0)
        }
    }

    #[test]
    fn read_io_stays_io() {
        let Err(error) = UsdzFileFormat.read(&failing_resolver(), &ar::ResolvedPath::new("pkg.usdz")) else {
            panic!("asset open fails");
        };
        let sdf::FormatError::Io(error) = error else {
            panic!("a storage failure must stay I/O, got: {error}");
        };
        assert_eq!(error.kind(), io::ErrorKind::PermissionDenied);
    }

    #[test]
    fn write_io_stays_io() {
        let mut data = sdf::Data::new();
        data.create_spec(sdf::Path::abs_root(), sdf::SpecType::PseudoRoot);
        let mut sink = FailingSink { tripped: false };
        let error = UsdzFileFormat.write(&data, &mut sink).expect_err("sink writes fail");
        let sdf::FormatError::Io(error) = error else {
            panic!("a storage failure must stay I/O, got: {error}");
        };
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
    }

    /// A `.usdz` whose root layer references another layer *inside the same
    /// archive*. The reference (`@./inner.usda@`) must resolve in-package —
    /// not against the host filesystem — for the inner opinion to compose onto
    /// the root prim. Exercises the full package-relative resolution path
    /// (bare-package anchoring + `create_identifier` + inner-layer read).
    #[test]
    fn resolves_packaged_reference() -> Result<()> {
        let root =
            b"#usda 1.0\n(defaultPrim = \"World\")\ndef \"World\" (prepend references = @./inner.usda@</Inner>) {}\n";
        let inner = b"#usda 1.0\ndef \"Inner\" { custom int probe = 42 }\n";

        let dir = tempfile::tempdir()?;
        let path = dir.path().join("pkg.usdz");
        let mut writer = ArchiveWriter::create(&path)?;
        writer.add_layer("root.usda", root)?; // first entry is the root layer
        writer.add_layer("inner.usda", inner)?;
        writer.finish()?;

        let stage = Stage::open(path.to_str().unwrap())?;
        assert_eq!(
            stage
                .attribute("/World.probe")?
                .get_at::<vt::Value>(TimeCode::new(0.0))?,
            Some(vt::Value::Int(42)),
            "reference to a layer inside the package should compose"
        );
        Ok(())
    }

    /// Anchoring a bare package to its root layer reads the archive's
    /// central directory, not the packaged entries.
    #[test]
    fn default_layer_central_directory() -> Result<()> {
        let mut writer = ArchiveWriter::new(Cursor::new(Vec::new()));
        writer.add_layer("root.usda", b"#usda 1.0\n")?;
        writer.add_layer("texture.bin", &vec![0; 1 << 20])?;
        let package = writer.finish()?.into_inner();
        let size = package.len();
        let read = Arc::new(AtomicUsize::new(0));
        let resolver = TestResolver({
            let read = read.clone();
            move || -> io::Result<Box<dyn ar::Asset>> {
                Ok(Box::new(CountingAsset {
                    inner: Cursor::new(package.clone()),
                    read: read.clone(),
                }))
            }
        });

        let resolved = UsdzFileFormat.resolve_layer(&resolver, &ar::ResolvedPath::new("pkg.usdz"));
        assert_eq!(resolved, Some(ar::ResolvedPath::new("pkg.usdz[root.usda]")));
        let read = read.load(Ordering::Relaxed);
        assert!(read < size / 4, "read {read} of {size} bytes");
        Ok(())
    }

    /// A package read from an asset that shares its bytes decodes its default
    /// layer from the shared bytes.
    #[test]
    fn shared_buffer_read() -> Result<()> {
        let mut writer = ArchiveWriter::new(Cursor::new(Vec::new()));
        writer.add_layer("root.usda", b"#usda 1.0\ndef \"Root\" {}\n")?;
        let package: Arc<[u8]> = writer.finish()?.into_inner().into();
        let resolver = TestResolver({
            let package = ar::AssetBuffer::from(package.clone());
            move || -> io::Result<Box<dyn ar::Asset>> { Ok(Box::new(Cursor::new(package.clone()))) }
        });

        let data = UsdzFileFormat.read(&resolver, &ar::ResolvedPath::new("pkg.usdz"))?;
        assert_eq!(data.spec_type(&sdf::path("/Root").unwrap()), Some(sdf::SpecType::Prim));
        Ok(())
    }

    /// A package over bytes in hand serves an entry as a view into them.
    #[test]
    fn entry_is_view() -> Result<()> {
        let layer = b"#usda 1.0\ndef \"Root\" {}\n";
        let mut writer = ArchiveWriter::new(Cursor::new(Vec::new()));
        writer.add_layer("root.usda", layer)?;
        let package = writer.finish()?.into_inner();
        let bounds = package.as_ptr_range();

        let mut archive = Archive::from_bytes(package)?;
        let ar::AssetBuffer::Shared(view) = archive.entry("root.usda")? else {
            panic!("a package in hand serves views");
        };
        assert!(
            bounds.start <= view.as_ptr() && view.as_ptr_range().end <= bounds.end,
            "the view lies inside the package"
        );
        assert_eq!(&*view, layer);
        Ok(())
    }

    /// A package over an asset with no shared bytes probes its directory
    /// alone and reads an entry's range through the ZIP reader: the
    /// directory, one local header and the entry, not the package.
    #[test]
    fn entry_bounded_read() -> Result<()> {
        let mut writer = ArchiveWriter::new(Cursor::new(Vec::new()));
        writer.add_layer("root.usda", b"#usda 1.0\n")?;
        writer.add_layer("texture.bin", &vec![0; 1 << 20])?;
        let package = writer.finish()?.into_inner();
        let size = package.len();
        let read = Arc::new(AtomicUsize::new(0));
        let mut archive = Archive::from_asset(Box::new(CountingAsset {
            inner: Cursor::new(package),
            read: read.clone(),
        }))?;

        assert!(archive.contains("root.usda"));
        assert!(archive.contains("texture.bin"));
        assert!(!archive.contains("missing.usda"));
        assert_eq!(archive.root_entry().unwrap().as_deref(), Some("root.usda"));
        let probed = read.load(Ordering::Relaxed);
        assert!(probed < size / 4, "the probes read {probed} of {size} bytes");

        let ar::AssetBuffer::Owned(bytes) = archive.entry("root.usda")? else {
            panic!("an asset without shared bytes is read");
        };
        assert_eq!(bytes, b"#usda 1.0\n");
        let entry = read.load(Ordering::Relaxed) - probed;
        assert!(entry < 4096, "the entry read {entry} bytes");
        Ok(())
    }

    /// A compressed entry is refused, as C++ refuses it.
    #[test]
    fn compressed_entry_rejected() -> Result<()> {
        let mut zip = zip::ZipWriter::new(Cursor::new(Vec::new()));
        let deflated = zip::write::SimpleFileOptions::default().compression_method(zip::CompressionMethod::Deflated);
        zip.start_file("root.usda", deflated).map_err(ArchiveError::from)?;
        zip.write_all(b"#usda 1.0\n")?;
        let package = zip.finish().map_err(ArchiveError::from)?.into_inner();

        let error = Archive::from_bytes(package)?
            .entry("root.usda")
            .expect_err("a deflated entry is refused");
        assert!(matches!(error, ArchiveError::Compressed { .. }), "{error:?}");
        Ok(())
    }

    /// A view is served without a checksum check; `verify` reports the
    /// corruption, and so does the bounded read of a package without shared
    /// bytes.
    #[test]
    fn corrupt_entry() -> Result<()> {
        let layer = b"#usda 1.0\ndef \"Root\" {}\n";
        let mut writer = ArchiveWriter::new(Cursor::new(Vec::new()));
        writer.add_layer("root.usda", layer)?;
        let mut package = writer.finish()?.into_inner();
        let offset = package
            .windows(layer.len())
            .position(|window| window == layer)
            .expect("the stored entry");
        package[offset + 1] ^= 0xff;

        let mut archive = Archive::from_bytes(package.clone())?;
        assert_eq!(archive.entry("root.usda")?[1], layer[1] ^ 0xff);
        let error = archive.verify("root.usda").expect_err("the checksum no longer matches");
        assert!(format!("{error:?}").to_lowercase().contains("checksum"), "{error:?}");

        let mut archive = Archive::from_asset(Box::new(Cursor::new(package)))?;
        assert!(
            archive.entry("root.usda").is_err(),
            "a checked read reports the corruption"
        );
        Ok(())
    }

    /// A nested package's entry is a view into the outer package.
    #[test]
    fn nested_entry_is_view() -> Result<()> {
        let mut inner = ArchiveWriter::new(Cursor::new(Vec::new()));
        inner.add_layer("inner.usda", b"#usda 1.0\n")?;
        let inner = inner.finish()?.into_inner();
        let mut outer = ArchiveWriter::new(Cursor::new(Vec::new()));
        outer.add_layer("root.usda", b"#usda 1.0\n")?;
        outer.add_layer("inner.usdz", &inner)?;
        let outer = outer.finish()?.into_inner();
        let bounds = outer.as_ptr_range();

        let mut archive = Archive::from_bytes(outer)?;
        let mut nested = Archive::from_bytes(archive.entry("inner.usdz")?)?;
        let ar::AssetBuffer::Shared(view) = nested.entry("inner.usda")? else {
            panic!("a nested package serves views");
        };
        assert!(
            bounds.start <= view.as_ptr() && view.as_ptr_range().end <= bounds.end,
            "the view lies inside the outer package"
        );
        assert_eq!(&*view, b"#usda 1.0\n");
        Ok(())
    }

    /// A production package opens as a stage.
    #[test]
    fn stage_over_package() -> Result<()> {
        let path = concat!(
            env!("CARGO_WORKSPACE_DIR"),
            "vendor/usd-wg-assets/full_assets/CarbonFrameBike/CarbonFrameBike.usdz"
        );
        if fs::metadata(path).is_err() {
            eprintln!("Skipping stage_over_package: fixture not available at {path}");
            return Ok(());
        }
        let stage = Stage::open(path)?;
        let mut prims = 0;
        stage.traverse(PrimPredicate::DEFAULT, |_| prims += 1)?;
        assert!(prims > 100, "{prims} prims");
        Ok(())
    }

    /// A `.usdz` holding another `.usdz`, as C++ reads one: a reference to the
    /// inner package composes its root layer, the nested package path
    /// `outer.usdz[inner.usdz]` opens as a stage, and the raw archive reads the
    /// nested entry's root layer.
    #[test]
    fn resolves_nested_package() -> Result<()> {
        let mut inner = ArchiveWriter::new(Cursor::new(Vec::new()));
        inner.add_layer("inner.usda", b"#usda 1.0\ndef \"Inner\" { custom int probe = 42 }\n")?;
        let inner = inner.finish()?.into_inner();
        let root = b"#usda 1.0\ndef \"World\" (prepend references = @./inner.usdz@</Inner>) {}\n";

        let dir = tempfile::tempdir()?;
        let path = dir.path().join("outer.usdz");
        let mut writer = ArchiveWriter::create(&path)?;
        writer.add_layer("root.usda", root)?;
        writer.add_layer("inner.usdz", &inner)?;
        writer.finish()?;

        let probe = |stage: &Stage, attr: &str| -> Result<Option<vt::Value>> {
            stage.attribute(attr)?.get_at::<vt::Value>(TimeCode::new(0.0))
        };
        let stage = Stage::open(path.to_str().unwrap())?;
        assert_eq!(probe(&stage, "/World.probe")?, Some(vt::Value::Int(42)));

        let nested = ar::join_package_relative_path(path.to_str().unwrap(), "inner.usdz");
        let stage = Stage::open(&nested)?;
        assert_eq!(probe(&stage, "/Inner.probe")?, Some(vt::Value::Int(42)));

        let data = Archive::open(&path)?.read("inner.usdz")?;
        assert!(data.has_spec(&sdf::path("/Inner")?));

        // A missing entry at any bracket level is unresolved, not an entry
        // that fails to read.
        let resolver = ar::DefaultResolver::new();
        for missing in ["inner.usdz[missing.usda]", "missing.usdz[inner.usda]"] {
            let nested = ar::join_package_relative_path(path.to_str().unwrap(), missing);
            assert_eq!(resolver.resolve(&nested), None, "{nested}");
        }
        Ok(())
    }

    /// A package whose first entry is another package is anchored at that
    /// package's root layer (C++ `_ExpandPackagePath`), and opens as it.
    #[test]
    fn nested_root_expanded() -> Result<()> {
        let inner = package(&[("root.usda", b"#usda 1.0\ndef \"Inner\" { custom int probe = 42 }\n")]);
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("outer.usdz");
        fs::write(
            &path,
            package(&[("inner.usdz", &inner), ("other.usda", b"#usda 1.0\n")]),
        )?;
        let outer = ar::ResolvedPath::new(path.canonicalize()?);

        let resolved = UsdzFileFormat.resolve_layer(&ar::DefaultResolver::new(), &outer);
        let expected = ar::join_package_relative_path(&outer.to_string_lossy(), "inner.usdz[root.usda]");
        assert_eq!(resolved.map(|path| path.to_string_lossy().into_owned()), Some(expected));
        let stage = Stage::open(path.to_str().unwrap())?;
        assert_eq!(
            stage
                .attribute("/Inner.probe")?
                .get_at::<vt::Value>(TimeCode::new(0.0))?,
            Some(vt::Value::Int(42))
        );
        Ok(())
    }

    /// The first entry is the root layer, whatever comes after it: a package
    /// whose first entry no layer format reads has none, and does not open.
    #[test]
    fn first_entry_not_layer() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("pkg.usdz");
        fs::write(&path, package(&[("tex.png", b"png"), ("root.usda", b"#usda 1.0\n")]))?;
        assert_eq!(Archive::open(&path)?.root_entry()?, None);
        let Err(error) = Archive::open(&path)?.read_root() else {
            panic!("a package with no root layer reads nothing");
        };
        assert!(matches!(innermost(&error), ArchiveError::NoRootLayer), "{error:?}");
        assert!(Stage::open(path.to_str().unwrap()).is_err());
        Ok(())
    }

    /// An outer package whose root is the nested `inner.usdz`, each level
    /// holding a second entry, and the outer package's canonical path.
    fn nested_with_siblings() -> Result<(tempfile::TempDir, String)> {
        let inner = package(&[("root.usda", b"#usda 1.0\n"), ("tex.png", b"png")]);
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("outer.usdz");
        fs::write(
            &path,
            package(&[("inner.usdz", &inner), ("other.usda", b"#usda 1.0\n")]),
        )?;
        let outer = path.canonicalize()?.to_string_lossy().into_owned();
        Ok((dir, outer))
    }

    /// Reading a packaged layer holds what each package around it holds, a
    /// nested package keyed by its own packaged path, from the one directory
    /// parse per package the read does.
    #[test]
    fn package_index_filled() -> Result<()> {
        let (_dir, outer) = nested_with_siblings()?;
        let registry = sdf::LayerRegistry::new(Box::new(ar::DefaultResolver::new()));
        let parses = package_stats().directory_parses;
        let _root = registry.find_or_open(&outer)?.expect("the package opens");
        assert_eq!(package_stats().directory_parses - parses, 2);

        let meta = |entries: &[&str]| sdf::PackageMeta {
            entries: entries.iter().map(|&entry| entry.to_owned()).collect(),
        };
        assert_eq!(
            registry.package_meta(&outer)?,
            Some(meta(&["inner.usdz", "other.usda"]))
        );
        let inner = ar::join_package_relative_path(&outer, "inner.usdz");
        assert_eq!(registry.package_meta(&inner)?, Some(meta(&["root.usda", "tex.png"])));
        Ok(())
    }

    /// A package's meta lives while a live layer holds it: one the layer lies
    /// in, or one its package's root descends through.
    #[test]
    fn package_index_dropped() -> Result<()> {
        let (_dir, outer) = nested_with_siblings()?;
        let inner = ar::join_package_relative_path(&outer, "inner.usdz");
        let registry = sdf::LayerRegistry::new(Box::new(ar::DefaultResolver::new()));
        let root = registry.find_or_open(&outer)?.expect("the package opens");
        let other = registry
            .find_or_open(&ar::join_package_relative_path(&outer, "other.usda"))?
            .expect("the sibling opens");

        drop(root);
        registry.sweep();
        assert!(
            registry.package_meta(&outer)?.is_some(),
            "the sibling holds the outer package"
        );
        assert!(
            registry.package_meta(&inner)?.is_some(),
            "the sibling holds the package the outer root descends through"
        );

        drop(other);
        registry.sweep();
        assert_eq!(registry.package_meta(&outer)?, None);
        assert_eq!(registry.package_meta(&inner)?, None);
        Ok(())
    }

    /// The entries a package held when the layer this sink is on last
    /// committed.
    struct SeenEntries {
        registry: Rc<sdf::LayerRegistry>,
        package: String,
        entries: Rc<RefCell<Vec<String>>>,
    }

    impl sdf::LayerSink for SeenEntries {
        fn after_commit(&self, _change: &sdf::CommittedLayerChange<'_>) {
            let meta = self.registry.package_meta(&self.package).expect("the store is free");
            self.entries.replace(meta.map(|meta| meta.entries).unwrap_or_default());
        }
    }

    /// A reload inside a cache scope that already opened the package reads
    /// the package as it is now.
    #[test]
    fn reload_under_outer_scope() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("pkg.usdz");
        fs::write(&path, package(&[("root.usda", b"#usda 1.0\ndef \"Old\" {}\n")]))?;
        let registry = sdf::LayerRegistry::new(Box::new(ar::DefaultResolver::new()));
        let _outer = ar::CacheScope::begin();
        let root = registry
            .find_or_open(path.to_str().unwrap())?
            .expect("the package opens");

        fs::write(
            &path,
            package(&[
                ("root.usda", b"#usda 1.0\ndef \"New\" {}\n"),
                ("x.usda", b"#usda 1.0\n"),
            ]),
        )?;
        assert!(root.reload(true)?);
        assert!(root.read(|layer| layer.data().has_spec(&sdf::path("/New").unwrap()))?);
        let meta = registry.package_meta(&path.canonicalize()?.to_string_lossy())?;
        assert_eq!(
            meta.expect("the layer holds its package").entries,
            ["root.usda", "x.usda"]
        );
        let entry = ar::join_package_relative_path(path.to_str().unwrap(), "x.usda");
        assert!(
            registry.find_or_open(&entry)?.is_some(),
            "the outer scope reads the new package"
        );
        Ok(())
    }

    /// A reload that reads a packaged layer again lists its package anew,
    /// before its observers run.
    #[test]
    fn package_index_reloaded() -> Result<()> {
        let (dir, outer) = nested_with_siblings()?;
        let registry = Rc::new(sdf::LayerRegistry::new(Box::new(ar::DefaultResolver::new())));
        let other = registry
            .find_or_open(&ar::join_package_relative_path(&outer, "other.usda"))?
            .expect("the sibling opens");
        let seen = Rc::new(RefCell::new(Vec::new()));
        other.add_sink(SeenEntries {
            registry: Rc::clone(&registry),
            package: outer.clone(),
            entries: Rc::clone(&seen),
        })?;
        fs::write(
            dir.path().join("outer.usdz"),
            package(&[
                ("other.usda", b"#usda 1.0\ndef \"New\" {}\n"),
                ("added.usda", b"#usda 1.0\n"),
            ]),
        )?;
        assert!(other.reload(true)?);
        let meta = registry.package_meta(&outer)?.expect("the sibling holds its package");
        assert_eq!(meta.entries, ["other.usda", "added.usda"]);
        assert_eq!(*seen.borrow(), ["other.usda", "added.usda"]);
        Ok(())
    }

    /// A package reopened after its last layer died is listed anew, whatever
    /// a dead, unswept layer of it held.
    #[test]
    fn package_index_reopened() -> Result<()> {
        let (dir, outer) = nested_with_siblings()?;
        let plain = dir.path().join("plain.usda");
        fs::write(&plain, "#usda 1.0\n")?;
        let registry = sdf::LayerRegistry::new(Box::new(ar::DefaultResolver::new()));
        let _keep = registry
            .find_or_open(plain.to_str().unwrap())?
            .expect("the layer opens");
        let other = ar::join_package_relative_path(&outer, "other.usda");
        drop(registry.find_or_open(&other)?.expect("the sibling opens"));
        assert_eq!(registry.package_meta(&outer)?, None, "a dead layer holds no package");
        fs::write(
            dir.path().join("outer.usdz"),
            package(&[("other.usda", b"#usda 1.0\n"), ("added.usda", b"#usda 1.0\n")]),
        )?;
        let _other = registry.find_or_open(&other)?.expect("the sibling opens again");
        let meta = registry.package_meta(&outer)?.expect("the sibling holds its package");
        assert_eq!(meta.entries, ["other.usda", "added.usda"]);
        Ok(())
    }

    /// A search path a package's sibling layer authors falls back beside the
    /// package's root layer, inside the nested package the root descends
    /// into, from the listings the stage's layers hold.
    #[test]
    fn search_path_at_nested_root() -> Result<()> {
        let inner = package(&[
            ("root.usda", b"#usda 1.0\n"),
            ("x.usda", b"#usda 1.0\ndef \"X\" { custom int probe = 7 }\n"),
        ]);
        let other: &[u8] = b"#usda 1.0\ndef \"P\" (\n    references = @x.usda@</X>\n) {}\n";
        let dir = tempfile::tempdir()?;
        fs::write(
            dir.path().join("outer.usdz"),
            package(&[("inner.usdz", &inner), ("other.usda", other)]),
        )?;
        let root = dir.path().join("root.usda");
        fs::write(
            &root,
            "#usda 1.0\ndef \"P\" (\n    references = @outer.usdz[other.usda]@</P>\n) {}\n",
        )?;

        let stage = Stage::open(root.to_str().unwrap())?;
        let value = stage.attribute("/P.probe")?.get_at::<vt::Value>(TimeCode::new(0.0))?;
        assert_eq!(value, Some(vt::Value::Int(7)));
        Ok(())
    }

    /// A reload that changes the package a layer's package root descends
    /// into holds the new one.
    #[test]
    fn root_chain_relisted() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("outer.usdz");
        fs::write(
            &path,
            package(&[("other.usda", b"#usda 1.0\n"), ("x.usda", b"#usda 1.0\n")]),
        )?;
        let outer = path.canonicalize()?.to_string_lossy().into_owned();
        let inner = ar::join_package_relative_path(&outer, "inner.usdz");
        let registry = sdf::LayerRegistry::new(Box::new(ar::DefaultResolver::new()));
        let other = registry
            .find_or_open(&ar::join_package_relative_path(&outer, "other.usda"))?
            .expect("the sibling opens");
        assert_eq!(registry.package_meta(&inner)?, None);

        let nested = package(&[("root.usda", b"#usda 1.0\n")]);
        fs::write(
            &path,
            package(&[("inner.usdz", &nested), ("other.usda", b"#usda 1.0\ndef \"New\" {}\n")]),
        )?;
        assert!(other.reload(true)?);
        let meta = registry.package_meta(&inner)?.expect("the new root chain is held");
        assert_eq!(meta.entries, ["root.usda"]);
        Ok(())
    }

    /// A reload of one layer in a package has the package's other live layers
    /// hold the root chain its new listing names too.
    #[test]
    fn sibling_chain_relisted() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("outer.usdz");
        fs::write(
            &path,
            package(&[("a.usda", b"#usda 1.0\n"), ("b.usda", b"#usda 1.0\n")]),
        )?;
        let outer = path.canonicalize()?.to_string_lossy().into_owned();
        let inner = ar::join_package_relative_path(&outer, "inner.usdz");
        let registry = sdf::LayerRegistry::new(Box::new(ar::DefaultResolver::new()));
        let open = |entry: &str| -> Result<sdf::LayerHandle> {
            Ok(registry
                .find_or_open(&ar::join_package_relative_path(&outer, entry))?
                .expect("the entry opens"))
        };
        let (a, b) = (open("a.usda")?, open("b.usda")?);

        let nested = package(&[("root.usda", b"#usda 1.0\n")]);
        fs::write(
            &path,
            package(&[
                ("inner.usdz", &nested),
                ("a.usda", b"#usda 1.0\n"),
                ("b.usda", b"#usda 1.0\ndef \"New\" {}\n"),
            ]),
        )?;
        assert!(b.reload(true)?);
        drop(b);
        registry.sweep();
        assert!(
            registry.package_meta(&inner)?.is_some(),
            "the layer not reloaded holds the new root chain"
        );
        drop(a);
        Ok(())
    }

    /// A reload that finds a nested package of the root chain unreadable
    /// holds it with no listing, and lets go of the packages below it.
    #[test]
    fn corrupt_chain_relisted() -> Result<()> {
        let deep = package(&[("root.usda", b"#usda 1.0\n")]);
        let inner = package(&[("deep.usdz", &deep)]);
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("outer.usdz");
        fs::write(&path, package(&[("inner.usdz", &inner), ("a.usda", b"#usda 1.0\n")]))?;
        let outer = path.canonicalize()?.to_string_lossy().into_owned();
        let inner = ar::join_package_relative_path(&outer, "inner.usdz");
        let deep = ar::nest_packaged_path(&inner, "deep.usdz");
        let registry = sdf::LayerRegistry::new(Box::new(ar::DefaultResolver::new()));
        let a = registry
            .find_or_open(&ar::join_package_relative_path(&outer, "a.usda"))?
            .expect("the layer opens");
        assert!(registry.package_meta(&deep)?.is_some());

        fs::write(
            &path,
            package(&[
                ("inner.usdz", b"not a package"),
                ("a.usda", b"#usda 1.0\ndef \"New\" {}\n"),
            ]),
        )?;
        assert!(a.reload(true)?);
        assert_eq!(registry.package_meta(&inner)?, None);
        assert_eq!(registry.package_meta(&deep)?, None);
        Ok(())
    }

    /// A layer opened beside a dead, unswept layer of its package holds the
    /// package's meta once the dead layer is freed.
    #[test]
    fn package_index_survives_sweep() -> Result<()> {
        let (dir, outer) = nested_with_siblings()?;
        let plain = dir.path().join("plain.usda");
        fs::write(&plain, "#usda 1.0\n")?;
        let registry = sdf::LayerRegistry::new(Box::new(ar::DefaultResolver::new()));
        let _keep = registry
            .find_or_open(plain.to_str().unwrap())?
            .expect("the layer opens");
        drop(registry.find_or_open(&outer)?.expect("the package opens"));
        let _other = registry
            .find_or_open(&ar::join_package_relative_path(&outer, "other.usda"))?
            .expect("the sibling opens");
        registry.sweep();
        assert!(registry.package_meta(&outer)?.is_some());
        Ok(())
    }

    /// The failure `error` wraps, through every entry that reached it.
    fn innermost(mut error: &ArchiveError) -> &ArchiveError {
        while let ArchiveError::Entry { source, .. } = error {
            error = source;
        }
        error
    }

    /// Packages nested as root entries read up to `MAX_NESTING` deep, and a
    /// deeper chain is refused with `NestedTooDeep`.
    #[test]
    fn nested_too_deep() -> Result<()> {
        let chain = |depth: usize| {
            let mut bytes = package(&[("root.usda", b"#usda 1.0\ndef \"Deep\" {}\n")]);
            for _ in 0..depth {
                bytes = package(&[("nested.usdz", &bytes)]);
            }
            bytes
        };
        let data = Archive::from_bytes(chain(MAX_NESTING))?.read_root()?;
        assert!(data.has_spec(&sdf::path("/Deep")?));
        let Err(error) = Archive::from_bytes(chain(MAX_NESTING + 1))?.read_root() else {
            panic!("a chain past the limit is refused");
        };
        assert!(matches!(innermost(&error), ArchiveError::NestedTooDeep), "{error:?}");

        // A stage opens the chain within the limit, and refuses the one past it.
        let dir = tempfile::tempdir()?;
        let within = dir.path().join("within.usdz");
        fs::write(&within, chain(MAX_NESTING))?;
        assert!(Stage::open(within.to_str().unwrap())?.prim("/Deep")?.is_valid()?);
        let past = dir.path().join("past.usdz");
        fs::write(&past, chain(MAX_NESTING + 1))?;
        assert!(Stage::open(past.to_str().unwrap()).is_err());
        Ok(())
    }

    /// The root entry is the one stored first, whatever order the central
    /// directory lists entries in (C++ walks local file headers).
    #[test]
    fn root_is_stored_first() -> Result<()> {
        let mut bytes = package(&[("root.usda", b"#usda 1.0\n"), ("tex.png", b"png")]);
        swap_central_records(&mut bytes);
        let zip = zip::ZipArchive::new(Cursor::new(bytes.clone())).expect("a zip");
        let listed = zip.name_for_index(0).expect("an entry").expect("a name");
        assert_eq!(listed, "tex.png", "the directory lists tex.png first");
        let archive = Archive::from_bytes(bytes)?;
        assert_eq!(archive.root_entry()?.as_deref(), Some("root.usda"));
        Ok(())
    }

    /// Swaps the first two records of the central directory of the package
    /// `bytes`, leaving the entries where they are stored.
    pub(crate) fn swap_central_records(bytes: &mut [u8]) {
        let u16_at = |bytes: &[u8], at: usize| usize::from(u16::from_le_bytes([bytes[at], bytes[at + 1]]));
        let end = bytes.len() - 22;
        assert_eq!(&bytes[end..end + 4], b"PK\x05\x06", "an end record with no comment");
        let start = u32::from_le_bytes(bytes[end + 16..end + 20].try_into().unwrap()) as usize;
        let record = |at: usize| 46 + u16_at(bytes, at + 28) + u16_at(bytes, at + 30) + u16_at(bytes, at + 32);
        let first = record(start);
        let second = record(start + first);
        bytes[start..start + first + second].rotate_left(first);
    }

    /// The bytes of a package holding `entries`, in order.
    pub(crate) fn package(entries: &[(&str, &[u8])]) -> Vec<u8> {
        let mut writer = ArchiveWriter::new(Cursor::new(Vec::new()));
        for (name, bytes) in entries {
            writer.add_layer(name, bytes).expect("a valid entry");
        }
        writer.finish().expect("a finished package").into_inner()
    }
}
