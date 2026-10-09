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

mod reader;
mod writer;

pub use reader::Archive;
pub(crate) use reader::is_layer_name;
pub use writer::ArchiveWriter;

use std::io::{self, Cursor};
use std::str;

use crate::{ar, sdf, tf, usda, usdc};

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

    /// The archive holds no USD layer to serve as the package's default.
    #[error("no USD layer found in USDZ archive")]
    NoDefaultLayer,

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
/// is fixed; reading back is name-agnostic ([`Archive::read_first_layer`] takes
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

    fn resolve_layer(&self, resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Option<ar::ResolvedPath> {
        // A package is anchored to its default (first) packaged layer. A package
        // nested in another (`pkg.usdz[inner.usdz]`) is anchored inside the
        // innermost bracket, `pkg.usdz[inner.usdz[first.usdc]]`.
        let package = resolved.to_string_lossy();
        // A package that cannot be opened, or that lists no default layer, falls
        // back to the bare package path so `read` surfaces the precise zip/parse
        // error, rather than being demoted to an unresolved (missing) asset.
        //
        // Only the central directory is read to list the default layer,
        // whatever the asset.
        let first = resolver
            .open_asset(resolved)
            .ok()
            .and_then(|asset| Archive::from_asset(asset).ok())
            .and_then(|archive| archive.first_layer_name());
        Some(match first {
            Some(first) => ar::ResolvedPath::new(ar::nest_packaged_path(&package, &first)),
            None => resolved.clone(),
        })
    }

    fn read_bytes(&self, bytes: ar::AssetBuffer, _source_name: &str) -> Result<sdf::LayerData, sdf::FormatError> {
        // A bare package has no named entry, so read its first (default) layer.
        //
        // Every failure here is a decode: the bytes are already in hand, so
        // even an I/O error comes from the cursor reading them and means the
        // package is truncated or corrupt.
        Archive::from_bytes(bytes)
            .and_then(|mut archive| archive.read_first_layer())
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
mod tests {
    use super::*;
    use crate::Result;
    use crate::ar::Resolver;
    use crate::ar::tests::TestResolver;
    use crate::sdf::FileFormat;
    use crate::usd::{PrimPredicate, Stage, TimeCode};
    use std::fs;
    use std::io::Write;
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
                .get_at::<sdf::Value>(TimeCode::new(0.0))?,
            Some(sdf::Value::Int(42)),
            "reference to a layer inside the package should compose"
        );
        Ok(())
    }

    /// Anchoring a bare package to its default layer reads the archive's
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
        assert_eq!(archive.first_layer_name().as_deref(), Some("root.usda"));
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
    /// inner package composes its default layer, the nested package path
    /// `outer.usdz[inner.usdz]` opens as a stage, and the raw archive reads the
    /// nested entry's default layer.
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

        let probe = |stage: &Stage, attr: &str| -> Result<Option<sdf::Value>> {
            stage.attribute(attr)?.get_at::<sdf::Value>(TimeCode::new(0.0))
        };
        let stage = Stage::open(path.to_str().unwrap())?;
        assert_eq!(probe(&stage, "/World.probe")?, Some(sdf::Value::Int(42)));

        let nested = ar::join_package_relative_path(path.to_str().unwrap(), "inner.usdz");
        let stage = Stage::open(&nested)?;
        assert_eq!(probe(&stage, "/Inner.probe")?, Some(sdf::Value::Int(42)));

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
}
