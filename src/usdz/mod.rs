//! USDZ archive format reader and writer.
//!
//! USDZ is a ZIP archive containing USD layer files (and optional adjacent
//! resources such as textures). Per the specification, archived files are
//! stored uncompressed (STORED, method 0) and aligned to a 64-byte boundary
//! so the contained data can be consumed in place without extraction.

mod reader;
mod writer;

pub use reader::Archive;
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

    /// The entry is itself a package; nested packages are not supported.
    #[error("Nested USDZ files are not yet supported: '{path}'")]
    NestedPackage {
        /// The nested package's entry path.
        path: String,
    },

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
    /// in memory, so a nested I/O failure there means truncated content.
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

    fn resolve_layer(&self, resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Option<ar::ResolvedPath> {
        // An already package-relative path (`pkg.usdz[inner]`, including a nested
        // `pkg.usdz[inner.usdz]`) already names its entry; only a bare package is
        // anchored to its default — first — packaged layer.
        let package = resolved.to_string_lossy();
        if ar::is_package_relative_path(&package) {
            return Some(resolved.clone());
        }
        // A package that cannot be opened, or that lists no default layer, falls
        // back to the bare package path so `read` surfaces the precise zip/parse
        // error, rather than being demoted to an unresolved (missing) asset.
        //
        // TODO(perf): `from_asset` slurps the whole package into memory only to
        // list its central directory (`first_layer_name`), and `read` then reads
        // it again to extract the anchored layer. The resolver's asset is `Seek`,
        // so a `ZipArchive` could read just the central directory here (as
        // `ar::open_package_archive` does off a `File`); carry that opened archive
        // through so a bare-package open touches the file once.
        match Archive::from_asset(resolver, resolved)
            .ok()
            .and_then(|a| a.first_layer_name())
        {
            Some(first) => Some(ar::ResolvedPath::new(ar::join_package_relative_path(&package, &first))),
            None => Some(resolved.clone()),
        }
    }

    fn read(
        &self,
        resolver: &dyn ar::Resolver,
        resolved: &ar::ResolvedPath,
    ) -> Result<sdf::LayerData, sdf::FormatError> {
        // A package-relative path reaches this format only when its named entry is
        // itself a package (an ordinary inner layer dispatches to its own format),
        // so it is a nested package — unsupported. Reported before opening the
        // outer archive, since the whole-package read would only be discarded.
        let s = resolved.to_string();
        if let Some((_, inner)) = ar::split_package_relative_path_outer(&s) {
            return Err(sdf::FormatError::Decode(Box::new(ArchiveError::NestedPackage {
                path: inner,
            })));
        }
        // A bare package has no named entry, so read its first (default) layer.
        //
        // Only the direct `Io` variant is a storage failure here: the package
        // is slurped into memory before any ZIP or entry decoding, so an I/O
        // error nested deeper comes from the in-memory cursor and means
        // truncated or corrupt content — a `Decode`.
        Archive::from_asset(resolver, resolved)
            .and_then(|mut archive| archive.read_first_layer())
            .map_err(|error| match error {
                ArchiveError::Io(error) => sdf::FormatError::Io(error),
                error => sdf::FormatError::Decode(Box::new(error)),
            })
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
    use crate::sdf::FileFormat;
    use crate::usd::{Stage, TimeCode};

    /// A resolver whose assets exist but cannot be opened, standing in for a
    /// storage failure underneath a resolved package.
    struct FailingResolver;

    impl ar::Resolver for FailingResolver {
        fn create_identifier(&self, asset_path: &str, _anchor: Option<&ar::ResolvedPath>) -> String {
            asset_path.to_string()
        }

        fn resolve(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
            Some(ar::ResolvedPath::new(asset_path))
        }

        fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
            Some(ar::ResolvedPath::new(asset_path))
        }

        fn open_asset(&self, _resolved_path: &ar::ResolvedPath) -> io::Result<Box<dyn ar::Asset>> {
            Err(io::Error::from(io::ErrorKind::PermissionDenied))
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
        let Err(error) = UsdzFileFormat.read(&FailingResolver, &ar::ResolvedPath::new("pkg.usdz")) else {
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
}
