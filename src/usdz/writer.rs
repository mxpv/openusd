//! USDZ archive writer.
//!
//! Produces ZIP archives that conform to the [USDZ
//! specification](https://openusd.org/release/spec_usdz.html): every entry is
//! STORED (uncompressed) and its data is aligned to a 64-byte boundary via
//! padding in the local file header's "extra field".
//!
//! The writer is intentionally bytes-in, bytes-out: callers serialize their
//! layers (e.g. via [`crate::usdc::CrateWriter`] or [`crate::usda::TextWriter`])
//! and hand the resulting bytes to [`ArchiveWriter::add_layer`]. Dependency
//! resolution and asset discovery (the C++ `UsdUtilsCreateNewUsdzPackage`
//! equivalent) are out of scope for v1.

use std::io::{Seek, Write};
use std::path::Path;

use anyhow::{Context, Result};
use zip::write::SimpleFileOptions;
use zip::{CompressionMethod, ZipWriter};

/// Alignment (in bytes) for file data inside a USDZ archive.
const USDZ_ALIGNMENT: u16 = 64;

/// Writer for USDZ archives.
///
/// ```no_run
/// use openusd::usdz::ArchiveWriter;
///
/// let out = std::fs::File::create("scene.usdz").unwrap();
/// let mut archive = ArchiveWriter::new(out);
/// archive.add_layer("scene.usdc", &std::fs::read("scene.usdc").unwrap()).unwrap();
/// archive.finish().unwrap();
/// ```
pub struct ArchiveWriter<W: Write + Seek> {
    inner: ZipWriter<W>,
}

impl<W: Write + Seek> ArchiveWriter<W> {
    /// Create a new writer that emits its archive to `out`.
    pub fn new(out: W) -> Self {
        Self {
            inner: ZipWriter::new(out),
        }
    }

    /// Add an entry to the archive. `name` is the archive-relative path,
    /// `bytes` is the raw file content. The first call should typically be a
    /// `.usda`/`.usdc`/`.usd` layer — per the USDZ spec, the first file in
    /// the archive is the package's root layer.
    pub fn add_layer(&mut self, name: &str, bytes: &[u8]) -> Result<()> {
        let options = SimpleFileOptions::default()
            .compression_method(CompressionMethod::Stored)
            .with_alignment(USDZ_ALIGNMENT);

        self.inner
            .start_file(name, options)
            .with_context(|| format!("failed to start USDZ entry {name}"))?;
        self.inner
            .write_all(bytes)
            .with_context(|| format!("failed to write USDZ entry {name}"))?;
        Ok(())
    }

    /// Finalize the archive, writing the central directory. Returns the
    /// underlying writer.
    pub fn finish(self) -> Result<W> {
        let w = self.inner.finish().context("failed to finalize USDZ archive")?;
        Ok(w)
    }
}

impl ArchiveWriter<std::fs::File> {
    /// Create a USDZ archive at `path`.
    pub fn create(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let file = std::fs::File::create(path)
            .with_context(|| format!("failed to create USDZ archive: {}", path.display()))?;
        Ok(Self::new(file))
    }
}
