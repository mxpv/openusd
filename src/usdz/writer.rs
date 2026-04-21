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

use anyhow::{bail, Context, Result};
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
    ///
    /// `name` must be an archive-relative forward-slash path: non-empty, not
    /// absolute, and containing no `..` segments or backslashes. Archives
    /// with path-traversing entries are rejected.
    pub fn add_layer(&mut self, name: &str, bytes: &[u8]) -> Result<()> {
        validate_entry_name(name)?;

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

/// Validate that `name` is safe to use as a ZIP entry path: a non-empty
/// relative path whose segments are all concrete filenames. USDZ archives
/// consumed by other tools interpret entry names as filesystem paths, so
/// absolute, traversing, directory-like, or double-separator forms can
/// escape the extraction root or produce ambiguous results.
fn validate_entry_name(name: &str) -> Result<()> {
    if name.is_empty() {
        bail!("USDZ entry name cannot be empty");
    }
    if name.contains('\\') {
        bail!("USDZ entry name {name:?} must not contain backslashes");
    }
    if name.starts_with('/') {
        bail!("USDZ entry name {name:?} must be relative, not absolute");
    }
    if name.ends_with('/') {
        bail!("USDZ entry name {name:?} must name a file, not a directory");
    }
    for seg in name.split('/') {
        match seg {
            "" => bail!("USDZ entry name {name:?} has an empty path segment"),
            "." | ".." => {
                bail!("USDZ entry name {name:?} must not contain `{seg}` segments")
            }
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn writer() -> ArchiveWriter<Cursor<Vec<u8>>> {
        ArchiveWriter::new(Cursor::new(Vec::new()))
    }

    #[test]
    fn rejects_unsafe_entry_names() {
        for name in [
            "",
            "/absolute",
            "..",
            "a/../b",
            "win\\style",
            "a//b",
            "a/",
            "./a",
            "a/.",
        ] {
            assert!(
                writer().add_layer(name, b"").is_err(),
                "expected rejection for {name:?}"
            );
        }
    }

    #[test]
    fn accepts_safe_relative_entry_names() {
        for name in ["scene.usdc", "Textures/Material/base.jpg", "nested/a.b.c"] {
            writer().add_layer(name, b"dummy").expect(name);
        }
    }
}
