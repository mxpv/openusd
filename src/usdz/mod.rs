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

use std::io::Cursor;

use anyhow::{bail, Context, Result};

use crate::{ar, sdf, tf, usdc};

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

    fn read(&self, resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Result<sdf::LayerData> {
        // A package-relative path reaches this format only when its named entry is
        // itself a package (an ordinary inner layer dispatches to its own format),
        // so it is a nested package — unsupported. Reported before opening the
        // outer archive, since the whole-package read would only be discarded.
        let s = resolved.to_string();
        if let Some((_, inner)) = ar::split_package_relative_path_outer(&s) {
            bail!("Nested USDZ files are not yet supported: '{inner}'");
        }
        // A bare package has no named entry, so read its first (default) layer.
        Archive::from_asset(resolver, resolved)?
            .read_first_layer()
            .context("failed to read first layer from USDZ archive")
    }

    fn write(&self, data: &dyn sdf::AbstractData, sink: &mut dyn sdf::WriteSeek) -> Result<()> {
        let mut buf = Vec::new();
        usdc::CrateWriter::write(data, &mut Cursor::new(&mut buf))?;
        let mut archive = ArchiveWriter::new(sink);
        archive.add_layer(USDZ_LAYER_NAME, &buf)?;
        archive.finish()?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::usd::{Stage, TimeCode};

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
                .attribute("/World.probe")
                .get_at::<sdf::Value>(TimeCode::new(0.0))?,
            Some(sdf::Value::Int(42)),
            "reference to a layer inside the package should compose"
        );
        Ok(())
    }
}
