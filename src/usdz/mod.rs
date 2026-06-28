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

use anyhow::{Context, Result};

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

    fn read(&self, resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Result<sdf::LayerData> {
        // `resolved` may be the package file (`pkg.usdz`) or a package-relative
        // path (`pkg.usdz[inner]`) once a package root has been anchored. This
        // format always reads the archive's first layer, so open the package
        // itself, not an inner entry.
        let s = resolved.to_string();
        let package = if ar::is_package_relative_path(&s) {
            match ar::split_package_relative_path_outer(&s) {
                Some((pkg, _)) => ar::ResolvedPath::new(pkg),
                None => resolved.clone(),
            }
        } else {
            resolved.clone()
        };
        let bytes = resolver.open_asset(&package)?.read_all()?;
        let mut archive = Archive::from_reader(Cursor::new(bytes)).context("failed to open USDZ archive")?;
        archive
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
