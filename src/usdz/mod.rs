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
        let bytes = resolver.open_asset(resolved)?.read_all()?;
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
