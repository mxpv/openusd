//! USDZ archive reader.

use std::{
    fs::File,
    io::{Cursor, Read, Seek},
    path::Path,
};

use anyhow::{bail, Context, Result};
use zip::ZipArchive;

use crate::{sdf, usda, usdc};

/// USDZ archive reader.
///
/// Provides access to USD files within a USDZ archive. The type parameter `R`
/// is the underlying reader; it defaults to [`File`] for the common case of
/// opening an archive from disk via [`Archive::open`]. Use
/// [`Archive::from_reader`] to construct an archive from any `Read + Seek`
/// source, such as an in-memory buffer supplied by a custom asset resolver.
pub struct Archive<R: Read + Seek = File> {
    archive: ZipArchive<R>,
}

impl Archive<File> {
    /// Opens a USDZ archive from a file path.
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let file = File::open(path).with_context(|| format!("Failed to open USDZ archive: {}", path.display()))?;
        let archive =
            ZipArchive::new(file).with_context(|| format!("Failed to read ZIP archive: {}", path.display()))?;
        Ok(Self { archive })
    }
}

impl<R: Read + Seek> Archive<R> {
    /// Creates an archive from any `Read + Seek` source.
    ///
    /// Use this when the archive bytes come from a custom asset resolver
    /// rather than directly from the filesystem.
    pub fn from_reader(reader: R) -> Result<Self> {
        let archive = ZipArchive::new(reader).context("Failed to read ZIP archive")?;
        Ok(Self { archive })
    }

    /// Returns the file name of the first layer in the archive.
    ///
    /// Per the [USDZ specification](https://openusd.org/release/spec_usdz.html),
    /// the first file in a USDZ package must be a native USD file (`.usda`, `.usdc`,
    /// or `.usd`) and serves as the root layer of the composed stage.
    pub fn first_layer_name(&self) -> Option<String> {
        self.archive
            .file_names()
            .find(|name| name.ends_with(".usdc") || name.ends_with(".usda") || name.ends_with(".usd"))
            .map(String::from)
    }

    /// Opens the first (root) layer from the archive.
    pub fn read_first_layer(&mut self) -> Result<Box<dyn sdf::AbstractData>> {
        let name = self.first_layer_name().context("no USD layer found in USDZ archive")?;
        self.read(&name)
    }

    /// Read either a USDA or USDC file from the archive.
    ///
    /// NOTE: Nested USDZ files are not yet supported.
    pub fn read(&mut self, file_path: &str) -> Result<Box<dyn sdf::AbstractData>> {
        let mut file = self
            .archive
            .by_name(file_path)
            .with_context(|| format!("File '{}' not found in archive", file_path))?;

        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer)
            .with_context(|| format!("Failed to read file '{}' from archive", file_path))?;

        if file_path.ends_with(".usdc") {
            let cursor = Cursor::new(buffer);
            let data = usdc::CrateData::open(cursor, true)
                .with_context(|| format!("Failed to parse USDC data from '{}'", file_path))?;
            Ok(Box::new(data))
        } else if file_path.ends_with(".usda") {
            let content =
                String::from_utf8(buffer).with_context(|| format!("File '{}' is not valid UTF-8", file_path))?;

            let mut parser = usda::parser::Parser::new(&content);
            let data = parser
                .parse()
                .with_context(|| format!("Failed to parse USDA data from '{}'", file_path))?;

            Ok(Box::new(usda::TextReader::from_data(data)))
        } else if file_path.ends_with(".usdz") {
            // TODO: Implement nested USDZ files support.
            bail!("Nested USDZ files are not yet supported: '{}'", file_path)
        } else {
            bail!(
                "Unsupported file format for '{}'. Expected .usda or .usdc extension",
                file_path
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_open_usdz() -> Result<()> {
        let mut archive = Archive::open("fixtures/test.usdz")?;
        let data = archive.read("file_1.usdc")?;
        let root = sdf::Path::abs_root();

        assert!(data.has_spec(&root));
        assert_eq!(data.spec_type(&root), Some(sdf::SpecType::PseudoRoot));

        Ok(())
    }
}
