//! USDZ archive reader.

use std::{
    fs::File,
    io::{self, Cursor, Read, Seek},
    path::Path,
};

use zip::ZipArchive;

use super::ArchiveError;
use crate::{ar, sdf, usda, usdc};

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
    pub fn open(path: impl AsRef<Path>) -> Result<Self, ArchiveError> {
        let path = path.as_ref();
        let file = File::open(path)
            .map_err(|error| io::Error::new(error.kind(), format!("unable to open {}: {error}", path.display())))?;
        let archive = ZipArchive::new(file)?;
        Ok(Self { archive })
    }
}

impl Archive<Cursor<Vec<u8>>> {
    /// Reads the entire package at `resolved` through the resolver's asset seam
    /// and opens it as an archive, so a host-provided byte source is honored.
    pub fn from_asset(resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Result<Self, ArchiveError> {
        let bytes = resolver.open_asset(resolved)?.read_all()?;
        Archive::from_reader(Cursor::new(bytes))
    }
}

impl<R: Read + Seek> Archive<R> {
    /// Creates an archive from any `Read + Seek` source.
    ///
    /// Use this when the archive bytes come from a custom asset resolver
    /// rather than directly from the filesystem.
    pub fn from_reader(reader: R) -> Result<Self, ArchiveError> {
        let archive = ZipArchive::new(reader)?;
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
    pub fn read_first_layer(&mut self) -> Result<Box<dyn sdf::AbstractData>, ArchiveError> {
        let name = self.first_layer_name().ok_or(ArchiveError::NoDefaultLayer)?;
        self.read(&name)
    }

    /// Read either a USDA or USDC file from the archive.
    ///
    /// NOTE: Nested USDZ files are not yet supported.
    pub fn read(&mut self, file_path: &str) -> Result<Box<dyn sdf::AbstractData>, ArchiveError> {
        let mut file = self
            .archive
            .by_name(file_path)
            .map_err(|e| ArchiveError::entry(file_path, e))?;

        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer)
            .map_err(|e| ArchiveError::entry(file_path, e))?;

        if file_path.ends_with(".usdz") {
            // TODO: Implement nested USDZ files support.
            return Err(ArchiveError::NestedPackage {
                path: file_path.to_owned(),
            });
        }

        // The named extension decides crate vs text; a format-agnostic `.usd`
        // (or any other name) falls back to the crate magic, mirroring USD's
        // content-based format detection. Per the USDZ spec the root layer may be
        // `.usd`, and Pixar's reference assets (e.g. Kitchen_set.usdz) ship it
        // that way.
        let is_crate = if file_path.ends_with(".usdc") {
            true
        } else if file_path.ends_with(".usda") {
            false
        } else {
            buffer.starts_with(usdc::MAGIC)
        };

        if is_crate {
            let data =
                usdc::CrateData::open(Cursor::new(buffer), true).map_err(|e| ArchiveError::entry(file_path, e))?;
            Ok(Box::new(data))
        } else {
            let content = String::from_utf8(buffer).map_err(|e| ArchiveError::Utf8 {
                name: file_path.to_owned(),
                source: e.utf8_error(),
            })?;
            let data = usda::parse(&content).map_err(|error| error.with_source_name(file_path))?;
            Ok(Box::new(data))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Result;

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
