//! USDZ archive reader.

use std::fs::File;
use std::io::{self, Cursor, Read};
use std::path::Path;
use std::str;

use zip::{CompressionMethod, ZipArchive};

use super::ArchiveError;
use crate::{ar, sdf, usda, usdc};

/// A USDZ package: the entries its central directory lists, over the asset
/// the package came from.
///
/// The directory is read once, at construction; an entry's local header is
/// read only when that entry is requested. The entry's bytes come as a view
/// of the package when the asset shares its bytes ([`ar::Asset::shared_buffer`]:
/// a buffer a host holds, or a mapped file), and as a bounded read of the
/// entry's range otherwise.
pub struct Archive {
    archive: ZipArchive<Box<dyn ar::Asset>>,
    /// The package's bytes when the asset shares them, which entry views
    /// slice.
    bytes: Option<ar::SharedBuffer>,
}

impl Archive {
    /// Opens the package at `path`.
    pub fn open(path: impl AsRef<Path>) -> Result<Self, ArchiveError> {
        let path = path.as_ref();
        let file = File::open(path)
            .map_err(|error| io::Error::new(error.kind(), format!("unable to open {}: {error}", path.display())))?;
        Self::from_asset(Box::new(file))
    }

    /// A package over `asset`, reading only its central directory.
    pub fn from_asset(asset: Box<dyn ar::Asset>) -> Result<Self, ArchiveError> {
        let bytes = asset.shared_buffer();
        let archive = ZipArchive::new(asset)?;
        Ok(Archive { archive, bytes })
    }

    /// A package over bytes already in hand, whose entries are views of them.
    pub fn from_bytes(bytes: impl Into<ar::AssetBuffer>) -> Result<Self, ArchiveError> {
        let bytes = bytes.into().into_shared();
        Self::from_asset(Box::new(Cursor::new(ar::AssetBuffer::Shared(bytes))))
    }

    /// Whether the package lists an entry called `name`.
    pub fn contains(&self, name: &str) -> bool {
        self.archive.index_for_name(name).is_some()
    }

    /// Returns the file name of the first layer in the archive.
    ///
    /// Per the [USDZ specification](https://openusd.org/release/spec_usdz.html),
    /// the first file in a USDZ package must be a native USD file (`.usda`, `.usdc`,
    /// or `.usd`) and serves as the root layer of the composed stage.
    pub fn first_layer_name(&self) -> Option<String> {
        self.archive
            .file_names()
            .find(|name| is_layer_name(name))
            .map(String::from)
    }

    /// Opens the first (root) layer from the archive.
    pub fn read_first_layer(&mut self) -> Result<Box<dyn sdf::AbstractData>, ArchiveError> {
        let name = self.first_layer_name().ok_or(ArchiveError::NoDefaultLayer)?;
        self.read(&name)
    }

    /// The bytes of the entry `name`.
    ///
    /// Only a stored, unencrypted entry is served, as the USDZ specification
    /// requires and C++ `usdzResolver` enforces. A package whose asset
    /// shares its bytes serves a view of them, unchecked, as C++ serves a
    /// mapped package; [`verify`](Self::verify) checks one on request. A
    /// package without shared bytes reads the entry's range through the ZIP
    /// reader, which checks the entry's checksum on the way.
    pub fn entry(&mut self, name: &str) -> Result<ar::AssetBuffer, ArchiveError> {
        let index = self
            .archive
            .index_for_name(name)
            .ok_or_else(|| ArchiveError::entry(name, zip::result::ZipError::FileNotFound))?;
        let (start, size) = {
            let file = self
                .archive
                .by_index_raw(index)
                .map_err(|error| ArchiveError::entry(name, error))?;
            if file.encrypted() {
                return Err(ArchiveError::Encrypted { name: name.to_owned() });
            }
            if file.compression() != CompressionMethod::Stored {
                return Err(ArchiveError::Compressed {
                    name: name.to_owned(),
                    method: file.compression(),
                });
            }
            // A stored entry's data is its size as stored; a directory whose
            // two sizes disagree would have a view reach into the next entry.
            if file.compressed_size() != file.size() {
                return Err(ArchiveError::entry(
                    name,
                    io::Error::new(io::ErrorKind::InvalidData, "stored entry sizes disagree"),
                ));
            }
            (file.data_start(), file.size())
        };
        let Some(bytes) = &self.bytes else {
            let mut file = self
                .archive
                .by_name(name)
                .map_err(|error| ArchiveError::entry(name, error))?;
            // The directory's size reserves the buffer once; a size the
            // package lies about fails here, before anything is read.
            let mut buffer = Vec::new();
            buffer
                .try_reserve_exact(usize::try_from(size).unwrap_or(usize::MAX))
                .map_err(|_| ArchiveError::entry(name, io::Error::from(io::ErrorKind::OutOfMemory)))?;
            file.read_to_end(&mut buffer)
                .map_err(|error| ArchiveError::entry(name, error))?;
            return Ok(ar::AssetBuffer::Owned(buffer));
        };
        // A stored entry's data is its size at `data_start`, which the raw
        // open located; a truncated package reaches past the view.
        let range = start
            .and_then(|start| usize::try_from(start).ok())
            .zip(usize::try_from(size).ok())
            .and_then(|(start, size)| Some(start..start.checked_add(size)?))
            .and_then(|range| bytes.slice(range));
        match range {
            Some(view) => Ok(ar::AssetBuffer::Shared(view)),
            None => Err(ArchiveError::entry(name, io::Error::from(io::ErrorKind::UnexpectedEof))),
        }
    }

    /// Reads the entry `name` through the ZIP reader, which checks its
    /// checksum, for a caller that wants the check a view skips.
    pub fn verify(&mut self, name: &str) -> Result<(), ArchiveError> {
        let mut file = self
            .archive
            .by_name(name)
            .map_err(|error| ArchiveError::entry(name, error))?;
        io::copy(&mut file, &mut io::sink()).map_err(|error| ArchiveError::entry(name, error))?;
        Ok(())
    }

    /// Read either a USDA or USDC file from the archive. A nested `.usdz`
    /// entry reads that package's default (first) layer.
    pub fn read(&mut self, file_path: &str) -> Result<Box<dyn sdf::AbstractData>, ArchiveError> {
        let bytes = self.entry(file_path)?;

        if file_path.ends_with(".usdz") {
            return Archive::from_bytes(bytes)
                .and_then(|mut nested| nested.read_first_layer())
                .map_err(|e| ArchiveError::entry(file_path, e));
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
            bytes.starts_with(usdc::MAGIC)
        };

        if is_crate {
            let data = usdc::CrateData::open(bytes, true).map_err(|e| ArchiveError::entry(file_path, e))?;
            Ok(Box::new(data))
        } else {
            let content = str::from_utf8(&bytes).map_err(|source| ArchiveError::Utf8 {
                name: file_path.to_owned(),
                source,
            })?;
            let data = usda::parse(content).map_err(|error| error.with_source_name(file_path))?;
            Ok(Box::new(data))
        }
    }
}

/// Whether `name` names a native USD layer, one a non-package format reads
/// (`.usd`, `.usda` or `.usdc`): the kind of entry
/// [`Archive::first_layer_name`] takes for the default layer.
pub(crate) fn is_layer_name(name: &str) -> bool {
    sdf::LayerRegistry::find_by_extension(ar::extension(name)).is_some_and(|format| !format.is_package())
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
