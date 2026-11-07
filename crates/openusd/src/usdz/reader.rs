//! USDZ archive reader.

use std::fs::File;
use std::io::{self, Cursor, Read};
use std::path::Path;
use std::str;

use zip::read::{ArchiveOffset, Config};
use zip::{CompressionMethod, ZipArchive};

use super::{ArchiveError, MAX_NESTING};
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
    /// The index of the entry stored first, the package's root, as C++
    /// walks local file headers from the start. The central directory may
    /// list entries in another order, and records where each is stored.
    first: Option<usize>,
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
    ///
    /// The archive starts at the asset's first byte, as C++ `SdfZipFile`
    /// reads it, so the directory is found from the offsets its end record
    /// gives, without searching the asset for it.
    pub fn from_asset(asset: Box<dyn ar::Asset>) -> Result<Self, ArchiveError> {
        let bytes = asset.shared_buffer();
        let config = Config {
            archive_offset: ArchiveOffset::Known(0),
        };
        let archive = ZipArchive::with_config(config, asset)?;
        let first = (0..archive.len())
            .filter_map(|index| Some((archive.by_index_data(index).ok()?.header_start(), index)))
            .min()
            .map(|(_, index)| index);
        Ok(Archive { archive, bytes, first })
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

    /// The name of the package's first entry, its root layer, when a layer
    /// format reads it (C++ `SdfUsdzFileFormat::GetPackageRootLayerPath` and
    /// `CanRead`): a native USD layer, or a package nested there.
    ///
    /// Per the [USDZ specification](https://openusd.org/release/spec_usdz.html),
    /// the first file in a USDZ package must be a native USD file (`.usda`, `.usdc`,
    /// or `.usd`) and serves as the root layer of the composed stage. A
    /// package whose first file is not one has no root layer: `None`.
    ///
    /// Fails when the first entry's name cannot be decoded.
    pub fn root_entry(&self) -> Result<Option<String>, ArchiveError> {
        let Some(index) = self.first else {
            return Ok(None);
        };
        let name = self.archive.by_index_data(index)?.name()?.into_owned();
        let reads = sdf::LayerRegistry::find_by_extension(ar::extension(&name)).is_some();
        Ok(reads.then_some(name))
    }

    /// Reads the package's root layer, the [`root_entry`](Self::root_entry),
    /// that of a package nested there read in turn.
    pub fn read_root(&mut self) -> Result<Box<dyn sdf::AbstractData>, ArchiveError> {
        self.read_root_at(0)
    }

    /// [`read_root`](Self::read_root) of a package nested `depth` deep.
    fn read_root_at(&mut self, depth: usize) -> Result<Box<dyn sdf::AbstractData>, ArchiveError> {
        let name = self.root_entry()?.ok_or(ArchiveError::NoRootLayer)?;
        self.read_at(&name, depth)
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

    /// Read either a USDA or USDC file from the archive. A nested package
    /// entry reads that package's root layer, up to [`MAX_NESTING`]
    /// packages deep.
    pub fn read(&mut self, file_path: &str) -> Result<Box<dyn sdf::AbstractData>, ArchiveError> {
        self.read_at(file_path, 0)
    }

    /// [`read`](Self::read) in a package nested `depth` deep.
    fn read_at(&mut self, file_path: &str, depth: usize) -> Result<Box<dyn sdf::AbstractData>, ArchiveError> {
        let bytes = self.entry(file_path)?;

        if is_package_name(file_path) {
            if depth >= MAX_NESTING {
                return Err(ArchiveError::NestedTooDeep);
            }
            return Archive::from_bytes(bytes)
                .and_then(|mut nested| nested.read_root_at(depth + 1))
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
/// (`.usd`, `.usda` or `.usdc`): the kind of entry a package is written with
/// first.
pub(crate) fn is_layer_name(name: &str) -> bool {
    sdf::LayerRegistry::find_by_extension(ar::extension(name)).is_some_and(|format| !format.is_package())
}

/// Whether `name` names a package, one a package format reads (`.usdz`).
pub(crate) fn is_package_name(name: &str) -> bool {
    sdf::LayerRegistry::find_by_extension(ar::extension(name)).is_some_and(|format| format.is_package())
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
