//! Pluggable per-format read/write seam (C++ `SdfFileFormat`).
//!
//! A [`FileFormat`] maps a concrete on-disk encoding (`usda` text, `usdc`
//! binary crate, `usdz` archive) to the shared [`AbstractData`] interface,
//! so [`Layer`](super::Layer) and the loader stay decoupled from any single
//! format. Formats are discovered by file extension via [`find_by_extension`]
//! / [`find_by_id`], mirroring C++ `SdfFileFormat::FindByExtension` /
//! `FindById` — lookup never sniffs content.
//!
//! The built-in formats are compiled in and held in a static registry. A
//! future `LayerRegistry` will own this registry alongside layer-instance
//! dedup; for now the lookup functions are free-standing.

use std::io::{Seek, Write};

use anyhow::Result;
use bitflags::bitflags;

use super::{AbstractData, LayerData};
use crate::usda::UsdaFileFormat;
use crate::usdc::UsdcFileFormat;
use crate::usdz::UsdzFileFormat;
use crate::{ar, tf};

bitflags! {
    /// The operations a [`FileFormat`] supports, mirroring C++ `SdfFileFormat`'s
    /// `supportsReading` / `supportsWriting` / `supportsEditing` plugInfo flags.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct FileFormatCaps: u8 {
        /// Can deserialize layer data via [`FileFormat::read`]
        /// (`SupportsReading`).
        const READ = 1 << 0;
        /// Can serialize layer data via [`FileFormat::write`]
        /// (`SupportsWriting`).
        const WRITE = 1 << 1;
        /// A layer backed by this format can be edited in place / used as an
        /// edit target (`SupportsEditing`).
        const EDIT = 1 << 2;
    }
}

impl FileFormatCaps {
    /// Whether [`READ`](Self::READ) is set.
    pub fn can_read(self) -> bool {
        self.contains(Self::READ)
    }

    /// Whether [`WRITE`](Self::WRITE) is set.
    pub fn can_write(self) -> bool {
        self.contains(Self::WRITE)
    }

    /// Whether [`EDIT`](Self::EDIT) is set.
    pub fn can_edit(self) -> bool {
        self.contains(Self::EDIT)
    }
}

/// A seekable write sink. `dyn Write + Seek` is not a legal trait object (both
/// are non-auto traits), so this supertrait gives [`FileFormat::write`] a
/// single object-safe sink type. The blanket impl covers every `Write + Seek`
/// type (`std::fs::File`, `Cursor<Vec<u8>>`, …).
pub trait WriteSeek: Write + Seek {}

impl<T: Write + Seek + ?Sized> WriteSeek for T {}

/// A scene-description file format: the read/write bridge between a concrete
/// encoding and [`AbstractData`].
///
/// `Sync` so the built-in formats can live in the static registry. Format
/// objects are stateless; lookup hands out `&'static dyn FileFormat`.
pub trait FileFormat: Sync {
    /// The format's stable identifier token (C++ `SdfFileFormat::GetFormatId`),
    /// e.g. `"usda"`.
    fn format_id(&self) -> tf::Token;

    /// File extensions this format claims, without the leading dot. The first
    /// is the canonical one; additional entries (e.g. `usdc` also claiming
    /// `usd`) let one format be the default for an ambiguous extension.
    fn extensions(&self) -> &[&str];

    /// The operations this format supports (C++ `SdfFileFormat`'s
    /// `supportsReading`/`Writing`/`Editing` plugInfo flags). Defaults to all
    /// three; an asymmetric encoding (e.g. an import-only third-party format)
    /// overrides this to drop a flag.
    /// [`Layer::export`](super::Layer::export) rejects a format lacking
    /// [`WRITE`](FileFormatCaps::WRITE).
    fn caps(&self) -> FileFormatCaps {
        FileFormatCaps::all()
    }

    /// Read a layer's data from `resolved`, opening the asset (and any
    /// sibling assets) through `resolver`.
    fn read(&self, resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Result<LayerData>;

    /// Serialize `data` to `sink` in this format.
    fn write(&self, data: &dyn AbstractData, sink: &mut dyn WriteSeek) -> Result<()>;
}

static USDA: UsdaFileFormat = UsdaFileFormat;
static USDC: UsdcFileFormat = UsdcFileFormat;
static USDZ: UsdzFileFormat = UsdzFileFormat;

// Poor man's sdf::LayerRegistry implementation :)

/// All built-in formats, in lookup order.
static FORMATS: &[&dyn FileFormat] = &[&USDA, &USDC, &USDZ];

/// Find the format claiming `ext` (without the leading dot, case-insensitive),
/// e.g. `"usda"` or `"usd"`. C++ `SdfFileFormat::FindByExtension`.
pub fn find_by_extension(ext: &str) -> Option<&'static dyn FileFormat> {
    FORMATS
        .iter()
        .copied()
        .find(|f| f.extensions().iter().any(|e| e.eq_ignore_ascii_case(ext)))
}

/// Find the format with the given [`format_id`](FileFormat::format_id), e.g.
/// `"usdc"`. C++ `SdfFileFormat::FindById`.
pub fn find_by_id(id: &str) -> Option<&'static dyn FileFormat> {
    FORMATS.iter().copied().find(|f| f.format_id() == id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::{DefaultResolver, Resolver};
    use crate::sdf::{self, SpecType};

    /// Build a one-prim layer's data for write/read round-tripping.
    fn sample_data() -> sdf::Data {
        let mut data = sdf::Data::new();
        let ps = data.create_spec(sdf::Path::abs_root(), SpecType::PseudoRoot);
        ps.add("primChildren", sdf::Value::TokenVec(vec!["Foo".into()]));
        let foo = sdf::path("/Foo").unwrap();
        let sp = data.create_spec(foo, SpecType::Prim);
        sp.add("specifier", sdf::Value::Specifier(sdf::Specifier::Def));
        sp.add("typeName", sdf::Value::Token("Xform".into()));
        data
    }

    fn roundtrip(format: &dyn FileFormat, ext: &str) {
        let data = sample_data();
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join(format!("rt.{ext}"));

        let mut file = std::fs::File::create(&path).unwrap();
        format.write(&data, &mut file).unwrap();
        drop(file);

        let resolver = DefaultResolver::new();
        let resolved = resolver.resolve(path.to_str().unwrap()).unwrap();
        let read = format.read(&resolver, &resolved).unwrap();

        let foo = sdf::path("/Foo").unwrap();
        assert_eq!(read.spec_type(&foo), Some(SpecType::Prim));
        assert_eq!(
            read.get_field(&foo, "typeName").unwrap().into_owned(),
            sdf::Value::Token("Xform".into())
        );
    }

    #[test]
    fn roundtrip_usda() {
        roundtrip(&UsdaFileFormat, "usda");
    }

    #[test]
    fn roundtrip_usdc() {
        roundtrip(&UsdcFileFormat, "usdc");
    }

    #[test]
    fn roundtrip_usdz() {
        roundtrip(&UsdzFileFormat, "usdz");
    }

    #[test]
    fn lookup_by_extension() {
        assert_eq!(find_by_extension("usda").unwrap().format_id(), "usda");
        assert_eq!(find_by_extension("usdc").unwrap().format_id(), "usdc");
        assert_eq!(find_by_extension("usd").unwrap().format_id(), "usdc");
        assert_eq!(find_by_extension("USDA").unwrap().format_id(), "usda");
        assert_eq!(find_by_extension("usdz").unwrap().format_id(), "usdz");
        assert!(find_by_extension("xyz").is_none());
        assert!(find_by_extension("").is_none());
    }

    #[test]
    fn lookup_by_id() {
        assert_eq!(find_by_id("usdc").unwrap().extensions(), &["usdc", "usd"]);
        assert!(find_by_id("usd").is_none());
    }

    #[test]
    fn builtin_capabilities() {
        for id in ["usda", "usdc"] {
            let caps = find_by_id(id).unwrap().caps();
            assert_eq!(caps, FileFormatCaps::all(), "{id} should read, write, and edit");
        }
        // usdz is a package format: writable as a new archive, but not editable
        // (savable) in place.
        let usdz = find_by_id("usdz").unwrap().caps();
        assert!(usdz.can_read() && usdz.can_write());
        assert!(!usdz.can_edit(), "usdz should not be editable in place");
    }
}
