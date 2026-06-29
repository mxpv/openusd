//! Pluggable per-format read/write seam (C++ `SdfFileFormat`).
//!
//! A [`FileFormat`] maps a concrete on-disk encoding (`usda` text, `usdc`
//! binary crate, `usdz` archive) to the shared [`AbstractData`] interface, so
//! [`Layer`](super::Layer) and the loader stay decoupled from any single
//! format. This module is the format abstraction (the trait); the registry that
//! holds the built-in formats and looks them up by extension/content lives with
//! [`LayerRegistry`](super::LayerRegistry) (`find_by_extension` / `find_by_id`),
//! mirroring C++ `SdfFileFormat::FindByExtension` / `FindById`.

use std::io::{Seek, Write};

use anyhow::Result;
use bitflags::bitflags;

use super::{AbstractData, LayerData};
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

    /// Resolves the real path of the layer to open at `resolved` — the location
    /// it physically loads from and anchors its relative asset paths against
    /// (C++ `SdfLayer::GetRealPath`) — or `None` if this format cannot read it
    /// there.
    ///
    /// The default is the identity: an ordinary layer loads from the location
    /// it resolved to. A package format overrides this to select the package's
    /// default layer (`pkg.usdz` → `pkg.usdz[root.usd]`), so the package
    /// composes as an ordinary layer stack and the paths authored inside it
    /// anchor in-package; a package it cannot open returns `None`. Opening the
    /// asset goes through `resolver` so a host-provided byte source is honored.
    fn resolve_layer(&self, _resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Option<ar::ResolvedPath> {
        Some(resolved.clone())
    }

    /// Whether this format can read an asset whose leading bytes are `prefix`
    /// (C++ `SdfFileFormat::CanRead`). Used to disambiguate an extension claimed
    /// by more than one format — binary vs text `.usd` — by content. The default
    /// has no content signature; a binary format overrides it to match its magic.
    fn matches_content(&self, _prefix: &[u8]) -> bool {
        false
    }

    /// Serialize `data` to `sink` in this format.
    fn write(&self, data: &dyn AbstractData, sink: &mut dyn WriteSeek) -> Result<()>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::{DefaultResolver, Resolver};
    use crate::sdf::{self, SpecType};
    use crate::usda::UsdaFileFormat;
    use crate::usdc::UsdcFileFormat;
    use crate::usdz::UsdzFileFormat;

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
}
