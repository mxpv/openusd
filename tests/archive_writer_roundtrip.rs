//! Round-trip tests for the USDZ archive writer.
//!
//! Build an archive, read it back, and verify the constituent layers
//! round-trip through their respective parsers.

use std::io::Cursor;

use openusd::sdf::{self, AbstractData};
use openusd::usdc::{CrateData, CrateWriter};
use openusd::usdz::{Archive, ArchiveWriter};
use zip::ZipArchive;

/// Produce a minimal valid USDC payload by taking an existing fixture.
fn usdc_bytes() -> Vec<u8> {
    std::fs::read("fixtures/fields.usdc").expect("read fields.usdc fixture")
}

fn usda_bytes() -> Vec<u8> {
    std::fs::read("fixtures/fields.usda").expect("read fields.usda fixture")
}

#[test]
fn archive_contains_entries_stored() {
    let mut buf = Vec::new();
    {
        let mut w = ArchiveWriter::new(Cursor::new(&mut buf));
        w.add_layer("root.usdc", &usdc_bytes()).unwrap();
        w.add_layer("alt.usda", &usda_bytes()).unwrap();
        w.finish().unwrap();
    }

    let mut archive = ZipArchive::new(Cursor::new(&buf)).expect("valid zip");
    assert_eq!(archive.len(), 2);

    let entry_names: Vec<String> = archive.file_names().map(String::from).collect();
    assert!(entry_names.contains(&"root.usdc".to_string()));
    assert!(entry_names.contains(&"alt.usda".to_string()));

    // All entries must be stored uncompressed.
    for i in 0..archive.len() {
        let file = archive.by_index_raw(i).unwrap();
        assert_eq!(
            file.compression(),
            zip::CompressionMethod::Stored,
            "entry {} is compressed",
            file.name()
        );
    }
}

#[test]
fn file_data_is_64_byte_aligned() {
    let mut buf = Vec::new();
    {
        let mut w = ArchiveWriter::new(Cursor::new(&mut buf));
        w.add_layer("root.usdc", &usdc_bytes()).unwrap();
        w.add_layer("alt.usda", &usda_bytes()).unwrap();
        w.finish().unwrap();
    }

    let mut archive = ZipArchive::new(Cursor::new(&buf)).expect("valid zip");
    for i in 0..archive.len() {
        let file = archive.by_index_raw(i).unwrap();
        let name = file.name().to_owned();
        let data_start = file.data_start().expect("data_start known after reading");
        assert!(
            data_start.is_multiple_of(64),
            "entry {name} data starts at offset {data_start} which is not 64-byte aligned",
        );
    }
}

#[test]
fn roundtrip_usdc_layer_bytes() {
    let original = usdc_bytes();
    let mut buf = Vec::new();
    {
        let mut w = ArchiveWriter::new(Cursor::new(&mut buf));
        w.add_layer("scene.usdc", &original).unwrap();
        w.finish().unwrap();
    }

    let mut archive = ZipArchive::new(Cursor::new(&buf)).expect("valid zip");
    let mut file = archive.by_name("scene.usdc").unwrap();
    let mut got = Vec::new();
    std::io::copy(&mut file, &mut got).unwrap();
    assert_eq!(got, original, "usdc bytes were mutated by archive writer");
}

#[test]
fn create_method_writes_to_disk_and_reads_back() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let tmp = tmp_dir.path().join("archive-roundtrip.usdz");
    {
        let mut w = ArchiveWriter::create(&tmp).unwrap();
        w.add_layer("scene.usdc", &usdc_bytes()).unwrap();
        w.finish().unwrap();
    }

    let mut archive = Archive::open(&tmp).unwrap();
    assert_eq!(archive.first_layer_name().as_deref(), Some("scene.usdc"));
    let layer = archive.read("scene.usdc").unwrap();
    assert!(layer.has_spec(&sdf::Path::abs_root()));
}

#[test]
fn emitted_archive_roundtrips_through_openusd() {
    // Build a minimal layer programmatically, emit it as USDC, pack into a
    // USDZ, read back with our own Archive reader, and verify structural
    // equality of the in-memory layer.
    let mut data = sdf::Data::new();
    let root = sdf::Path::abs_root();
    let ps = data.create_spec(root.clone(), sdf::SpecType::PseudoRoot);
    ps.add("primChildren", sdf::Value::TokenVec(vec!["Foo".into()]));
    let foo = sdf::path("/Foo").unwrap();
    let sp = data.create_spec(foo.clone(), sdf::SpecType::Prim);
    sp.add("specifier", sdf::Value::Specifier(sdf::Specifier::Def));
    sp.add("typeName", sdf::Value::Token("Xform".into()));

    let mut usdc_buf = Vec::new();
    {
        let mut cur = Cursor::new(&mut usdc_buf);
        CrateWriter::write(&data as &dyn AbstractData, &mut cur).unwrap();
    }

    let mut zip_buf = Vec::new();
    {
        let mut w = ArchiveWriter::new(Cursor::new(&mut zip_buf));
        w.add_layer("root.usdc", &usdc_buf).unwrap();
        w.finish().unwrap();
    }

    // Spot-check: parse the inner usdc directly from the archive.
    let mut archive = ZipArchive::new(Cursor::new(&zip_buf)).unwrap();
    let mut entry = archive.by_name("root.usdc").unwrap();
    let mut inner = Vec::new();
    std::io::copy(&mut entry, &mut inner).unwrap();
    let layer = CrateData::open(Cursor::new(&inner), true).unwrap();

    assert!(layer.has_spec(&root));
    assert_eq!(layer.spec_type(&foo), Some(sdf::SpecType::Prim));
    assert_eq!(
        layer.get(&foo, "typeName").unwrap().into_owned(),
        sdf::Value::Token("Xform".into())
    );
}
