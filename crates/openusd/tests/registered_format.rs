//! A file format the program registers (`sdf::LayerRegistry::register_format`):
//! found by its extension after the built-in ones, and its layers opened,
//! sublayered and referenced as any other.

use openusd::sdf::{self, FileFormat, FileFormatCaps, FormatError, LayerData, LayerRegistry, SpecType};
use openusd::vt::Value;
use openusd::{ar, tf, usd};

/// A format whose every file holds one Xform, `/Made`, with a child `Kid`.
struct Made;

impl FileFormat for Made {
    fn format_id(&self) -> tf::Token {
        "xmstest".into()
    }

    fn extensions(&self) -> &[&str] {
        &["xmst"]
    }

    fn caps(&self) -> FileFormatCaps {
        FileFormatCaps::READ
    }

    fn read_bytes(&self, _bytes: ar::AssetBuffer, _source_name: &str) -> Result<LayerData, FormatError> {
        let mut data = sdf::Data::new();
        let root = data.create_spec(sdf::Path::abs_root(), SpecType::PseudoRoot);
        root.add("primChildren", Value::TokenVec(vec!["Made".into()]));
        let made = data.create_spec(sdf::path("/Made").unwrap(), SpecType::Prim);
        made.add("specifier", Value::Specifier(sdf::Specifier::Def));
        made.add("typeName", Value::Token("Xform".into()));
        made.add("primChildren", Value::TokenVec(vec!["Kid".into()]));
        let kid = data.create_spec(sdf::path("/Made/Kid").unwrap(), SpecType::Prim);
        kid.add("specifier", Value::Specifier(sdf::Specifier::Def));
        kid.add("typeName", Value::Token("Xform".into()));
        Ok(Box::new(data))
    }

    fn write(&self, _data: &dyn sdf::AbstractData, _sink: &mut dyn sdf::WriteSeek) -> Result<(), FormatError> {
        Err(FormatError::Encode {
            reason: "the test format is read only".into(),
        })
    }
}

static MADE: Made = Made;

#[test]
fn a_registered_format_opens_sublayers_and_references() {
    assert!(
        LayerRegistry::find_by_extension("xmst").is_none(),
        "not before it is registered"
    );
    assert!(LayerRegistry::register_format(&MADE));
    assert!(!LayerRegistry::register_format(&MADE), "once");
    assert_eq!(LayerRegistry::find_by_extension("XMST").unwrap().format_id(), "xmstest");
    assert_eq!(LayerRegistry::find_by_id("xmstest").unwrap().extensions(), &["xmst"]);
    assert_eq!(
        LayerRegistry::find_by_extension("usda").unwrap().format_id(),
        "usda",
        "built-ins first"
    );

    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("made.xmst");
    std::fs::write(&file, b"anything").unwrap();
    let names =
        |s: &usd::Stage| -> Vec<String> { s.root_prims().unwrap().iter().map(|t| t.as_str().to_string()).collect() };

    // Opened on its own.
    let alone = usd::Stage::open(file.to_str().unwrap()).unwrap();
    assert_eq!(names(&alone), vec!["Made"]);

    // Sublayered, and referenced.
    let root = dir.path().join("shot.usda");
    std::fs::write(
        &root,
        "#usda 1.0\n(\n    subLayers = [@./made.xmst@]\n)\n\ndef Xform \"Ref\" (\n    prepend references = @./made.xmst@</Made>\n)\n{\n}\n",
    )
    .unwrap();
    let shot = usd::Stage::open(root.to_str().unwrap()).unwrap();
    let mut got = names(&shot);
    got.sort();
    assert_eq!(got, vec!["Made", "Ref"]);
    let kid = shot.prim("/Ref/Kid").unwrap();
    assert!(kid.is_valid().unwrap(), "the referenced prim's child");
    assert_eq!(
        kid.type_name().unwrap().map(|t| t.as_str().to_string()),
        Some("Xform".to_string())
    );
}
