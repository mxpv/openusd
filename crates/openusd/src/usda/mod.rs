//! Text file format (`usda`) reader and writer.

use std::fs;
use std::io;
use std::path::Path;

mod cursor;
mod error;
pub mod parser;
pub mod token;
mod types;
mod writer;

use parser::Parser;

pub use error::ParseError;
pub use writer::TextWriter;

use crate::{ar, sdf, tf};

/// Parse `usda` text into an in-memory [`sdf::Data`] store.
pub fn parse(text: &str) -> Result<sdf::Data, ParseError> {
    let specs = Parser::new(text).parse()?;
    Ok(sdf::Data::from_specs(specs))
}

/// The header every `usda` layer opens with (C++ `SdfUsdaFileFormat`'s file
/// cookie), the literal the lexer's magic token requires before the version.
/// Content-based format detection matches it; the trailing space is part of
/// the cookie, so `#usdaFOO` is not text this format claims.
pub const MAGIC: &[u8] = b"#usda ";

/// How deep the bodies in a `usda` layer may nest, counting prims, variants
/// and the dictionaries in their values together, and in the writer the value
/// arrays too. The reader and writer recurse once per body, and this bounds
/// the stack they use. The reader refuses a deeper layer from an arbitrary
/// file, and the writer one read from a crate file or built in memory.
pub const MAX_NESTING: usize = 256;

/// Read a `usda` file from disk into an in-memory [`sdf::Data`] store.
pub fn read_file(path: impl AsRef<Path>) -> crate::Result<sdf::Data> {
    let path = path.as_ref();
    let text = fs::read_to_string(path)
        .map_err(|error| io::Error::new(error.kind(), format!("unable to read {}: {error}", path.display())))?;

    Ok(parse(&text).map_err(|error| error.with_source_name(path.display().to_string()))?)
}

/// Text format (`.usda`) as an [`sdf::FileFormat`], wrapping [`parse`] and
/// [`TextWriter`].
pub struct UsdaFileFormat;

impl sdf::FileFormat for UsdaFileFormat {
    fn format_id(&self) -> tf::Token {
        tf::Token::new("usda")
    }

    fn extensions(&self) -> &[&str] {
        &["usda"]
    }

    fn skip_anonymous_reload(&self) -> bool {
        false
    }

    fn matches_content(&self, prefix: &[u8]) -> bool {
        // The lexer skips whitespace before the cookie, so a layer that opens
        // with a blank line is still text (C++ `CanRead` reads the cookie the
        // same way).
        let start = prefix
            .iter()
            .position(|byte| !byte.is_ascii_whitespace())
            .unwrap_or(prefix.len());
        prefix[start..].starts_with(MAGIC)
    }

    fn read_bytes(&self, bytes: ar::AssetBuffer, source_name: &str) -> Result<sdf::LayerData, sdf::FormatError> {
        // The parse copies out everything it keeps and never copies `bytes`
        // wholesale, whether they are compiled into the program, owned, or
        // shared with an asset.
        let text = str::from_utf8(&bytes).map_err(|error| sdf::FormatError::Decode(Box::new(error)))?;
        let data = parse(text)
            .map_err(|error| sdf::FormatError::Decode(Box::new(error.with_source_name(source_name.to_owned()))))?;
        Ok(Box::new(data))
    }

    fn write(&self, data: &dyn sdf::AbstractData, mut sink: &mut dyn sdf::WriteSeek) -> Result<(), sdf::FormatError> {
        TextWriter::write(data, &mut sink)
    }
}

#[cfg(test)]
mod tests {
    use std::fmt;
    use std::sync::Arc;

    use super::*;
    use crate::sdf::{AbstractData, FileFormat, SpecType};
    use crate::vt;

    /// Text shared with an asset parses from the shared bytes.
    #[test]
    fn shared_buffer_parse() {
        let bytes: Arc<[u8]> = b"#usda 1.0\ndef \"Root\"\n{\n}\n".to_vec().into();
        let data = UsdaFileFormat.read_bytes(bytes.into(), "shared.usda").expect("parse");
        assert_eq!(data.spec_type(&sdf::path("/Root").unwrap()), Some(SpecType::Prim));
    }

    #[test]
    fn parse_builds_data() {
        let data = parse("#usda 1.0\ndef \"Root\"\n{\n    float size = 2.5\n}\n").expect("parse");

        let root = sdf::path("/Root").unwrap();
        assert_eq!(data.spec_type(&root), Some(SpecType::Prim));

        let size = root.append_property("size").unwrap();
        assert_eq!(data.spec_type(&size), Some(SpecType::Attribute));
        assert_eq!(
            data.field(&size, "default").unwrap().into_owned(),
            vt::Value::Float(2.5)
        );
    }

    /// Reads `text(MAX_NESTING)`, writes it and reads that back, then checks
    /// that `text(MAX_NESTING + 1)` is refused.
    fn round_trip_then_refuse(text: impl Fn(usize) -> String) -> crate::Result<()> {
        let data = parse(&text(MAX_NESTING))?;
        let mut written = Vec::new();
        TextWriter::write(&data, &mut io::Cursor::new(&mut written))?;
        parse(&String::from_utf8(written).expect("usda is UTF-8"))?;
        assert_too_deep(parse(&text(MAX_NESTING + 1)).expect_err("one level too deep"));
        Ok(())
    }

    fn assert_too_deep(error: impl fmt::Display) {
        assert!(error.to_string().contains("nested more than"), "{error}");
    }

    /// Prims and variants nested `MAX_NESTING` deep read and write back; one
    /// level deeper is refused by the reader, and by the writer for a layer
    /// holding one.
    #[test]
    fn prim_nesting_limit() -> crate::Result<()> {
        round_trip_then_refuse(|depth| {
            format!(
                "#usda 1.0
{}{}",
                "def \"P\" {
"
                .repeat(depth),
                "}
"
                .repeat(depth)
            )
        })?;
        round_trip_then_refuse(|depth| {
            format!(
                "#usda 1.0
def \"P\" {{
{}{}}}
",
                "variantSet \"v\" = {
\"x\" {
"
                .repeat(depth - 1),
                "}
}
"
                .repeat(depth - 1)
            )
        })?;

        let mut deep = sdf::Data::new();
        deep.create_spec(sdf::Path::abs_root(), SpecType::PseudoRoot)
            .add("primChildren", vt::Value::token_vec(["P"]));
        let mut path = sdf::Path::abs_root();
        for _ in 0..=MAX_NESTING {
            path = path.append_path("P")?;
            deep.create_spec(path.clone(), SpecType::Prim)
                .add("primChildren", vt::Value::token_vec(["P"]));
        }
        assert_too_deep(TextWriter::write(&deep, &mut io::Cursor::new(Vec::new())).expect_err("one level too deep"));
        Ok(())
    }

    /// Dictionaries nested `MAX_NESTING` deep read and write back, whether
    /// an entry spells its own `dictionary` or leaves it untyped; one level
    /// deeper is refused by the reader, and by the writer, which counts a
    /// value array as a level too.
    #[test]
    fn dictionary_nesting_limit() -> crate::Result<()> {
        // Each spells a `customData` dictionary holding `depth` in all,
        // itself included.
        let spellings: [fn(usize) -> String; 2] = [
            |depth| {
                format!(
                    "{}{{
int x = 1
{}",
                    "{
dictionary d = "
                        .repeat(depth - 1),
                    "}
"
                    .repeat(depth)
                )
            },
            |depth| {
                format!(
                    "{}{{
}}{}",
                    "{
\"d\" = "
                        .repeat(depth - 1),
                    "
}"
                    .repeat(depth - 1)
                )
            },
        ];
        for value in spellings {
            round_trip_then_refuse(|depth| {
                format!(
                    "#usda 1.0
def \"P\" (
    customData = {}
)
{{
}}
",
                    value(depth)
                )
            })?;
        }

        let mut value = vt::Value::Int(1);
        for _ in 0..MAX_NESTING {
            value = vt::Value::Dictionary(vt::Dictionary::from([("d".to_owned(), value)]));
        }
        TextWriter::value_to_string(&value)?;
        let value = vt::Value::ValueVec(vec![value]);
        assert_too_deep(TextWriter::value_to_string(&value).expect_err("one level too deep"));
        Ok(())
    }

    /// Prims and the dictionaries in their metadata share one budget: a
    /// dictionary on the innermost of `MAX_NESTING` nested prims reads and
    /// writes back, and one more inside it is refused.
    #[test]
    fn shared_nesting_limit() -> crate::Result<()> {
        let text = |value: &str| {
            format!(
                "#usda 1.0
{}def \"Q\" (
    customData = {value}
)
{{
}}
{}",
                "def \"P\" {
"
                .repeat(MAX_NESTING - 1),
                "}
"
                .repeat(MAX_NESTING - 1)
            )
        };
        let data = parse(&text(
            "{
int x = 1
}",
        ))?;
        TextWriter::write(&data, &mut io::Cursor::new(Vec::new()))?;
        assert_too_deep(
            parse(&text(
                "{
dictionary d = {
}
}",
            ))
            .expect_err("one level too deep"),
        );
        Ok(())
    }

    /// An untyped array holds no array or dictionary.
    #[test]
    fn untyped_nested_array() {
        let text = |value| {
            format!(
                "#usda 1.0
def \"P\" (
    customData = {{
\"l\" = {value}
}}
)
{{
}}
"
            )
        };
        parse(&text("[1]")).expect("flat array");
        for nested in [
            "[[1]]", "[{
}]",
        ] {
            let error = parse(&text(nested)).expect_err("nested array");
            assert!(error.to_string().contains("cannot hold"), "{error}");
        }
    }
}
