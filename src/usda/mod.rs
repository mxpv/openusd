//! Text file format (`usda`) reader and writer.

use std::fs;
use std::path::Path;

use anyhow::{Context, Result};

pub mod parser;
pub mod token;
mod writer;

use parser::Parser;

pub use writer::TextWriter;

use crate::{ar, sdf, tf};

/// Parse `usda` text into an in-memory [`sdf::Data`] store.
pub fn parse(text: &str) -> Result<sdf::Data> {
    let mut parser = Parser::new(text);
    let specs = parser.parse()?;
    Ok(sdf::Data::from_specs(specs))
}

/// Read a `usda` file from disk into an in-memory [`sdf::Data`] store.
pub fn read_file(path: impl AsRef<Path>) -> Result<sdf::Data> {
    let path = path.as_ref();
    let text = fs::read_to_string(path).with_context(|| format!("Unable to read file: {}", path.display()))?;

    let mut parser = Parser::new(&text);
    let specs = parser.parse().map_err(|e| match parser.last_error_highlight() {
        Some(h) => e.context(format!("{}:{}: {}", path.display(), h.line, h.column)),
        None => e.context(format!("{}: parse error", path.display())),
    })?;
    Ok(sdf::Data::from_specs(specs))
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

    fn read(&self, resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Result<sdf::LayerData> {
        let bytes = resolver.open_asset(resolved)?.read_all()?;
        let text = String::from_utf8(bytes).context("layer is not valid UTF-8")?;
        Ok(Box::new(parse(&text).context("failed to parse USDA layer")?))
    }

    fn write(&self, data: &dyn sdf::AbstractData, mut sink: &mut dyn sdf::WriteSeek) -> Result<()> {
        TextWriter::write(data, &mut sink)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::{AbstractData, SpecType};

    #[test]
    fn parse_builds_data() {
        let data = parse("#usda 1.0\ndef \"Root\"\n{\n    float size = 2.5\n}\n").expect("parse");

        let root = sdf::path("/Root").unwrap();
        assert_eq!(data.spec_type(&root), Some(SpecType::Prim));

        let size = root.append_property("size").unwrap();
        assert_eq!(data.spec_type(&size), Some(SpecType::Attribute));
        assert_eq!(
            data.get_field(&size, "default").unwrap().into_owned(),
            sdf::Value::Float(2.5)
        );
    }
}
