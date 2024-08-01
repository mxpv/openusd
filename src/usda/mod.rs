//! `usda` impelements text file parser.

use std::borrow::Cow;
use std::{collections::HashMap, fs, path::Path};

use anyhow::{bail, Result};

pub mod parser;
pub mod tok;

use anyhow::Context;
use parser::Parser;

use crate::sdf;

pub struct TextReader {
    data: HashMap<sdf::Path, sdf::Spec>,
}

impl TextReader {
    pub fn read(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let data = fs::read_to_string(path).with_context(|| format!("Unable to read file: {}", path.display()))?;

        let mut parser = Parser::new(&data);
        let data = parser.parse().context("Unable to parse text file")?;

        Ok(Self { data })
    }
}

impl sdf::AbstractData for TextReader {
    fn has_spec(&self, path: &sdf::Path) -> bool {
        self.data.contains_key(path)
    }

    fn has_field(&self, path: &sdf::Path, field: &str) -> bool {
        self.data
            .get(path)
            .map_or(false, |spec| spec.fields.contains_key(field))
    }

    fn spec_type(&self, path: &sdf::Path) -> Option<sdf::SpecType> {
        self.data.get(path).map(|spec| spec.ty)
    }

    fn get(&mut self, path: &sdf::Path, field: &str) -> Result<Cow<sdf::Value>> {
        let Some(spec) = self.data.get(path) else {
            bail!("No spec found for path: {}", path)
        };

        let Some(field) = spec.fields.get(field) else {
            bail!("No field found for path '{}' and field '{}'", path, field)
        };

        Ok(Cow::Borrowed(field))
    }

    fn list(&self, path: &sdf::Path) -> Option<Vec<String>> {
        self.data.get(path).map(|spec| spec.fields.keys().cloned().collect())
    }
}
