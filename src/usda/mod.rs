//! Text file format (`usda`) reader.

use std::borrow::Cow;
use std::{collections::HashMap, fs, path::Path};

use anyhow::{bail, Result};

pub mod parser;
pub mod token;

use anyhow::Context;
use parser::Parser;

use crate::sdf;

/// High level interface to text data.
#[derive(Clone)]
pub struct TextReader {
    pub data: HashMap<sdf::Path, sdf::Spec>,
}

impl TextReader {
    /// Read a file on disk.
    pub fn read(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let data = fs::read_to_string(path).with_context(|| format!("Unable to read file: {}", path.display()))?;

        let mut parser = Parser::new(&data);
        let data = parser.parse().context("Unable to parse text file")?;

        Ok(Self { data })
    }

    /// Create from parsed data.
    pub fn from_data(data: HashMap<sdf::Path, sdf::Spec>) -> Self {
        Self { data }
    }

    /// Returns a list of child paths for a given prim path.
    pub fn get_name_children(&self, path: &sdf::Path) -> Vec<sdf::Path> {
        use crate::sdf::schema::ChildrenKey;
        if let Some(spec) = self.data.get(path) {
            if let Some(sdf::Value::TokenVec(children)) = spec.fields.get(ChildrenKey::PrimChildren.as_str()) {
                return children
                    .iter()
                    .filter_map(|name| path.append_path(name.as_str()).ok())
                    .collect();
            }
        }
        Vec::new()
    }

    /// Returns the value of an attribute if it exists and matches the requested type.
    /// This looks for the 'default' field on the property spec at the given path.
    pub fn get_attribute_value<T: sdf::FromValue>(&mut self, path: &sdf::Path) -> Option<T> {
        use crate::sdf::AbstractData;
        if let Ok(val) = self.get(path, "default") {
            T::from_value(&val)
        } else {
            None
        }
    }

    /// Helper to get an attribute value directly from a prim path and attribute name.
    pub fn get_prim_attribute_value<T: sdf::FromValue>(&mut self, prim_path: &sdf::Path, attr_name: &str) -> Option<T> {
        let prop_path = prim_path.append_property(attr_name).ok()?;
        self.get_attribute_value(&prop_path)
    }
}

impl sdf::AbstractData for TextReader {
    fn has_spec(&self, path: &sdf::Path) -> bool {
        self.data.contains_key(path)
    }

    fn has_field(&self, path: &sdf::Path, field: &str) -> bool {
        self.data.get(path).is_some_and(|spec| spec.fields.contains_key(field))
    }

    fn spec_type(&self, path: &sdf::Path) -> Option<sdf::SpecType> {
        self.data.get(path).map(|spec| spec.ty)
    }

    fn get(&mut self, path: &sdf::Path, field: &str) -> Result<Cow<'_, sdf::Value>> {
        let Some(spec) = self.data.get(path) else {
            bail!("No spec found for path: {path}")
        };

        let Some(field) = spec.fields.get(field) else {
            bail!("No field found for path '{path}' and field '{field}'")
        };

        Ok(Cow::Borrowed(field))
    }

    fn list(&self, path: &sdf::Path) -> Option<Vec<String>> {
        self.data.get(path).map(|spec| spec.fields.keys().cloned().collect())
    }
}
