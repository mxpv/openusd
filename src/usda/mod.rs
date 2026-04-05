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
    data: HashMap<sdf::Path, sdf::Spec>,
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

    /// Returns an iterator over all specs in the reader.
    pub fn iter(&self) -> impl Iterator<Item = (&sdf::Path, &sdf::Spec)> {
        self.data.iter()
    }

    /// Returns a list of child prim paths for a given prim path.
    pub fn prim_children(&self, path: &sdf::Path) -> Vec<sdf::Path> {
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
    /// This looks for the `default` field on the property spec at the given path.
    pub fn attribute_value<T>(&self, path: &sdf::Path) -> Option<T>
    where
        for<'a> T: TryFrom<&'a sdf::Value>,
    {
        let spec = self.data.get(path)?;
        let field = spec.fields.get("default")?;
        T::try_from(field).ok()
    }

    /// Returns an attribute value directly from a prim path and attribute name.
    pub fn prim_attribute_value<T>(&self, prim_path: &sdf::Path, attr_name: &str) -> Option<T>
    where
        for<'a> T: TryFrom<&'a sdf::Value>,
    {
        let prop_path = prim_path.append_property(attr_name).ok()?;
        self.attribute_value(&prop_path)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::{self, SpecType};

    /// Build a minimal TextReader with a prim at `/Root` that has a float attribute `size`.
    fn test_reader() -> TextReader {
        let root = sdf::path("/Root").unwrap();
        let mut prim_spec = sdf::Spec::new(SpecType::Prim);
        prim_spec
            .fields
            .insert("primChildren".into(), sdf::Value::TokenVec(vec![]));

        let attr_path = root.append_property("size").unwrap();
        let mut attr_spec = sdf::Spec::new(SpecType::Attribute);
        attr_spec.fields.insert("default".into(), sdf::Value::Float(2.5));

        let data = HashMap::from([(root, prim_spec), (attr_path, attr_spec)]);
        TextReader::from_data(data)
    }

    #[test]
    fn attribute_value_returns_matching_type() {
        let reader = test_reader();
        let path = sdf::path("/Root").unwrap().append_property("size").unwrap();
        assert_eq!(reader.attribute_value::<f32>(&path), Some(2.5));
    }

    #[test]
    fn attribute_value_returns_none_on_type_mismatch() {
        let reader = test_reader();
        let path = sdf::path("/Root").unwrap().append_property("size").unwrap();
        assert_eq!(reader.attribute_value::<i32>(&path), None);
    }

    #[test]
    fn attribute_value_returns_none_for_missing_path() {
        let reader = test_reader();
        let path = sdf::path("/Missing").unwrap().append_property("size").unwrap();
        assert_eq!(reader.attribute_value::<f32>(&path), None);
    }

    #[test]
    fn prim_attribute_value_shorthand() {
        let reader = test_reader();
        let prim = sdf::path("/Root").unwrap();
        assert_eq!(reader.prim_attribute_value::<f32>(&prim, "size"), Some(2.5));
        assert_eq!(reader.prim_attribute_value::<f32>(&prim, "missing"), None);
    }
}
