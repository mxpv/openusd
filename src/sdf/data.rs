//! Mutable scene description container.
//!
//! Parallels C++ `SdfData`. A flat map from [`Path`] to [`Spec`] that can be
//! populated programmatically and then handed to a writer.

use std::{borrow::Cow, collections::HashMap};

use anyhow::{bail, Result};

use crate::sdf::{AbstractData, Path, Spec, SpecType, Value};

/// In-memory mutable layer data.
#[derive(Default, Debug, Clone)]
pub struct Data {
    specs: HashMap<Path, Spec>,
}

impl Data {
    /// Create an empty container.
    pub fn new() -> Self {
        Self::default()
    }

    /// Copy every spec and field from `src` into a new `Data`.
    pub fn from_abstract(src: &dyn AbstractData) -> Result<Self> {
        let mut out = Self::new();
        for path in src.paths() {
            let ty = src
                .spec_type(&path)
                .ok_or_else(|| anyhow::anyhow!("path {path} reported by paths() has no spec"))?;
            let spec = out.create_spec(path.clone(), ty);
            if let Some(fields) = src.list(&path) {
                for name in fields {
                    let value = src.get(&path, &name)?.into_owned();
                    spec.add(&name, value);
                }
            }
        }
        Ok(out)
    }

    /// Insert an empty spec at `path`. Replaces any existing spec.
    pub fn create_spec(&mut self, path: Path, ty: SpecType) -> &mut Spec {
        self.specs.insert(path.clone(), Spec::new(ty));
        self.specs.get_mut(&path).expect("just inserted")
    }

    /// Remove the spec at `path` and return it, if any.
    pub fn erase_spec(&mut self, path: &Path) -> Option<Spec> {
        self.specs.remove(path)
    }

    /// Borrow the spec at `path`.
    pub fn spec(&self, path: &Path) -> Option<&Spec> {
        self.specs.get(path)
    }

    /// Mutably borrow the spec at `path`.
    pub fn spec_mut(&mut self, path: &Path) -> Option<&mut Spec> {
        self.specs.get_mut(path)
    }

    /// Iterate `(path, spec)` pairs in unspecified order.
    pub fn iter(&self) -> impl Iterator<Item = (&Path, &Spec)> {
        self.specs.iter()
    }

    /// Number of specs in the container.
    pub fn len(&self) -> usize {
        self.specs.len()
    }

    /// Returns `true` if the container holds no specs.
    pub fn is_empty(&self) -> bool {
        self.specs.is_empty()
    }

    /// Write the layer to a `.usda` file on disk.
    pub fn write_usda(&self, path: impl AsRef<std::path::Path>) -> Result<()> {
        crate::usda::TextWriter::write_to_file(self as &dyn AbstractData, path)
    }

    /// Write the layer to a `.usdc` file on disk.
    pub fn write_usdc(&self, path: impl AsRef<std::path::Path>) -> Result<()> {
        crate::usdc::CrateWriter::write_to_file(self as &dyn AbstractData, path)
    }
}

impl AbstractData for Data {
    fn has_spec(&self, path: &Path) -> bool {
        self.specs.contains_key(path)
    }

    fn has_field(&self, path: &Path, field: &str) -> bool {
        self.specs.get(path).is_some_and(|spec| spec.contains(field))
    }

    fn spec_type(&self, path: &Path) -> Option<SpecType> {
        self.specs.get(path).map(|spec| spec.ty)
    }

    fn get(&self, path: &Path, field: &str) -> Result<Cow<'_, Value>> {
        let Some(spec) = self.specs.get(path) else {
            bail!("No spec found for path: {path}")
        };
        let Some(value) = spec.get(field) else {
            bail!("No field found for path '{path}' and field '{field}'")
        };
        Ok(Cow::Borrowed(value))
    }

    fn list(&self, path: &Path) -> Option<Vec<String>> {
        self.specs
            .get(path)
            .map(|spec| spec.fields.iter().map(|(k, _)| k.clone()).collect())
    }

    fn paths(&self) -> Vec<Path> {
        let mut paths: Vec<Path> = self.specs.keys().cloned().collect();
        paths.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        paths
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::path;

    #[test]
    fn create_and_query_spec() {
        let mut data = Data::new();
        let root = path("/Root").unwrap();
        let spec = data.create_spec(root.clone(), SpecType::Prim);
        spec.add("primChildren", Value::TokenVec(vec!["child".into()]));

        assert!(data.has_spec(&root));
        assert_eq!(data.spec_type(&root), Some(SpecType::Prim));
        assert!(data.has_field(&root, "primChildren"));
        assert_eq!(data.list(&root).unwrap(), vec!["primChildren".to_string()]);

        let value = data.get(&root, "primChildren").unwrap().into_owned();
        assert_eq!(value, Value::TokenVec(vec!["child".into()]));
    }

    #[test]
    fn erase_spec_removes() {
        let mut data = Data::new();
        let root = path("/Root").unwrap();
        data.create_spec(root.clone(), SpecType::Prim);

        let removed = data.erase_spec(&root).unwrap();
        assert_eq!(removed.ty, SpecType::Prim);
        assert!(!data.has_spec(&root));
        assert!(data.erase_spec(&root).is_none());
    }

    #[test]
    fn paths_are_sorted() {
        let mut data = Data::new();
        data.create_spec(path("/Zebra").unwrap(), SpecType::Prim);
        data.create_spec(path("/Apple").unwrap(), SpecType::Prim);
        data.create_spec(path("/Mango").unwrap(), SpecType::Prim);

        let paths = data.paths();
        let strs: Vec<&str> = paths.iter().map(|p| p.as_str()).collect();
        assert_eq!(strs, vec!["/Apple", "/Mango", "/Zebra"]);
    }

    #[test]
    fn from_abstract_copies_all_specs() {
        let mut source = Data::new();
        let root = path("/Root").unwrap();
        let root_spec = source.create_spec(root.clone(), SpecType::Prim);
        root_spec.add("primChildren", Value::TokenVec(vec!["child".into()]));
        root_spec.add("kind", Value::Token("component".into()));

        let child = path("/Root/child").unwrap();
        let child_spec = source.create_spec(child.clone(), SpecType::Prim);
        child_spec.add("specifier", Value::Int(0));

        let copy = Data::from_abstract(&source as &dyn AbstractData).unwrap();

        assert_eq!(copy.len(), 2);
        assert_eq!(copy.list(&root).unwrap(), vec!["primChildren", "kind"]);
        assert_eq!(copy.get(&child, "specifier").unwrap().into_owned(), Value::Int(0));
    }
}
