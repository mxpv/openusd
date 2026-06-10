//! Mutable scene description container.
//!
//! Parallels C++ `SdfData`. A flat map from [`Path`] to [`SpecData`] that can
//! be populated programmatically and then handed to a writer.

use std::{borrow::Cow, collections::HashMap};

use anyhow::Result;

use crate::sdf::{AbstractData, Path, SpecData, SpecType, Value};

/// In-memory mutable layer data.
#[derive(Default, Debug, Clone)]
pub struct Data {
    specs: HashMap<Path, SpecData>,
}

impl Data {
    /// Create an empty container.
    pub fn new() -> Self {
        Self::default()
    }

    /// Build a container from a map of pre-parsed spec records, the form a
    /// reader (e.g. the usda parser) produces.
    pub fn from_specs(specs: HashMap<Path, SpecData>) -> Self {
        Self { specs }
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
                    spec.add(&name, src.get(&path, &name)?.into_owned());
                }
            }
        }
        Ok(out)
    }

    /// Insert an empty spec record at `path`, returning it for field authoring.
    /// Replaces any existing spec. The convenience counterpart to the
    /// field-level [`AbstractData::create_spec`], which returns nothing because
    /// the trait can't name `SpecData`.
    pub fn create_spec(&mut self, path: Path, ty: SpecType) -> &mut SpecData {
        self.specs.insert(path.clone(), SpecData::new(ty));
        self.specs.get_mut(&path).expect("just inserted")
    }

    /// Remove the spec record at `path` and return it, if any.
    pub fn erase_spec(&mut self, path: &Path) -> Option<SpecData> {
        self.specs.remove(path)
    }

    /// Borrow the spec record at `path`.
    pub fn spec(&self, path: &Path) -> Option<&SpecData> {
        self.specs.get(path)
    }

    /// Mutably borrow the spec record at `path`. The way to reach a
    /// `&mut SpecData` for in-place field edits, since the [`AbstractData`]
    /// interface is field-level.
    pub fn spec_mut(&mut self, path: &Path) -> Option<&mut SpecData> {
        self.specs.get_mut(path)
    }

    /// Iterate `(path, spec)` pairs in unspecified order.
    pub fn iter(&self) -> impl Iterator<Item = (&Path, &SpecData)> {
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

    fn try_get(&self, path: &Path, field: &str) -> Result<Option<Cow<'_, Value>>> {
        Ok(self.specs.get(path).and_then(|spec| spec.get(field)).map(Cow::Borrowed))
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

    fn create_spec(&mut self, path: Path, ty: SpecType) {
        self.specs.insert(path, SpecData::new(ty));
    }

    fn erase_spec(&mut self, path: &Path) {
        self.specs.remove(path);
    }

    fn set_field(&mut self, path: &Path, field: &str, value: Value) {
        match self.specs.get_mut(path) {
            Some(spec) => spec.add(field, value),
            None => debug_assert!(false, "set_field on absent spec at {path}"),
        }
    }

    fn erase_field(&mut self, path: &Path, field: &str) {
        if let Some(spec) = self.specs.get_mut(path) {
            spec.remove(field);
        }
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
        data.create_spec(root.clone(), SpecType::Prim);
        data.spec_mut(&root)
            .unwrap()
            .add("primChildren", Value::TokenVec(vec!["child".into()]));

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
        assert!(data.has_spec(&root));

        data.erase_spec(&root);
        assert!(!data.has_spec(&root));
        // Erasing an absent spec is a no-op.
        data.erase_spec(&root);
        assert!(!data.has_spec(&root));
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
        source.create_spec(root.clone(), SpecType::Prim);
        let root_spec = source.spec_mut(&root).unwrap();
        root_spec.add("primChildren", Value::TokenVec(vec!["child".into()]));
        root_spec.add("kind", Value::Token("component".into()));

        let child = path("/Root/child").unwrap();
        source.create_spec(child.clone(), SpecType::Prim);
        source.spec_mut(&child).unwrap().add("specifier", Value::Int(0));

        let copy = Data::from_abstract(&source as &dyn AbstractData).unwrap();

        assert_eq!(copy.len(), 2);
        assert_eq!(copy.list(&root).unwrap(), vec!["primChildren", "kind"]);
        assert_eq!(copy.get(&child, "specifier").unwrap().into_owned(), Value::Int(0));
    }
}
