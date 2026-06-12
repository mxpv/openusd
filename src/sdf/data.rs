//! Mutable scene description container.
//!
//! Parallels C++ `SdfData`. A flat map from [`Path`] to [`SpecData`] that can
//! be populated programmatically and then handed to a writer.

use std::{borrow::Cow, collections::HashMap};

use anyhow::Result;

use crate::sdf::{Path, SpecData, SpecType, Value};

/// The scene-description storage interface, mirroring C++ `SdfAbstractData`.
///
/// An `AbstractData` is an anonymous container of specs (keyed by [`Path`]) and
/// their fields. Like `SdfAbstractData`, the interface is *field-level* and
/// read+write: readers, writers, composition, and authoring all operate through
/// the same set of `has_*` / `try_field` / `create_spec` / `set_field` methods,
/// regardless of whether the backing store decodes eagerly (text, [`Data`]) or
/// lazily (the binary crate reader). The typed spec views
/// ([`PrimSpec`](crate::sdf::PrimSpec) and friends) are a higher-tier
/// convenience layered on top of this interface, paralleling how `SdfPrimSpec`
/// sits above `SdfAbstractData`.
pub trait AbstractData {
    /// Returns `true` if this data has a spec for the given path.
    fn has_spec(&self, path: &Path) -> bool;

    /// Returns `true` if this data has a field for the given path.
    fn has_field(&self, path: &Path, field: &str) -> bool;

    /// Returns the type of the spec at the given path.
    fn spec_type(&self, path: &Path) -> Option<SpecType>;

    /// Returns the value for a field, or `None` if not authored.
    ///
    /// The value can be either owned or borrowed depending on internals.
    /// In the binary format, the data is typically compressed and/or encoded,
    /// so memory allocation is required to store unpacked result, so owned
    /// values are typically expected. With text parsers, there is a data copy
    /// already stored, so a borrowed value is returned to avoid unnecessary copies.
    ///
    /// Errors propagate I/O or decoding failures; a missing spec or field is
    /// signalled by `Ok(None)`.
    fn try_field(&self, path: &Path, field: &str) -> Result<Option<Cow<'_, Value>>, DataError>;

    /// Returns the value for a field, erroring if not authored.
    ///
    /// Use [`AbstractData::try_field`] when absence is an expected condition.
    fn get_field(&self, path: &Path, field: &str) -> Result<Cow<'_, Value>, DataError> {
        self.try_field(path, field)?.ok_or_else(|| DataError::Missing {
            path: path.clone(),
            field: field.to_owned(),
        })
    }

    /// Returns the field names for a given path in authored order.
    fn list_fields(&self, path: &Path) -> Option<Vec<String>>;

    /// Returns every authored path, sorted lexicographically.
    ///
    /// The order is deterministic and stable across repeated calls. Emitters
    /// rely on this for reproducible output.
    fn spec_paths(&self) -> Vec<Path>;

    /// Creates an empty spec of type `ty` at `path`, replacing any existing
    /// spec there. Mirrors C++ `SdfAbstractData::CreateSpec`. Fields are
    /// authored separately via [`set_field`](Self::set_field).
    fn create_spec(&mut self, path: Path, ty: SpecType);

    /// Removes the spec at `path` along with all its fields. Mirrors C++
    /// `SdfAbstractData::EraseSpec`. No-op if no spec exists there.
    fn erase_spec(&mut self, path: &Path);

    /// Sets (or replaces) `field` on the spec at `path`, preserving authored
    /// field order. Mirrors C++ `SdfAbstractData::Set`. The spec must already
    /// exist (create it with [`create_spec`](Self::create_spec) first); setting
    /// a field on an absent spec drops the write (debug builds assert).
    ///
    /// This *replaces* the field value; it does not merge list ops. List-op
    /// accumulation across multiple operator statements is the reader's job
    /// (see `SpecData::add_list_op`), so authoring a list op through this trait
    /// overwrites rather than folds.
    //
    // TODO: lift list-op merge onto this trait so the in-memory and crate
    // backends agree and the typed-view mutators stop re-implementing the fold.
    fn set_field(&mut self, path: &Path, field: &str, value: Value);

    /// Removes `field` from the spec at `path`. Mirrors C++
    /// `SdfAbstractData::EraseField`. No-op if the spec or field is absent.
    fn erase_field(&mut self, path: &Path, field: &str);
}

/// A failure reading a field value through [`AbstractData::try_field`] /
/// [`AbstractData::get_field`].
///
/// Eager backends ([`Data`], the text reader) never fail a field read; only a
/// lazy backend that decodes on demand — the `.usdc` crate reader — can error,
/// when an authored value fails to decode or decompress.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum DataError {
    /// A backend failed to decode or decompress an authored field value.
    //
    // TODO: the crate reader's value decoder still returns `anyhow::Error`, so
    // its failure is boxed here rather than typed. Give the decoder its own
    // error and have this variant wrap it directly.
    #[error("failed to decode field {field:?} at {path}")]
    Decode {
        /// The spec path whose field failed to decode.
        path: Path,
        /// The name of the field that failed to decode.
        field: String,
        /// The backend-specific decode failure.
        #[source]
        source: Box<dyn std::error::Error + Send + Sync + 'static>,
    },

    /// [`get_field`](AbstractData::get_field) was asked for a field that is not
    /// authored on the spec.
    #[error("no field {field:?} at {path}")]
    Missing {
        /// The spec path that was queried.
        path: Path,
        /// The name of the absent field.
        field: String,
    },
}

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
        for path in src.spec_paths() {
            let ty = src
                .spec_type(&path)
                .ok_or_else(|| anyhow::anyhow!("path {path} reported by paths() has no spec"))?;
            let spec = out.create_spec(path.clone(), ty);
            if let Some(fields) = src.list_fields(&path) {
                for name in fields {
                    spec.add(&name, src.get_field(&path, &name)?.into_owned());
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

    fn try_field(&self, path: &Path, field: &str) -> Result<Option<Cow<'_, Value>>, DataError> {
        Ok(self.specs.get(path).and_then(|spec| spec.get(field)).map(Cow::Borrowed))
    }

    fn list_fields(&self, path: &Path) -> Option<Vec<String>> {
        self.specs
            .get(path)
            .map(|spec| spec.fields.iter().map(|(k, _)| k.clone()).collect())
    }

    fn spec_paths(&self) -> Vec<Path> {
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
        assert_eq!(data.list_fields(&root).unwrap(), vec!["primChildren".to_string()]);

        let value = data.get_field(&root, "primChildren").unwrap().into_owned();
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

        let paths = data.spec_paths();
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
        assert_eq!(copy.list_fields(&root).unwrap(), vec!["primChildren", "kind"]);
        assert_eq!(copy.get_field(&child, "specifier").unwrap().into_owned(), Value::Int(0));
    }
}
