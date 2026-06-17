//! Mutable scene description container.
//!
//! Parallels C++ `SdfData`. A flat map from [`Path`] to [`SpecData`] that can
//! be populated programmatically and then handed to a writer.

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

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

impl<T: AbstractData + ?Sized> AbstractData for Box<T> {
    fn has_spec(&self, path: &Path) -> bool {
        (**self).has_spec(path)
    }

    fn has_field(&self, path: &Path, field: &str) -> bool {
        (**self).has_field(path, field)
    }

    fn spec_type(&self, path: &Path) -> Option<SpecType> {
        (**self).spec_type(path)
    }

    fn try_field(&self, path: &Path, field: &str) -> Result<Option<Cow<'_, Value>>, DataError> {
        (**self).try_field(path, field)
    }

    fn list_fields(&self, path: &Path) -> Option<Vec<String>> {
        (**self).list_fields(path)
    }

    fn spec_paths(&self) -> Vec<Path> {
        (**self).spec_paths()
    }

    fn create_spec(&mut self, path: Path, ty: SpecType) {
        (**self).create_spec(path, ty)
    }

    fn erase_spec(&mut self, path: &Path) {
        (**self).erase_spec(path)
    }

    fn set_field(&mut self, path: &Path, field: &str, value: Value) {
        (**self).set_field(path, field, value)
    }

    fn erase_field(&mut self, path: &Path, field: &str) {
        (**self).erase_field(path, field)
    }
}

/// A copy-on-write staging layer over a base [`AbstractData`].
///
/// Writes stage in an overlay, leaving `base` untouched until
/// [`commit`](Self::commit) flushes the staged patch or
/// [`rollback`](Self::rollback) discards it for free; reads return the
/// staged-over-base view. A self-contained staging primitive — for example a
/// layer wraps it (behind a recording proxy) so an authoring transaction can be
/// applied or abandoned wholesale.
///
/// The overlay is field-granular: editing one field of a pre-existing spec
/// stages only that field, so an untouched sibling field — even a large array or
/// time-sample value — is never copied. A newly created spec stages its full
/// field set, since it has no base to read through to.
///
/// See the `sdf::layer` module documentation for why a layer's edits stage
/// copy-on-write rather than applying immediately.
pub struct CowData<T: AbstractData> {
    base: T,
    /// Per-spec staged changes keyed by path; see [`Patch`]. Empty until a write
    /// stages a change, so every read passes straight through to `base`.
    overlay: HashMap<Path, Patch>,
}

/// A staged change to one spec in a [`CowData`] overlay.
///
/// Exposed (with [`CowData::overlay`]) so the change tracker can read what the
/// overlay touched and derive a [`ChangeList`](super::ChangeList) from it; see
/// [`ChangeList::from_overlay`](super::ChangeList::from_overlay).
pub enum Patch {
    /// A spec created (or re-created, replacing a base spec) this transaction.
    /// Holds its whole field set, so reads ignore the base and commit
    /// reproduces it wholesale.
    Created(SpecData),
    /// A pre-existing base spec erased in the overlay.
    Tombstone,
    /// A pre-existing base spec with field-level edits staged over it. Only the
    /// touched fields are stored; untouched fields read through to the base.
    Edited {
        /// Fields set or overwritten this transaction, in first-touch order.
        /// Disjoint from `erased`.
        set: Vec<(String, Value)>,
        /// Fields removed from the base this transaction. Disjoint from `set`.
        erased: HashSet<String>,
    },
}

impl Patch {
    /// A fresh field-level edit over a pre-existing base spec, with no staged
    /// field writes and the given erased fields.
    fn edited(erased: HashSet<String>) -> Self {
        Patch::Edited {
            set: Vec::new(),
            erased,
        }
    }
}

impl<T: AbstractData> CowData<T> {
    /// Wrap `base` with an empty overlay.
    pub fn new(base: T) -> Self {
        Self {
            base,
            overlay: HashMap::new(),
        }
    }

    /// Whether the overlay holds no staged change — every read passes straight
    /// through to `base`.
    pub fn is_empty(&self) -> bool {
        self.overlay.is_empty()
    }

    /// Flush every staged patch into `base` and clear the overlay. A
    /// [`Created`](Patch::Created) spec is recreated with its fields, an
    /// [`Edited`](Patch::Edited) spec replays its set and erased fields onto the
    /// base, and a [`Tombstone`](Patch::Tombstone) erases the base spec.
    /// O(touched fields).
    pub fn commit(&mut self) {
        for (path, patch) in self.overlay.drain() {
            match patch {
                Patch::Created(spec) => {
                    self.base.create_spec(path.clone(), spec.ty);
                    for (field, value) in spec.fields {
                        self.base.set_field(&path, &field, value);
                    }
                }
                Patch::Tombstone => self.base.erase_spec(&path),
                Patch::Edited { set, erased } => {
                    for (field, value) in set {
                        self.base.set_field(&path, &field, value);
                    }
                    for field in erased {
                        self.base.erase_field(&path, &field);
                    }
                }
            }
        }
    }

    /// Drop the staged patch, restoring the base view. Free — `base` was never
    /// written.
    pub fn rollback(&mut self) {
        self.overlay.clear();
    }

    /// Consume the staging layer and return the base backend. Pending staged
    /// edits are discarded; [`commit`](Self::commit) first to keep them.
    pub fn into_inner(self) -> T {
        self.base
    }

    /// Borrow the base backend.
    pub fn base(&self) -> &T {
        &self.base
    }

    /// Mutably borrow the base backend, bypassing the overlay. A caller that
    /// writes through this skips staging entirely; it must keep the overlay
    /// empty (e.g. only write through here when no edit is staged), or a staged
    /// change would shadow the write on reads.
    pub fn base_mut(&mut self) -> &mut T {
        &mut self.base
    }

    /// The staged changes keyed by path, for a consumer that needs to know what
    /// the overlay touched without committing it — notably
    /// [`ChangeList::from_overlay`](super::ChangeList::from_overlay), which
    /// derives a composition-invalidation record by reading each [`Patch`]
    /// against the still-pristine [`base`](Self::base).
    pub fn overlay(&self) -> &HashMap<Path, Patch> {
        &self.overlay
    }

    /// The staged patch for `path`, or `None` when the read should fall through
    /// to `base` — both when the overlay is entirely empty (the committed steady
    /// state, kept lookup-free) and when this path is simply unstaged.
    //
    // TODO(perf): the empty-overlay fast path here is defeated while a layer
    // holds uncommitted direct edits (those made outside a transaction stay
    // staged until the next flush), so each read pays a `HashMap` lookup until
    // then. Stage-managed layers flush at every transaction, so this only bites
    // a standalone layer edited heavily without committing.
    fn staged(&self, path: &Path) -> Option<&Patch> {
        if self.overlay.is_empty() {
            None
        } else {
            self.overlay.get(path)
        }
    }
}

impl<T: AbstractData> AbstractData for CowData<T> {
    fn has_spec(&self, path: &Path) -> bool {
        match self.staged(path) {
            Some(Patch::Tombstone) => false,
            // `Edited` exists only over a base spec, so the spec is present.
            Some(_) => true,
            None => self.base.has_spec(path),
        }
    }

    fn has_field(&self, path: &Path, field: &str) -> bool {
        match self.staged(path) {
            Some(Patch::Created(spec)) => spec.contains(field),
            Some(Patch::Tombstone) => false,
            Some(Patch::Edited { set, erased }) => {
                !erased.contains(field) && (set.iter().any(|(f, _)| f == field) || self.base.has_field(path, field))
            }
            None => self.base.has_field(path, field),
        }
    }

    fn spec_type(&self, path: &Path) -> Option<SpecType> {
        match self.staged(path) {
            Some(Patch::Created(spec)) => Some(spec.ty),
            Some(Patch::Tombstone) => None,
            Some(Patch::Edited { .. }) | None => self.base.spec_type(path),
        }
    }

    fn try_field(&self, path: &Path, field: &str) -> Result<Option<Cow<'_, Value>>, DataError> {
        match self.staged(path) {
            Some(Patch::Created(spec)) => Ok(spec.get(field).map(Cow::Borrowed)),
            Some(Patch::Tombstone) => Ok(None),
            Some(Patch::Edited { set, erased }) => {
                if erased.contains(field) {
                    Ok(None)
                } else if let Some((_, value)) = set.iter().find(|(f, _)| f == field) {
                    Ok(Some(Cow::Borrowed(value)))
                } else {
                    self.base.try_field(path, field)
                }
            }
            None => self.base.try_field(path, field),
        }
    }

    fn list_fields(&self, path: &Path) -> Option<Vec<String>> {
        match self.staged(path) {
            Some(Patch::Created(spec)) => Some(spec.fields.iter().map(|(k, _)| k.clone()).collect()),
            Some(Patch::Tombstone) => None,
            Some(Patch::Edited { set, erased }) => {
                // Base fields in authored order minus the erased ones, then the
                // newly-set fields appended — the same order commit reproduces.
                let mut names: Vec<String> = self
                    .base
                    .list_fields(path)
                    .unwrap_or_default()
                    .into_iter()
                    .filter(|f| !erased.contains(f))
                    .collect();
                // TODO(perf): the dedup is `names.iter().any` per staged field,
                // O(base × set). `set` is tiny for a typical edit (a handful of
                // fields), and this only runs while the overlay is dirty; a
                // name set would beat it only for specs edited many-fields-wide.
                for (field, _) in set {
                    if !names.iter().any(|n| n == field) {
                        names.push(field.clone());
                    }
                }
                Some(names)
            }
            None => self.base.list_fields(path),
        }
    }

    fn spec_paths(&self) -> Vec<Path> {
        if self.overlay.is_empty() {
            return self.base.spec_paths();
        }
        // TODO(perf): `base.spec_paths()` is already sorted, but splicing in the
        // staged-created paths forces a full re-sort of the merged list; a sorted
        // merge would avoid it. Only runs mid-transaction, while the overlay is
        // dirty.
        let mut paths: Vec<Path> = self
            .base
            .spec_paths()
            .into_iter()
            .filter(|p| !matches!(self.overlay.get(p), Some(Patch::Tombstone)))
            .collect();
        for (path, patch) in &self.overlay {
            if matches!(patch, Patch::Created(_)) && !self.base.has_spec(path) {
                paths.push(path.clone());
            }
        }
        paths.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        paths
    }

    fn create_spec(&mut self, path: Path, ty: SpecType) {
        self.overlay.insert(path, Patch::Created(SpecData::new(ty)));
    }

    fn erase_spec(&mut self, path: &Path) {
        if self.base.has_spec(path) {
            self.overlay.insert(path.clone(), Patch::Tombstone);
        } else {
            // A spec that never reached the base needs no tombstone; dropping the
            // staged entry restores the (absent) base view.
            self.overlay.remove(path);
        }
    }

    fn set_field(&mut self, path: &Path, field: &str, value: Value) {
        // Ensure an overlay entry before the mutating match: a pre-existing base
        // spec gets an empty `Edited` patch on first touch (no field copy), and
        // a write to an absent spec is dropped (matching the eager backends).
        if !self.overlay.contains_key(path) {
            if self.base.has_spec(path) {
                self.overlay.insert(path.clone(), Patch::edited(HashSet::new()));
            } else {
                debug_assert!(false, "set_field on absent spec at {path}");
                return;
            }
        }
        match self.overlay.get_mut(path).expect("entry ensured above") {
            Patch::Created(spec) => spec.add(field, value),
            Patch::Edited { set, erased } => {
                erased.remove(field);
                match set.iter_mut().find(|(f, _)| f == field) {
                    Some(slot) => slot.1 = value,
                    None => set.push((field.to_owned(), value)),
                }
            }
            Patch::Tombstone => debug_assert!(false, "set_field on erased spec at {path}"),
        }
    }

    fn erase_field(&mut self, path: &Path, field: &str) {
        // Whether the base holds the field decides if the erase must outlive as a
        // tombstone; read it before borrowing the overlay mutably.
        let base_has_field = self.base.has_field(path, field);
        if !self.overlay.contains_key(path) {
            // First touch of a pre-existing spec: only a base field needs an
            // erased entry; a staged-only spec has nothing to erase.
            if base_has_field {
                let mut erased = HashSet::new();
                erased.insert(field.to_owned());
                self.overlay.insert(path.clone(), Patch::edited(erased));
            }
            return;
        }
        match self.overlay.get_mut(path).expect("entry present") {
            Patch::Created(spec) => {
                spec.remove(field);
            }
            Patch::Tombstone => {}
            Patch::Edited { set, erased } => {
                set.retain(|(f, _)| f != field);
                if base_has_field {
                    erased.insert(field.to_owned());
                }
            }
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

    /// Reads see the staged-over-base view while the base is left untouched
    /// until commit.
    #[test]
    fn cow_reads_through() {
        let mut base = Data::new();
        let a = path("/A").unwrap();
        base.create_spec(a.clone(), SpecType::Prim);
        base.spec_mut(&a).unwrap().add("kind", Value::Token("group".into()));

        let mut cow = CowData::new(base);
        assert!(cow.is_empty());
        assert!(cow.has_spec(&a));
        assert_eq!(cow.get_field(&a, "kind").unwrap().into_owned(), Value::token("group"));

        cow.set_field(&a, "kind", Value::token("component"));
        assert!(!cow.is_empty());
        assert_eq!(
            cow.get_field(&a, "kind").unwrap().into_owned(),
            Value::token("component")
        );
        // The base still holds the original opinion: the write only staged.
        let base = cow.into_inner();
        assert_eq!(base.get_field(&a, "kind").unwrap().into_owned(), Value::token("group"));
    }

    /// `commit` flushes the staged patch into the base — added specs, modified
    /// fields, and tombstoned removals alike.
    #[test]
    fn cow_commit_flushes() {
        let mut base = Data::new();
        let keep = path("/Keep").unwrap();
        let doomed = path("/Doomed").unwrap();
        base.create_spec(keep.clone(), SpecType::Prim);
        base.create_spec(doomed.clone(), SpecType::Prim);

        let mut cow = CowData::new(base);
        let fresh = path("/Fresh").unwrap();
        cow.create_spec(fresh.clone(), SpecType::Prim);
        cow.set_field(&keep, "kind", Value::token("group"));
        cow.erase_spec(&doomed);
        cow.commit();
        assert!(cow.is_empty());

        let base = cow.into_inner();
        assert!(base.has_spec(&fresh));
        assert!(!base.has_spec(&doomed));
        assert_eq!(
            base.get_field(&keep, "kind").unwrap().into_owned(),
            Value::token("group")
        );
    }

    /// `rollback` drops the staged patch, leaving the base exactly as it was.
    #[test]
    fn cow_rollback_restores() {
        let mut base = Data::new();
        let a = path("/A").unwrap();
        base.create_spec(a.clone(), SpecType::Prim);

        let mut cow = CowData::new(base);
        cow.create_spec(path("/B").unwrap(), SpecType::Prim);
        cow.erase_spec(&a);
        cow.rollback();

        assert!(cow.is_empty());
        assert!(cow.has_spec(&a));
        assert!(!cow.has_spec(&path("/B").unwrap()));
    }

    /// `spec_paths` is the base specs minus tombstones, plus staged additions,
    /// in sorted order.
    #[test]
    fn cow_spec_paths_merge() {
        let mut base = Data::new();
        base.create_spec(path("/B").unwrap(), SpecType::Prim);
        base.create_spec(path("/D").unwrap(), SpecType::Prim);

        let mut cow = CowData::new(base);
        cow.create_spec(path("/A").unwrap(), SpecType::Prim);
        cow.erase_spec(&path("/D").unwrap());

        let paths = cow.spec_paths();
        let paths: Vec<&str> = paths.iter().map(|p| p.as_str()).collect();
        assert_eq!(paths, vec!["/A", "/B"]);
    }

    /// Editing one field of a pre-existing spec stages only that field;
    /// untouched fields still read through to the base, and `list_fields`
    /// reports the base order with the new field appended. Erasing a base field
    /// hides it from reads while leaving siblings intact.
    #[test]
    fn cow_field_granular() {
        let mut base = Data::new();
        let a = path("/A").unwrap();
        base.create_spec(a.clone(), SpecType::Prim);
        let spec = base.spec_mut(&a).unwrap();
        spec.add("kind", Value::Token("group".into()));
        spec.add("doc", Value::String("hi".into()));

        let mut cow = CowData::new(base);
        cow.set_field(&a, "kind", Value::token("component"));
        cow.set_field(&a, "custom", Value::Bool(true));
        cow.erase_field(&a, "doc");

        // Touched field staged, untouched-but-present field reads through base,
        // erased field hidden, new field visible.
        assert_eq!(
            cow.get_field(&a, "kind").unwrap().into_owned(),
            Value::token("component")
        );
        assert_eq!(cow.get_field(&a, "custom").unwrap().into_owned(), Value::Bool(true));
        assert!(!cow.has_field(&a, "doc"));
        assert_eq!(cow.list_fields(&a).unwrap(), vec!["kind", "custom"]);

        cow.commit();
        let base = cow.into_inner();
        assert_eq!(
            base.get_field(&a, "kind").unwrap().into_owned(),
            Value::token("component")
        );
        assert_eq!(base.get_field(&a, "custom").unwrap().into_owned(), Value::Bool(true));
        assert!(!base.has_field(&a, "doc"));
        assert_eq!(base.list_fields(&a).unwrap(), vec!["kind", "custom"]);
    }
}
