//! Mutable scene description container.
//!
//! Parallels C++ `SdfData`. A flat map from [`Path`] to [`SpecData`] that can
//! be populated programmatically and then handed to a writer.

use std::{borrow::Cow, collections::HashSet, sync::Arc};

use crate::sdf::{self, FieldKey, Path, PathMap, SpecData, SpecType, TimeSampleMap};
use crate::vt::{self, Value};

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
pub trait AbstractData: Send + Sync {
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

    /// Returns the times of the samples in the `timeSamples` field at `path`,
    /// ordered, or none if the field holds no samples.
    ///
    /// The default reads the whole field; a format that decodes the sample
    /// times on their own overrides it. C++
    /// `SdfAbstractData::ListTimeSamplesForPath`.
    fn sample_times(&self, path: &Path) -> Result<Vec<f64>, DataError> {
        field_times(self, path)
    }

    /// Returns the times of the two samples in the `timeSamples` field at
    /// `path` that bracket `time`, or `None` if the field holds no samples.
    ///
    /// The pair is the one [`sdf::bracketing_time_samples`] finds among
    /// [`sample_times`](Self::sample_times). C++
    /// `SdfAbstractData::GetBracketingTimeSamplesForPath`.
    fn bracketing_time_samples(&self, path: &Path, time: f64) -> Result<Option<(f64, f64)>, DataError> {
        Ok(sdf::bracketing_time_samples(&self.sample_times(path)?, time))
    }

    /// Returns the sample authored at exactly `time` in the `timeSamples`
    /// field at `path`, or `None` if there is none.
    ///
    /// The default reads the whole field; a format that decodes samples one
    /// by one overrides it. C++ `SdfAbstractData::QueryTimeSample`.
    fn query_time_sample(&self, path: &Path, time: f64) -> Result<Option<Cow<'_, Value>>, DataError> {
        field_sample(self, path, time)
    }

    /// Returns the kind of the sample authored at exactly `time` in the
    /// `timeSamples` field at `path`, or `None` if there is none.
    ///
    /// The default decodes the sample. A format that stores each sample's
    /// type answers from it. C++ `SdfAbstractData::QueryTimeSampleTypeid`.
    fn time_sample_kind(&self, path: &Path, time: f64) -> Result<Option<vt::ValueKind>, DataError> {
        Ok(self
            .query_time_sample(path, time)?
            .map(|value| vt::ValueKind::from(value.as_ref())))
    }

    /// Returns the kind of each sample in the `timeSamples` field at `path`,
    /// in the order of [`sample_times`](Self::sample_times), or none if the
    /// field holds no samples: one read of the field however many samples it
    /// holds.
    ///
    /// The default reads the whole field once. A format that stores each
    /// sample's type answers from those, decoding no value. C++ has no query
    /// for every kind at once; it asks `QueryTimeSampleTypeid` of one sample.
    fn sample_kinds(&self, path: &Path) -> Result<Vec<vt::ValueKind>, DataError> {
        field_kinds(self, path)
    }

    /// Returns the number of samples in the `timeSamples` field at `path`,
    /// zero if the field holds no samples.
    ///
    /// Counts [`sample_times`](Self::sample_times). C++
    /// `SdfAbstractData::GetNumTimeSamplesForPath`.
    fn num_time_samples(&self, path: &Path) -> Result<usize, DataError> {
        Ok(self.sample_times(path)?.len())
    }

    /// Returns the `timeSamples` field at `path` as a read at `time` needs
    /// it: a map holding at least the samples that bracket `time`, or
    /// whatever else the field holds. `None` if the field is not authored.
    ///
    /// Interpolating the result at `time` gives what interpolating the whole
    /// field does. The default returns the whole field, which costs nothing
    /// where the data lends it; a format that decodes samples one by one
    /// overrides it to decode only the bracketing pair.
    fn bracketing_samples(&self, path: &Path, _time: f64) -> Result<Option<Cow<'_, Value>>, DataError> {
        self.try_field(path, FieldKey::TimeSamples.as_str())
    }

    /// Returns the value for a field, erroring if not authored.
    ///
    /// Use [`AbstractData::try_field`] when absence is an expected condition.
    fn field(&self, path: &Path, field: &str) -> Result<Cow<'_, Value>, DataError> {
        self.try_field(path, field)?.ok_or_else(|| DataError::Missing {
            path: path.clone(),
            field: field.to_owned(),
        })
    }

    /// The kind of the value of `field` at `path`, or `None` if not authored.
    /// Mirrors C++ `SdfAbstractData::GetTypeid`.
    ///
    /// The default decodes the value. A backend that stores each value's type
    /// may answer from it without decoding, and then names a kind even for a
    /// value that fails to decode.
    fn field_kind(&self, path: &Path, field: &str) -> Result<Option<vt::ValueKind>, DataError> {
        Ok(self.try_field(path, field)?.map(|value| vt::ValueKind::from(&*value)))
    }

    /// Returns the field names for a given path in authored order.
    fn list_fields(&self, path: &Path) -> Option<Vec<String>>;

    /// Which of `fields` the spec at `path` authors: bit `i` is set when
    /// `fields[i]` is, for up to 32 names. Zero when there is no spec. One
    /// query asks about several fields of a spec at once, as composition does
    /// to learn which arcs a site authors.
    fn field_mask(&self, path: &Path, fields: &[&str]) -> u32 {
        mask_of(fields, |field| self.has_field(path, field))
    }

    /// Returns every authored path, sorted lexicographically.
    ///
    /// The order is deterministic and stable across repeated calls. Emitters
    /// rely on this for reproducible output.
    fn spec_paths(&self) -> Vec<Path>;

    /// Creates an empty spec of type `ty` at `path`, replacing any existing
    /// spec there. Mirrors C++ `SdfAbstractData::CreateSpec`. Fields are
    /// authored separately via [`set_field`](Self::set_field).
    ///
    /// Only the spec record is written. The caller also lists the new spec in
    /// its parent's children field (`primChildren`, `propertyChildren` and
    /// the like), which is how name enumeration, the text writer and
    /// composition find it. The typed spec constructors
    /// ([`PrimSpec::new`](crate::sdf::PrimSpec::new) and friends) do both.
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
/// [`AbstractData::field`].
///
/// Eager backends ([`Data`], the text reader) never fail a field read; only a
/// lazy backend that decodes on demand — the `.usdc` crate reader — can error,
/// when an authored value fails to decode or decompress.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum DataError {
    /// A backend failed to decode or decompress an authored field value.
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

    /// [`field`](AbstractData::field) was asked for a field that is not
    /// authored on the spec.
    #[error("no field {field:?} at {path}")]
    Missing {
        /// The spec path that was queried.
        path: Path,
        /// The name of the absent field.
        field: String,
    },

    /// A backend listed a path in [`spec_paths`](AbstractData::spec_paths)
    /// but reports no spec there — an [`AbstractData`] contract violation.
    #[error("path {path} reported by spec_paths() has no spec")]
    MissingSpec {
        /// The path with no spec behind it.
        path: Path,
    },
}

/// In-memory mutable layer data.
#[derive(Default, Debug, Clone)]
pub struct Data {
    specs: PathMap<SpecData>,
}

impl Data {
    /// Create an empty container.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a container holding the pseudo-root alone, the content of a
    /// layer with nothing authored.
    pub fn rooted() -> Self {
        let mut data = Self::new();
        data.create_spec(Path::abs_root(), SpecType::PseudoRoot);
        data
    }

    /// Build a container from a map of pre-parsed spec records, the form a
    /// reader (e.g. the usda parser) produces.
    pub fn from_specs(specs: PathMap<SpecData>) -> Self {
        Self { specs }
    }

    /// Copy every spec and field from `src` into a new `Data`.
    ///
    /// A backend whose `spec_paths` reports a path it then holds no spec for
    /// violates the [`AbstractData`] contract; the copy surfaces that as
    /// [`DataError::MissingSpec`] rather than panicking.
    pub fn from_abstract(src: &dyn AbstractData) -> Result<Self, DataError> {
        let mut out = Self::new();
        for path in src.spec_paths() {
            let ty = src
                .spec_type(&path)
                .ok_or_else(|| DataError::MissingSpec { path: path.clone() })?;
            let spec = out.create_spec(path.clone(), ty);
            if let Some(fields) = src.list_fields(&path) {
                for name in fields {
                    spec.add(&name, src.field(&path, &name)?.into_owned());
                }
            }
        }
        Ok(out)
    }

    /// Insert an empty spec record at `path`, returning it for field authoring.
    /// Replaces any existing spec. The convenience counterpart to the
    /// field-level [`AbstractData::create_spec`], which returns nothing because
    /// the trait can't name `SpecData`. Takes an owned, already-validated
    /// [`Path`], like the trait method; parse text with [`Path::new`] at the
    /// boundary.
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

    fn field_mask(&self, path: &Path, fields: &[&str]) -> u32 {
        self.specs
            .get(path)
            .map_or(0, |spec| mask_of(fields, |field| spec.contains(field)))
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

    fn sample_times(&self, path: &Path) -> Result<Vec<f64>, DataError> {
        (**self).sample_times(path)
    }

    fn bracketing_time_samples(&self, path: &Path, time: f64) -> Result<Option<(f64, f64)>, DataError> {
        (**self).bracketing_time_samples(path, time)
    }

    fn query_time_sample(&self, path: &Path, time: f64) -> Result<Option<Cow<'_, Value>>, DataError> {
        (**self).query_time_sample(path, time)
    }

    fn time_sample_kind(&self, path: &Path, time: f64) -> Result<Option<vt::ValueKind>, DataError> {
        (**self).time_sample_kind(path, time)
    }

    fn sample_kinds(&self, path: &Path) -> Result<Vec<vt::ValueKind>, DataError> {
        (**self).sample_kinds(path)
    }

    fn bracketing_samples(&self, path: &Path, time: f64) -> Result<Option<Cow<'_, Value>>, DataError> {
        (**self).bracketing_samples(path, time)
    }

    fn field_kind(&self, path: &Path, field: &str) -> Result<Option<vt::ValueKind>, DataError> {
        (**self).field_kind(path, field)
    }

    fn list_fields(&self, path: &Path) -> Option<Vec<String>> {
        (**self).list_fields(path)
    }

    fn field_mask(&self, path: &Path, fields: &[&str]) -> u32 {
        (**self).field_mask(path, fields)
    }

    fn spec_paths(&self) -> Vec<Path> {
        (**self).spec_paths()
    }

    fn create_spec(&mut self, path: Path, ty: SpecType) {
        (**self).create_spec(path, ty);
    }

    fn erase_spec(&mut self, path: &Path) {
        (**self).erase_spec(path);
    }

    fn set_field(&mut self, path: &Path, field: &str, value: Value) {
        (**self).set_field(path, field, value);
    }

    fn erase_field(&mut self, path: &Path, field: &str) {
        (**self).erase_field(path, field);
    }
}

/// Data shared by everyone holding it, which a write copies first: each
/// mutator goes through [`Arc::make_mut`], so the others keep the data as it
/// was. A write that changes nothing copies nothing.
///
/// TODO(perf): the copy is of the whole data, every spec and value. Specs
/// held each behind its own `Arc` (or a persistent map) would let a write
/// copy only the specs it touches.
impl<T: AbstractData + Clone> AbstractData for Arc<T> {
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

    fn sample_times(&self, path: &Path) -> Result<Vec<f64>, DataError> {
        (**self).sample_times(path)
    }

    fn bracketing_time_samples(&self, path: &Path, time: f64) -> Result<Option<(f64, f64)>, DataError> {
        (**self).bracketing_time_samples(path, time)
    }

    fn query_time_sample(&self, path: &Path, time: f64) -> Result<Option<Cow<'_, Value>>, DataError> {
        (**self).query_time_sample(path, time)
    }

    fn time_sample_kind(&self, path: &Path, time: f64) -> Result<Option<vt::ValueKind>, DataError> {
        (**self).time_sample_kind(path, time)
    }

    fn sample_kinds(&self, path: &Path) -> Result<Vec<vt::ValueKind>, DataError> {
        (**self).sample_kinds(path)
    }

    fn bracketing_samples(&self, path: &Path, time: f64) -> Result<Option<Cow<'_, Value>>, DataError> {
        (**self).bracketing_samples(path, time)
    }

    fn field_kind(&self, path: &Path, field: &str) -> Result<Option<vt::ValueKind>, DataError> {
        (**self).field_kind(path, field)
    }

    fn list_fields(&self, path: &Path) -> Option<Vec<String>> {
        (**self).list_fields(path)
    }

    fn field_mask(&self, path: &Path, fields: &[&str]) -> u32 {
        (**self).field_mask(path, fields)
    }

    fn spec_paths(&self) -> Vec<Path> {
        (**self).spec_paths()
    }

    fn create_spec(&mut self, path: Path, ty: SpecType) {
        Arc::make_mut(self).create_spec(path, ty);
    }

    fn erase_spec(&mut self, path: &Path) {
        if self.has_spec(path) {
            Arc::make_mut(self).erase_spec(path);
        }
    }

    fn set_field(&mut self, path: &Path, field: &str, value: Value) {
        if self.has_spec(path) {
            Arc::make_mut(self).set_field(path, field, value);
        }
    }

    fn erase_field(&mut self, path: &Path, field: &str) {
        if self.has_field(path, field) {
            Arc::make_mut(self).erase_field(path, field);
        }
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
    overlay: PathMap<Patch>,
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
    Created {
        /// The spec's type and every field it holds.
        spec: SpecData,
        /// Fields a write this transaction changed from the value the spec
        /// held, or an erase removed, whatever they end holding, as
        /// [`Edited`](Patch::Edited) records them, those of a spec the
        /// create replaced among them.
        changed: HashSet<String>,
    },
    /// A pre-existing base spec erased in the overlay.
    Tombstone {
        /// Fields a write changed before the erase, as the patch it replaced
        /// recorded them.
        changed: HashSet<String>,
    },
    /// A pre-existing base spec with field-level edits staged over it. Only the
    /// touched fields are stored; untouched fields read through to the base.
    Edited {
        /// Fields set or overwritten this transaction, in first-touch order.
        /// Disjoint from `erased`.
        set: Vec<(String, Value)>,
        /// Fields removed from the base this transaction. Disjoint from `set`.
        erased: HashSet<String>,
        /// Fields a write this transaction changed from the value it staged
        /// over, or an erase removed, whatever they end holding. C++
        /// `SdfLayer::SetField` records a change for each write that changes
        /// a field, so one changed and then put back still reports one. The
        /// first write of a field is compared with the base once, at commit
        /// ([`ChangeList::from_overlay`](super::ChangeList::from_overlay)).
        changed: HashSet<String>,
        /// The `primChildren` and `propertyChildren` lists a write this
        /// transaction permuted, the same names in another order: C++ raises
        /// a reorder for each such write, whatever the list ends holding.
        reordered: HashSet<String>,
    },
}

impl Patch {
    /// The fields a write changed while this patch was staged over `base`'s
    /// spec at `path`, which a patch replacing it carries on. A first write
    /// over a base spec, whose change is otherwise found at commit, counts
    /// when it staged another value than the base holds; every field of a
    /// created spec was written into it.
    fn into_changed<D: AbstractData + ?Sized>(self, base: &D, path: &Path) -> HashSet<String> {
        match self {
            Patch::Created { spec, mut changed } => {
                changed.extend(spec.fields.into_iter().map(|(field, _)| field));
                changed
            }
            Patch::Tombstone { changed } => changed,
            Patch::Edited { set, mut changed, .. } => {
                let moved = set
                    .into_iter()
                    .filter(|(field, value)| !matches!(base.try_field(path, field), Ok(Some(held)) if *held == *value));
                changed.extend(moved.map(|(field, _)| field));
                changed
            }
        }
    }

    /// A fresh field-level edit over a pre-existing base spec, with no staged
    /// field writes and the given erased fields, each changed by its erase.
    fn edited(erased: HashSet<String>) -> Self {
        Patch::Edited {
            set: Vec::new(),
            changed: erased.clone(),
            erased,
            reordered: HashSet::new(),
        }
    }
}

impl<T: AbstractData> CowData<T> {
    /// Wrap `base` with an empty overlay.
    pub fn new(base: T) -> Self {
        Self {
            base,
            overlay: PathMap::default(),
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
                Patch::Created { spec, .. } => {
                    self.base.create_spec(path.clone(), spec.ty);
                    for (field, value) in spec.fields {
                        self.base.set_field(&path, &field, value);
                    }
                }
                Patch::Tombstone { .. } => self.base.erase_spec(&path),
                Patch::Edited { set, erased, .. } => {
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
    pub fn overlay(&self) -> &PathMap<Patch> {
        &self.overlay
    }

    /// Where a read of `field` at `path` finds its answer.
    fn staged_field(&self, path: &Path, field: &str) -> Staged<'_> {
        let Some(patch) = self.staged(path) else {
            return Staged::Base;
        };
        match patch {
            Patch::Created { spec, .. } => Staged::Overlay(spec.get(field)),
            Patch::Tombstone { .. } => Staged::Overlay(None),
            Patch::Edited { erased, .. } if erased.contains(field) => Staged::Overlay(None),
            Patch::Edited { set, .. } => match set.iter().find(|(f, _)| f == field) {
                Some((_, value)) => Staged::Overlay(Some(value)),
                None => Staged::Base,
            },
        }
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
            Some(Patch::Tombstone { .. }) => false,
            // `Edited` exists only over a base spec, so the spec is present.
            Some(_) => true,
            None => self.base.has_spec(path),
        }
    }

    fn has_field(&self, path: &Path, field: &str) -> bool {
        match self.staged_field(path, field) {
            Staged::Overlay(value) => value.is_some(),
            Staged::Base => self.base.has_field(path, field),
        }
    }

    fn spec_type(&self, path: &Path) -> Option<SpecType> {
        match self.staged(path) {
            Some(Patch::Created { spec, .. }) => Some(spec.ty),
            Some(Patch::Tombstone { .. }) => None,
            Some(Patch::Edited { .. }) | None => self.base.spec_type(path),
        }
    }

    fn try_field(&self, path: &Path, field: &str) -> Result<Option<Cow<'_, Value>>, DataError> {
        match self.staged_field(path, field) {
            Staged::Overlay(value) => Ok(value.map(Cow::Borrowed)),
            Staged::Base => self.base.try_field(path, field),
        }
    }

    fn sample_times(&self, path: &Path) -> Result<Vec<f64>, DataError> {
        match self.staged_field(path, FieldKey::TimeSamples.as_str()) {
            Staged::Overlay(_) => field_times(self, path),
            Staged::Base => self.base.sample_times(path),
        }
    }

    fn query_time_sample(&self, path: &Path, time: f64) -> Result<Option<Cow<'_, Value>>, DataError> {
        match self.staged_field(path, FieldKey::TimeSamples.as_str()) {
            Staged::Overlay(_) => field_sample(self, path, time),
            Staged::Base => self.base.query_time_sample(path, time),
        }
    }

    fn time_sample_kind(&self, path: &Path, time: f64) -> Result<Option<vt::ValueKind>, DataError> {
        match self.staged_field(path, FieldKey::TimeSamples.as_str()) {
            Staged::Overlay(_) => Ok(field_sample(self, path, time)?.map(|value| vt::ValueKind::from(value.as_ref()))),
            Staged::Base => self.base.time_sample_kind(path, time),
        }
    }

    fn sample_kinds(&self, path: &Path) -> Result<Vec<vt::ValueKind>, DataError> {
        match self.staged_field(path, FieldKey::TimeSamples.as_str()) {
            Staged::Overlay(_) => field_kinds(self, path),
            Staged::Base => self.base.sample_kinds(path),
        }
    }

    fn bracketing_samples(&self, path: &Path, time: f64) -> Result<Option<Cow<'_, Value>>, DataError> {
        match self.staged_field(path, FieldKey::TimeSamples.as_str()) {
            Staged::Overlay(value) => Ok(value.map(Cow::Borrowed)),
            Staged::Base => self.base.bracketing_samples(path, time),
        }
    }

    fn field_kind(&self, path: &Path, field: &str) -> Result<Option<vt::ValueKind>, DataError> {
        match self.staged_field(path, field) {
            Staged::Overlay(value) => Ok(value.map(vt::ValueKind::from)),
            Staged::Base => self.base.field_kind(path, field),
        }
    }

    fn list_fields(&self, path: &Path) -> Option<Vec<String>> {
        match self.staged(path) {
            Some(Patch::Created { spec, .. }) => Some(spec.fields.iter().map(|(k, _)| k.clone()).collect()),
            Some(Patch::Tombstone { .. }) => None,
            Some(Patch::Edited { set, erased, .. }) => {
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
            .filter(|p| !matches!(self.overlay.get(p), Some(Patch::Tombstone { .. })))
            .collect();
        for (path, patch) in &self.overlay {
            if matches!(patch, Patch::Created { .. }) && !self.base.has_spec(path) {
                paths.push(path.clone());
            }
        }
        paths.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        paths
    }

    fn create_spec(&mut self, path: Path, ty: SpecType) {
        let changed = match self.overlay.remove(&path) {
            Some(patch) => patch.into_changed(&self.base, &path),
            None => HashSet::new(),
        };
        self.overlay.insert(
            path,
            Patch::Created {
                spec: SpecData::new(ty),
                changed,
            },
        );
    }

    fn erase_spec(&mut self, path: &Path) {
        if self.base.has_spec(path) {
            let changed = match self.overlay.remove(path) {
                Some(patch) => patch.into_changed(&self.base, path),
                None => HashSet::new(),
            };
            self.overlay.insert(path.clone(), Patch::Tombstone { changed });
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
        // A child-name list a write permutes raises a reorder whatever the list
        // ends holding, so its write reads the list it replaces, from the base
        // on a first write. Every other field is compared with the base only
        // at commit.
        //
        // TODO(perf): each write of a child-name list that does not only
        // append hashes both lists until one write permutes it; a batch
        // adding many children one at a time pays it per child.
        let permutes = sdf::is_children_field(field)
            && matches!(self.overlay.get(path), Some(Patch::Edited { reordered, .. }) if !reordered.contains(field))
            && matches!(self.try_field(path, field), Ok(Some(held)) if super::change::permutes(field, &held, &value));
        match self.overlay.get_mut(path).expect("entry ensured above") {
            Patch::Created { spec, changed } => {
                if !changed.contains(field) && spec.get(field).is_some_and(|held| *held != value) {
                    changed.insert(field.to_owned());
                }
                spec.add(field, value);
            }
            Patch::Edited {
                set,
                erased,
                changed,
                reordered,
            } => {
                if permutes {
                    reordered.insert(field.to_owned());
                }
                erased.remove(field);
                match set.iter_mut().find(|(f, _)| f == field) {
                    Some(slot) => {
                        if !changed.contains(field) && slot.1 != value {
                            changed.insert(field.to_owned());
                        }
                        slot.1 = value;
                    }
                    None => set.push((field.to_owned(), value)),
                }
            }
            Patch::Tombstone { .. } => debug_assert!(false, "set_field on erased spec at {path}"),
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
            Patch::Created { spec, changed } => {
                if spec.get(field).is_some() {
                    changed.insert(field.to_owned());
                }
                spec.remove(field);
            }
            Patch::Tombstone { .. } => {}
            Patch::Edited {
                set, erased, changed, ..
            } => {
                // The erase changes the field when it removes a staged value
                // or one the base holds that no earlier erase removed.
                let staged = set.iter().any(|(f, _)| f == field);
                if staged || (base_has_field && !erased.contains(field)) {
                    changed.insert(field.to_owned());
                }
                set.retain(|(f, _)| f != field);
                if base_has_field {
                    erased.insert(field.to_owned());
                }
            }
        }
    }
}

/// Where [`CowData`] reads a field from.
enum Staged<'a> {
    /// The overlay decides: the value it stages, or `None` when it removes
    /// the field.
    Overlay(Option<&'a Value>),
    /// The overlay leaves the field to the base.
    Base,
}

/// The [`AbstractData::field_mask`] of `fields`, given which one a spec
/// authors.
pub(crate) fn mask_of(fields: &[&str], mut authors: impl FnMut(&str) -> bool) -> u32 {
    fields
        .iter()
        .take(32)
        .enumerate()
        .filter(|&(_, field)| authors(field))
        .fold(0, |mask, (bit, _)| mask | 1 << bit)
}

/// Reads the sample times of the `timeSamples` field at `path`, read whole.
pub(crate) fn field_times<D: AbstractData + ?Sized>(data: &D, path: &Path) -> Result<Vec<f64>, DataError> {
    Ok(match data.try_field(path, FieldKey::TimeSamples.as_str())?.as_deref() {
        Some(Value::TimeSamples(samples)) => samples.iter().map(|(t, _)| *t).collect(),
        _ => Vec::new(),
    })
}

/// The kind of each sample in the `timeSamples` field at `path`, in time
/// order, read whole once.
pub(crate) fn field_kinds<D: AbstractData + ?Sized>(data: &D, path: &Path) -> Result<Vec<vt::ValueKind>, DataError> {
    Ok(match data.try_field(path, FieldKey::TimeSamples.as_str())?.as_deref() {
        Some(Value::TimeSamples(samples)) => samples.iter().map(|(_, value)| vt::ValueKind::from(value)).collect(),
        _ => Vec::new(),
    })
}

/// Finds the sample at exactly `time` in the `timeSamples` field at `path`,
/// read whole.
pub(crate) fn field_sample<'a, D: AbstractData + ?Sized>(
    data: &'a D,
    path: &Path,
    time: f64,
) -> Result<Option<Cow<'a, Value>>, DataError> {
    let find = |samples: &TimeSampleMap| {
        samples
            .binary_search_by(|(t, _)| sdf::compare_sample_times(*t, time))
            .ok()
    };
    Ok(match data.try_field(path, FieldKey::TimeSamples.as_str())? {
        Some(Cow::Borrowed(Value::TimeSamples(samples))) => find(samples).map(|i| Cow::Borrowed(&samples[i].1)),
        Some(Cow::Owned(Value::TimeSamples(mut samples))) => {
            find(&samples).map(|i| Cow::Owned(samples.swap_remove(i).1))
        }
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::path;

    #[test]
    fn sample_times_kinds() -> Result<(), DataError> {
        let mut data = Data::new();
        let (x, y) = (path("/A.x").unwrap(), path("/A.y").unwrap());
        for p in [&x, &y] {
            data.create_spec(p.clone(), SpecType::Attribute);
        }
        let samples = vec![(0.0, Value::ValueBlock), (10.0, Value::Double(2.0))];
        data.set_field(&x, "timeSamples", Value::TimeSamples(samples));
        data.set_field(&y, "timeSamples", Value::ValueBlock);

        assert_eq!(data.sample_times(&x)?, [0.0, 10.0]);
        assert_eq!(data.time_sample_kind(&x, 0.0)?, Some(vt::ValueKind::ValueBlock));
        assert_eq!(data.time_sample_kind(&x, 10.0)?, Some(vt::ValueKind::Double));
        assert_eq!(data.time_sample_kind(&x, 5.0)?, None);
        assert_eq!(
            data.sample_kinds(&x)?,
            [vt::ValueKind::ValueBlock, vt::ValueKind::Double]
        );
        assert!(data.sample_times(&y)?.is_empty());
        assert!(data.sample_kinds(&y)?.is_empty());
        Ok(())
    }

    #[test]
    fn time_samples_whole() -> Result<(), DataError> {
        let mut data = Data::new();
        let (x, y, z) = (path("/A.x").unwrap(), path("/A.y").unwrap(), path("/A.z").unwrap());
        for p in [&x, &y, &z] {
            data.create_spec(p.clone(), SpecType::Attribute);
        }
        let samples = vec![(0.0, Value::Double(1.0)), (10.0, Value::Double(2.0))];
        data.set_field(&x, "timeSamples", Value::TimeSamples(samples));
        data.set_field(&y, "timeSamples", Value::ValueBlock);

        assert_eq!(data.bracketing_time_samples(&x, 5.0)?, Some((0.0, 10.0)));
        assert_eq!(data.query_time_sample(&x, 10.0)?.as_deref(), Some(&Value::Double(2.0)));
        assert_eq!(data.query_time_sample(&x, 5.0)?, None);
        assert_eq!(data.bracketing_time_samples(&y, 5.0)?, None);
        assert_eq!(data.bracketing_time_samples(&z, 5.0)?, None);
        assert_eq!(data.query_time_sample(&z, 0.0)?, None);
        // A read at a time is lent the whole field, a block included.
        let whole = data.bracketing_samples(&x, 5.0)?.expect("x is authored");
        assert!(matches!(whole, Cow::Borrowed(Value::TimeSamples(samples)) if samples.len() == 2));
        assert_eq!(data.bracketing_samples(&y, 5.0)?.as_deref(), Some(&Value::ValueBlock));
        assert_eq!(data.bracketing_samples(&z, 5.0)?, None);
        assert_eq!([&x, &y, &z].map(|p| data.num_time_samples(p).unwrap()), [2, 0, 0]);
        Ok(())
    }

    /// Data shared across threads: a layer on each reads it.
    #[test]
    fn data_crosses_threads() {
        fn shared<T: Send + Sync>() {}
        shared::<Data>();
    }

    /// A write to shared data copies it, and leaves the other holder's as
    /// it was.
    #[test]
    fn shared_write_copies() {
        let root = path("/Root").unwrap();
        let mut data = Data::new();
        data.create_spec(root.clone(), SpecType::Prim);
        let original = Arc::new(data);
        let mut copy = Arc::clone(&original);
        copy.set_field(&root, "comment", Value::from("edited"));
        assert!(!Arc::ptr_eq(&original, &copy));
        assert!(!original.has_field(&root, "comment"));
        assert!(copy.has_field(&root, "comment"));
    }

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

        let value = data.field(&root, "primChildren").unwrap().into_owned();
        assert_eq!(value, Value::TokenVec(vec!["child".into()]));
    }

    /// Bit `i` of the mask stands for the `i`th field asked about.
    #[test]
    fn field_mask_bits() {
        let mut data = Data::new();
        let root = path("/Root").unwrap();
        data.create_spec(root.clone(), SpecType::Prim);
        data.spec_mut(&root)
            .unwrap()
            .add("references", Value::TokenVec(Vec::new()));
        data.spec_mut(&root)
            .unwrap()
            .add("specializes", Value::TokenVec(Vec::new()));

        let fields = ["references", "payload", "specializes"];
        assert_eq!(data.field_mask(&root, &fields), 0b101);
        assert_eq!(data.field_mask(&path("/Other").unwrap(), &fields), 0);
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
        assert_eq!(copy.field(&child, "specifier").unwrap().into_owned(), Value::Int(0));
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
        assert_eq!(cow.field(&a, "kind").unwrap().into_owned(), Value::token("group"));

        cow.set_field(&a, "kind", Value::token("component"));
        assert!(!cow.is_empty());
        assert_eq!(cow.field(&a, "kind").unwrap().into_owned(), Value::token("component"));
        // The base still holds the original opinion: the write only staged.
        let base = cow.into_inner();
        assert_eq!(base.field(&a, "kind").unwrap().into_owned(), Value::token("group"));
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
        assert_eq!(base.field(&keep, "kind").unwrap().into_owned(), Value::token("group"));
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
        assert_eq!(cow.field(&a, "kind").unwrap().into_owned(), Value::token("component"));
        assert_eq!(cow.field(&a, "custom").unwrap().into_owned(), Value::Bool(true));
        assert!(!cow.has_field(&a, "doc"));
        assert_eq!(cow.list_fields(&a).unwrap(), vec!["kind", "custom"]);

        cow.commit();
        let base = cow.into_inner();
        assert_eq!(base.field(&a, "kind").unwrap().into_owned(), Value::token("component"));
        assert_eq!(base.field(&a, "custom").unwrap().into_owned(), Value::Bool(true));
        assert!(!base.has_field(&a, "doc"));
        assert_eq!(base.list_fields(&a).unwrap(), vec!["kind", "custom"]);
    }
}
