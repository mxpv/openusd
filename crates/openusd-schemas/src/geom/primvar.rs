//! A primvar: a `primvars:` attribute read together with the metadata and the
//! indices that say how its values lie on the geometry (C++ `UsdGeomPrimvar`).

use openusd::{Error, Result};
use openusd::{gf, sdf, tf, usd};

use super::{Interpolation, PRIMVARS_NAMESPACE, tokens};
use crate::{PrimvarIndexError, SchemaError};

/// A primvar: an attribute in the `primvars:` namespace, with the
/// `interpolation` and `elementSize` that lay its values out over a prim and
/// the `<name>:indices` attribute that may index them (C++ `UsdGeomPrimvar`).
///
/// The view holds an attribute whose name is a primvar's, whether or not
/// anything defines it: [`attribute`](Self::attribute) reaches the handle for
/// what the attribute itself answers, such as
/// [`is_defined`](usd::Attribute::is_defined) and
/// [`has_authored_value`](usd::Attribute::has_authored_value).
///
/// Values read through [`get_at`](Self::get_at) as they are authored, and
/// through [`compute_flattened`](Self::compute_flattened) with the indices
/// applied. The interpolation's element count applies to the indices of an
/// indexed primvar, not to its values.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Primvar {
    attribute: usd::Attribute,
}

impl Primvar {
    /// Whether `name` is an attribute name a primvar can have: one in the
    /// `primvars:` namespace that does not end in `:indices` (C++
    /// `UsdGeomPrimvar::IsValidPrimvarName`).
    pub fn is_valid_primvar_name(name: &str) -> bool {
        name.starts_with(PRIMVARS_NAMESPACE) && !name.ends_with(INDICES_SUFFIX)
    }

    /// Wrap `attribute` when its name is a primvar's (C++
    /// `UsdGeomPrimvar::IsPrimvar`, without asking whether anything defines
    /// the attribute).
    pub fn from_attribute(attribute: usd::Attribute) -> Option<Self> {
        Self::is_valid_primvar_name(attribute.name()).then_some(Self { attribute })
    }

    /// Wrap an attribute whose name the caller built as a primvar's.
    pub(crate) fn new(attribute: usd::Attribute) -> Self {
        Self { attribute }
    }

    /// The underlying composed USD attribute.
    pub fn attribute(&self) -> &usd::Attribute {
        &self.attribute
    }

    /// Consume this view and return its underlying USD attribute.
    pub fn into_attribute(self) -> usd::Attribute {
        self.attribute
    }

    /// The primvar's name, with the `primvars:` namespace stripped (C++
    /// `GetPrimvarName`): `st` for `primvars:st`, `skel:jointWeights` for
    /// `primvars:skel:jointWeights`.
    pub fn primvar_name(&self) -> &str {
        self.attribute
            .name()
            .strip_prefix(PRIMVARS_NAMESPACE)
            .unwrap_or_default()
    }

    /// How the primvar's values lie on the geometry (C++ `GetInterpolation`),
    /// [`Interpolation::Constant`] where none is authored.
    ///
    /// An authored token that names no interpolation is an error.
    pub fn interpolation(&self) -> Result<Interpolation> {
        Ok(self
            .attribute
            .get_metadata::<Interpolation>(tokens::INTERPOLATION)?
            .unwrap_or_default())
    }

    /// Author the primvar's `interpolation` (C++ `SetInterpolation`).
    pub fn set_interpolation(self, interpolation: Interpolation) -> Result<Self, usd::StageAuthoringError> {
        Ok(Self {
            attribute: self.attribute.set_metadata(tokens::INTERPOLATION, interpolation)?,
        })
    }

    /// Whether a layer authors the primvar's `interpolation` (C++
    /// `HasAuthoredInterpolation`).
    pub fn has_authored_interpolation(&self) -> Result<bool> {
        self.attribute.has_authored_metadata(tokens::INTERPOLATION)
    }

    /// Whether the primvar's `interpolation` token is `constant`, the one
    /// interpolation that inherits down namespace. An unauthored one is, and
    /// a token that names no interpolation is not.
    pub(super) fn is_constant(&self) -> Result<bool> {
        Ok(self
            .attribute
            .get_metadata::<tf::Token>(tokens::INTERPOLATION)?
            .is_none_or(|token| token == tokens::CONSTANT))
    }

    /// How many consecutive values make up one element of the primvar (C++
    /// `GetElementSize`), 1 where none is authored: 9 for the coefficients of
    /// a spherical harmonic stored in a `float[]`.
    pub fn element_size(&self) -> Result<i32> {
        Ok(self.attribute.get_metadata::<i32>(tokens::ELEMENT_SIZE)?.unwrap_or(1))
    }

    /// Author the primvar's `elementSize` (C++ `SetElementSize`). A size below
    /// one is [`SchemaError::InvalidElementSize`], and nothing is authored.
    pub fn set_element_size(self, element_size: i32) -> Result<Self, SchemaError> {
        element_stride(self.attribute.path(), element_size)?;
        Ok(Self {
            attribute: self
                .attribute
                .set_metadata(tokens::ELEMENT_SIZE, sdf::Value::Int(element_size))?,
        })
    }

    /// Whether a layer authors the primvar's `elementSize` (C++
    /// `HasAuthoredElementSize`).
    pub fn has_authored_element_size(&self) -> Result<bool> {
        self.attribute.has_authored_metadata(tokens::ELEMENT_SIZE)
    }

    /// The index that stands for "no authored value" in the primvar's indices
    /// (C++ `GetUnauthoredValuesIndex`), -1 where none is authored, which
    /// says the primvar has no such index.
    pub fn unauthored_values_index(&self) -> Result<i32> {
        Ok(self
            .attribute
            .get_metadata::<i32>(tokens::UNAUTHORED_VALUES_INDEX)?
            .unwrap_or(-1))
    }

    /// Author the primvar's `unauthoredValuesIndex` (C++
    /// `SetUnauthoredValuesIndex`).
    pub fn set_unauthored_values_index(self, index: i32) -> Result<Self, usd::StageAuthoringError> {
        Ok(Self {
            attribute: self
                .attribute
                .set_metadata(tokens::UNAUTHORED_VALUES_INDEX, sdf::Value::Int(index))?,
        })
    }

    /// The `<name>:indices` attribute that indexes the primvar's values (C++
    /// `GetIndicesAttr`), whether or not anything defines it.
    pub fn indices_attr(&self) -> usd::Attribute {
        self.attribute.prim().attribute(self.sibling_name(INDICES_SUFFIX))
    }

    /// Author the indices attribute, as an `int[]` holding no value (C++
    /// `CreateIndicesAttr`). The primvar is not indexed until the attribute
    /// holds one.
    pub fn create_indices_attr(&self) -> Result<usd::Attribute, usd::StageAuthoringError> {
        self.indices_builder().build()
    }

    /// Author the primvar's indices at `time`, or as the default where `time`
    /// is `None` (C++ `SetIndices`).
    ///
    /// Only an array-valued primvar is indexed: any other, one nothing
    /// defines included, is [`SchemaError::PrimvarNotArray`].
    pub fn set_indices(&self, indices: Vec<i32>, time: impl Into<Option<usd::TimeCode>>) -> Result<(), SchemaError> {
        self.require_array()?;
        self.indices_builder()
            .set_at(sdf::Value::IntVec(indices), time)
            .build()?;
        Ok(())
    }

    /// Block the primvar's indices, so it reads as its own values whatever a
    /// weaker layer indexes them with (C++ `BlockIndices`). Refused for a
    /// primvar that is not array-valued, as
    /// [`set_indices`](Self::set_indices) is.
    pub fn block_indices(&self) -> Result<(), SchemaError> {
        self.require_array()?;
        self.indices_builder().block().build()?;
        Ok(())
    }

    /// The primvar's indices at `time` (C++ `GetIndices`), or `None` where
    /// the indices attribute reads no `int[]` value there.
    pub fn indices(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<Option<Vec<i32>>> {
        self.indices_attr().get_at(time)
    }

    /// Whether the primvar is indexed (C++ `IsIndexed`): its indices
    /// attribute has an authored value, at any time. Blocked indices are no
    /// value, so a block un-indexes the primvar.
    pub fn is_indexed(&self) -> Result<bool> {
        self.indices_attr().has_authored_value()
    }

    /// The primvar's value at `time` decoded to `T`, as authored and with no
    /// indices applied (C++ `UsdGeomPrimvar::Get`). Read as
    /// [`usd::Attribute::get_at`] reads, except for an
    /// [id target](Self::is_id_target), which answers in place of the
    /// attribute's own value.
    pub fn get_at<T>(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<Option<T>>
    where
        T: sdf::FromValue,
        T::Error: Into<Error>,
    {
        self.read::<T>(time.into())?
            .map(T::try_from)
            .transpose()
            .map_err(Into::into)
    }

    /// The primvar's value at `time` with its indices applied (C++
    /// `ComputeFlattened`): for each index, the
    /// [`element_size`](Self::element_size) values it selects, in the order
    /// the indices list them. `T` is the array type to decode to, or
    /// [`sdf::Value`] for whatever the primvar holds.
    ///
    /// `None` where the primvar reads no value. A value that is not an
    /// array, and the value of a primvar that is not indexed, come back as
    /// authored. Empty indices flatten to an empty array.
    ///
    /// An indexed primvar that cannot be flattened is an error:
    /// [`PrimvarIndicesMissing`](SchemaError::PrimvarIndicesMissing) where
    /// the indices read nothing at `time`,
    /// [`InvalidElementSize`](SchemaError::InvalidElementSize) for an element
    /// size below one, and
    /// [`PrimvarIndexOutOfRange`](SchemaError::PrimvarIndexOutOfRange) where
    /// an index is negative or selects values past the end.
    ///
    /// The values and the indices are each read at `time` from their own
    /// samples.
    pub fn compute_flattened<T>(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<Option<T>, SchemaError>
    where
        T: sdf::FromValue,
        T::Error: Into<Error>,
    {
        let time = time.into();
        let Some(value) = self.read::<T>(time)? else {
            return Ok(None);
        };
        let indices = self.indices_attr();
        let flattened = match value.array_len() {
            Some(len) if indices.has_authored_value()? => self.flatten(value, len, &indices, time)?,
            _ => value,
        };
        T::try_from(flattened)
            .map(Some)
            .map_err(|error| SchemaError::Core(error.into()))
    }

    /// The sample times of the primvar's values, and of its indices where it
    /// is indexed, as one ascending list (C++ `GetTimeSamples`).
    pub fn time_sample_times(&self) -> Result<Vec<f64>> {
        self.time_samples_in_interval(f64::NEG_INFINITY..=f64::INFINITY)
    }

    /// [`time_sample_times`](Self::time_sample_times) within `interval` (C++
    /// `GetTimeSamplesInInterval`).
    pub fn time_samples_in_interval(&self, interval: impl Into<gf::Interval>) -> Result<Vec<f64>> {
        let indices = self.indices_attr();
        if indices.has_authored_value()? {
            return usd::Attribute::unioned_time_samples_in_interval(&[self.attribute.clone(), indices], interval);
        }
        self.attribute.time_samples_in_interval(interval)
    }

    /// Whether the flattened value may change over time (C++
    /// `ValueMightBeTimeVarying`): the values might, or the indices of an
    /// indexed primvar might. Each is asked about its own samples, so one
    /// sample on each is not time-varying.
    pub fn value_might_be_time_varying(&self) -> Result<bool> {
        let indices = self.indices_attr();
        if indices.has_authored_value()? && indices.value_might_be_time_varying()? {
            return Ok(true);
        }
        self.attribute.value_might_be_time_varying()
    }

    /// Whether the primvar takes its value from an id target (C++
    /// `IsIdTarget`): it is a `string` or `string[]` primvar and its
    /// `<name>:idFrom` relationship is defined.
    ///
    /// An id target stands for the path of the object the relationship
    /// targets. Where the relationship is defined it answers alone, and a
    /// value authored on the attribute is not read: a `string` primvar reads
    /// the path of its one target, and no value with any other number of
    /// targets, and a `string[]` primvar reads the path of its first.
    pub fn is_id_target(&self) -> Result<bool> {
        Ok(self.id_target()?.is_some())
    }

    /// Author the primvar's id target (C++ `SetIdTarget`): `path`, or the
    /// primvar's own prim where `path` is empty. The target need not exist.
    ///
    /// Only a `string` or `string[]` primvar takes one: any other is
    /// [`SchemaError::IdTargetType`].
    pub fn set_id_target(&self, path: &sdf::Path) -> Result<(), SchemaError> {
        let type_name = self.type_name()?;
        if !type_name.as_ref().is_some_and(holds_strings) {
            return Err(SchemaError::IdTargetType {
                primvar: self.attribute.path().clone(),
                type_name: type_name.map(|name| name.as_token()).unwrap_or_default(),
            });
        }
        let target = match path.is_empty() {
            true => self.attribute.path().prim_path(),
            false => path.clone(),
        };
        self.attribute
            .prim()
            .relationship_builder(self.sibling_name(ID_FROM_SUFFIX))
            .set_targets([target])
            .build()?;
        Ok(())
    }

    /// The value at `time` that `T` reads, undecoded: the id target's where
    /// the primvar has one and `T` reads strings, else the attribute's, with
    /// the opinion chosen as a typed read of `T` chooses it.
    fn read<T: sdf::FromValue>(&self, time: Option<usd::TimeCode>) -> Result<Option<sdf::Value>> {
        let reads_strings = T::accepts_kind(sdf::ValueKind::String) || T::accepts_kind(sdf::ValueKind::StringVec);
        if reads_strings && let Some((relationship, is_array)) = self.id_target()? {
            let targets = relationship.forwarded_targets()?;
            let value = match (is_array, targets.as_slice()) {
                (false, [only]) => Some(sdf::Value::String(only.as_str().to_owned())),
                (true, [first, ..]) => Some(sdf::Value::StringVec(vec![first.as_str().to_owned()])),
                _ => None,
            };
            return Ok(value.filter(|value| T::accepts_kind(sdf::ValueKind::from(value))));
        }
        self.attribute.value_at::<T>(time)
    }

    /// The defined `<name>:idFrom` relationship of a `string` or `string[]`
    /// primvar, with whether the primvar is the array, or `None` where the
    /// primvar has no id target.
    ///
    // TODO(perf): every read that takes strings, an untyped one included,
    // asks for the declared type here, and a string primvar then asks whether
    // the relationship is defined. A per-primvar cache of the two, stamped as
    // `usd::AttributeQuery` stamps its source, would let a loop over times
    // resolve them once.
    fn id_target(&self) -> Result<Option<(usd::Relationship, bool)>> {
        let Some(type_name) = self.type_name()?.filter(holds_strings) else {
            return Ok(None);
        };
        let relationship = self.attribute.prim().relationship(self.sibling_name(ID_FROM_SUFFIX));
        Ok(relationship.is_defined()?.then(|| (relationship, type_name.is_array())))
    }

    /// `values`, an array of `len` elements, gathered through the values of
    /// the primvar's `indices` attribute at `time`.
    fn flatten(
        &self,
        values: sdf::Value,
        len: usize,
        indices: &usd::Attribute,
        time: Option<usd::TimeCode>,
    ) -> Result<sdf::Value, SchemaError> {
        let primvar = self.attribute.path();
        let Some(indices) = indices.get_at::<Vec<i32>>(time)? else {
            return Err(SchemaError::PrimvarIndicesMissing {
                primvar: primvar.clone(),
            });
        };
        let stride = element_stride(primvar, self.element_size()?)?;

        let mut starts = Vec::with_capacity(indices.len());
        let mut invalid = 0;
        let mut first = Vec::new();
        for (position, &index) in indices.iter().enumerate() {
            if let Some(start) = element_start(index, stride, len) {
                starts.push(start);
                continue;
            }
            invalid += 1;
            if first.len() < REPORTED_INDICES {
                first.push((position, index));
            }
        }
        if invalid > 0 {
            return Err(SchemaError::PrimvarIndexOutOfRange(Box::new(PrimvarIndexError {
                primvar: primvar.clone(),
                invalid,
                len,
                element_size: stride,
                first,
            })));
        }

        let positions = starts.into_iter().flat_map(|start| start..start + stride);
        // Only an attribute array gathers, and no other array is an
        // attribute's value.
        Ok(values.gather(positions).unwrap_or(values))
    }

    /// The primvar's composed value type, whatever its spelling, or `None`
    /// where nothing declares the attribute.
    pub(super) fn type_name(&self) -> Result<Option<sdf::ValueTypeName>> {
        Ok(self
            .attribute
            .get_metadata::<tf::Token>(sdf::FieldKey::TypeName.as_str())?
            .map(sdf::ValueTypeName::from))
    }

    /// That the primvar is array-valued, which is what lets it be indexed.
    fn require_array(&self) -> Result<(), SchemaError> {
        let type_name = self.type_name()?;
        if type_name.as_ref().is_some_and(sdf::ValueTypeName::is_array) {
            return Ok(());
        }
        Err(SchemaError::PrimvarNotArray {
            primvar: self.attribute.path().clone(),
            type_name: type_name.map(|name| name.as_token()).unwrap_or_default(),
        })
    }

    /// The indices attribute as it is authored: an `int[]` that is no custom
    /// property.
    fn indices_builder(&self) -> usd::AttributeBuilder<'static> {
        self.attribute
            .prim()
            .attribute_builder(self.sibling_name(INDICES_SUFFIX), sdf::ValueTypeName::INT_ARRAY)
            .custom(false)
    }

    /// The name of the property kept beside the primvar under `suffix`.
    fn sibling_name(&self, suffix: &str) -> String {
        format!("{}{suffix}", self.attribute.name())
    }
}

/// The suffix of the attribute that indexes a primvar: `primvars:st:indices`
/// for `primvars:st`.
pub(super) const INDICES_SUFFIX: &str = ":indices";

/// The suffix of the relationship that gives a string primvar its id target.
const ID_FROM_SUFFIX: &str = ":idFrom";

/// How many out-of-range indices a [`PrimvarIndexError`] lists.
const REPORTED_INDICES: usize = 5;

/// How many values one element of the primvar at `primvar` holds, for an
/// `elementSize` of `element_size`: the size itself, which is at least one.
pub(super) fn element_stride(primvar: &sdf::Path, element_size: i32) -> Result<usize, SchemaError> {
    match usize::try_from(element_size) {
        Ok(stride) if stride >= 1 => Ok(stride),
        _ => Err(SchemaError::InvalidElementSize {
            primvar: primvar.clone(),
            element_size,
        }),
    }
}

/// Whether `type_name` is the `string` or `string[]` an id target stands in
/// for.
fn holds_strings(type_name: &sdf::ValueTypeName) -> bool {
    *type_name == sdf::ValueTypeName::STRING || *type_name == sdf::ValueTypeName::STRING_ARRAY
}

/// Where the element `index` selects starts in an array of `len` values, each
/// element `stride` values long, or `None` where the index is negative or the
/// element runs past the end.
fn element_start(index: i32, stride: usize, len: usize) -> Option<usize> {
    let index = usize::try_from(index).ok()?;
    let end = index.checked_add(1)?.checked_mul(stride)?;
    (end <= len).then(|| end - stride)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use openusd::usd::{self, SchemaBase, Stage, TimeCode};
    use openusd::{sdf, tf};

    use super::Primvar;
    use crate::geom::{Interpolation, Mesh, PrimvarsAPI, tokens};
    use crate::{PrimvarIndexError, SchemaError};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// A stage holding the mesh `/Mesh`, seen as its primvars.
    fn mesh() -> Result<PrimvarsAPI> {
        let stage = crate::tests::stage("anon.usda")?;
        Ok(PrimvarsAPI::from_prim_unchecked(
            Mesh::define(&stage, "/Mesh")?.prim().clone(),
        ))
    }

    /// The `float[]` primvar `x` on a mesh, holding `values`.
    fn floats(values: &[f32]) -> Result<Primvar> {
        mesh()?
            .primvar_builder("x", "float[]")
            .set(sdf::Value::FloatVec(values.to_vec()))
            .build()
    }

    /// The primvar `name` of `/Mesh` in a stage opened from the mesh's
    /// `properties`, for scenes the stage-tier setters refuse to author.
    fn authored(properties: &str, name: &str) -> Result<(tempfile::TempDir, Primvar)> {
        let usda = format!("#usda 1.0\ndef Mesh \"Mesh\"\n{{\n{properties}\n}}\n");
        let (dir, stage) = crate::tests::from_usda(&usda)?;
        let primvar = PrimvarsAPI::from_prim_unchecked(stage.prim("/Mesh")?).primvar(name)?;
        Ok((dir, primvar))
    }

    fn flat(primvar: &Primvar) -> Result<Option<Vec<f32>>> {
        primvar.compute_flattened::<Vec<f32>>(None)
    }

    fn out_of_range(error: SchemaError) -> PrimvarIndexError {
        match error {
            SchemaError::PrimvarIndexOutOfRange(error) => *error,
            other => panic!("expected out-of-range indices, got {other:?}"),
        }
    }

    /// A primvar's name is in the namespace and does not end in `:indices`;
    /// the reserved word anywhere else, and `idFrom`, are ordinary names.
    #[test]
    fn primvar_name_rule() -> Result {
        assert!(Primvar::is_valid_primvar_name("primvars:st"));
        assert!(Primvar::is_valid_primvar_name("primvars:skel:jointWeights"));
        assert!(Primvar::is_valid_primvar_name("primvars:st:indices:more"));
        assert!(Primvar::is_valid_primvar_name("primvars:st:idFrom"));
        assert!(!Primvar::is_valid_primvar_name("st"));
        assert!(!Primvar::is_valid_primvar_name("primvars:st:indices"));

        let weights = mesh()?.create_primvar("skel:jointWeights", "float[]")?;
        assert_eq!(weights.attribute().name(), "primvars:skel:jointWeights");
        assert_eq!(weights.primvar_name(), "skel:jointWeights");
        Ok(())
    }

    /// The indices attribute sits in the namespace without being a primvar,
    /// and an attribute outside the namespace is none either.
    #[test]
    fn indices_not_primvar() -> Result {
        let primvar = floats(&[1.0])?;
        let indices = primvar.create_indices_attr()?;
        assert_eq!(indices.name(), "primvars:x:indices");
        assert!(Primvar::from_attribute(indices).is_none());
        let plain = primvar.attribute().prim().create_attribute("x", "float[]")?;
        assert!(Primvar::from_attribute(plain).is_none());
        assert!(Primvar::from_attribute(primvar.attribute().clone()).is_some());
        Ok(())
    }

    #[test]
    fn interpolation_fallback_constant() -> Result {
        let primvar = floats(&[1.0])?;
        assert_eq!(primvar.interpolation()?, Interpolation::Constant);
        assert!(!primvar.has_authored_interpolation()?);

        let primvar = primvar.set_interpolation(Interpolation::FaceVarying)?;
        assert_eq!(primvar.interpolation()?, Interpolation::FaceVarying);
        assert!(primvar.has_authored_interpolation()?);
        Ok(())
    }

    /// An authored token that names no interpolation is the opinion that
    /// wins, and reading it is an error.
    #[test]
    fn unknown_interpolation_errors() -> Result {
        let (_dir, primvar) = authored(
            "    float[] primvars:x = [1] (\n        interpolation = \"frobosity\"\n    )",
            "x",
        )?;
        assert!(primvar.interpolation().is_err());
        assert!(!primvar.is_constant()?);
        Ok(())
    }

    #[test]
    fn element_size_fallback() -> Result {
        let primvar = floats(&[1.0])?;
        assert_eq!(primvar.element_size()?, 1);
        assert!(!primvar.has_authored_element_size()?);

        let primvar = primvar.set_element_size(3)?;
        assert_eq!(primvar.element_size()?, 3);
        assert!(primvar.has_authored_element_size()?);
        Ok(())
    }

    /// A size below one is refused, and leaves the primvar as it was.
    #[test]
    fn element_size_rejects_zero() -> Result {
        let primvar = floats(&[1.0])?.set_element_size(2)?;
        for size in [0, -1] {
            let error = primvar.clone().set_element_size(size).expect_err("below one");
            assert!(matches!(
                error,
                SchemaError::InvalidElementSize { element_size, .. } if element_size == size
            ));
        }
        assert_eq!(primvar.element_size()?, 2);
        Ok(())
    }

    /// An `elementSize` that is no `int` is an error, not the fallback.
    #[test]
    fn non_int_size_errors() -> Result {
        let primvar = floats(&[1.0])?;
        primvar
            .attribute()
            .clone()
            .set_metadata(tokens::ELEMENT_SIZE, sdf::Value::Float(2.0))?;
        assert!(primvar.element_size().is_err());
        Ok(())
    }

    #[test]
    fn unauthored_index_fallback() -> Result {
        let primvar = floats(&[1.0])?;
        assert_eq!(primvar.unauthored_values_index()?, -1);
        assert_eq!(primvar.set_unauthored_values_index(2)?.unauthored_values_index()?, 2);
        Ok(())
    }

    /// Indices make the primvar indexed, on an `int[]` attribute that is no
    /// custom property.
    #[test]
    fn set_indices_makes_indexed() -> Result {
        let primvar = floats(&[1.0, 2.0])?;
        assert!(!primvar.is_indexed()?);
        assert_eq!(primvar.indices(None)?, None);

        primvar.set_indices(vec![1, 0], None)?;
        assert!(primvar.is_indexed()?);
        assert_eq!(primvar.indices(None)?, Some(vec![1, 0]));
        let indices = primvar.indices_attr();
        assert_eq!(indices.type_name()?, Some(sdf::ValueTypeName::INT_ARRAY));
        assert!(!indices.is_custom()?);
        Ok(())
    }

    /// A primvar that is no array takes no indices and no block of them, and
    /// neither does one nothing defines.
    #[test]
    fn scalar_rejects_indices() -> Result {
        let api = mesh()?;
        let scalar = api.create_primvar("s", "float")?;
        for primvar in [scalar, api.primvar("undefined")?] {
            let error = primvar.set_indices(vec![0], None).expect_err("no array");
            assert!(matches!(error, SchemaError::PrimvarNotArray { .. }));
            let error = primvar.block_indices().expect_err("no array");
            assert!(matches!(error, SchemaError::PrimvarNotArray { .. }));
            assert!(!primvar.indices_attr().is_defined()?);
        }
        Ok(())
    }

    /// Blocked indices are no value: the attribute stays and the primvar is
    /// not indexed.
    #[test]
    fn block_indices_unindexes() -> Result {
        let primvar = floats(&[1.0, 2.0])?;
        primvar.set_indices(vec![1, 0], None)?;
        primvar.set_indices(vec![0], TimeCode::new(1.0))?;
        primvar.block_indices()?;

        assert!(!primvar.is_indexed()?);
        assert!(primvar.indices_attr().is_defined()?);
        assert_eq!(flat(&primvar)?, Some(vec![1.0, 2.0]));
        Ok(())
    }

    #[test]
    fn created_indices_not_indexed() -> Result {
        let primvar = floats(&[1.0])?;
        assert!(primvar.create_indices_attr()?.is_defined()?);
        assert!(!primvar.is_indexed()?);
        Ok(())
    }

    /// Indices authored only as samples index the primvar.
    #[test]
    fn sampled_indices_indexed() -> Result {
        let primvar = floats(&[1.0, 2.0])?;
        primvar.set_indices(vec![1], TimeCode::new(1.0))?;
        assert!(primvar.is_indexed()?);
        assert_eq!(primvar.indices(None)?, None);
        assert_eq!(primvar.indices(TimeCode::new(1.0))?, Some(vec![1]));
        Ok(())
    }

    /// Indices of another type have an authored value, so the primvar is
    /// indexed, but read as no indices: flattening says so.
    #[test]
    fn wrong_type_indices_unread() -> Result {
        let (_dir, primvar) = authored(
            "    float[] primvars:x = [1, 2]\n    float[] primvars:x:indices = [0, 1]",
            "x",
        )?;
        assert!(primvar.is_indexed()?);
        assert_eq!(primvar.indices(None)?, None);
        assert!(matches!(flat(&primvar), Err(SchemaError::PrimvarIndicesMissing { .. })));
        Ok(())
    }

    #[test]
    fn flatten_unindexed_passthrough() -> Result {
        let primvar = floats(&[1.0, 2.0, 3.0])?;
        assert_eq!(flat(&primvar)?, Some(vec![1.0, 2.0, 3.0]));
        Ok(())
    }

    /// A primvar with no value flattens to none, indexed or not.
    #[test]
    fn flatten_no_value() -> Result {
        let primvar = mesh()?.create_primvar("x", "float[]")?;
        assert_eq!(flat(&primvar)?, None);
        primvar.set_indices(vec![0], None)?;
        assert_eq!(flat(&primvar)?, None);
        Ok(())
    }

    /// A value that is no array has nothing to index, whatever sits in the
    /// indices attribute beside it.
    #[test]
    fn flatten_scalar_passthrough() -> Result {
        let (_dir, primvar) = authored(
            "    string primvars:s = \"one\"\n    int[] primvars:s:indices = [5]",
            "s",
        )?;
        assert!(primvar.is_indexed()?);
        assert_eq!(primvar.compute_flattened::<String>(None)?, Some("one".to_owned()));
        Ok(())
    }

    #[test]
    fn flatten_gathers() -> Result {
        let primvar = floats(&[10.0, 20.0, 30.0])?;
        primvar.set_indices(vec![2, 0, 0, 1], None)?;
        assert_eq!(flat(&primvar)?, Some(vec![30.0, 10.0, 10.0, 20.0]));
        assert_eq!(primvar.get_at::<Vec<f32>>(None)?, Some(vec![10.0, 20.0, 30.0]));
        Ok(())
    }

    /// Empty indices select nothing, from values and from none alike.
    #[test]
    fn flatten_empty_indices() -> Result {
        for values in [&[1.0, 2.0][..], &[]] {
            let primvar = floats(values)?;
            primvar.set_indices(Vec::new(), None)?;
            assert_eq!(flat(&primvar)?, Some(Vec::new()));
        }
        Ok(())
    }

    /// Each index selects one element, `elementSize` values long, and an
    /// element that runs past the values is out of range.
    #[test]
    fn flatten_element_size() -> Result {
        let values: Vec<f32> = (0..9u8).map(f32::from).collect();
        let primvar = floats(&values)?;
        primvar.set_indices(vec![0, 1, 2, 0, 1, 2], None)?;
        assert_eq!(flat(&primvar)?, Some(vec![0.0, 1.0, 2.0, 0.0, 1.0, 2.0]));

        let primvar = primvar.set_element_size(2)?;
        let pairs: Vec<f32> = (0..6u8).map(f32::from).collect();
        assert_eq!(flat(&primvar)?, Some([pairs.clone(), pairs].concat()));

        let primvar = primvar.set_element_size(3)?;
        assert_eq!(flat(&primvar)?, Some([values.clone(), values].concat()));

        // Index 2 at four values an element needs values 8 to 11 of 9.
        let primvar = primvar.set_element_size(4)?;
        let error = out_of_range(flat(&primvar).expect_err("out of range"));
        assert_eq!((error.invalid, error.len, error.element_size), (2, 9, 4));
        assert_eq!(error.first, vec![(2, 2), (5, 2)]);
        Ok(())
    }

    /// The values and the indices are each read at the time asked for.
    #[test]
    fn flatten_at_time() -> Result {
        let primvar = mesh()?.create_primvar("x", "float[]")?;
        let (one, two) = (TimeCode::new(1.0), TimeCode::new(2.0));
        primvar
            .attribute()
            .clone()
            .set_at(sdf::Value::FloatVec(vec![1.0, 2.0]), one)?
            .set_at(sdf::Value::FloatVec(vec![3.0, 4.0]), two)?;
        primvar.set_indices(vec![1, 0], one)?;
        primvar.set_indices(Vec::new(), two)?;

        assert_eq!(primvar.compute_flattened::<Vec<f32>>(one)?, Some(vec![2.0, 1.0]));
        assert_eq!(primvar.compute_flattened::<Vec<f32>>(two)?, Some(Vec::new()));
        Ok(())
    }

    /// An array of any attribute type flattens, read typed or as a value.
    #[test]
    fn flatten_token_array() -> Result {
        let tokens = |names: &[&str]| names.iter().copied().map(tf::Token::from).collect::<Vec<_>>();
        let primvar = mesh()?
            .primvar_builder("t", "token[]")
            .set(sdf::Value::TokenVec(tokens(&["a", "b"])))
            .indices(vec![1, 1, 0])
            .build()?;

        assert_eq!(
            primvar.compute_flattened::<sdf::Value>(None)?,
            Some(sdf::Value::TokenVec(tokens(&["b", "b", "a"])))
        );
        assert_eq!(
            primvar.compute_flattened::<Vec<tf::Token>>(None)?,
            Some(tokens(&["b", "b", "a"]))
        );
        Ok(())
    }

    #[test]
    fn flatten_negative_index() -> Result {
        let primvar = floats(&[1.0, 2.0, 3.0])?;
        primvar.set_indices(vec![0, -1, 2], None)?;
        let error = out_of_range(flat(&primvar).expect_err("negative index"));
        assert_eq!(error.invalid, 1);
        assert_eq!(error.first, vec![(1, -1)]);
        assert_eq!(&error.primvar, primvar.attribute().path());
        Ok(())
    }

    #[test]
    fn flatten_index_past_end() -> Result {
        let primvar = floats(&[1.0, 2.0, 3.0])?;
        primvar.set_indices(vec![0, 3], None)?;
        let error = out_of_range(flat(&primvar).expect_err("index 3 of 3 values"));
        assert_eq!((error.invalid, error.len), (1, 3));
        assert_eq!(error.first, vec![(1, 3)]);
        Ok(())
    }

    /// Every bad index is counted, and the first five are listed.
    #[test]
    fn flatten_lists_five() -> Result {
        let primvar = floats(&[1.0])?;
        primvar.set_indices(vec![0, 9, 8, 7, 6, 5, 4, 3], None)?;
        let error = out_of_range(flat(&primvar).expect_err("seven bad indices"));
        assert_eq!(error.invalid, 7);
        assert_eq!(error.first, vec![(1, 9), (2, 8), (3, 7), (4, 6), (5, 5)]);
        Ok(())
    }

    /// Indices that hold no value at the time asked for are missing there,
    /// and answer where they hold one.
    #[test]
    fn flatten_missing_indices() -> Result {
        let primvar = floats(&[1.0, 2.0])?;
        let (one, two) = (TimeCode::new(1.0), TimeCode::new(2.0));
        primvar.set_indices(vec![1], one)?;
        primvar.indices_attr().set_at(sdf::Value::ValueBlock, two)?;

        assert_eq!(primvar.compute_flattened::<Vec<f32>>(one)?, Some(vec![2.0]));
        assert!(matches!(
            primvar.compute_flattened::<Vec<f32>>(two),
            Err(SchemaError::PrimvarIndicesMissing { .. })
        ));
        Ok(())
    }

    /// An authored element size below one cannot be flattened by.
    #[test]
    fn flatten_zero_size() -> Result {
        let primvar = floats(&[1.0, 2.0])?;
        primvar.set_indices(vec![0], None)?;
        primvar
            .attribute()
            .clone()
            .set_metadata(tokens::ELEMENT_SIZE, sdf::Value::Int(0))?;
        assert!(matches!(
            flat(&primvar),
            Err(SchemaError::InvalidElementSize { element_size: 0, .. })
        ));
        Ok(())
    }

    /// A typed flatten gathers the opinion a typed read selects: at the
    /// default time, a stronger value of another type is passed over.
    #[test]
    fn flatten_typed_skips_kind() -> Result {
        let dir = tempfile::tempdir().map_err(openusd::Error::from)?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text).map_err(openusd::Error::from);
        write(
            "root.usda",
            "#usda 1.0\n(\n    subLayers = [@weak.usda@]\n)\ndef \"A\"\n{\n    double[] primvars:x = [7, 8]\n}\n",
        )?;
        write(
            "weak.usda",
            "#usda 1.0\ndef \"A\"\n{\n    float[] primvars:x = [1, 2, 3]\n    int[] primvars:x:indices = [2, 0]\n}\n",
        )?;
        let stage = Stage::open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        let primvar = PrimvarsAPI::from_prim_unchecked(stage.prim("/A")?).primvar("x")?;

        assert_eq!(flat(&primvar)?, Some(vec![3.0, 1.0]));
        // Read as a value, the stronger array of two answers, and index 2
        // reaches past it.
        let error = primvar
            .compute_flattened::<sdf::Value>(None)
            .expect_err("index 2 of 2 values");
        assert_eq!(out_of_range(error).len, 2);
        Ok(())
    }

    /// An indexed primvar's sample times are its values' and its indices'.
    #[test]
    fn samples_union_indices() -> Result {
        let primvar = mesh()?.create_primvar("x", "float[]")?;
        let at = TimeCode::new;
        primvar
            .attribute()
            .clone()
            .set_at(sdf::Value::FloatVec(vec![1.0]), at(1.0))?
            .set_at(sdf::Value::FloatVec(vec![2.0]), at(2.0))?;
        assert_eq!(primvar.time_sample_times()?, vec![1.0, 2.0]);

        primvar.set_indices(vec![0], at(0.0))?;
        primvar.set_indices(vec![0], at(3.0))?;
        assert_eq!(primvar.time_sample_times()?, vec![0.0, 1.0, 2.0, 3.0]);
        assert_eq!(primvar.time_samples_in_interval(0.5..=1.5)?, vec![1.0]);
        Ok(())
    }

    /// Blocked indices do not index the primvar, and their samples are not its
    /// own.
    #[test]
    fn blocked_indices_not_unioned() -> Result {
        let primvar = mesh()?.create_primvar("x", "float[]")?;
        primvar
            .attribute()
            .clone()
            .set_at(sdf::Value::FloatVec(vec![1.0]), TimeCode::new(1.0))?;
        primvar.set_indices(vec![0], TimeCode::new(5.0))?;
        assert_eq!(primvar.time_sample_times()?, vec![1.0, 5.0]);

        primvar.block_indices()?;
        assert_eq!(primvar.time_sample_times()?, vec![1.0]);
        Ok(())
    }

    #[test]
    fn varying_from_indices() -> Result {
        let primvar = floats(&[1.0, 2.0])?;
        assert!(!primvar.value_might_be_time_varying()?);
        primvar.set_indices(vec![0], TimeCode::new(1.0))?;
        primvar.set_indices(vec![1], TimeCode::new(2.0))?;
        assert!(primvar.value_might_be_time_varying()?);
        Ok(())
    }

    /// One sample on the values and one on the indices is each of them
    /// constant, though the two share a time.
    #[test]
    fn single_sample_not_varying() -> Result {
        let primvar = mesh()?.create_primvar("x", "float[]")?;
        let one = TimeCode::new(1.0);
        primvar
            .attribute()
            .clone()
            .set_at(sdf::Value::FloatVec(vec![1.0]), one)?;
        primvar.set_indices(vec![0], one)?;
        assert_eq!(primvar.time_sample_times()?, vec![1.0]);
        assert!(!primvar.value_might_be_time_varying()?);
        Ok(())
    }

    /// The string primvar `id` on a mesh, holding `authored`.
    fn id_primvar(type_name: &str, authored: sdf::Value) -> Result<Primvar> {
        mesh()?.primvar_builder("id", type_name).set(authored).build()
    }

    fn id_relationship(primvar: &Primvar) -> usd::Relationship {
        primvar.attribute().prim().relationship("primvars:id:idFrom")
    }

    #[test]
    fn id_target_needs_string() -> Result {
        let primvar = floats(&[1.0])?;
        let error = primvar
            .set_id_target(&sdf::path("/Mesh")?)
            .expect_err("a float[] takes no id target");
        assert!(matches!(error, SchemaError::IdTargetType { .. }));
        assert!(!primvar.is_id_target()?);
        let relationship = primvar.attribute().prim().relationship("primvars:x:idFrom");
        assert!(!relationship.is_defined()?);
        Ok(())
    }

    /// The target's path is the value, whether or not anything is there.
    #[test]
    fn id_target_reads_path() -> Result {
        let primvar = mesh()?.create_primvar("id", "string")?;
        assert!(!primvar.is_id_target()?);
        primvar.set_id_target(&sdf::path("/my/string/path")?)?;

        assert!(primvar.is_id_target()?);
        assert_eq!(primvar.get_at::<String>(None)?, Some("/my/string/path".to_owned()));
        assert_eq!(
            primvar.get_at::<sdf::Value>(None)?,
            Some(sdf::Value::String("/my/string/path".to_owned()))
        );
        Ok(())
    }

    /// An empty target is the primvar's own prim.
    #[test]
    fn id_target_defaults_prim() -> Result {
        let primvar = mesh()?.create_primvar("id", "string")?;
        primvar.set_id_target(&sdf::Path::default())?;
        assert_eq!(primvar.get_at::<String>(None)?, Some("/Mesh".to_owned()));
        Ok(())
    }

    #[test]
    fn id_target_beats_value() -> Result {
        let primvar = id_primvar("string", sdf::Value::String("authored".to_owned()))?;
        assert_eq!(primvar.get_at::<String>(None)?, Some("authored".to_owned()));
        primvar.set_id_target(&sdf::path("/Target")?)?;
        assert_eq!(primvar.get_at::<String>(None)?, Some("/Target".to_owned()));
        Ok(())
    }

    /// A string primvar stands for one target: with two it reads no value,
    /// and the authored string does not answer in their place.
    #[test]
    fn two_targets_no_value() -> Result {
        let primvar = id_primvar("string", sdf::Value::String("authored".to_owned()))?;
        primvar.set_id_target(&sdf::path("/One")?)?;
        id_relationship(&primvar).add_target("/Two")?;
        assert_eq!(primvar.get_at::<String>(None)?, None);

        id_relationship(&primvar).set_targets(Vec::<sdf::Path>::new())?;
        assert_eq!(primvar.get_at::<String>(None)?, None);
        Ok(())
    }

    /// A string array primvar reads its first target, one or several.
    #[test]
    fn id_target_array() -> Result {
        let primvar = id_primvar("string[]", sdf::Value::StringVec(vec!["authored".to_owned()]))?;
        primvar.set_id_target(&sdf::path("/One")?)?;
        assert_eq!(primvar.get_at::<Vec<String>>(None)?, Some(vec!["/One".to_owned()]));

        id_relationship(&primvar).add_target("/Two")?;
        assert_eq!(primvar.get_at::<Vec<String>>(None)?, Some(vec!["/One".to_owned()]));
        // The target is an array of strings, which a read of one string does
        // not take.
        assert_eq!(primvar.get_at::<String>(None)?, None);
        Ok(())
    }

    /// Flattening reads through the id target as a plain read does.
    #[test]
    fn flatten_reads_id_target() -> Result {
        let primvar = id_primvar("string", sdf::Value::String("authored".to_owned()))?;
        primvar.set_id_target(&sdf::path("/Target")?)?;
        assert_eq!(primvar.compute_flattened::<String>(None)?, Some("/Target".to_owned()));
        Ok(())
    }
}
