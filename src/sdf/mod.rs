//! Scene description foundations.
//!
//! This module contains common data types used by parsers.
//! Roughly this correspond to C++ SDF module <https://openusd.org/dev/api/sdf_page_front.html>

use std::{collections::HashMap, fmt::Debug};

use bytemuck::{Pod, Zeroable};
use strum::FromRepr;

use crate::tf::Token;

mod asset_path;
mod change;
mod copy;
mod data;
pub mod expr;
mod file_format;
mod layer;
pub(crate) mod layer_registry;
mod ordering;
mod path;
pub mod path_expr;
mod path_table;
pub mod schema;
pub mod sink;
mod spec;
mod value;

pub use asset_path::AssetPath;
pub(crate) use asset_path::{
    AssetExpressionFailure, AssetOutcome, evaluate_asset_paths, holds_asset_expression, resolve_asset_paths,
};
pub use change::{ChangeEntry, ChangeFlags, ChangeList};
pub use copy::{
    CopyChildren, CopyChildrenArgs, CopyValue, CopyValueArgs, copy_spec, copy_spec_with, copy_spec_within,
    should_copy_children, should_copy_value,
};
pub(crate) use copy::{author_spec, is_children_field};
pub use data::{AbstractData, CowData, Data, DataError, Patch};
pub use expr::{Evaluation, EvaluationValue, Expr, ExprError, StringEvaluation, StringSegment};
pub use file_format::{FileFormat, FileFormatCaps, FormatError, WriteSeek};
pub use layer::{
    AuthoringError, EditError, ExportError, Layer, LayerEdit, LayerSink, LayerSinkId, PendingLayerChange,
    default_prim_path,
};
pub(crate) use layer::{dry_run_layers, edit_layers};
pub use layer_registry::LayerRegistry;
pub(crate) use layer_registry::LoadError;
pub use ordering::{apply_ordering, element_cmp};
pub use path::{IntoPath, Path, PathComponent, PathComponents, PathElement, PathParseError, path, try_into_path};
pub use path_expr::{EvalError, ExpressionReference, PathExpression, PathPattern, PredicateExpression};
pub use path_table::PathTable;
pub use schema::{ChildrenKey, FieldKey, folds_list_ops};
pub use spec::{
    AttributeSpec, AttributeSpecMut, AttributeSpecRef, PrimSpec, PrimSpecMut, PrimSpecRef, PropertySpec,
    PropertySpecMut, PropertySpecRef, PseudoRootSpec, PseudoRootSpecMut, PseudoRootSpecRef, RelationshipSpec,
    RelationshipSpecMut, RelationshipSpecRef, Spec, SpecData, SpecError, SpecMut, SpecRef, SpecType,
};
pub use value::{CastError, FromValueCast, Value, dictionary_over};

#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, FromRepr)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub enum Specifier {
    Def,
    Over,
    Class,
}

/// An enum that defines permission levels.
///
/// Permissions control which layers may refer to or express
/// opinions about a prim. Opinions expressed about a prim, or
/// relationships to that prim, by layers that are not allowed
/// permission to access the prim will be ignored.
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, FromRepr)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub enum Permission {
    Public,
    Private,
}

/// An enum that identifies variability types for attributes.
/// Variability indicates whether the attribute may vary over time and
/// value coordinates, and if its value comes through authoring or
/// or from its owner.
#[repr(i32)]
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, FromRepr)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub enum Variability {
    #[default]
    Varying,
    Uniform,
}

/// A time-coded `double` (C++ `SdfTimeCode`) — the value held by a
/// `timecode`-typed attribute (e.g. `UsdMediaSpatialAudio.startTime`). Unlike
/// a plain `double`, a `TimeCode` value is retimed by layer offsets during
/// composition.
///
/// This is the authored *value* type, distinct from a time-query *parameter*
/// (C++ `UsdTimeCode`, passed to `Attribute::get_at`). Read it with
/// `Attribute::get::<sdf::TimeCode>()` and author it with
/// `set(sdf::TimeCode(..))`; it round-trips through [`Value::TimeCode`].
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Default, derive_more::From)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct TimeCode(pub f64);

impl TimeCode {
    /// The wrapped time value.
    #[inline]
    pub fn value(self) -> f64 {
        self.0
    }
}

impl TryFrom<Value> for TimeCode {
    type Error = CastError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::TimeCode(v) => Ok(v),
            other => Err(CastError::TypeMismatch {
                target: "TimeCode",
                actual: (&other).into(),
            }),
        }
    }
}

/// Represents a time offset and scale between layers.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Pod, Zeroable)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct LayerOffset {
    /// Time offset.
    pub offset: f64,
    /// Scale factor.
    pub scale: f64,
}

impl Default for LayerOffset {
    fn default() -> Self {
        Self {
            offset: 0.0,
            scale: 1.0,
        }
    }
}

impl LayerOffset {
    /// Identity layer offset: offset 0, scale 1.
    pub const IDENTITY: LayerOffset = LayerOffset {
        offset: 0.0,
        scale: 1.0,
    };

    #[inline]
    pub fn new(offset: f64, scale: f64) -> Self {
        Self { offset, scale }
    }

    /// A pure time scaling `(0.0, scale)` with no offset. Composed onto another
    /// offset it scales without shifting — used to fold a `timeCodesPerSecond`
    /// retiming ratio into an arc's offset (spec 12.3.2).
    #[inline]
    pub fn scale_only(scale: f64) -> Self {
        Self { offset: 0.0, scale }
    }

    #[inline]
    pub fn is_valid(&self) -> bool {
        self.offset.is_finite() && self.scale.is_finite()
    }

    /// Returns `true` if this is the identity offset `(0.0, 1.0)`.
    #[inline]
    pub fn is_identity(&self) -> bool {
        self.offset == 0.0 && self.scale == 1.0
    }

    /// Applies this offset to a time value as `offset + scale * time` — the
    /// retiming a layer offset performs on the time coordinate of samples and
    /// clip schedules.
    #[inline]
    pub fn apply(&self, time: f64) -> f64 {
        self.offset + self.scale * time
    }

    /// Applies this offset to every time coordinate a value holds, mapping it
    /// out of the frame of the layer that authored it (spec 12.3.2.1, C++
    /// `Usd_ApplyLayerOffsetToValue`).
    ///
    /// A `timecode` is a time coordinate, not a plain number, so an offset
    /// retimes the value itself just as [`apply`](Self::apply) retimes the times
    /// a sample map is keyed by: an attribute authoring `timecode t = 5` in a
    /// layer sublayered with `(offset = 10; scale = 2)` resolves to `20` on the
    /// stage. Dictionaries and sample maps are recursed into, either being able
    /// to carry a timecode at any depth; every other value is left as it stands,
    /// as is any value at all under the identity offset.
    ///
    /// [`Value::holds_time_codes`] answers in advance whether this would rewrite
    /// anything, for a caller holding the value behind a borrow.
    pub fn apply_to_value(&self, value: &mut Value) {
        if self.is_identity() {
            return;
        }
        match value {
            Value::TimeCode(time) => *time = TimeCode(self.apply(time.value())),
            Value::TimeCodeVec(times) => {
                for time in times {
                    *time = TimeCode(self.apply(time.value()));
                }
            }
            Value::TimeSamples(samples) => self.apply_to_samples(samples),
            Value::Dictionary(entries) => {
                for entry in entries.values_mut() {
                    self.apply_to_value(entry);
                }
            }
            Value::ValueVec(values) => {
                for value in values {
                    self.apply_to_value(value);
                }
            }
            _ => {}
        }
    }

    /// Applies this offset to a sample map in place: every key is a time in the
    /// authoring layer's frame, and every sample may itself be time-valued.
    ///
    /// A [`TimeSampleMap`] is keyed in ascending time, which a negative scale
    /// reverses; the keys are restored to ascending order so a bracketing search
    /// over the result stays valid. Composition never authors one — a
    /// non-positive scale [sanitizes](Self::sanitized) to the identity — but the
    /// arithmetic here is defined for any offset.
    pub fn apply_to_samples(&self, samples: &mut TimeSampleMap) {
        for (time, sample) in samples.iter_mut() {
            *time = self.apply(*time);
            self.apply_to_value(sample);
        }
        if self.scale < 0.0 {
            samples.reverse();
        }
    }

    /// Interpolates a sample map at stage `time`, returning the result in stage
    /// time.
    ///
    /// `samples` stays in its authoring layer's frame: `time` maps backwards
    /// through this offset to select and blend the samples, and the interpolated
    /// value maps forward again through [`apply_to_value`](Self::apply_to_value).
    /// The lerp fraction is invariant under an affine offset, so the result is
    /// the one stage-frame samples would give, and a per-time query allocates
    /// only the value it returns.
    ///
    /// `interp` supplies the interpolation policy, which lives above this tier.
    pub fn sample_in_stage_time(
        &self,
        samples: &TimeSampleMap,
        time: f64,
        interp: impl Fn(&TimeSampleMap, f64) -> Option<Value>,
    ) -> Option<Value> {
        let mut value = interp(samples, self.inverse().apply(time))?;
        self.apply_to_value(&mut value);
        Some(value)
    }

    /// Returns the inverse offset, undoing [`apply`](Self::apply): if `self`
    /// maps a source time `t` to `offset + scale * t`, the inverse maps that
    /// result back to `t`. The identity inverts to itself; a `scale == 0`
    /// offset has no inverse and yields the identity.
    #[inline]
    pub fn inverse(&self) -> LayerOffset {
        if self.scale == 0.0 {
            return LayerOffset::IDENTITY;
        }
        LayerOffset {
            offset: -self.offset / self.scale,
            scale: 1.0 / self.scale,
        }
    }

    /// Returns `true` if this offset is well-formed for composition:
    /// finite `offset` and a strictly positive, finite `scale`.
    ///
    /// Per spec 10.3.1.1 / 10.3.2.1.2, a non-positive scale is a composition
    /// error.
    #[inline]
    pub fn is_valid_composition(&self) -> bool {
        self.offset.is_finite() && self.scale.is_finite() && self.scale > 0.0
    }

    /// Returns this offset if valid for composition, or the identity otherwise.
    ///
    /// Matches OpenUSD behaviour of silently dropping back to identity when a
    /// non-positive or non-finite scale is authored.
    #[inline]
    pub fn sanitized(self) -> Self {
        if self.is_valid_composition() {
            self
        } else {
            Self::IDENTITY
        }
    }

    /// Concatenates `self` (outer / closer to root) with `inner` (deeper).
    ///
    /// Given two offsets where a time value `t` in the inner frame maps to
    /// the outer frame as `t * inner.scale + inner.offset`, and outer's own
    /// transform is `t * outer.scale + outer.offset`, the composed transform
    /// from the deepest frame to the outermost is:
    ///
    /// ```text
    /// offset = outer.offset + outer.scale * inner.offset
    /// scale  = outer.scale * inner.scale
    /// ```
    #[inline]
    pub fn concatenate(&self, inner: &LayerOffset) -> LayerOffset {
        LayerOffset {
            offset: self.offset + self.scale * inner.offset,
            scale: self.scale * inner.scale,
        }
    }
}

/// Represents a payload and all its meta data.
///
/// A payload represents a prim reference to an external layer. A payload
/// is similar to a prim reference (see `SdfReference`) with the major
/// difference that payloads are explicitly loaded by the user.
///
/// Unloaded payloads represent a boundary that lazy composition and
/// system behaviors will not traverse across, providing a user-visible
/// way to manage the working set of the scene.
#[derive(Debug, Default, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Payload {
    /// The asset path to the external layer.
    #[cfg_attr(feature = "serde", serde(rename = "asset", skip_serializing_if = "String::is_empty"))]
    pub asset_path: String,
    /// The root prim path to the referenced prim in the external layer.
    #[cfg_attr(feature = "serde", serde(rename = "path", skip_serializing_if = "Path::is_empty"))]
    pub prim_path: Path,
    /// The layer offset to transform time.
    #[cfg_attr(
        feature = "serde",
        serde(rename = "layerOffset", skip_serializing_if = "Option::is_none")
    )]
    pub layer_offset: Option<LayerOffset>,
}

/// Represents a reference and all its meta data.
///
/// A reference is expressed on a prim in a given layer and it identifies a
/// prim in a layer stack. All opinions in the namespace hierarchy
/// under the referenced prim will be composed with the opinions in the
/// namespace hierarchy under the referencing prim.
#[derive(Debug, Default, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Reference {
    /// The asset path to the external layer.
    #[cfg_attr(feature = "serde", serde(rename = "asset", skip_serializing_if = "String::is_empty"))]
    pub asset_path: String,
    /// The path to the referenced prim in the external layer.
    #[cfg_attr(feature = "serde", serde(rename = "path", skip_serializing_if = "Path::is_empty"))]
    pub prim_path: Path,
    /// The layer offset to transform time.
    #[cfg_attr(feature = "serde", serde(rename = "layerOffset"))]
    pub layer_offset: LayerOffset,
    /// The custom data associated with the reference.
    #[cfg_attr(
        feature = "serde",
        serde(rename = "customData", skip_serializing_if = "HashMap::is_empty")
    )]
    pub custom_data: HashMap<String, Value>,
}

mod list_op;

pub use list_op::ListOp;

/// A USD dictionary value (C++ `VtDictionary`): the payload of
/// [`Value::Dictionary`], keyed by name.
pub type Dictionary = std::collections::HashMap<String, Value>;

pub type IntListOp = ListOp<i32>;
pub type UintListOp = ListOp<u32>;

pub type Int64ListOp = ListOp<i64>;
pub type Uint64ListOp = ListOp<u64>;

pub type StringListOp = ListOp<String>;
pub type TokenListOp = ListOp<Token>;
pub type PathListOp = ListOp<Path>;
pub type ReferenceListOp = ListOp<Reference>;
pub type PayloadListOp = ListOp<Payload>;

pub type TimeSampleMap = Vec<(f64, Value)>;

/// A single namespace relocation `(source, target)`: the prim at `source` is
/// moved to `target` in composed namespace. An empty `target` is a deletion
/// that makes `source` a prohibited (invalid) child name. Mirrors C++
/// `SdfRelocate`, a `std::pair<SdfPath, SdfPath>`.
pub type Relocate = (Path, Path);

/// The ordered list of [`Relocate`]s authored in a layer's `relocates`
/// metadata. Mirrors C++ `SdfRelocates`, a `std::vector<SdfRelocate>`.
pub type RelocateList = Vec<Relocate>;

/// A boxed layer data source, used throughout the layer stack.
pub type LayerData = Box<dyn AbstractData>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layer_offset_identity_is_identity() {
        assert!(LayerOffset::IDENTITY.is_identity());
        assert!(LayerOffset::default().is_identity());
        assert!(!LayerOffset::new(0.0, 2.0).is_identity());
        assert!(!LayerOffset::new(1.0, 1.0).is_identity());
    }

    #[test]
    fn layer_offset_valid_composition_rejects_non_positive_scale() {
        assert!(LayerOffset::new(10.0, 1.0).is_valid_composition());
        assert!(!LayerOffset::new(10.0, 0.0).is_valid_composition());
        assert!(!LayerOffset::new(10.0, -1.0).is_valid_composition());
        assert!(!LayerOffset::new(f64::INFINITY, 1.0).is_valid_composition());
        assert!(!LayerOffset::new(0.0, f64::NAN).is_valid_composition());
    }

    #[test]
    fn samples_offset_scale() {
        let mut samples: TimeSampleMap = vec![(1.0, Value::Double(0.0)), (5.0, Value::Double(1.0))];
        LayerOffset::new(10.0, 2.0).apply_to_samples(&mut samples);
        let times: Vec<f64> = samples.iter().map(|(t, _)| *t).collect();
        assert_eq!(times, vec![12.0, 20.0]);
    }

    #[test]
    fn samples_negative_scale() {
        // Reversing the time axis must leave the keys ascending, which is what
        // a bracketing search over the result relies on.
        let mut samples: TimeSampleMap = vec![(1.0, Value::Double(0.0)), (5.0, Value::Double(1.0))];
        LayerOffset::new(0.0, -1.0).apply_to_samples(&mut samples);
        let times: Vec<f64> = samples.iter().map(|(t, _)| *t).collect();
        assert_eq!(times, vec![-5.0, -1.0]);
        assert_eq!(samples[0].1, Value::Double(1.0));
    }

    #[test]
    fn value_identity_passthrough() {
        let samples: TimeSampleMap = vec![(1.0, Value::Double(0.0))];
        let mut value = Value::TimeSamples(samples.clone());
        LayerOffset::IDENTITY.apply_to_value(&mut value);
        assert_eq!(value, Value::TimeSamples(samples));
    }

    #[test]
    fn value_time_codes() {
        let offset = LayerOffset::new(10.0, 2.0);

        let mut scalar = Value::TimeCode(TimeCode(5.0));
        offset.apply_to_value(&mut scalar);
        assert_eq!(scalar, Value::TimeCode(TimeCode(20.0)));

        let mut array = Value::TimeCodeVec(vec![TimeCode(5.0), TimeCode(10.0)]);
        offset.apply_to_value(&mut array);
        assert_eq!(array, Value::TimeCodeVec(vec![TimeCode(20.0), TimeCode(30.0)]));

        // A plain number is not a time coordinate, whatever it holds.
        let mut plain = Value::Double(5.0);
        offset.apply_to_value(&mut plain);
        assert_eq!(plain, Value::Double(5.0));
    }

    #[test]
    fn value_nested() {
        let offset = LayerOffset::new(10.0, 2.0);

        // A dictionary carries timecodes at any depth.
        let inner = HashMap::from([("deep".to_string(), Value::TimeCode(TimeCode(5.0)))]);
        let mut dict = Value::Dictionary(HashMap::from([
            ("nested".to_string(), Value::Dictionary(inner)),
            ("kept".to_string(), Value::Double(5.0)),
        ]));
        assert!(dict.holds_time_codes());
        offset.apply_to_value(&mut dict);
        let entries = dict.try_as_dictionary_ref().expect("dictionary");
        assert_eq!(entries.get("kept"), Some(&Value::Double(5.0)));
        let nested = entries.get("nested").expect("nested").try_as_dictionary_ref().unwrap();
        assert_eq!(nested.get("deep"), Some(&Value::TimeCode(TimeCode(20.0))));

        // A sample map's keys and its time-valued samples both move.
        let mut samples = Value::TimeSamples(vec![(1.0, Value::TimeCode(TimeCode(5.0)))]);
        offset.apply_to_value(&mut samples);
        assert_eq!(
            samples,
            Value::TimeSamples(vec![(12.0, Value::TimeCode(TimeCode(20.0)))])
        );
    }

    #[test]
    fn layer_offset_sanitized_drops_invalid_to_identity() {
        assert_eq!(LayerOffset::new(10.0, 2.0).sanitized(), LayerOffset::new(10.0, 2.0));
        assert_eq!(LayerOffset::new(5.0, -1.0).sanitized(), LayerOffset::IDENTITY);
        assert_eq!(LayerOffset::new(5.0, 0.0).sanitized(), LayerOffset::IDENTITY);
    }

    #[test]
    fn layer_offset_concatenate_matches_spec_formula() {
        let outer = LayerOffset::new(10.0, 2.0);
        let inner = LayerOffset::new(20.0, 1.0);
        // Matches BasicTimeOffset_root pcp.txt: (10,2) concat (20,1) = (50, 2).
        assert_eq!(outer.concatenate(&inner), LayerOffset::new(50.0, 2.0));
    }

    #[test]
    fn layer_offset_concatenate_is_associative() {
        let a = LayerOffset::new(10.0, 2.0);
        let b = LayerOffset::new(20.0, 0.5);
        let c = LayerOffset::new(5.0, 3.0);
        let ab_c = a.concatenate(&b).concatenate(&c);
        let a_bc = a.concatenate(&b.concatenate(&c));
        assert!((ab_c.offset - a_bc.offset).abs() < 1e-12);
        assert!((ab_c.scale - a_bc.scale).abs() < 1e-12);
    }

    #[test]
    fn layer_offset_identity_is_neutral() {
        let a = LayerOffset::new(10.0, 2.0);
        assert_eq!(a.concatenate(&LayerOffset::IDENTITY), a);
        assert_eq!(LayerOffset::IDENTITY.concatenate(&a), a);
    }

    #[test]
    fn layer_offset_inverse_undoes_apply() {
        // A dyadic scale round-trips exactly.
        let a = LayerOffset::new(10.0, 2.0);
        assert_eq!(a.inverse(), LayerOffset::new(-5.0, 0.5));
        assert_eq!(a.inverse().apply(a.apply(7.0)), 7.0);
        // A non-dyadic scale (e.g. a 1/3 retiming ratio) round-trips only to
        // within float rounding, not exactly.
        let b = LayerOffset::new(1.0, 3.0);
        assert!((b.inverse().apply(b.apply(7.0)) - 7.0).abs() < 1e-9);
        // The identity inverts to itself; a zero scale has no inverse.
        assert_eq!(LayerOffset::IDENTITY.inverse(), LayerOffset::IDENTITY);
        assert_eq!(LayerOffset::new(3.0, 0.0).inverse(), LayerOffset::IDENTITY);
    }
}
