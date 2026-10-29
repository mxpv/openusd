//! A [`Value`] as C++ streams the `VtValue` holding it (`operator<<` over
//! `VtValue`, the text C++ `TfStringify` makes of one).

use std::fmt::{self, Write as _};
use std::hash::Hash;
use std::slice;

use bytemuck::Pod;

use crate::{gf, sdf, tf};

use super::{Dictionary, Value};

/// The text C++ writes for the `VtValue` this value converts to, through
/// `VtStreamOut` (`vt/streamOut.h`), as C++ `TfStringify` makes it of one.
///
/// - A bool is `1` or `0`, and a `uchar` its number.
/// - A float or double takes the shortest digits that read back to it; a
///   half, a time code and a layer offset take six significant digits
///   (`%g`).
/// - A string, a token and an unregistered value are written raw, unquoted;
///   an asset path between `@`s, as [`sdf::AssetPath::asset_path`] gives it.
/// - An array is `[a, b]`, a vector or quaternion `(a, b, c)` (a quaternion
///   real part first), a matrix `( (a, b), (c, d) )`, and a dictionary
///   `{'key': value}` sorted by key.
/// - A list op is its C++ type alias with each list it authors, as
///   `SdfTokenListOp(Prepended Items: [a, b])`.
/// - A value block is `None`, an opaque value `OpaqueValue`, and an empty
///   value nothing.
///
/// C++ writes a `SdfPathVector` and a vector of layer offsets through the
/// generic `std::vector` stream of `tf/ostreamMethods.h`, `[ a b ]`. C++
/// writes the token and string vectors of fields such as `primOrder` and
/// `subLayers` that way too, but a [`Value::TokenVec`] or
/// [`Value::StringVec`] does not say which field it came from and is written
/// as an array, `[a, b]`.
///
/// A width and alignment pad the whole text, and a precision cuts it to that
/// many characters, as for a `str`.
impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO(perf): the `tf` number writers take a `String`, so the text is
        // built apart and copied; writing them over `fmt::Write` would stream
        // it straight into `f`.
        let mut s = String::new();
        stream(&mut s, self);
        f.pad(&s)
    }
}

/// Writes `value` as [`Value`]'s `Display` describes.
fn stream(s: &mut String, value: &Value) {
    match value {
        Value::None | Value::Value => {}
        Value::Bool(v) => boolean(s, v),
        Value::BoolVec(v) => separated(s, ARRAY, v, boolean),
        Value::Uchar(v) => display(s, v),
        Value::UcharVec(v) => separated(s, ARRAY, v, display),
        Value::Int(v) => display(s, v),
        Value::IntVec(v) => separated(s, ARRAY, v, display),
        Value::Uint(v) => display(s, v),
        Value::UintVec(v) => separated(s, ARRAY, v, display),
        Value::Int64(v) => display(s, v),
        Value::Int64Vec(v) => separated(s, ARRAY, v, display),
        Value::Uint64(v) => display(s, v),
        Value::Uint64Vec(v) => separated(s, ARRAY, v, display),
        Value::Half(v) => half(s, v),
        Value::HalfVec(v) => separated(s, ARRAY, v, half),
        Value::Float(v) => float(s, v),
        Value::FloatVec(v) => separated(s, ARRAY, v, float),
        Value::Double(v) => float(s, v),
        Value::DoubleVec(v) => separated(s, ARRAY, v, float),
        Value::String(v) | Value::UnregisteredValue(v) => s.push_str(v),
        Value::StringVec(v) => separated(s, ARRAY, v, text),
        Value::Token(v) => s.push_str(v.as_str()),
        Value::TokenVec(v) => separated(s, ARRAY, v, text),
        Value::AssetPath(v) => asset_path(s, v),
        Value::AssetPathVec(v) => separated(s, ARRAY, v, asset_path),
        Value::Opaque => s.push_str("OpaqueValue"),
        Value::Quath(v) => gf_tuple(s, v, half),
        Value::Quatf(v) => gf_tuple(s, v, float::<f32>),
        Value::Quatd(v) => gf_tuple(s, v, float::<f64>),
        Value::QuathVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, half)),
        Value::QuatfVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, float::<f32>)),
        Value::QuatdVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, float::<f64>)),
        Value::Vec2h(v) => gf_tuple(s, v, half),
        Value::Vec2f(v) => gf_tuple(s, v, float::<f32>),
        Value::Vec2d(v) => gf_tuple(s, v, float::<f64>),
        Value::Vec2i(v) => gf_tuple(s, v, display),
        Value::Vec2hVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, half)),
        Value::Vec2fVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, float::<f32>)),
        Value::Vec2dVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, float::<f64>)),
        Value::Vec2iVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, display)),
        Value::Vec3h(v) => gf_tuple(s, v, half),
        Value::Vec3f(v) => gf_tuple(s, v, float::<f32>),
        Value::Vec3d(v) => gf_tuple(s, v, float::<f64>),
        Value::Vec3i(v) => gf_tuple(s, v, display),
        Value::Vec3hVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, half)),
        Value::Vec3fVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, float::<f32>)),
        Value::Vec3dVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, float::<f64>)),
        Value::Vec3iVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, display)),
        Value::Vec4h(v) => gf_tuple(s, v, half),
        Value::Vec4f(v) => gf_tuple(s, v, float::<f32>),
        Value::Vec4d(v) => gf_tuple(s, v, float::<f64>),
        Value::Vec4i(v) => gf_tuple(s, v, display),
        Value::Vec4hVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, half)),
        Value::Vec4fVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, float::<f32>)),
        Value::Vec4dVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, float::<f64>)),
        Value::Vec4iVec(v) => separated(s, ARRAY, v, |s, v| gf_tuple(s, v, display)),
        Value::Matrix2d(m) => matrix(s, &m.0, 2),
        Value::Matrix3d(m) => matrix(s, &m.0, 3),
        Value::Matrix4d(m) => matrix(s, &m.0, 4),
        Value::Matrix2dVec(v) => separated(s, ARRAY, v, |s, m| matrix(s, &m.0, 2)),
        Value::Matrix3dVec(v) => separated(s, ARRAY, v, |s, m| matrix(s, &m.0, 3)),
        Value::Matrix4dVec(v) => separated(s, ARRAY, v, |s, m| matrix(s, &m.0, 4)),
        Value::Specifier(v) => s.push_str(specifier(*v)),
        Value::Permission(v) => s.push_str(permission(*v)),
        Value::Variability(v) => s.push_str(variability(*v)),
        Value::Dictionary(v) | Value::UnregisteredDictionary(v) => dictionary(s, v),
        Value::TokenListOp(op) => list_op(s, "SdfTokenListOp", op, text),
        Value::StringListOp(op) => list_op(s, "SdfStringListOp", op, text),
        Value::UnregisteredValueListOp(op) => list_op(s, "SdfUnregisteredValueListOp", op, text),
        Value::PathListOp(op) => list_op(s, "SdfPathListOp", op, path),
        Value::ReferenceListOp(op) => list_op(s, "SdfReferenceListOp", op, reference),
        Value::PayloadListOp(op) => list_op(s, "SdfPayloadListOp", op, payload),
        Value::IntListOp(op) => list_op(s, "SdfIntListOp", op, display),
        Value::Int64ListOp(op) => list_op(s, "SdfInt64ListOp", op, display),
        Value::UIntListOp(op) => list_op(s, "SdfUIntListOp", op, display),
        Value::UInt64ListOp(op) => list_op(s, "SdfUInt64ListOp", op, display),
        Value::Payload(v) => payload(s, v),
        Value::PathVec(v) => vector(s, v, path),
        Value::LayerOffsetVec(v) => vector(s, v, layer_offset),
        Value::Relocates(relocates) => {
            for (source, target) in relocates {
                writeln!(s, "{source}: {target}").expect("writing to a String cannot fail");
            }
        }
        Value::VariantSelectionMap(selections) => {
            let mut sorted: Vec<_> = selections.iter().collect();
            sorted.sort();
            s.push_str("< ");
            for (set, selection) in sorted {
                write!(s, "<{set}: {selection}> ").expect("writing to a String cannot fail");
            }
            s.push('>');
        }
        Value::TimeSamples(samples) => {
            for (time, value) in samples {
                tf::stringify_general(s, *time);
                s.push_str(": ");
                stream(s, value);
                s.push('\n');
            }
        }
        Value::ValueBlock => s.push_str("None"),
        Value::ValueVec(v) => separated(s, ARRAY, v, stream),
        Value::TimeCode(v) => time_code(s, v),
        Value::TimeCodeVec(v) => separated(s, ARRAY, v, time_code),
        Value::PathExpression(v) => display(s, v),
        Value::PathExpressionVec(v) => separated(s, ARRAY, v, display),
    }
}

/// `items` between the `[open, close]` brackets, separated by `", "`.
pub(crate) fn separated<T>(s: &mut String, [open, close]: [&str; 2], items: &[T], item: impl Fn(&mut String, &T)) {
    s.push_str(open);
    for (i, value) in items.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        item(s, value);
    }
    s.push_str(close);
}

/// The brackets of `[a, b]`, C++ `VtArray`'s stream and
/// `std::vector<VtValue>`'s.
const ARRAY: [&str; 2] = ["[", "]"];

/// The brackets of `(a, b, c)`, a `Gf` vector's or quaternion's stream.
pub(crate) const TUPLE: [&str; 2] = ["(", ")"];

/// A [`TUPLE`] of the components of `v`, a `gf` vector or quaternion, in
/// their memory order: a quaternion's real part comes first, as C++ streams
/// it.
pub(crate) fn gf_tuple<V: GfTuple>(s: &mut String, v: &V, component: impl Fn(&mut String, &V::Component)) {
    separated(s, TUPLE, bytemuck::cast_slice(slice::from_ref(v)), component);
}

/// A `gf` vector or quaternion, a run of [`Component`](Self::Component)s in
/// memory.
pub(crate) trait GfTuple: Pod {
    /// The type of each component.
    type Component: Pod;
}

macro_rules! gf_tuple {
    ($($ty:ident: $component:ty),* $(,)?) => {
        $(impl GfTuple for gf::$ty {
            type Component = $component;
        })*
    };
}

gf_tuple!(
    Vec2h: gf::f16, Vec3h: gf::f16, Vec4h: gf::f16, Quath: gf::f16,
    Vec2f: f32, Vec3f: f32, Vec4f: f32, Quatf: f32,
    Vec2d: f64, Vec3d: f64, Vec4d: f64, Quatd: f64,
    Vec2i: i32, Vec3i: i32, Vec4i: i32,
);

/// `( (a, b), (c, d) )`, a `GfMatrix`'s stream of its `dim` rows.
pub(crate) fn matrix(s: &mut String, entries: &[f64], dim: usize) {
    s.push_str("( ");
    for (i, row) in entries.chunks(dim).enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        separated(s, TUPLE, row, float);
    }
    s.push_str(" )");
}

/// `[ a b ]`, the generic `std::vector` stream of `tf/ostreamMethods.h`.
fn vector<T>(s: &mut String, items: &[T], item: impl Fn(&mut String, &T)) {
    s.push_str("[ ");
    for value in items {
        item(s, value);
        s.push(' ');
    }
    s.push(']');
}

/// `{'key': value}`, a `VtDictionary`'s stream, sorted by key as its
/// `std::map` is.
fn dictionary(s: &mut String, dict: &Dictionary) {
    let mut entries: Vec<_> = dict.iter().collect();
    entries.sort_by_key(|(key, _)| *key);
    separated(s, ["{", "}"], &entries, |s, (key, value)| {
        write!(s, "'{key}': ").expect("writing to a String cannot fail");
        stream(s, value);
    });
}

/// `Alias(Name Items: [a, b], …)`, an `SdfListOp`'s stream: the explicit list
/// alone where the op is explicit, empty or not, and otherwise each list it
/// holds of deleted, added, prepended, appended and ordered items.
fn list_op<T: Clone + PartialEq + Hash>(
    s: &mut String,
    alias: &str,
    op: &sdf::ListOp<T>,
    item: impl Fn(&mut String, &T),
) {
    let lists: Vec<(&str, &[T])> = if op.is_explicit() {
        vec![("Explicit", op.explicit_items())]
    } else {
        [
            ("Deleted", op.deleted_items()),
            ("Added", op.added_items()),
            ("Prepended", op.prepended_items()),
            ("Appended", op.appended_items()),
            ("Ordered", op.ordered_items()),
        ]
        .into_iter()
        .filter(|(_, items)| !items.is_empty())
        .collect()
    };
    s.push_str(alias);
    separated(s, ["(", ")"], &lists, |s, (name, items)| {
        write!(s, "{name} Items: ").expect("writing to a String cannot fail");
        separated(s, ARRAY, items, &item);
    });
}

/// A value through its `Display`, which for a number is its plain
/// `std::ostream` stream.
pub(crate) fn display<T: fmt::Display>(s: &mut String, v: &T) {
    write!(s, "{v}").expect("writing to a String cannot fail");
}

/// A bool as C++ streams one in a `VtValue`, `1` or `0`.
pub(crate) fn boolean(s: &mut String, v: &bool) {
    s.push(if *v { '1' } else { '0' });
}

/// A string or token, raw.
fn text(s: &mut String, v: &impl AsRef<str>) {
    s.push_str(v.as_ref());
}

/// A float or double through C++ `TfStreamFloat` / `TfStreamDouble`.
pub(crate) fn float<F: zmij::Float + Into<f64>>(s: &mut String, v: &F) {
    tf::stringify_float(s, *v);
}

/// A half through `std::ostream`, as the float it widens to.
pub(crate) fn half(s: &mut String, v: &gf::f16) {
    tf::stringify_general(s, v.to_f64());
}

/// A time code through `std::ostream`, as its double.
fn time_code(s: &mut String, v: &sdf::TimeCode) {
    tf::stringify_general(s, v.0);
}

/// `@path@` (C++ `SdfAssetPath`'s stream).
fn asset_path(s: &mut String, v: &sdf::AssetPath) {
    write!(s, "@{}@", v.asset_path()).expect("writing to a String cannot fail");
}

/// A path's text.
fn path(s: &mut String, v: &sdf::Path) {
    s.push_str(v.as_str());
}

/// `SdfLayerOffset(offset, scale)`.
fn layer_offset(s: &mut String, v: &sdf::LayerOffset) {
    s.push_str("SdfLayerOffset(");
    tf::stringify_general(s, v.offset);
    s.push_str(", ");
    tf::stringify_general(s, v.scale);
    s.push(')');
}

/// `SdfReference(asset, prim, offset, customData)`, the asset path raw.
fn reference(s: &mut String, v: &sdf::Reference) {
    write!(s, "SdfReference({}, {}, ", v.asset_path, v.prim_path).expect("writing to a String cannot fail");
    layer_offset(s, &v.layer_offset);
    s.push_str(", ");
    dictionary(s, &v.custom_data);
    s.push(')');
}

/// `SdfPayload(asset, prim, offset)`, the asset path raw.
fn payload(s: &mut String, v: &sdf::Payload) {
    write!(s, "SdfPayload({}, {}, ", v.asset_path, v.prim_path).expect("writing to a String cannot fail");
    layer_offset(s, &v.layer_offset);
    s.push(')');
}

/// The `TfEnum` name C++ streams an `SdfSpecifier` by.
fn specifier(v: sdf::Specifier) -> &'static str {
    match v {
        sdf::Specifier::Def => "SdfSpecifierDef",
        sdf::Specifier::Over => "SdfSpecifierOver",
        sdf::Specifier::Class => "SdfSpecifierClass",
    }
}

/// The `TfEnum` name C++ streams an `SdfPermission` by.
fn permission(v: sdf::Permission) -> &'static str {
    match v {
        sdf::Permission::Public => "SdfPermissionPublic",
        sdf::Permission::Private => "SdfPermissionPrivate",
    }
}

/// The `TfEnum` name C++ streams an `SdfVariability` by.
fn variability(v: sdf::Variability) -> &'static str {
    match v {
        sdf::Variability::Varying => "SdfVariabilityVarying",
        sdf::Variability::Uniform => "SdfVariabilityUniform",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::sdf;

    /// What C++ `TfStringify` writes for each value, per `VtStreamOut`.
    #[test]
    fn stream_out_forms() {
        let dict = |entries: &[(&str, Value)]| {
            Value::Dictionary(
                entries
                    .iter()
                    .map(|(key, value)| ((*key).to_owned(), value.clone()))
                    .collect(),
            )
        };
        let prepended =
            sdf::TokenListOp::default().with(sdf::ListOpType::Prepended, [tf::Token::from("a"), tf::Token::from("b")]);
        let mixed = sdf::IntListOp::default()
            .with(sdf::ListOpType::Deleted, [1])
            .with(sdf::ListOpType::Appended, [2]);
        let mut evaluated_empty = sdf::AssetPath::new("a.png");
        evaluated_empty.set_evaluated_path("");
        for (value, written) in [
            (Value::None, ""),
            (Value::Bool(true), "1"),
            (Value::BoolVec(vec![true, false]), "[1, 0]"),
            (Value::Uchar(65), "65"),
            (Value::Int(-7), "-7"),
            (Value::Float(0.1), "0.1"),
            (Value::Double(1e20), "1e20"),
            (Value::Double(1e-7), "1e-7"),
            (Value::Half(gf::f16::from_f64(0.1)), "0.0999756"),
            (Value::String("hello".into()), "hello"),
            (Value::StringVec(vec!["a".into(), "b".into()]), "[a, b]"),
            (Value::Token(tf::Token::from("foo")), "foo"),
            (Value::AssetPath(sdf::AssetPath::new("a.png")), "@a.png@"),
            (Value::AssetPath(evaluated_empty), "@a.png@"),
            (Value::IntVec(vec![]), "[]"),
            (Value::IntVec(vec![1, 2, 3]), "[1, 2, 3]"),
            (Value::Vec3f(gf::vec3f(1.0, 2.0, 3.0)), "(1, 2, 3)"),
            (Value::Vec2d(gf::vec2d(0.1, 1e20)), "(0.1, 1e20)"),
            (Value::Vec4i(gf::vec4i(1, 2, 3, 4)), "(1, 2, 3, 4)"),
            (Value::Quatf(gf::quatf(1.0, 0.0, 0.5, 0.0)), "(1, 0, 0.5, 0)"),
            (Value::Matrix2d(gf::Mat2d::IDENTITY), "( (1, 0), (0, 1) )"),
            (
                dict(&[
                    ("b", Value::String("hello".into())),
                    ("a", Value::Int(1)),
                    ("c", dict(&[("d", Value::Vec2i(gf::vec2i(1, 2)))])),
                ]),
                "{'a': 1, 'b': hello, 'c': {'d': (1, 2)}}",
            ),
            (dict(&[]), "{}"),
            (Value::TokenListOp(prepended), "SdfTokenListOp(Prepended Items: [a, b])"),
            (
                Value::IntListOp(mixed),
                "SdfIntListOp(Deleted Items: [1], Appended Items: [2])",
            ),
            (
                Value::IntListOp(sdf::IntListOp::explicit(vec![])),
                "SdfIntListOp(Explicit Items: [])",
            ),
            (Value::IntListOp(sdf::IntListOp::default()), "SdfIntListOp()"),
            (Value::Specifier(sdf::Specifier::Def), "SdfSpecifierDef"),
            (Value::TimeCode(sdf::TimeCode(1234567.0)), "1.23457e+06"),
            (Value::ValueBlock, "None"),
            (Value::Opaque, "OpaqueValue"),
            (
                Value::ValueVec(vec![Value::Int(1), Value::Token(tf::Token::from("a"))]),
                "[1, a]",
            ),
        ] {
            assert_eq!(value.to_string(), written, "{value:?}");
        }
        assert_eq!(format!("{:>4}", Value::Int(7)), "   7", "width pads the text");
    }
}
