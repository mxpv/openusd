//! One `vt::Value` as the Rust that rebuilds it.
//!
//! A schema's fallbacks and metadata are values, and a declaration table holds
//! them as expressions rather than as parsed data. Which shapes can be written
//! is therefore part of what the generator supports, so the match below names
//! every `vt::Value` variant: a new one does not compile until someone decides
//! whether a schema can declare it and what it should look like.
//!
//! A kind a schema cannot declare travels back as its [`vt::ValueKind`], which
//! the caller reports against the field that held it.

use openusd::{gf, tf, vt};

use super::ident;
use proc_macro2::{Ident, Literal, TokenStream};
use quote::quote;

/// One `gf` value as the call that rebuilds it, and one array of them as the
/// vector of those calls.
///
/// The families differ only in how many components they carry and what those
/// are called, so they are written once here rather than a dozen times below.
macro_rules! gf {
    ($variant:ident, $ctor:ident, $write:expr, $value:expr, $($component:ident),+) => {{
        let value = $value;
        let components: Vec<TokenStream> = vec![$($write(value.$component)),+];
        quote! { ::openusd::vt::Value::$variant(::openusd::gf::$ctor(#(#components),*)) }
    }};
}

macro_rules! gf_array {
    ($variant:ident, $ctor:ident, $write:expr, $values:expr, $($component:ident),+) => {{
        let items: Vec<TokenStream> = $values
            .iter()
            .map(|value| {
                let components: Vec<TokenStream> = vec![$($write(value.$component)),+];
                quote! { ::openusd::gf::$ctor(#(#components),*) }
            })
            .collect();
        quote! { ::openusd::vt::Value::$variant(::std::vec![#(#items),*]) }
    }};
}

/// A value as the Rust that rebuilds it, and `None` for one no literal covers.
///
/// Only what a schema actually declares needs to be here: a fallback or a piece
/// of metadata. A kind this does not cover stops the build rather than being
/// dropped or replaced, since a schema whose fallback went missing would answer
/// differently from the one it was generated from.
pub(super) fn value_expr(value: &vt::Value) -> Result<TokenStream, vt::ValueKind> {
    Ok(match value {
        // A property authored `= None` blocks the fallback it would otherwise
        // inherit, which is a value like any other here. An `opaque` attribute
        // carries no value at all, and says so with one.
        vt::Value::ValueBlock => quote! { ::openusd::vt::Value::ValueBlock },
        vt::Value::Opaque => quote! { ::openusd::vt::Value::Opaque },
        vt::Value::Bool(value) => quote! { ::openusd::vt::Value::Bool(#value) },
        vt::Value::Uchar(value) => quote! { ::openusd::vt::Value::Uchar(#value) },
        vt::Value::Int(value) => quote! { ::openusd::vt::Value::Int(#value) },
        vt::Value::Uint(value) => quote! { ::openusd::vt::Value::Uint(#value) },
        vt::Value::Int64(value) => quote! { ::openusd::vt::Value::Int64(#value) },
        vt::Value::Uint64(value) => quote! { ::openusd::vt::Value::Uint64(#value) },
        vt::Value::Half(value) => {
            let value = half(*value);
            quote! { ::openusd::vt::Value::Half(#value) }
        }
        vt::Value::Float(value) => {
            let value = float(*value);
            quote! { ::openusd::vt::Value::Float(#value) }
        }
        vt::Value::Double(value) => {
            let value = double(*value);
            quote! { ::openusd::vt::Value::Double(#value) }
        }
        vt::Value::TimeCode(value) => {
            let value = double(value.value());
            quote! { ::openusd::vt::Value::TimeCode(::openusd::sdf::TimeCode(#value)) }
        }
        // A field of one of these shapes is written through the `Field`
        // constructor for it; inside a dictionary there is no constructor to
        // reach, so they are values here too.
        vt::Value::String(text) => {
            let text = text.as_str();
            quote! { ::openusd::vt::Value::String(::std::string::String::from(#text)) }
        }
        vt::Value::StringVec(texts) => {
            let texts = texts.iter().map(String::as_str);
            quote! {
                ::openusd::vt::Value::StringVec(::std::vec![#(::std::string::String::from(#texts)),*])
            }
        }
        vt::Value::Token(token) => {
            let token = token.as_str();
            quote! { ::openusd::vt::Value::token(#token) }
        }
        vt::Value::TokenVec(tokens) => {
            let tokens = tokens.iter().map(tf::Token::as_str);
            quote! {
                ::openusd::vt::Value::TokenVec(::std::vec![#(::openusd::tf::Token::new(#tokens)),*])
            }
        }
        vt::Value::AssetPath(path) => {
            let path = path.authored_path.as_str();
            quote! { ::openusd::vt::Value::AssetPath(::openusd::sdf::AssetPath::new(#path)) }
        }

        vt::Value::BoolVec(values) => quote! { ::openusd::vt::Value::BoolVec(::std::vec![#(#values),*]) },
        vt::Value::UcharVec(values) => quote! { ::openusd::vt::Value::UcharVec(::std::vec![#(#values),*]) },
        vt::Value::IntVec(values) => quote! { ::openusd::vt::Value::IntVec(::std::vec![#(#values),*]) },
        vt::Value::UintVec(values) => quote! { ::openusd::vt::Value::UintVec(::std::vec![#(#values),*]) },
        vt::Value::Int64Vec(values) => quote! { ::openusd::vt::Value::Int64Vec(::std::vec![#(#values),*]) },
        vt::Value::Uint64Vec(values) => quote! { ::openusd::vt::Value::Uint64Vec(::std::vec![#(#values),*]) },
        vt::Value::HalfVec(values) => {
            let values = values.iter().map(|value| half(*value));
            quote! { ::openusd::vt::Value::HalfVec(::std::vec![#(#values),*]) }
        }
        vt::Value::FloatVec(values) => {
            let values = values.iter().map(|value| float(*value));
            quote! { ::openusd::vt::Value::FloatVec(::std::vec![#(#values),*]) }
        }
        vt::Value::DoubleVec(values) => {
            let values = values.iter().map(|value| double(*value));
            quote! { ::openusd::vt::Value::DoubleVec(::std::vec![#(#values),*]) }
        }
        vt::Value::AssetPathVec(paths) => {
            let paths = paths.iter().map(|path| path.authored_path.as_str());
            quote! {
                ::openusd::vt::Value::AssetPathVec(::std::vec![#(::openusd::sdf::AssetPath::new(#paths)),*])
            }
        }

        vt::Value::Vec2i(value) => gf!(Vec2i, vec2i, int, value, x, y),
        vt::Value::Vec3i(value) => gf!(Vec3i, vec3i, int, value, x, y, z),
        vt::Value::Vec4i(value) => gf!(Vec4i, vec4i, int, value, x, y, z, w),
        vt::Value::Vec2h(value) => gf!(Vec2h, vec2h, half, value, x, y),
        vt::Value::Vec3h(value) => gf!(Vec3h, vec3h, half, value, x, y, z),
        vt::Value::Vec4h(value) => gf!(Vec4h, vec4h, half, value, x, y, z, w),
        vt::Value::Vec2f(value) => gf!(Vec2f, vec2f, float, value, x, y),
        vt::Value::Vec3f(value) => gf!(Vec3f, vec3f, float, value, x, y, z),
        vt::Value::Vec4f(value) => gf!(Vec4f, vec4f, float, value, x, y, z, w),
        vt::Value::Vec2d(value) => gf!(Vec2d, vec2d, double, value, x, y),
        vt::Value::Vec3d(value) => gf!(Vec3d, vec3d, double, value, x, y, z),
        vt::Value::Vec4d(value) => gf!(Vec4d, vec4d, double, value, x, y, z, w),
        vt::Value::Quath(value) => gf!(Quath, quath, half, value, w, x, y, z),
        vt::Value::Quatf(value) => gf!(Quatf, quatf, float, value, w, x, y, z),
        vt::Value::Quatd(value) => gf!(Quatd, quatd, double, value, w, x, y, z),

        vt::Value::Vec2iVec(values) => gf_array!(Vec2iVec, vec2i, int, values, x, y),
        vt::Value::Vec3iVec(values) => gf_array!(Vec3iVec, vec3i, int, values, x, y, z),
        vt::Value::Vec4iVec(values) => gf_array!(Vec4iVec, vec4i, int, values, x, y, z, w),
        vt::Value::Vec2hVec(values) => gf_array!(Vec2hVec, vec2h, half, values, x, y),
        vt::Value::Vec3hVec(values) => gf_array!(Vec3hVec, vec3h, half, values, x, y, z),
        vt::Value::Vec4hVec(values) => gf_array!(Vec4hVec, vec4h, half, values, x, y, z, w),
        vt::Value::Vec2fVec(values) => gf_array!(Vec2fVec, vec2f, float, values, x, y),
        vt::Value::Vec3fVec(values) => gf_array!(Vec3fVec, vec3f, float, values, x, y, z),
        vt::Value::Vec4fVec(values) => gf_array!(Vec4fVec, vec4f, float, values, x, y, z, w),
        vt::Value::Vec2dVec(values) => gf_array!(Vec2dVec, vec2d, double, values, x, y),
        vt::Value::Vec3dVec(values) => gf_array!(Vec3dVec, vec3d, double, values, x, y, z),
        vt::Value::Vec4dVec(values) => gf_array!(Vec4dVec, vec4d, double, values, x, y, z, w),
        vt::Value::QuathVec(values) => gf_array!(QuathVec, quath, half, values, w, x, y, z),
        vt::Value::QuatfVec(values) => gf_array!(QuatfVec, quatf, float, values, w, x, y, z),
        vt::Value::QuatdVec(values) => gf_array!(QuatdVec, quatd, double, values, w, x, y, z),

        // The matrix types are not named after the variants that carry them.
        vt::Value::Matrix2d(value) => matrix(&value.0, "Matrix2d", "Mat2d"),
        vt::Value::Matrix3d(value) => matrix(&value.0, "Matrix3d", "Mat3d"),
        vt::Value::Matrix4d(value) => matrix(&value.0, "Matrix4d", "Mat4d"),
        vt::Value::Matrix2dVec(values) => {
            matrices(values.iter().map(|value| value.0.as_slice()), "Matrix2dVec", "Mat2d")
        }
        vt::Value::Matrix3dVec(values) => {
            matrices(values.iter().map(|value| value.0.as_slice()), "Matrix3dVec", "Mat3d")
        }
        vt::Value::Matrix4dVec(values) => {
            matrices(values.iter().map(|value| value.0.as_slice()), "Matrix4dVec", "Mat4d")
        }

        vt::Value::TimeCodeVec(values) => {
            let values = values.iter().map(|value| double(value.value()));
            quote! {
                ::openusd::vt::Value::TimeCodeVec(::std::vec![#(::openusd::sdf::TimeCode(#values)),*])
            }
        }
        vt::Value::PathExpression(expression) => {
            let text = expression.to_string();
            quote! {
                ::openusd::vt::Value::PathExpression(::openusd::sdf::PathExpression::parse(#text))
            }
        }
        vt::Value::PathExpressionVec(expressions) => {
            let texts = expressions.iter().map(ToString::to_string);
            quote! {
                ::openusd::vt::Value::PathExpressionVec(
                    ::std::vec![#(::openusd::sdf::PathExpression::parse(#texts)),*],
                )
            }
        }
        vt::Value::Dictionary(entries) => {
            let entries = dictionary(entries)?;
            quote! { ::openusd::vt::Value::Dictionary(#entries) }
        }
        // Named rather than caught by a wildcard: each is a shape no schema
        // can give a property, so a declaration holding one is a mistake to
        // report rather than a value to write. Composition arcs and the
        // list-ops behind them never reach a schematics; `TimeSamples` is a
        // value over time, which a fallback is not; `Specifier`, `Permission`
        // and `Variability` are a spec's own declaration, which the
        // declaration already carries; and the rest are internal to value
        // resolution.
        vt::Value::None
        | vt::Value::Value
        | vt::Value::ValueVec(_)
        | vt::Value::Specifier(_)
        | vt::Value::Permission(_)
        | vt::Value::Variability(_)
        | vt::Value::TokenListOp(_)
        | vt::Value::StringListOp(_)
        | vt::Value::PathListOp(_)
        | vt::Value::ReferenceListOp(_)
        | vt::Value::IntListOp(_)
        | vt::Value::Int64ListOp(_)
        | vt::Value::UIntListOp(_)
        | vt::Value::UInt64ListOp(_)
        | vt::Value::PayloadListOp(_)
        | vt::Value::Payload(_)
        | vt::Value::PathVec(_)
        | vt::Value::Relocates(_)
        | vt::Value::VariantSelectionMap(_)
        | vt::Value::TimeSamples(_)
        | vt::Value::LayerOffsetVec(_)
        | vt::Value::UnregisteredValue(_)
        | vt::Value::UnregisteredValueListOp(_)
        | vt::Value::UnregisteredDictionary(_) => return Err(vt::ValueKind::from(value)),
    })
}

/// A matrix as the row-major array it wraps. `variant` names the value it is
/// held in and `matrix` the `gf` type, which are not always the same word.
fn matrix(cells: &[f64], variant: &str, matrix: &str) -> TokenStream {
    let (variant, matrix) = (ident(variant), ident(matrix));
    let cells = cells.iter().map(|cell| double(*cell));
    quote! { ::openusd::vt::Value::#variant(::openusd::gf::#matrix([#(#cells),*])) }
}

/// An array of matrices, each written as [`matrix`] writes one.
fn matrices<'a>(cells: impl Iterator<Item = &'a [f64]>, variant: &str, matrix: &str) -> TokenStream {
    let name = ident(matrix);
    let items = cells.map(|cells| {
        let cells = cells.iter().map(|cell| double(*cell));
        quote! { ::openusd::gf::#name([#(#cells),*]) }
    });
    let variant = ident(variant);
    quote! { ::openusd::vt::Value::#variant(::std::vec![#(#items),*]) }
}

/// A dictionary as the map that rebuilds it.
///
/// Written in key order rather than the map's own, so two runs over the same
/// schema generate the same text. A value inside it with no literal fails the
/// whole dictionary, naming its own kind rather than the dictionary's.
fn dictionary(entries: &vt::Dictionary) -> Result<TokenStream, vt::ValueKind> {
    let mut sorted: Vec<(&String, &vt::Value)> = entries.iter().collect();
    sorted.sort_by_key(|(key, _)| *key);

    let entries = sorted
        .into_iter()
        .map(|(key, value)| {
            let key = key.as_str();
            let value = value_expr(value)?;
            Ok(quote! { (::std::string::String::from(#key), #value) })
        })
        .collect::<Result<Vec<_>, vt::ValueKind>>()?;

    // `from` rather than `from_iter`: the consumer compiling this denies
    // `clippy::from_iter_instead_of_collect`, and generated code is not
    // something its author can reach in to fix.
    Ok(quote! { ::openusd::vt::Dictionary::from([#(#entries),*]) })
}

/// An `i32` as itself.
fn int(value: i32) -> TokenStream {
    quote! { #value }
}

/// An expression that reads back as exactly this `f32`.
///
/// Infinities and NaN have no literal — a physics joint's limits are authored
/// as `inf` — so they are named instead, through the primitive rather than the
/// bare type, which a schema could have taken the name of.
fn float(value: f32) -> TokenStream {
    if let Some(name) = nonfinite(value.is_nan(), value.is_infinite(), value.is_sign_negative()) {
        return quote! { ::core::primitive::f32::#name };
    }
    let value = Literal::f32_suffixed(value);
    quote! { #value }
}

/// An expression that reads back as exactly this `f64`.
fn double(value: f64) -> TokenStream {
    if let Some(name) = nonfinite(value.is_nan(), value.is_infinite(), value.is_sign_negative()) {
        return quote! { ::core::primitive::f64::#name };
    }
    let value = Literal::f64_suffixed(value);
    quote! { #value }
}

/// The constant naming a value no float literal can hold.
fn nonfinite(is_nan: bool, is_infinite: bool, is_negative: bool) -> Option<Ident> {
    let name = match (is_nan, is_infinite, is_negative) {
        (true, _, _) => "NAN",
        (_, true, false) => "INFINITY",
        (_, true, true) => "NEG_INFINITY",
        _ => return None,
    };
    Some(ident(name))
}

/// The expression that rebuilds exactly this `f16`.
///
/// Written from its bits: a half has no Rust literal, and going through an
/// `f32` would be a conversion the value has to survive rather than be
/// written.
fn half(value: gf::f16) -> TokenStream {
    let bits = value.to_bits();
    quote! { ::openusd::gf::f16::from_bits(#bits) }
}
