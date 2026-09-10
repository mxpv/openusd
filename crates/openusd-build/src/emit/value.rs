//! One `sdf::Value` as the Rust that rebuilds it.
//!
//! A schema's fallbacks and metadata are values, and a declaration table holds
//! them as expressions rather than as parsed data. Which shapes can be written
//! is therefore part of what the generator supports, so the match below names
//! every `sdf::Value` variant: a new one does not compile until someone decides
//! whether a schema can declare it and what it should look like.
//!
//! A kind a schema cannot declare travels back as its [`sdf::ValueKind`], which
//! the caller reports against the field that held it.

use openusd::{gf, sdf, tf};

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
        quote! { ::openusd::sdf::Value::$variant(::openusd::gf::$ctor(#(#components),*)) }
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
        quote! { ::openusd::sdf::Value::$variant(::std::vec![#(#items),*]) }
    }};
}

/// A value as the Rust that rebuilds it, and `None` for one no literal covers.
///
/// Only what a schema actually declares needs to be here: a fallback or a piece
/// of metadata. A kind this does not cover stops the build rather than being
/// dropped or replaced, since a schema whose fallback went missing would answer
/// differently from the one it was generated from.
pub(super) fn value_expr(value: &sdf::Value) -> Result<TokenStream, sdf::ValueKind> {
    Ok(match value {
        // A property authored `= None` blocks the fallback it would otherwise
        // inherit, which is a value like any other here. An `opaque` attribute
        // carries no value at all, and says so with one.
        sdf::Value::ValueBlock => quote! { ::openusd::sdf::Value::ValueBlock },
        sdf::Value::Opaque => quote! { ::openusd::sdf::Value::Opaque },
        sdf::Value::Bool(value) => quote! { ::openusd::sdf::Value::Bool(#value) },
        sdf::Value::Uchar(value) => quote! { ::openusd::sdf::Value::Uchar(#value) },
        sdf::Value::Int(value) => quote! { ::openusd::sdf::Value::Int(#value) },
        sdf::Value::Uint(value) => quote! { ::openusd::sdf::Value::Uint(#value) },
        sdf::Value::Int64(value) => quote! { ::openusd::sdf::Value::Int64(#value) },
        sdf::Value::Uint64(value) => quote! { ::openusd::sdf::Value::Uint64(#value) },
        sdf::Value::Half(value) => {
            let value = half(*value);
            quote! { ::openusd::sdf::Value::Half(#value) }
        }
        sdf::Value::Float(value) => {
            let value = float(*value);
            quote! { ::openusd::sdf::Value::Float(#value) }
        }
        sdf::Value::Double(value) => {
            let value = double(*value);
            quote! { ::openusd::sdf::Value::Double(#value) }
        }
        sdf::Value::TimeCode(value) => {
            let value = double(value.value());
            quote! { ::openusd::sdf::Value::TimeCode(::openusd::sdf::TimeCode(#value)) }
        }
        // A field of one of these shapes is written through the `Field`
        // constructor for it; inside a dictionary there is no constructor to
        // reach, so they are values here too.
        sdf::Value::String(text) => {
            let text = text.as_str();
            quote! { ::openusd::sdf::Value::String(::std::string::String::from(#text)) }
        }
        sdf::Value::StringVec(texts) => {
            let texts = texts.iter().map(String::as_str);
            quote! {
                ::openusd::sdf::Value::StringVec(::std::vec![#(::std::string::String::from(#texts)),*])
            }
        }
        sdf::Value::Token(token) => {
            let token = token.as_str();
            quote! { ::openusd::sdf::Value::token(#token) }
        }
        sdf::Value::TokenVec(tokens) => {
            let tokens = tokens.iter().map(tf::Token::as_str);
            quote! {
                ::openusd::sdf::Value::TokenVec(::std::vec![#(::openusd::tf::Token::new(#tokens)),*])
            }
        }
        sdf::Value::AssetPath(path) => {
            let path = path.authored_path.as_str();
            quote! { ::openusd::sdf::Value::AssetPath(::openusd::sdf::AssetPath::new(#path)) }
        }

        sdf::Value::BoolVec(values) => quote! { ::openusd::sdf::Value::BoolVec(::std::vec![#(#values),*]) },
        sdf::Value::UcharVec(values) => quote! { ::openusd::sdf::Value::UcharVec(::std::vec![#(#values),*]) },
        sdf::Value::IntVec(values) => quote! { ::openusd::sdf::Value::IntVec(::std::vec![#(#values),*]) },
        sdf::Value::UintVec(values) => quote! { ::openusd::sdf::Value::UintVec(::std::vec![#(#values),*]) },
        sdf::Value::Int64Vec(values) => quote! { ::openusd::sdf::Value::Int64Vec(::std::vec![#(#values),*]) },
        sdf::Value::Uint64Vec(values) => quote! { ::openusd::sdf::Value::Uint64Vec(::std::vec![#(#values),*]) },
        sdf::Value::HalfVec(values) => {
            let values = values.iter().map(|value| half(*value));
            quote! { ::openusd::sdf::Value::HalfVec(::std::vec![#(#values),*]) }
        }
        sdf::Value::FloatVec(values) => {
            let values = values.iter().map(|value| float(*value));
            quote! { ::openusd::sdf::Value::FloatVec(::std::vec![#(#values),*]) }
        }
        sdf::Value::DoubleVec(values) => {
            let values = values.iter().map(|value| double(*value));
            quote! { ::openusd::sdf::Value::DoubleVec(::std::vec![#(#values),*]) }
        }
        sdf::Value::AssetPathVec(paths) => {
            let paths = paths.iter().map(|path| path.authored_path.as_str());
            quote! {
                ::openusd::sdf::Value::AssetPathVec(::std::vec![#(::openusd::sdf::AssetPath::new(#paths)),*])
            }
        }

        sdf::Value::Vec2i(value) => gf!(Vec2i, vec2i, int, value, x, y),
        sdf::Value::Vec3i(value) => gf!(Vec3i, vec3i, int, value, x, y, z),
        sdf::Value::Vec4i(value) => gf!(Vec4i, vec4i, int, value, x, y, z, w),
        sdf::Value::Vec2h(value) => gf!(Vec2h, vec2h, half, value, x, y),
        sdf::Value::Vec3h(value) => gf!(Vec3h, vec3h, half, value, x, y, z),
        sdf::Value::Vec4h(value) => gf!(Vec4h, vec4h, half, value, x, y, z, w),
        sdf::Value::Vec2f(value) => gf!(Vec2f, vec2f, float, value, x, y),
        sdf::Value::Vec3f(value) => gf!(Vec3f, vec3f, float, value, x, y, z),
        sdf::Value::Vec4f(value) => gf!(Vec4f, vec4f, float, value, x, y, z, w),
        sdf::Value::Vec2d(value) => gf!(Vec2d, vec2d, double, value, x, y),
        sdf::Value::Vec3d(value) => gf!(Vec3d, vec3d, double, value, x, y, z),
        sdf::Value::Vec4d(value) => gf!(Vec4d, vec4d, double, value, x, y, z, w),
        sdf::Value::Quath(value) => gf!(Quath, quath, half, value, w, x, y, z),
        sdf::Value::Quatf(value) => gf!(Quatf, quatf, float, value, w, x, y, z),
        sdf::Value::Quatd(value) => gf!(Quatd, quatd, double, value, w, x, y, z),

        sdf::Value::Vec2iVec(values) => gf_array!(Vec2iVec, vec2i, int, values, x, y),
        sdf::Value::Vec3iVec(values) => gf_array!(Vec3iVec, vec3i, int, values, x, y, z),
        sdf::Value::Vec4iVec(values) => gf_array!(Vec4iVec, vec4i, int, values, x, y, z, w),
        sdf::Value::Vec2hVec(values) => gf_array!(Vec2hVec, vec2h, half, values, x, y),
        sdf::Value::Vec3hVec(values) => gf_array!(Vec3hVec, vec3h, half, values, x, y, z),
        sdf::Value::Vec4hVec(values) => gf_array!(Vec4hVec, vec4h, half, values, x, y, z, w),
        sdf::Value::Vec2fVec(values) => gf_array!(Vec2fVec, vec2f, float, values, x, y),
        sdf::Value::Vec3fVec(values) => gf_array!(Vec3fVec, vec3f, float, values, x, y, z),
        sdf::Value::Vec4fVec(values) => gf_array!(Vec4fVec, vec4f, float, values, x, y, z, w),
        sdf::Value::Vec2dVec(values) => gf_array!(Vec2dVec, vec2d, double, values, x, y),
        sdf::Value::Vec3dVec(values) => gf_array!(Vec3dVec, vec3d, double, values, x, y, z),
        sdf::Value::Vec4dVec(values) => gf_array!(Vec4dVec, vec4d, double, values, x, y, z, w),
        sdf::Value::QuathVec(values) => gf_array!(QuathVec, quath, half, values, w, x, y, z),
        sdf::Value::QuatfVec(values) => gf_array!(QuatfVec, quatf, float, values, w, x, y, z),
        sdf::Value::QuatdVec(values) => gf_array!(QuatdVec, quatd, double, values, w, x, y, z),

        // The matrix types are not named after the variants that carry them.
        sdf::Value::Matrix2d(value) => matrix(&value.0, "Matrix2d", "Mat2d"),
        sdf::Value::Matrix3d(value) => matrix(&value.0, "Matrix3d", "Mat3d"),
        sdf::Value::Matrix4d(value) => matrix(&value.0, "Matrix4d", "Matrix4d"),
        sdf::Value::Matrix2dVec(values) => {
            matrices(values.iter().map(|value| value.0.as_slice()), "Matrix2dVec", "Mat2d")
        }
        sdf::Value::Matrix3dVec(values) => {
            matrices(values.iter().map(|value| value.0.as_slice()), "Matrix3dVec", "Mat3d")
        }
        sdf::Value::Matrix4dVec(values) => {
            matrices(values.iter().map(|value| value.0.as_slice()), "Matrix4dVec", "Matrix4d")
        }

        sdf::Value::TimeCodeVec(values) => {
            let values = values.iter().map(|value| double(value.value()));
            quote! {
                ::openusd::sdf::Value::TimeCodeVec(::std::vec![#(::openusd::sdf::TimeCode(#values)),*])
            }
        }
        sdf::Value::PathExpression(expression) => {
            let text = expression.to_string();
            quote! {
                ::openusd::sdf::Value::PathExpression(::openusd::sdf::PathExpression::parse(#text))
            }
        }
        sdf::Value::PathExpressionVec(expressions) => {
            let texts = expressions.iter().map(ToString::to_string);
            quote! {
                ::openusd::sdf::Value::PathExpressionVec(
                    ::std::vec![#(::openusd::sdf::PathExpression::parse(#texts)),*],
                )
            }
        }
        sdf::Value::Dictionary(entries) => {
            let entries = dictionary(entries)?;
            quote! { ::openusd::sdf::Value::Dictionary(#entries) }
        }
        // Named rather than caught by a wildcard: each is a shape no schema
        // can give a property, so a declaration holding one is a mistake to
        // report rather than a value to write. Composition arcs and the
        // list-ops behind them never reach a schematics; `TimeSamples` is a
        // value over time, which a fallback is not; `Specifier`, `Permission`
        // and `Variability` are a spec's own declaration, which the
        // declaration already carries; and the rest are internal to value
        // resolution.
        sdf::Value::None
        | sdf::Value::Value
        | sdf::Value::ValueVec(_)
        | sdf::Value::Specifier(_)
        | sdf::Value::Permission(_)
        | sdf::Value::Variability(_)
        | sdf::Value::TokenListOp(_)
        | sdf::Value::StringListOp(_)
        | sdf::Value::PathListOp(_)
        | sdf::Value::ReferenceListOp(_)
        | sdf::Value::IntListOp(_)
        | sdf::Value::Int64ListOp(_)
        | sdf::Value::UIntListOp(_)
        | sdf::Value::UInt64ListOp(_)
        | sdf::Value::PayloadListOp(_)
        | sdf::Value::Payload(_)
        | sdf::Value::PathVec(_)
        | sdf::Value::Relocates(_)
        | sdf::Value::VariantSelectionMap(_)
        | sdf::Value::TimeSamples(_)
        | sdf::Value::LayerOffsetVec(_)
        | sdf::Value::UnregisteredValue(_)
        | sdf::Value::UnregisteredValueListOp(_) => return Err(sdf::ValueKind::from(value)),
    })
}

/// A matrix as the row-major array it wraps. `variant` names the value it is
/// held in and `matrix` the `gf` type, which are not always the same word.
fn matrix(cells: &[f64], variant: &str, matrix: &str) -> TokenStream {
    let (variant, matrix) = (ident(variant), ident(matrix));
    let cells = cells.iter().map(|cell| double(*cell));
    quote! { ::openusd::sdf::Value::#variant(::openusd::gf::#matrix([#(#cells),*])) }
}

/// An array of matrices, each written as [`matrix`] writes one.
fn matrices<'a>(cells: impl Iterator<Item = &'a [f64]>, variant: &str, matrix: &str) -> TokenStream {
    let name = ident(matrix);
    let items = cells.map(|cells| {
        let cells = cells.iter().map(|cell| double(*cell));
        quote! { ::openusd::gf::#name([#(#cells),*]) }
    });
    let variant = ident(variant);
    quote! { ::openusd::sdf::Value::#variant(::std::vec![#(#items),*]) }
}

/// A dictionary as the map that rebuilds it.
///
/// Written in key order rather than the map's own, so two runs over the same
/// schema generate the same text. A value inside it with no literal fails the
/// whole dictionary, naming its own kind rather than the dictionary's.
fn dictionary(entries: &sdf::Dictionary) -> Result<TokenStream, sdf::ValueKind> {
    let mut sorted: Vec<(&String, &sdf::Value)> = entries.iter().collect();
    sorted.sort_by_key(|(key, _)| *key);

    let entries = sorted
        .into_iter()
        .map(|(key, value)| {
            let key = key.as_str();
            let value = value_expr(value)?;
            Ok(quote! { (::std::string::String::from(#key), #value) })
        })
        .collect::<Result<Vec<_>, sdf::ValueKind>>()?;

    // `from` rather than `from_iter`: the consumer compiling this denies
    // `clippy::from_iter_instead_of_collect`, and generated code is not
    // something its author can reach in to fix.
    Ok(quote! { ::openusd::sdf::Dictionary::from([#(#entries),*]) })
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
