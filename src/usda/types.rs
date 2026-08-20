//! USDA value productions: the type table and the parsers that decode a
//! complete value from the token stream.
//!
//! These read from a [`Cursor`] and nothing else. Building specs, registering
//! children, and anchoring paths against the current prim stay in
//! [`super::parser`].

use std::{
    any::type_name,
    borrow::Cow,
    collections::HashMap,
    fmt::{self, Debug},
    str::FromStr,
};

use super::error::{Ctx, RawError, bail, ensure};

use crate::{gf, sdf};

use super::cursor::Cursor;
use super::token::Token;

/// Base data type without array semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Type {
    Bool,
    Uchar,
    Int,
    Int2,
    Int3,
    Int4,
    Uint,
    Int64,
    Uint64,
    Half,
    Half2,
    Half3,
    Half4,
    Float,
    Float2,
    Float3,
    Float4,
    Double,
    Double2,
    Double3,
    Double4,
    Quath,
    Quatf,
    Quatd,
    String,
    Token,
    Asset,
    TimeCode,
    PathExpression,
    Matrix2d,
    Matrix3d,
    Matrix4d,
    Dictionary,
    /// Unrecognized type name; the raw name is preserved in `TypeInfo::type_name`.
    Custom,
}

/// Result of parsing a type declaration, holding the parsed base type,
/// the original token text, and whether `[]` was present.
#[derive(Debug, Clone, Copy)]
pub(super) struct TypeInfo<'a> {
    ty: Type,
    type_name: &'a str,
    is_array: bool,
}

impl<'a> TypeInfo<'a> {
    pub(super) const fn scalar(ty: Type) -> Self {
        TypeInfo {
            ty,
            type_name: "",
            is_array: false,
        }
    }
}

impl fmt::Display for TypeInfo<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_array {
            write!(f, "{}[]", self.type_name)
        } else {
            write!(f, "{}", self.type_name)
        }
    }
}

/// Tries to parse a type declaration: a recognized type name optionally followed by `[]`.
///
/// Returns `Ok(None)` if the next token is not a known type (without consuming it).
pub(super) fn parse_type<'source>(cursor: &mut Cursor<'source>) -> Result<Option<TypeInfo<'source>>, RawError> {
    let base = match cursor.peek()? {
        Some(Token::Identifier(name)) => *name,
        Some(Token::Dictionary) => "dictionary",
        _ => return Ok(None),
    };

    let ty = parse_base_type(base).unwrap_or(Type::Custom);
    cursor.bump()?;

    let mut is_array = false;
    if cursor.at_punctuation('[')? {
        cursor.bump()?;
        cursor.expect_punctuation(']')?;
        is_array = true;
    }

    Ok(Some(TypeInfo {
        ty,
        type_name: base,
        is_array,
    }))
}

/// Decode a typed value based on USD's scalar/array/role type tables.
pub(super) fn parse_value(cursor: &mut Cursor<'_>, info: TypeInfo<'_>) -> Result<sdf::Value, RawError> {
    // None means "value block" (explicitly unset) regardless of type.
    if cursor.eat(&Token::None)? {
        return Ok(sdf::Value::ValueBlock);
    }

    let value = match (info.ty, info.is_array) {
        (Type::Bool, false) => sdf::Value::Bool(parse_bool(cursor)?),
        (Type::Bool, true) => sdf::Value::BoolVec(parse_array_with(cursor, parse_bool)?),

        (Type::Asset, false) => sdf::Value::AssetPath(cursor.expect_asset_ref()?.into()),
        (Type::Asset, true) => {
            sdf::Value::AssetPathVec(parse_array_with(cursor, |c| Ok(c.expect_asset_ref()?.into()))?)
        }

        (Type::TimeCode, false) => sdf::Value::TimeCode(parse_token::<f64>(cursor)?.into()),
        (Type::TimeCode, true) => sdf::Value::TimeCodeVec(
            parse_array::<f64>(cursor)?
                .into_iter()
                .map(sdf::TimeCode::from)
                .collect(),
        ),

        (Type::Uchar, false) => sdf::Value::Uchar(parse_token(cursor)?),
        (Type::Uchar, true) => sdf::Value::UcharVec(parse_array(cursor)?),

        (Type::Int, false) => sdf::Value::Int(parse_token(cursor)?),
        (Type::Int, true) => sdf::Value::IntVec(parse_array(cursor)?),
        (Type::Int2, false) => sdf::Value::Vec2i(parse_gf::<i32, _, 2>(cursor)?),
        (Type::Int2, true) => sdf::Value::Vec2iVec(parse_gf_array::<i32, _, 2>(cursor)?),
        (Type::Int3, false) => sdf::Value::Vec3i(parse_gf::<i32, _, 3>(cursor)?),
        (Type::Int3, true) => sdf::Value::Vec3iVec(parse_gf_array::<i32, _, 3>(cursor)?),
        (Type::Int4, false) => sdf::Value::Vec4i(parse_gf::<i32, _, 4>(cursor)?),
        (Type::Int4, true) => sdf::Value::Vec4iVec(parse_gf_array::<i32, _, 4>(cursor)?),
        (Type::Uint, false) => sdf::Value::Uint(parse_token(cursor)?),
        (Type::Uint, true) => sdf::Value::UintVec(parse_array(cursor)?),
        (Type::Int64, false) => sdf::Value::Int64(parse_token(cursor)?),
        (Type::Int64, true) => sdf::Value::Int64Vec(parse_array(cursor)?),
        (Type::Uint64, false) => sdf::Value::Uint64(parse_token(cursor)?),
        (Type::Uint64, true) => sdf::Value::Uint64Vec(parse_array(cursor)?),

        (Type::Half, false) => sdf::Value::Half(parse_token(cursor)?),
        (Type::Half, true) => sdf::Value::HalfVec(parse_array(cursor)?),
        (Type::Half2, false) => sdf::Value::Vec2h(parse_gf::<gf::f16, _, 2>(cursor)?),
        (Type::Half2, true) => sdf::Value::Vec2hVec(parse_gf_array::<gf::f16, _, 2>(cursor)?),
        (Type::Half3, false) => sdf::Value::Vec3h(parse_gf::<gf::f16, _, 3>(cursor)?),
        (Type::Half3, true) => sdf::Value::Vec3hVec(parse_gf_array::<gf::f16, _, 3>(cursor)?),
        (Type::Half4, false) => sdf::Value::Vec4h(parse_gf::<gf::f16, _, 4>(cursor)?),
        (Type::Half4, true) => sdf::Value::Vec4hVec(parse_gf_array::<gf::f16, _, 4>(cursor)?),

        (Type::Float, false) => sdf::Value::Float(parse_token(cursor)?),
        (Type::Float, true) => sdf::Value::FloatVec(parse_array(cursor)?),
        (Type::Float2, false) => sdf::Value::Vec2f(parse_gf::<f32, _, 2>(cursor)?),
        (Type::Float2, true) => sdf::Value::Vec2fVec(parse_gf_array::<f32, _, 2>(cursor)?),
        (Type::Float3, false) => sdf::Value::Vec3f(parse_gf::<f32, _, 3>(cursor)?),
        (Type::Float3, true) => sdf::Value::Vec3fVec(parse_gf_array::<f32, _, 3>(cursor)?),
        (Type::Float4, false) => sdf::Value::Vec4f(parse_gf::<f32, _, 4>(cursor)?),
        (Type::Float4, true) => sdf::Value::Vec4fVec(parse_gf_array::<f32, _, 4>(cursor)?),

        (Type::Double, false) => sdf::Value::Double(parse_token(cursor)?),
        (Type::Double, true) => sdf::Value::DoubleVec(parse_array(cursor)?),
        (Type::Double2, false) => sdf::Value::Vec2d(parse_gf::<f64, _, 2>(cursor)?),
        (Type::Double2, true) => sdf::Value::Vec2dVec(parse_gf_array::<f64, _, 2>(cursor)?),
        (Type::Double3, false) => sdf::Value::Vec3d(parse_gf::<f64, _, 3>(cursor)?),
        (Type::Double3, true) => sdf::Value::Vec3dVec(parse_gf_array::<f64, _, 3>(cursor)?),
        (Type::Double4, false) => sdf::Value::Vec4d(parse_gf::<f64, _, 4>(cursor)?),
        (Type::Double4, true) => sdf::Value::Vec4dVec(parse_gf_array::<f64, _, 4>(cursor)?),

        // Quaternion fields in USDA are (w, x, y, z) — same as gf::Quat* field order.
        (Type::Quath, false) => sdf::Value::Quath(parse_gf::<gf::f16, _, 4>(cursor)?),
        (Type::Quatf, false) => sdf::Value::Quatf(parse_gf::<f32, _, 4>(cursor)?),
        (Type::Quatd, false) => sdf::Value::Quatd(parse_gf::<f64, _, 4>(cursor)?),
        (Type::Quath, true) => sdf::Value::QuathVec(parse_gf_array::<gf::f16, _, 4>(cursor)?),
        (Type::Quatf, true) => sdf::Value::QuatfVec(parse_gf_array::<f32, _, 4>(cursor)?),
        (Type::Quatd, true) => sdf::Value::QuatdVec(parse_gf_array::<f64, _, 4>(cursor)?),

        (Type::String, false) => sdf::Value::String(cursor.expect_string()?.into_owned()),
        (Type::String, true) => sdf::Value::StringVec(parse_array(cursor)?),
        (Type::Token, false) => sdf::Value::token(cursor.expect_string()?.as_ref()),
        (Type::Token, true) => sdf::Value::token_vec(parse_array::<String>(cursor)?),

        (Type::PathExpression, false) => {
            sdf::Value::PathExpression(sdf::PathExpression::parse(cursor.expect_string()?.as_ref()))
        }
        (Type::PathExpression, true) => sdf::Value::PathExpressionVec(
            parse_array::<String>(cursor)?
                .iter()
                .map(|text| sdf::PathExpression::parse(text))
                .collect(),
        ),

        (Type::Matrix2d, false) => sdf::Value::Matrix2d(gf::Mat2d(parse_matrix::<2, 4>(cursor)?)),
        (Type::Matrix3d, false) => sdf::Value::Matrix3d(gf::Mat3d(parse_matrix::<3, 9>(cursor)?)),
        (Type::Matrix4d, false) => sdf::Value::Matrix4d(gf::Matrix4d(parse_matrix::<4, 16>(cursor)?)),
        (Type::Matrix2d, true) => {
            sdf::Value::Matrix2dVec(parse_matrix_array::<2, 4>(cursor)?.into_iter().map(gf::Mat2d).collect())
        }
        (Type::Matrix3d, true) => {
            sdf::Value::Matrix3dVec(parse_matrix_array::<3, 9>(cursor)?.into_iter().map(gf::Mat3d).collect())
        }
        (Type::Matrix4d, true) => sdf::Value::Matrix4dVec(
            parse_matrix_array::<4, 16>(cursor)?
                .into_iter()
                .map(gf::Matrix4d)
                .collect(),
        ),

        (Type::Dictionary, _) => parse_dictionary(cursor)?,

        (Type::Custom, _) => bail!("Cannot parse value for unrecognized type: {}", info.type_name),
    };

    Ok(value)
}

/// Parse a single attribute metadata value (scalar or array) from within a metadata block.
pub(super) fn parse_untyped_value(cursor: &mut Cursor<'_>) -> Result<sdf::Value, RawError> {
    // Handle array case: parse each element as a typed scalar, then collect
    // into the most specific Vec variant that fits all elements.
    if cursor.at_punctuation('[')? {
        let values = parse_array_with(cursor, parse_untyped_value)?;

        // Infer the array type from the first element.
        return Ok(match values.first() {
            Some(sdf::Value::Double(_)) => sdf::Value::DoubleVec(
                values
                    .into_iter()
                    .map(|v| v.try_as_double().unwrap_or_default())
                    .collect(),
            ),
            Some(sdf::Value::Int64(_)) => sdf::Value::Int64Vec(
                values
                    .into_iter()
                    .map(|v| v.try_as_int_64().unwrap_or_default())
                    .collect(),
            ),
            Some(sdf::Value::AssetPath(_)) => sdf::Value::AssetPathVec(
                values
                    .into_iter()
                    .map(|v| v.try_as_asset_path().unwrap_or_default())
                    .collect(),
            ),
            _ => sdf::Value::StringVec(
                values
                    .into_iter()
                    .map(|v| match v {
                        sdf::Value::String(s) => s,
                        sdf::Value::Token(s) => s.into(),
                        other => format!("{other:?}"),
                    })
                    .collect(),
            ),
        });
    }

    // Handle dictionary case by peeking, so parse_dictionary can consume the '{'
    if cursor.at_punctuation('{')? {
        return parse_dictionary(cursor);
    }

    let token = cursor.bump()?;
    match token {
        Token::None => Ok(sdf::Value::ValueBlock),
        Token::String(value) => Ok(sdf::Value::String(value.into_owned())),
        Token::AssetRef(asset_path) => Ok(sdf::Value::AssetPath(sdf::AssetPath::new(asset_path))),
        Token::Identifier(value) | Token::NamespacedIdentifier(value) => Ok(sdf::Value::token(value)),
        Token::Number(raw) => {
            if let Ok(int) = raw.parse::<i64>() {
                Ok(sdf::Value::Int64(int))
            } else if let Ok(float) = raw.parse::<f64>() {
                Ok(sdf::Value::Double(float))
            } else {
                bail!("Unable to parse numeric metadata value: {raw}");
            }
        }
        other => bail!("Unsupported property metadata value token: {other:?}"),
    }
}

/// Parse a dictionary value from `{` to `}`.
pub(super) fn parse_dictionary(cursor: &mut Cursor<'_>) -> Result<sdf::Value, RawError> {
    let mut dict = HashMap::new();

    parse_block(cursor, '{', '}', |c| {
        // Try optional type hint, then read the key.
        let type_hint = parse_type(c)?;

        let key_token = c.bump()?;
        let key = match key_token {
            Token::Identifier(s) | Token::NamespacedIdentifier(s) => s.to_owned(),
            Token::String(s) => s.into_owned(),
            other => other
                .keyword_lexeme()
                .map(str::to_owned)
                .ok_or_else(|| RawError::new(format!("Expected identifier as dictionary key, got: {other:?}")))?,
        };

        c.expect_punctuation('=')?;

        let value = if let Some(info) = type_hint {
            parse_value(c, info)?
        } else {
            parse_untyped_value(c)?
        };
        dict.insert(key, value);
        Ok(())
    })?;

    Ok(sdf::Value::Dictionary(dict))
}

/// Parse a time sample map: `{ time : value, time : value, ... }`.
///
/// Per-time values are dispatched two ways:
///
/// - When the property's declared type and the next token agree
///   on shape (a tuple type opening with `(` or `[`, or any
///   array type opening with `[`), route through [`parse_value`]
///   so the value lands in the matching typed variant
///   (`gf::Vec3f` / `QuatfVec` / `gf::Matrix4d` / `IntVec` / `FloatVec` /
///   `TokenVec` / …).
///
/// - Otherwise fall through to [`parse_untyped_value`]
///   so malformed-but-historically-accepted samples still load
///   — the spec corpus's `attributes.usda` deliberately authors
///   bare scalars (`5.67`, `-7`) and `None` against typed
///   `vector3f` properties to verify the parser's tolerance.
pub(super) fn parse_time_samples(cursor: &mut Cursor<'_>, info: TypeInfo<'_>) -> Result<sdf::TimeSampleMap, RawError> {
    let mut samples = Vec::new();
    parse_block(cursor, '{', '}', |c| {
        let time_str = c.bump()?;
        let time: f64 = match time_str {
            Token::Number(s) => s.parse()?,
            other => bail!("Expected time value, got {other:?}"),
        };
        c.expect_punctuation(':')?;
        let value = if next_is_typed_value(c, info)? {
            parse_value(c, info)?
        } else {
            parse_untyped_value(c)?
        };
        samples.push((time, value));
        Ok(())
    })?;
    Ok(samples)
}

/// Parse a spline value: `{ curveType, knots... }`.
///
/// The result is stored as a `Dictionary` matching the baseline JSON structure:
/// `{ curveType, preExtrapolation, postExtrapolation, loopParameters, knots, knotCustomData }`.
pub(super) fn parse_spline(cursor: &mut Cursor<'_>) -> Result<sdf::Value, RawError> {
    let mut curve_type: Option<String> = None;
    let mut pre_extrapolation = sdf::Value::ValueBlock;
    let mut post_extrapolation = sdf::Value::ValueBlock;
    let mut loop_params = sdf::Value::ValueBlock;
    let mut knots = Vec::new();
    let mut knot_custom_data: HashMap<String, sdf::Value> = HashMap::new();

    parse_block(cursor, '{', '}', |c| {
        let token = c.bump()?;
        // `pre`, `post`, and `loop` introduce a keyed entry (`pre : mode`); a
        // bare identifier with no `:` after it names the curve type.
        let keyed = matches!(token, Token::Identifier(_)) && c.at_punctuation(':')?;
        match token {
            // Curve type: `bezier`, `hermite`, etc.
            Token::Identifier(name) if !keyed && !matches!(name, "pre" | "post" | "loop") => {
                curve_type = Some(name.to_owned());
            }
            // Extrapolation: `pre : mode` or `post: mode [(slope)]`
            // With no space, the tokenizer produces `NamespacedIdentifier("pre:")`.
            Token::Identifier(dir @ ("pre" | "post")) if keyed => {
                c.expect_punctuation(':')?;
                let extrap = parse_extrapolation(c)?;
                if dir == "pre" {
                    pre_extrapolation = extrap;
                } else {
                    post_extrapolation = extrap;
                }
            }
            Token::NamespacedIdentifier("pre:") => {
                pre_extrapolation = parse_extrapolation(c)?;
            }
            Token::NamespacedIdentifier("post:") => {
                post_extrapolation = parse_extrapolation(c)?;
            }
            // Loop parameters
            Token::Identifier("loop") | Token::NamespacedIdentifier("loop:") => {
                if matches!(token, Token::Identifier(_)) {
                    c.expect_punctuation(':')?;
                }
                let vals = parse_tuple::<f64, 5>(c)?;
                loop_params = sdf::Value::Dictionary(HashMap::from([
                    ("protoStart".to_owned(), sdf::Value::Double(vals[0])),
                    ("protoEnd".to_owned(), sdf::Value::Double(vals[1])),
                    ("numPreLoops".to_owned(), sdf::Value::Double(vals[2])),
                    ("numPostLoops".to_owned(), sdf::Value::Double(vals[3])),
                    ("valueOffset".to_owned(), sdf::Value::Double(vals[4])),
                ]));
            }
            // Knot: `time : value [& preValue] [; pre (...)] [; post mode [...]] [; { customData }]`
            Token::Number(time_str) => {
                let time: f64 = time_str.parse()?;
                c.expect_punctuation(':')?;
                let first: f64 = parse_token(c)?;

                let mut pre_slope = 0.0;
                let mut pre_width = 0.0;
                let mut post_slope = 0.0;
                let mut post_width = 0.0;
                let mut interp_mode = "held".to_owned();

                // `time : value` or `time : preValue & value`
                let (pre_value, value) = if c.eat_punctuation('&')? {
                    let actual: f64 = parse_token(c)?;
                    (first, actual)
                } else {
                    (0.0, first)
                };

                // Optional semicolon-separated knot attributes
                while c.eat_punctuation(';')? {
                    if c.at_punctuation('{')? {
                        // Per-knot custom data
                        let sdf::Value::Dictionary(dict) = parse_dictionary(c)? else {
                            unreachable!();
                        };
                        let time_key = if time.fract() == 0.0 && time.is_finite() {
                            format!("{}", time as i64)
                        } else {
                            format!("{time}")
                        };
                        knot_custom_data.insert(time_key, sdf::Value::Dictionary(dict));
                        continue;
                    }

                    let dir = c.expect_identifier()?;
                    match dir {
                        "pre" => {
                            let vals = parse_tuple::<f64, 2>(c)?;
                            pre_slope = vals[0];
                            pre_width = vals[1];
                        }
                        "post" => {
                            // `post mode` or `post mode (slope, width)`
                            let mode = c.expect_identifier()?;
                            interp_mode = mode.to_owned();
                            if c.at_punctuation('(')? {
                                let vals = parse_tuple::<f64, 2>(c)?;
                                post_slope = vals[0];
                                post_width = vals[1];
                            }
                        }
                        other => bail!("Unexpected knot attribute: {other}"),
                    }
                }

                knots.push(sdf::Value::Dictionary(HashMap::from([
                    ("time".to_owned(), sdf::Value::Double(time)),
                    ("value".to_owned(), sdf::Value::Double(value)),
                    ("preValue".to_owned(), sdf::Value::Double(pre_value)),
                    ("preTangentSlope".to_owned(), sdf::Value::Double(pre_slope)),
                    ("preTangentWidth".to_owned(), sdf::Value::Double(pre_width)),
                    ("postTangentSlope".to_owned(), sdf::Value::Double(post_slope)),
                    ("postTangentWidth".to_owned(), sdf::Value::Double(post_width)),
                    ("nextInterpolationMode".to_owned(), sdf::Value::token(interp_mode)),
                ])));
            }
            other => bail!("Unexpected spline token: {other:?}"),
        }
        Ok(())
    })?;

    Ok(sdf::Value::Dictionary(HashMap::from([
        (
            "curveType".to_owned(),
            sdf::Value::token(curve_type.unwrap_or_else(|| "bezier".to_owned())),
        ),
        ("preExtrapolation".to_owned(), pre_extrapolation),
        ("postExtrapolation".to_owned(), post_extrapolation),
        ("loopParameters".to_owned(), loop_params),
        ("knots".to_owned(), sdf::Value::ValueVec(knots)),
        ("knotCustomData".to_owned(), sdf::Value::Dictionary(knot_custom_data)),
    ])))
}

/// Parses a single `<...>` path reference token into an `sdf::Path`.
pub(super) fn parse_path_reference(cursor: &mut Cursor<'_>) -> Result<sdf::Path, RawError> {
    path_ref_to_path(cursor.expect_path_ref()?)
}

/// Parse one reference entry, including optional target prim path and layer offset.
pub(super) fn parse_reference(cursor: &mut Cursor<'_>) -> Result<sdf::Reference, RawError> {
    let mut reference = sdf::Reference::default();

    match cursor.bump()? {
        Token::AssetRef(asset_path) => {
            reference.asset_path = asset_path.to_string();
            if matches!(cursor.peek()?, Some(Token::PathRef(_))) {
                reference.prim_path = path_ref_to_path(cursor.expect_path_ref()?)?;
            }
        }
        Token::PathRef(path) => {
            reference.prim_path = path_ref_to_path(path)?;
        }
        token => {
            bail!("Expected asset reference (@...@) or path reference (<...>), got {token:?}");
        }
    }
    reject_variant_selection_in_path(&reference.prim_path, "Reference")?;

    if cursor.at_punctuation('(')? {
        let (offset, custom_data) =
            parse_reference_layer_offset(cursor).context("Unable to parse reference layer offset")?;
        reference.layer_offset = offset;
        reference.custom_data = custom_data;
    }

    Ok(reference)
}

/// Parse one payload entry, including optional target prim path and layer offset.
pub(super) fn parse_payload(cursor: &mut Cursor<'_>) -> Result<sdf::Payload, RawError> {
    let mut payload = sdf::Payload::default();

    match cursor.bump()? {
        Token::AssetRef(asset_path) => {
            payload.asset_path = asset_path.to_string();
            if matches!(cursor.peek()?, Some(Token::PathRef(_))) {
                payload.prim_path = path_ref_to_path(cursor.expect_path_ref()?)?;
            }
        }
        Token::PathRef(path) => {
            payload.prim_path = path_ref_to_path(path)?;
        }
        token => {
            bail!("Expected asset reference (@...@) or path reference (<...>), got {token:?}");
        }
    }
    reject_variant_selection_in_path(&payload.prim_path, "Payload")?;

    if cursor.at_punctuation('(')? {
        let (offset, _custom_data) =
            parse_reference_layer_offset(cursor).context("Unable to parse payload layer offset")?;
        payload.layer_offset = Some(offset);
    }

    Ok(payload)
}

/// Parses a relocates dictionary: `{ <source>: <target>, ... }`.
pub(super) fn parse_relocates(cursor: &mut Cursor<'_>) -> Result<Vec<(sdf::Path, sdf::Path)>, RawError> {
    let mut pairs = Vec::new();
    parse_block(cursor, '{', '}', |c| {
        let src = c.expect_path_ref().context("Expected relocate source path")?;
        c.expect_punctuation(':')
            .context("Expected ':' between relocate source and target")?;
        let tgt = c.expect_path_ref().context("Expected relocate target path")?;
        // An empty target (`<>`) removes the relocation, so only the source
        // must name a prim.
        let src_path = sdf::Path::new(src)?;
        let tgt_path = path_ref_to_path(tgt)?;
        reject_variant_selection_in_path(&src_path, "Relocate source")?;
        reject_variant_selection_in_path(&tgt_path, "Relocate target")?;
        pairs.push((src_path, tgt_path));
        Ok(())
    })?;
    Ok(pairs)
}

/// Parse `subLayers` entries along with their optional `(offset/scale)` metadata.
pub(super) fn parse_sublayers(cursor: &mut Cursor<'_>) -> Result<(Vec<String>, Vec<sdf::LayerOffset>), RawError> {
    let mut sublayers = Vec::new();
    let mut sublayer_offsets = Vec::new();

    parse_block(cursor, '[', ']', |c| {
        sublayers.push(c.expect_asset_ref()?.to_string());

        let mut layer_offset = sdf::LayerOffset::default();
        if c.at_punctuation('(')? {
            let mut offset = None;
            let mut scale = None;

            parse_block(c, '(', ')', |entry| {
                let token = entry.bump()?;
                entry.expect_punctuation('=')?;
                let value = parse_value(entry, TypeInfo::scalar(Type::Double))?;
                match token {
                    Token::Offset => {
                        offset = Some(value);
                    }
                    Token::Scale => {
                        scale = Some(value);
                    }
                    _ => bail!("Unexpected token type: {token:?}"),
                }
                Ok(())
            })?;

            if let Some(offset) = offset {
                layer_offset.offset = offset.try_as_double().context("Unexpected offset type, want double")?;
            }
            if let Some(scale) = scale {
                layer_offset.scale = scale.try_as_double().context("Unexpected scale type, want double")?;
            }
        }
        sublayer_offsets.push(layer_offset);
        Ok(())
    })?;

    debug_assert_eq!(sublayers.len(), sublayer_offsets.len());

    Ok((sublayers, sublayer_offsets))
}

/// Rejects a composition-arc target path that contains a variant selection.
/// Inherit, specialize, reference, payload, and relocate paths address prims,
/// not variant selections, so a `{set=sel}` element anywhere in the path is a
/// parse error (C++ `Sdf_TextFileFormatParser` raises the same error, e.g.
/// "Inherit paths cannot contain variant selections"). `arc` names the field.
pub(super) fn reject_variant_selection_in_path(path: &sdf::Path, arc: &str) -> Result<(), RawError> {
    ensure!(
        !path.contains_prim_variant_selection(),
        "{arc} paths cannot contain variant selections: <{path}>"
    );
    Ok(())
}

/// Parses a scalar type name into a `Type`. Does not handle arrays.
///
/// See
/// - <https://openusd.org/dev/api/_usd__page__datatypes.html#Usd_Basic_Datatypes>
/// - <https://openusd.org/dev/api/_usd__page__datatypes.html#Usd_Roles>
fn parse_base_type(name: &str) -> Result<Type, RawError> {
    let ty = match name {
        "bool" => Type::Bool,
        "uchar" => Type::Uchar,
        "int" => Type::Int,
        "int2" => Type::Int2,
        "int3" => Type::Int3,
        "int4" => Type::Int4,
        "uint" => Type::Uint,
        "int64" => Type::Int64,
        "uint64" => Type::Uint64,
        "half" => Type::Half,
        "half2" | "texCoord2h" => Type::Half2,
        "half3" | "point3h" | "normal3h" | "vector3h" | "color3h" | "texCoord3h" => Type::Half3,
        "half4" | "color4h" => Type::Half4,
        "float" => Type::Float,
        "float2" | "texCoord2f" => Type::Float2,
        "float3" | "point3f" | "normal3f" | "vector3f" | "color3f" | "texCoord3f" => Type::Float3,
        "float4" | "color4f" => Type::Float4,
        "double" => Type::Double,
        "double2" | "texCoord2d" => Type::Double2,
        "double3" | "point3d" | "normal3d" | "vector3d" | "color3d" | "texCoord3d" => Type::Double3,
        "double4" | "color4d" => Type::Double4,
        "matrix2d" => Type::Matrix2d,
        "matrix3d" => Type::Matrix3d,
        "matrix4d" | "frame4d" => Type::Matrix4d,
        "quatd" => Type::Quatd,
        "quatf" => Type::Quatf,
        "quath" => Type::Quath,
        "string" => Type::String,
        "token" => Type::Token,
        "asset" => Type::Asset,
        "timecode" => Type::TimeCode,
        "pathExpression" => Type::PathExpression,
        "dictionary" => Type::Dictionary,
        _ => bail!("Unsupported type: {name}"),
    };
    Ok(ty)
}

/// Heuristic: should the next token be parsed under [`parse_value`]
/// for `info`, or is the type-blind metadata-value path safer?
///
/// Returns `true` when the next token opens a literal whose shape
/// matches the declared type:
///
/// - `(` for a tuple type (vector / quat / matrix row / matrix).
/// - `[` for any array type (scalar arrays like `int[]`,
///   `float[]`, `token[]`, as well as arrays of tuples like
///   `quatf[]` or `matrix4d[]`).
/// - a bare number for a scalar `timecode`, so a sample like
///   `1: 24` resolves to [`sdf::Value::TimeCode`] rather than the
///   type-blind path's `Int64` / `Double`.
///
/// Anything else (scalar literal, `None`, identifier) flows
/// through the type-blind path so the spec corpus's lenient
/// `vector3f`-with-bare-scalar samples keep parsing.
fn next_is_typed_value(cursor: &mut Cursor<'_>, info: TypeInfo<'_>) -> Result<bool, RawError> {
    let is_tuple_type = matches!(
        info.ty,
        Type::Int2
            | Type::Int3
            | Type::Int4
            | Type::Half2
            | Type::Half3
            | Type::Half4
            | Type::Float2
            | Type::Float3
            | Type::Float4
            | Type::Double2
            | Type::Double3
            | Type::Double4
            | Type::Quath
            | Type::Quatf
            | Type::Quatd
            | Type::Matrix2d
            | Type::Matrix3d
            | Type::Matrix4d
    );
    Ok(match cursor.peek()? {
        Some(Token::Punctuation('(')) => is_tuple_type,
        Some(Token::Punctuation('[')) => is_tuple_type || info.is_array,
        Some(Token::Number(_)) => info.ty == Type::TimeCode && !info.is_array,
        _ => false,
    })
}

/// Parse an extrapolation mode: `mode [(slope)]`.
fn parse_extrapolation(cursor: &mut Cursor<'_>) -> Result<sdf::Value, RawError> {
    let mode = cursor.expect_identifier()?;
    if mode == "none" {
        return Ok(sdf::Value::ValueBlock);
    }
    let slope = if cursor.at_punctuation('(')? {
        cursor.expect_punctuation('(')?;
        let v = parse_token::<f64>(cursor)?;
        cursor.expect_punctuation(')')?;
        v
    } else {
        0.0
    };
    Ok(sdf::Value::Dictionary(HashMap::from([
        ("mode".to_owned(), sdf::Value::token(mode)),
        ("slope".to_owned(), sdf::Value::Double(slope)),
    ])))
}

/// Parse `(offset = ...; scale = ...; customData = {...})` blocks attached to
/// references or sublayers.
fn parse_reference_layer_offset(
    cursor: &mut Cursor<'_>,
) -> Result<(sdf::LayerOffset, HashMap<String, sdf::Value>), RawError> {
    let mut layer_offset = sdf::LayerOffset::default();
    let mut custom_data = HashMap::new();

    parse_block(cursor, '(', ')', |c| {
        let token = c.bump()?;
        c.expect_punctuation('=')?;

        match token {
            Token::Offset => {
                let value = parse_value(c, TypeInfo::scalar(Type::Double))?;
                layer_offset.offset = value.try_as_double().context("Expected double for offset")?;
            }
            Token::Scale => {
                let value = parse_value(c, TypeInfo::scalar(Type::Double))?;
                layer_offset.scale = value.try_as_double().context("Expected double for scale")?;
            }
            Token::CustomData => {
                let sdf::Value::Dictionary(dict) = parse_dictionary(c)? else {
                    unreachable!("parse_dictionary always returns Dictionary");
                };
                custom_data = dict;
            }
            unexpected => bail!("Unexpected token in layer offset: {unexpected:?}"),
        }

        Ok(())
    })?;

    Ok((layer_offset, custom_data))
}

/// Parses a delimited block: `open` ... entries ... `close`.
///
/// Calls `entry` for each item. Commas between entries are consumed automatically.
/// Handles empty blocks and trailing commas.
fn parse_block<'source>(
    cursor: &mut Cursor<'source>,
    open: char,
    close: char,
    mut entry: impl FnMut(&mut Cursor<'source>) -> Result<(), RawError>,
) -> Result<(), RawError> {
    cursor.expect_punctuation(open)?;
    loop {
        if cursor.eat_punctuation(close)? {
            break;
        }
        entry(cursor)?;
        while cursor.eat_punctuation(',')? || cursor.eat_punctuation(';')? {}
    }
    Ok(())
}

/// Parse a `[...]` array, using `parse_element` for each item.
pub(super) fn parse_array_with<'source, T>(
    cursor: &mut Cursor<'source>,
    mut parse_element: impl FnMut(&mut Cursor<'source>) -> Result<T, RawError>,
) -> Result<Vec<T>, RawError> {
    let mut out = Vec::new();
    parse_block(cursor, '[', ']', |c| {
        out.push(parse_element(c)?);
        Ok(())
    })?;
    Ok(out)
}

/// Parse single token as `T` which can be deserialized from string (such as `int`, `float`, etc).
pub(super) fn parse_token<T: FromStr>(cursor: &mut Cursor<'_>) -> Result<T, RawError>
where
    <T as FromStr>::Err: Debug,
{
    let token = cursor.bump()?;
    let value_str = match token {
        Token::Number(s) | Token::Identifier(s) | Token::NamespacedIdentifier(s) => Cow::Borrowed(s),
        Token::String(s) => s,
        Token::Inf => Cow::Borrowed("inf"),
        Token::Punctuation('-') => {
            // Handle negative inf
            let next = cursor.bump()?;
            if matches!(next, Token::Inf) {
                Cow::Borrowed("-inf")
            } else {
                bail!("Expected number after '-', got {next:?}")
            }
        }
        Token::Punctuation('+') => {
            // Handle positive inf
            let next = cursor.bump()?;
            if matches!(next, Token::Inf) {
                Cow::Borrowed("inf")
            } else {
                bail!("Expected number after '+', got {next:?}")
            }
        }
        _ => bail!("Expected a number, identifier, or string, got {token:?}"),
    };
    let value = T::from_str(&value_str).map_err(|err| {
        RawError::new(format!(
            "Failed to parse {} from '{}': {:?}",
            type_name::<T>(),
            value_str,
            err
        ))
    })?;

    Ok(value)
}

/// Parse USD's flexible boolean literal forms (identifiers, numeric, or string).
/// A `true` / `false` word, however it was spelled — bare, namespaced, or
/// quoted.
pub(super) fn parse_bool(cursor: &mut Cursor<'_>) -> Result<bool, RawError> {
    let token = cursor.bump()?;
    match token {
        Token::Identifier(value) | Token::NamespacedIdentifier(value) => parse_bool_word(value),
        Token::String(value) => parse_bool_word(&value),
        Token::Number(value) => {
            let parsed = value.parse::<f64>().context("Unable to parse numeric bool")?;
            if parsed == 0.0 {
                Ok(false)
            } else if parsed == 1.0 {
                Ok(true)
            } else {
                bail!("Numeric bool literals must be 0 or 1, got {value}");
            }
        }
        other => bail!("Unexpected token for bool literal: {other:?}"),
    }
}

/// Whether `word` is the boolean `true` or `false`, case-insensitively.
fn parse_bool_word(word: &str) -> Result<bool, RawError> {
    if word.eq_ignore_ascii_case("true") {
        Ok(true)
    } else if word.eq_ignore_ascii_case("false") {
        Ok(false)
    } else {
        bail!("Unexpected value for bool literal: {word}")
    }
}

/// Parse fixed-size tuples, preserving order and surfacing contextual errors.
fn parse_tuple<T, const N: usize>(cursor: &mut Cursor<'_>) -> Result<[T; N], RawError>
where
    T: FromStr + Default + Copy,
    <T as FromStr>::Err: Debug,
{
    let mut values = [T::default(); N];
    let mut len = 0;
    parse_block(cursor, '(', ')', |c| {
        ensure!(len < N, "tuple has too many elements (expected {N})");
        values[len] = parse_token::<T>(c)?;
        len += 1;
        Ok(())
    })?;
    ensure!(len == N, "tuple has too few elements (expected {N}, got {len})");
    Ok(values)
}

/// Parse a `[scalar, ...]` array of `FromStr` values.
fn parse_array<T>(cursor: &mut Cursor<'_>) -> Result<Vec<T>, RawError>
where
    T: FromStr,
    <T as FromStr>::Err: Debug,
{
    parse_array_with(cursor, parse_token)
}

/// Parse a single matrix literal, flattening rows in row-major order.
///
/// Handles both bare `(row), (row), ...` and bracket-wrapped `[ (row), ... ]` forms.
fn parse_matrix<const N: usize, const M: usize>(cursor: &mut Cursor<'_>) -> Result<[f64; M], RawError> {
    if cursor.at_punctuation('[')? {
        let mut arr = parse_matrix_array::<N, M>(cursor)?;
        ensure!(arr.len() == 1, "expected a single matrix value");
        return Ok(arr.remove(0));
    }

    let mut values = [0_f64; M];
    let mut idx = 0;
    parse_block(cursor, '(', ')', |c| {
        let row = parse_tuple::<f64, N>(c)?;
        for v in row {
            ensure!(idx < M, "matrix{N}d literal has too many elements");
            values[idx] = v;
            idx += 1;
        }
        Ok(())
    })?;
    ensure!(idx == M, "matrix{N}d literal must contain {N} rows");
    Ok(values)
}

/// Parse `[ matrix, matrix, ... ]`.
fn parse_matrix_array<const N: usize, const M: usize>(cursor: &mut Cursor<'_>) -> Result<Vec<[f64; M]>, RawError> {
    parse_array_with(cursor, parse_matrix::<N, M>)
}

// Parse a tuple and convert it to a gf type via `From<[E; N]>`.
fn parse_gf<E, T, const N: usize>(cursor: &mut Cursor<'_>) -> Result<T, RawError>
where
    E: FromStr + Default + Copy,
    <E as FromStr>::Err: Debug,
    T: From<[E; N]>,
{
    Ok(T::from(parse_tuple::<E, N>(cursor)?))
}

// Parse an array of tuples and convert each element to a gf type via `From<[E; N]>`.
fn parse_gf_array<E, T, const N: usize>(cursor: &mut Cursor<'_>) -> Result<Vec<T>, RawError>
where
    E: FromStr + Default + Copy,
    <E as FromStr>::Err: Debug,
    T: From<[E; N]>,
{
    parse_array_with(cursor, parse_gf::<E, T, N>)
}

/// Converts the text of a `<...>` path-reference token into a path. `<>`
/// carries the empty path (e.g. a reference resolving to the target layer's
/// defaultPrim), as in C++.
fn path_ref_to_path(text: &str) -> Result<sdf::Path, RawError> {
    if text.is_empty() {
        return Ok(sdf::Path::default());
    }
    Ok(sdf::Path::new(text)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_array() {
        let mut cursor = Cursor::new("[]");
        let array = parse_array::<u32>(&mut cursor).unwrap();
        assert!(array.is_empty());
    }

    #[test]
    fn tuple_literal() {
        let mut cursor = Cursor::new("(1, 2, 3)");
        let result = parse_tuple::<u32, 3>(&mut cursor).unwrap();
        assert_eq!(result, [1_u32, 2, 3]);
    }

    #[test]
    fn array_literal() {
        let mut cursor = Cursor::new("[1, 2, 3]");
        let result = parse_array::<u32>(&mut cursor).unwrap();
        assert_eq!(result, vec![1_u32, 2, 3]);
    }

    #[test]
    fn array_of_tuples() {
        let mut cursor = Cursor::new("[(1, 2), (3, 4)]");
        let result = parse_array_with(&mut cursor, parse_tuple::<u32, 2>).unwrap();
        assert_eq!(result, vec![[1_u32, 2], [3, 4]]);
    }

    #[test]
    fn type_scalar() {
        let mut cursor = Cursor::new("float x");
        let info = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(info.ty, Type::Float);
        assert_eq!(info.type_name, "float");
        assert!(!info.is_array);
        assert_eq!(info.to_string(), "float");
    }

    #[test]
    fn type_array_no_space() {
        // `float[]` lexes as three tokens: float [ ]
        let mut cursor = Cursor::new("float[] x");
        let info = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(info.ty, Type::Float);
        assert_eq!(info.type_name, "float");
        assert!(info.is_array);
        assert_eq!(info.to_string(), "float[]");
    }

    #[test]
    fn type_array_spaced() {
        let mut cursor = Cursor::new("int [] x");
        let info = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(info.ty, Type::Int);
        assert!(info.is_array);
        assert_eq!(info.to_string(), "int[]");
    }

    #[test]
    fn type_alias() {
        let mut cursor = Cursor::new("point3f x");
        let info = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(info.ty, Type::Float3);
        assert_eq!(info.type_name, "point3f");
        assert_eq!(info.to_string(), "point3f");
    }

    #[test]
    fn type_dictionary() {
        let mut cursor = Cursor::new("dictionary x");
        let info = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(info.ty, Type::Dictionary);
        assert!(!info.is_array);
    }

    #[test]
    fn type_unknown_name() {
        let mut cursor = Cursor::new("foobar x");
        let info = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(info.ty, Type::Custom);
        assert_eq!(info.type_name, "foobar");
    }

    #[test]
    fn type_matrix_array() {
        let mut cursor = Cursor::new("matrix4d[] x");
        let info = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(info.ty, Type::Matrix4d);
        assert!(info.is_array);
        assert_eq!(info.to_string(), "matrix4d[]");
    }

    #[test]
    fn reference_asset_only() {
        let mut cursor = Cursor::new("@./model.usda@");
        let reference = parse_reference(&mut cursor).unwrap();
        assert_eq!(reference.asset_path, "./model.usda");
        assert_eq!(reference.prim_path, sdf::Path::default());
    }

    #[test]
    fn reference_with_prim_path() {
        let mut cursor = Cursor::new("@./model.usda@</Root>");
        let reference = parse_reference(&mut cursor).unwrap();
        assert_eq!(reference.asset_path, "./model.usda");
        assert_eq!(reference.prim_path.as_str(), "/Root");
    }

    #[test]
    fn reference_path_only() {
        let mut cursor = Cursor::new("</Foo>");
        let reference = parse_reference(&mut cursor).unwrap();
        assert!(reference.asset_path.is_empty());
        assert_eq!(reference.prim_path.as_str(), "/Foo");
    }

    #[test]
    fn reference_invalid_token() {
        let mut cursor = Cursor::new("123");
        assert!(parse_reference(&mut cursor).is_err());
    }

    #[test]
    // Validates sublayer parsing captures offsets, scales, and defaults when missing.
    fn layer_offsets() {
        let mut cursor = Cursor::new(
            r#"
[
    @./someAnimation.usd@ (offset = 10; scale = 0.5),
    @./another.usd@
]
            "#,
        );

        let (sublayers, offsets) = parse_sublayers(&mut cursor).unwrap();

        assert_eq!(
            sublayers,
            vec!["./someAnimation.usd".to_string(), "./another.usd".to_string()]
        );

        assert_eq!(offsets[0].offset, 10.0);
        assert_eq!(offsets[0].scale, 0.5);

        // Default one
        assert_eq!(offsets[1].offset, 0.0);
        assert_eq!(offsets[1].scale, 1.0);
    }
}
