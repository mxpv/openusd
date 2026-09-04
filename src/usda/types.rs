//! USDA value productions: the type table and the parsers that decode a
//! complete value from the token stream.
//!
//! These read from a [`Cursor`] and nothing else. Building specs, registering
//! children, and anchoring paths against the current prim stay in
//! [`super::parser`].

use std::{any::type_name, borrow::Cow, collections::HashMap, fmt::Debug, str::FromStr};

use super::error::{Ctx, RawError, bail, ensure};

use crate::{gf, sdf};

use super::cursor::Cursor;
use super::token::Token;

/// Tries to parse a type declaration: an identifier optionally followed by
/// `[]`.
///
/// Returns `Ok(None)` if the next token is not an identifier (without
/// consuming it). A spelling the type table does not know is carried as an
/// unregistered [`sdf::ValueTypeName`], so it reaches the `typeName` field
/// verbatim; a registered spelling with `[]` resolves to its array type, and
/// `opaque[]`, which has none, stays unregistered.
pub(super) fn parse_type(cursor: &mut Cursor<'_>) -> Result<Option<sdf::ValueTypeName>, RawError> {
    let Some(Token::Identifier(base)) = cursor.peek()? else {
        return Ok(None);
    };
    let base = *base;
    cursor.bump()?;

    if !cursor.at_punctuation('[')? {
        return Ok(Some(sdf::ValueTypeName::from(base)));
    }
    cursor.bump()?;
    cursor.expect_punctuation(']')?;
    Ok(Some(sdf::ValueTypeName::from(format!("{base}[]"))))
}

/// Decode a value of the declared type `ty`, dispatching on the
/// [`sdf::ValueKind`] the type table assigns it.
///
/// `None` is a value block whatever the type. A registered type's literal
/// must have the type's shape (§16.2.16.6 of the core spec); an unregistered
/// type and an `opaque` type have no value to parse.
pub(super) fn parse_value(cursor: &mut Cursor<'_>, ty: &sdf::ValueTypeName) -> Result<sdf::Value, RawError> {
    // None means "value block" (explicitly unset) regardless of type.
    if cursor.eat(&Token::None)? {
        return Ok(sdf::Value::ValueBlock);
    }

    // TODO: record the literal of an unregistered type's value as
    // `sdf::Value::UnregisteredValue` (C++ `SdfUnregisteredValue`), which the
    // writer would then emit verbatim; the writer quotes that variant today.
    let Some(kind) = ty.kind() else {
        bail!("Cannot parse a value for unregistered type `{ty}`");
    };
    ensure!(kind != sdf::ValueKind::Opaque, "`{ty}` attributes cannot have a value");
    check_shape(cursor, ty)?;

    let value = match kind {
        sdf::ValueKind::Bool => sdf::Value::Bool(parse_bool(cursor)?),
        sdf::ValueKind::BoolVec => sdf::Value::BoolVec(parse_array_with(cursor, parse_bool)?),

        sdf::ValueKind::AssetPath => sdf::Value::AssetPath(cursor.expect_asset_ref()?.into()),
        sdf::ValueKind::AssetPathVec => {
            sdf::Value::AssetPathVec(parse_array_with(cursor, |c| Ok(c.expect_asset_ref()?.into()))?)
        }

        sdf::ValueKind::TimeCode => sdf::Value::TimeCode(parse_token::<f64>(cursor)?.into()),
        sdf::ValueKind::TimeCodeVec => sdf::Value::TimeCodeVec(
            parse_array::<f64>(cursor)?
                .into_iter()
                .map(sdf::TimeCode::from)
                .collect(),
        ),

        sdf::ValueKind::Uchar => sdf::Value::Uchar(parse_token(cursor)?),
        sdf::ValueKind::UcharVec => sdf::Value::UcharVec(parse_array(cursor)?),

        sdf::ValueKind::Int => sdf::Value::Int(parse_token(cursor)?),
        sdf::ValueKind::IntVec => sdf::Value::IntVec(parse_array(cursor)?),
        sdf::ValueKind::Vec2i => sdf::Value::Vec2i(parse_gf::<i32, _, 2>(cursor)?),
        sdf::ValueKind::Vec2iVec => sdf::Value::Vec2iVec(parse_gf_array::<i32, _, 2>(cursor)?),
        sdf::ValueKind::Vec3i => sdf::Value::Vec3i(parse_gf::<i32, _, 3>(cursor)?),
        sdf::ValueKind::Vec3iVec => sdf::Value::Vec3iVec(parse_gf_array::<i32, _, 3>(cursor)?),
        sdf::ValueKind::Vec4i => sdf::Value::Vec4i(parse_gf::<i32, _, 4>(cursor)?),
        sdf::ValueKind::Vec4iVec => sdf::Value::Vec4iVec(parse_gf_array::<i32, _, 4>(cursor)?),
        sdf::ValueKind::Uint => sdf::Value::Uint(parse_token(cursor)?),
        sdf::ValueKind::UintVec => sdf::Value::UintVec(parse_array(cursor)?),
        sdf::ValueKind::Int64 => sdf::Value::Int64(parse_token(cursor)?),
        sdf::ValueKind::Int64Vec => sdf::Value::Int64Vec(parse_array(cursor)?),
        sdf::ValueKind::Uint64 => sdf::Value::Uint64(parse_token(cursor)?),
        sdf::ValueKind::Uint64Vec => sdf::Value::Uint64Vec(parse_array(cursor)?),

        sdf::ValueKind::Half => sdf::Value::Half(parse_token(cursor)?),
        sdf::ValueKind::HalfVec => sdf::Value::HalfVec(parse_array(cursor)?),
        sdf::ValueKind::Vec2h => sdf::Value::Vec2h(parse_gf::<gf::f16, _, 2>(cursor)?),
        sdf::ValueKind::Vec2hVec => sdf::Value::Vec2hVec(parse_gf_array::<gf::f16, _, 2>(cursor)?),
        sdf::ValueKind::Vec3h => sdf::Value::Vec3h(parse_gf::<gf::f16, _, 3>(cursor)?),
        sdf::ValueKind::Vec3hVec => sdf::Value::Vec3hVec(parse_gf_array::<gf::f16, _, 3>(cursor)?),
        sdf::ValueKind::Vec4h => sdf::Value::Vec4h(parse_gf::<gf::f16, _, 4>(cursor)?),
        sdf::ValueKind::Vec4hVec => sdf::Value::Vec4hVec(parse_gf_array::<gf::f16, _, 4>(cursor)?),

        sdf::ValueKind::Float => sdf::Value::Float(parse_token(cursor)?),
        sdf::ValueKind::FloatVec => sdf::Value::FloatVec(parse_array(cursor)?),
        sdf::ValueKind::Vec2f => sdf::Value::Vec2f(parse_gf::<f32, _, 2>(cursor)?),
        sdf::ValueKind::Vec2fVec => sdf::Value::Vec2fVec(parse_gf_array::<f32, _, 2>(cursor)?),
        sdf::ValueKind::Vec3f => sdf::Value::Vec3f(parse_gf::<f32, _, 3>(cursor)?),
        sdf::ValueKind::Vec3fVec => sdf::Value::Vec3fVec(parse_gf_array::<f32, _, 3>(cursor)?),
        sdf::ValueKind::Vec4f => sdf::Value::Vec4f(parse_gf::<f32, _, 4>(cursor)?),
        sdf::ValueKind::Vec4fVec => sdf::Value::Vec4fVec(parse_gf_array::<f32, _, 4>(cursor)?),

        sdf::ValueKind::Double => sdf::Value::Double(parse_token(cursor)?),
        sdf::ValueKind::DoubleVec => sdf::Value::DoubleVec(parse_array(cursor)?),
        sdf::ValueKind::Vec2d => sdf::Value::Vec2d(parse_gf::<f64, _, 2>(cursor)?),
        sdf::ValueKind::Vec2dVec => sdf::Value::Vec2dVec(parse_gf_array::<f64, _, 2>(cursor)?),
        sdf::ValueKind::Vec3d => sdf::Value::Vec3d(parse_gf::<f64, _, 3>(cursor)?),
        sdf::ValueKind::Vec3dVec => sdf::Value::Vec3dVec(parse_gf_array::<f64, _, 3>(cursor)?),
        sdf::ValueKind::Vec4d => sdf::Value::Vec4d(parse_gf::<f64, _, 4>(cursor)?),
        sdf::ValueKind::Vec4dVec => sdf::Value::Vec4dVec(parse_gf_array::<f64, _, 4>(cursor)?),

        // Quaternion fields in USDA are (w, x, y, z) — same as gf::Quat* field order.
        sdf::ValueKind::Quath => sdf::Value::Quath(parse_gf::<gf::f16, _, 4>(cursor)?),
        sdf::ValueKind::Quatf => sdf::Value::Quatf(parse_gf::<f32, _, 4>(cursor)?),
        sdf::ValueKind::Quatd => sdf::Value::Quatd(parse_gf::<f64, _, 4>(cursor)?),
        sdf::ValueKind::QuathVec => sdf::Value::QuathVec(parse_gf_array::<gf::f16, _, 4>(cursor)?),
        sdf::ValueKind::QuatfVec => sdf::Value::QuatfVec(parse_gf_array::<f32, _, 4>(cursor)?),
        sdf::ValueKind::QuatdVec => sdf::Value::QuatdVec(parse_gf_array::<f64, _, 4>(cursor)?),

        sdf::ValueKind::String => sdf::Value::String(cursor.expect_string()?.into_owned()),
        sdf::ValueKind::StringVec => sdf::Value::StringVec(parse_array(cursor)?),
        sdf::ValueKind::Token => sdf::Value::token(cursor.expect_string()?.as_ref()),
        sdf::ValueKind::TokenVec => sdf::Value::token_vec(parse_array::<String>(cursor)?),

        sdf::ValueKind::PathExpression => {
            sdf::Value::PathExpression(sdf::PathExpression::parse(cursor.expect_string()?.as_ref()))
        }
        sdf::ValueKind::PathExpressionVec => sdf::Value::PathExpressionVec(
            parse_array::<String>(cursor)?
                .iter()
                .map(|text| sdf::PathExpression::parse(text))
                .collect(),
        ),

        sdf::ValueKind::Matrix2d => sdf::Value::Matrix2d(gf::Mat2d(parse_matrix::<2, 4>(cursor)?)),
        sdf::ValueKind::Matrix3d => sdf::Value::Matrix3d(gf::Mat3d(parse_matrix::<3, 9>(cursor)?)),
        sdf::ValueKind::Matrix4d => sdf::Value::Matrix4d(gf::Matrix4d(parse_matrix::<4, 16>(cursor)?)),
        sdf::ValueKind::Matrix2dVec => {
            sdf::Value::Matrix2dVec(parse_matrix_array::<2, 4>(cursor)?.into_iter().map(gf::Mat2d).collect())
        }
        sdf::ValueKind::Matrix3dVec => {
            sdf::Value::Matrix3dVec(parse_matrix_array::<3, 9>(cursor)?.into_iter().map(gf::Mat3d).collect())
        }
        sdf::ValueKind::Matrix4dVec => sdf::Value::Matrix4dVec(
            parse_matrix_array::<4, 16>(cursor)?
                .into_iter()
                .map(gf::Matrix4d)
                .collect(),
        ),

        // The table never assigns a metadata-only kind to an attribute type.
        other => bail!("`{ty}` ({other}) is not an attribute value type"),
    };

    Ok(value)
}

/// Checks that the literal about to be parsed opens with the shape `ty`
/// requires (§16.2.16.6 of the core spec): a `[` for an array type, a `(`
/// for a tuple or matrix type, neither for a scalar. Arity inside the
/// literal is checked by the tuple and matrix parsers.
fn check_shape(cursor: &mut Cursor<'_>, ty: &sdf::ValueTypeName) -> Result<(), RawError> {
    let opens_list = cursor.at_punctuation('[')?;
    let opens_tuple = cursor.at_punctuation('(')?;
    if ty.is_array() {
        ensure!(
            opens_list,
            "`{ty}` is an array type, so its value must be a `[...]` list"
        );
    } else if ty.dimensions() != Some(sdf::Dimensions::Scalar) {
        ensure!(
            opens_tuple,
            "`{ty}` is a tuple type, so its value must be a `(...)` tuple"
        );
    } else {
        ensure!(
            !opens_list && !opens_tuple,
            "`{ty}` is a scalar type, so its value can be neither a list nor a tuple"
        );
    }
    Ok(())
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
        // A nested dictionary is introduced by the `dictionary` keyword (a
        // keyword in the grammar, not a value type); any other entry declares
        // a value type, then the key.
        let nested = c.eat(&Token::Dictionary)?;
        let type_hint = if nested { None } else { parse_type(c)? };

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

        let value = if nested {
            parse_dictionary(c)?
        } else if let Some(ty) = type_hint {
            parse_value(c, &ty)?
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
/// Every sample is decoded under the property's declared type through
/// [`parse_value`], so a `float` sample written `4` lands as `Float`, a
/// `token` sample as `Token`, a `None` as a value block, and a literal of
/// the wrong shape is an error (§16.2.16.6 of the core spec).
pub(super) fn parse_time_samples(
    cursor: &mut Cursor<'_>,
    ty: &sdf::ValueTypeName,
) -> Result<sdf::TimeSampleMap, RawError> {
    let mut samples = Vec::new();
    parse_block(cursor, '{', '}', |c| {
        let time_str = c.bump()?;
        let time: f64 = match time_str {
            Token::Number(s) => s.parse()?,
            other => bail!("Expected time value, got {other:?}"),
        };
        c.expect_punctuation(':')?;
        let value = parse_value(c, ty)?;
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
                let value = parse_value(entry, &sdf::ValueTypeName::DOUBLE)?;
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
                let value = parse_value(c, &sdf::ValueTypeName::DOUBLE)?;
                layer_offset.offset = value.try_as_double().context("Expected double for offset")?;
            }
            Token::Scale => {
                let value = parse_value(c, &sdf::ValueTypeName::DOUBLE)?;
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

/// Parse a single matrix literal `((row), (row), ...)`, flattening rows in
/// row-major order.
fn parse_matrix<const N: usize, const M: usize>(cursor: &mut Cursor<'_>) -> Result<[f64; M], RawError> {
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
        let ty = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(ty, sdf::ValueTypeName::FLOAT);
        assert_eq!(ty.as_str(), "float");
        assert!(ty.is_scalar());
        assert!(matches!(cursor.peek().unwrap(), Some(Token::Identifier("x"))));
    }

    #[test]
    fn type_array() {
        // `float[]` lexes as three tokens: float [ ]; a space before `[]` is
        // the same declaration.
        for text in ["float[] x", "float [] x"] {
            let mut cursor = Cursor::new(text);
            let ty = parse_type(&mut cursor).unwrap().unwrap();
            assert_eq!(ty, sdf::ValueTypeName::FLOAT_ARRAY);
            assert_eq!(ty.as_str(), "float[]");
            assert!(ty.is_array());
        }
        let mut cursor = Cursor::new("matrix4d[] x");
        let ty = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(ty, sdf::ValueTypeName::MATRIX4D_ARRAY);
        assert_eq!(ty.dimensions(), Some(sdf::Dimensions::Matrix(4, 4)));
    }

    #[test]
    fn type_alias() {
        let mut cursor = Cursor::new("point3f x");
        let ty = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(ty, sdf::ValueTypeName::POINT3F);
        assert_eq!(ty.kind(), Some(sdf::ValueKind::Vec3f));
        assert_eq!(ty.role(), Some(sdf::Role::Point));
        assert_eq!(ty.as_str(), "point3f");
        let mut cursor = Cursor::new("Color x");
        let legacy = parse_type(&mut cursor).unwrap().unwrap();
        assert_eq!(legacy, sdf::ValueTypeName::COLOR3D);
        assert_eq!(legacy.as_str(), "Color");
    }

    #[test]
    fn dictionary_not_type() {
        let mut cursor = Cursor::new("dictionary x");
        assert!(parse_type(&mut cursor).unwrap().is_none());
        assert!(matches!(cursor.peek().unwrap(), Some(Token::Dictionary)));

        let mut cursor = Cursor::new("{ dictionary sub = { int a = 1 }, string s = \"x\" }");
        let dict = parse_dictionary(&mut cursor).unwrap().try_as_dictionary().unwrap();
        let sub = dict["sub"].clone().try_as_dictionary().unwrap();
        assert_eq!(sub["a"], sdf::Value::Int(1));
        assert_eq!(dict["s"], sdf::Value::String("x".into()));
    }

    #[test]
    fn type_unknown() {
        for (text, spelling) in [
            ("foobar x", "foobar"),
            ("foobar[] x", "foobar[]"),
            ("opaque[] x", "opaque[]"),
        ] {
            let mut cursor = Cursor::new(text);
            let ty = parse_type(&mut cursor).unwrap().unwrap();
            assert!(!ty.is_registered(), "{spelling}");
            assert_eq!(ty.as_str(), spelling);
        }
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
