//! Low-level building blocks shared across the schema families.
//!
//! The view-gate helpers ([`get_typed`], [`get_typed_any`], [`get_with_api`])
//! back the type-gated `get` lookups every trait-view family shares, and the
//! small value readers ([`read_token`], [`value_as_asset_str`]) plus the
//! [`impl_token_value!`] macro cover the decoding that would otherwise be
//! duplicated verbatim. Attribute *authoring* is inlined per family via the
//! [`Attribute`](crate::usd::Attribute) builder, so no shared authoring
//! helpers live here.

// Each helper is used by at least one schema feature, but typically not
// all — silence the dead-code warning on per-feature builds.
#![allow(dead_code)]

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::{Prim, Stage};

/// Resolve the `default` field of the attribute `name` on `prim` as a raw
/// [`Value`]. The building block the typed `read_*` helpers below share.
pub(crate) fn attr_value(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    stage.field::<Value>(prim.append_property(name)?, FieldKey::Default)
}

/// Read a `token` (or `string`) attribute as a `String`.
pub(crate) fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Token(s) | Value::String(s)) => Some(s),
        _ => None,
    })
}

/// Coerce an `asset` (or `string` / `token`) value to its path string.
pub(crate) fn value_as_asset_str(value: &Value) -> Option<&str> {
    match value {
        Value::AssetPath(s) | Value::String(s) | Value::Token(s) => Some(s),
        _ => None,
    }
}

/// Wrap `path` as a concrete view's `Prim` if its composed `typeName` equals
/// `type_name` — the type-gate every typed view's `get` performs.
pub(crate) fn get_typed(stage: &Stage, path: impl Into<Path>, type_name: &str) -> Result<Option<Prim>> {
    let prim = stage.prim_at(path);
    if prim.type_name()?.as_deref() != Some(type_name) {
        return Ok(None);
    }
    Ok(Some(prim))
}

/// Like [`get_typed`], but matches any of `type_names` — for views that share
/// one Rust type across several concrete schemas.
pub(crate) fn get_typed_any(stage: &Stage, path: impl Into<Path>, type_names: &[&str]) -> Result<Option<Prim>> {
    let prim = stage.prim_at(path);
    match prim.type_name()? {
        Some(t) if type_names.contains(&t.as_str()) => Ok(Some(prim)),
        _ => Ok(None),
    }
}

/// Wrap `path` as an applied-API view's `Prim` if any of `apis` appears in the
/// prim's composed `apiSchemas` — the gate every single-apply API view's `get`
/// performs.
pub(crate) fn get_with_api(stage: &Stage, path: impl Into<Path>, apis: &[&str]) -> Result<Option<Prim>> {
    let prim = stage.prim_at(path);
    let applied = prim.api_schemas()?;
    if apis.iter().any(|a| applied.iter().any(|s| s == a)) {
        Ok(Some(prim))
    } else {
        Ok(None)
    }
}

/// Bidirectional conversion between a token-valued schema enum and
/// [`Value`], both delegating to the enum's `as_token` / `from_token`. `From`
/// authors a [`Value::Token`] so the enum passes straight to
/// [`Attribute::set`](crate::usd::Attribute::set) (`attr.set(Axis::X)?`), and
/// `TryFrom` decodes one (accepting `token` or `string`) so
/// [`Attribute::get`](crate::usd::Attribute::get) extracts it directly
/// (`attr.get::<Axis>()?`). Each enum must expose
/// `fn as_token(self) -> &'static str` and `fn from_token(&str) -> Option<Self>`.
macro_rules! impl_token_value {
    ($($ty:ty),+ $(,)?) => {$(
        impl From<$ty> for $crate::sdf::Value {
            fn from(value: $ty) -> Self {
                $crate::sdf::Value::Token(value.as_token().to_string())
            }
        }

        impl TryFrom<$crate::sdf::Value> for $ty {
            type Error = $crate::sdf::ValueConversionError;

            fn try_from(value: $crate::sdf::Value) -> Result<Self, Self::Error> {
                match &value {
                    $crate::sdf::Value::Token(s) | $crate::sdf::Value::String(s) => <$ty>::from_token(s),
                    _ => None,
                }
                .ok_or_else(|| $crate::sdf::ValueConversionError::new(stringify!($ty), &value))
            }
        }
    )+};
}

pub(crate) use impl_token_value;
