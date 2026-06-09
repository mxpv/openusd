//! Low-level building blocks shared across the schema families.
//!
//! The view-gate helpers ([`get_typed`], [`get_typed_any`], [`get_with_api`])
//! back the type-gated `get` lookups every trait-view family shares, and the
//! small value reader ([`read_token`]) plus the
//! [`impl_token_value!`] macro cover the decoding that would otherwise be
//! duplicated verbatim. Attribute *authoring* is inlined per family via the
//! [`Attribute`](crate::usd::Attribute) builder, so no shared authoring
//! helpers live here.

// Each helper is used by at least one schema feature, but typically not
// all — silence the dead-code warning on per-feature builds.
#![allow(dead_code)]

use anyhow::Result;

use crate::sdf::{FieldKey, Path};
use crate::tf;
use crate::usd::{Prim, Stage};

/// Read a `token`-valued attribute. A non-token value reads as absent
/// (`token` attributes never resolve to a `Value::String`).
pub(crate) fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<tf::Token>> {
    stage.field::<tf::Token>(prim.append_property(name)?, FieldKey::Default)
}

/// Wrap `path` as a concrete view's `Prim` if its composed `typeName` equals
/// `type_name` — the type-gate every typed view's `get` performs.
pub(crate) fn get_typed(stage: &Stage, path: impl Into<Path>, type_name: impl Into<tf::Token>) -> Result<Option<Prim>> {
    let prim = stage.prim_at(path);
    if prim.type_name()? != Some(type_name.into()) {
        return Ok(None);
    }
    Ok(Some(prim))
}

/// Like [`get_typed`], but matches any of `type_names` — for views that share
/// one Rust type across several concrete schemas.
pub(crate) fn get_typed_any(
    stage: &Stage,
    path: impl Into<Path>,
    type_names: &[impl AsRef<str>],
) -> Result<Option<Prim>> {
    let prim = stage.prim_at(path);
    match prim.type_name()? {
        Some(t) if type_names.iter().any(|n| n.as_ref() == t.as_str()) => Ok(Some(prim)),
        _ => Ok(None),
    }
}

/// Wrap `path` as an applied-API view's `Prim` if any of `apis` appears in the
/// prim's composed `apiSchemas` — the gate every single-apply API view's `get`
/// performs.
pub(crate) fn get_with_api(stage: &Stage, path: impl Into<Path>, apis: &[impl AsRef<str>]) -> Result<Option<Prim>> {
    let prim = stage.prim_at(path);
    let applied = prim.api_schemas()?;
    if apis.iter().any(|a| applied.iter().any(|s| s.as_str() == a.as_ref())) {
        Ok(Some(prim))
    } else {
        Ok(None)
    }
}

/// Bidirectional conversion between a token-valued schema enum and
/// [`Value`], both delegating to the enum's `as_token` / `from_token`. `From`
/// authors a [`Value::Token`] so the enum passes straight to
/// [`Attribute::set`](crate::usd::Attribute::set) (`attr.set(Axis::X)?`), and
/// `TryFrom` decodes one (these attributes are `token`-valued, so only a
/// `Value::Token` decodes) so [`Attribute::get`](crate::usd::Attribute::get)
/// extracts it directly (`attr.get::<Axis>()?`). Each enum must expose
/// `fn as_token(self) -> &'static str` and
/// `fn from_token(impl Into<tf::Token>) -> Option<Self>`.
macro_rules! impl_token_value {
    ($($ty:ty),+ $(,)?) => {$(
        impl From<$ty> for $crate::sdf::Value {
            fn from(value: $ty) -> Self {
                $crate::sdf::Value::Token(value.as_token().into())
            }
        }

        impl TryFrom<$crate::sdf::Value> for $ty {
            type Error = $crate::sdf::ValueConversionError;

            fn try_from(value: $crate::sdf::Value) -> Result<Self, Self::Error> {
                match &value {
                    $crate::sdf::Value::Token(s) => <$ty>::from_token(s.as_str()),
                    _ => None,
                }
                .ok_or_else(|| $crate::sdf::ValueConversionError::new(stringify!($ty), &value))
            }
        }
    )+};
}

pub(crate) use impl_token_value;
