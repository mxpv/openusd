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

use std::slice;

use anyhow::Result;

use crate::sdf::{FieldKey, Path};
use crate::tf;
use crate::usd::{Prim, Stage};

/// Read a `token`-valued attribute. A non-token value reads as absent
/// (`token` attributes never resolve to a `Value::String`).
pub(crate) fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<tf::Token>> {
    stage.field::<tf::Token>(prim.append_property(name)?, FieldKey::Default)
}

/// Wrap `path` as a concrete view's `Prim` if the prim is `type_name` or
/// derives from it — the type-gate every typed view's `get` performs, matching
/// how a C++ schema's `Get` validates through [`Prim::is_a`].
pub(crate) fn get_typed(stage: &Stage, path: impl Into<Path>, type_name: impl Into<tf::Token>) -> Result<Option<Prim>> {
    get_typed_any(stage, path, slice::from_ref(&type_name.into()))
}

/// Like [`get_typed`], but matches any of `type_names` — for views that share
/// one Rust type across several concrete schemas.
///
/// A prim backed by a registered schema is gated on derivation, so a base
/// view matches a derived prim. A prim the registry has no schema for is gated
/// on its authored `typeName` alone, which is what resolves the views while
/// [`SchemaRegistryBuilder::compiled_in`](crate::usd::SchemaRegistryBuilder::compiled_in)
/// registers no schema data.
// TODO: drop the authored-name arm once every stage's registry carries the
// schema data — it answers for prims whose type the *stage's* registry does not
// know, so a partially registered custom registry still needs it.
// TODO: express a versioned family (`DomeLight` / `DomeLight_1`) as one query
// over `SchemaInfo::family`, the way C++ `UsdPrim::IsInFamily` does, rather
// than as a hand-maintained list at the call site.
pub(crate) fn get_typed_any(
    stage: &Stage,
    path: impl Into<Path>,
    type_names: &[impl AsRef<str>],
) -> Result<Option<Prim>> {
    let prim = stage.prim(path);
    let registry = stage.schema_registry();

    // Derivation is a question about the prim's schema type, which is empty
    // unless a registered type backs it. Deriving it is only worth the composed
    // reads when there are schemas for it to resolve against.
    let schema_type = match registry.is_empty() {
        true => None,
        false => Some(prim.prim_type_info()?.schema_type_name().clone()).filter(|name| !name.as_str().is_empty()),
    };

    let matched = match &schema_type {
        Some(schema_type) => type_names
            .iter()
            .any(|name| registry.is_a(schema_type, &tf::Token::from(name.as_ref()))),
        None => {
            let authored = prim.type_name()?;
            type_names.iter().any(|name| authored.as_deref() == Some(name.as_ref()))
        }
    };
    Ok(matched.then_some(prim))
}

/// Wrap `path` as an applied-API view's `Prim` if any of `apis` appears in the
/// prim's composed `apiSchemas` — the gate every single-apply API view's `get`
/// performs.
pub(crate) fn get_with_api(stage: &Stage, path: impl Into<Path>, apis: &[impl AsRef<str>]) -> Result<Option<Prim>> {
    let prim = stage.prim(path);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::usd::SchemaRegistry;

    #[test]
    fn typed_gate_subtype() -> Result<()> {
        let stage = Stage::builder()
            .schema_registry(SchemaRegistry::test_registry())
            .in_memory("anon.usda")?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // A base view is valid for a derived prim, as the C++ schema's `Get`
        // is; a sibling is not.
        assert!(get_typed(&stage, "/Sun", "NonboundableLightBase")?.is_some());
        assert!(get_typed(&stage, "/Sun", "DistantLight")?.is_some());
        assert!(get_typed(&stage, "/Sun", "DomeLight_1")?.is_none());

        // The reverse direction does not hold: a prim authored as the abstract
        // base is not any of the concrete types under it.
        stage.define_prim("/Base")?.set_type_name("NonboundableLightBase")?;
        assert!(get_typed(&stage, "/Base", "DistantLight")?.is_none());
        Ok(())
    }

    #[test]
    fn typed_gate_no_schema_data() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // With nothing registered there are no derivations to honour.
        assert!(get_typed(&stage, "/Sun", "DistantLight")?.is_some());
        assert!(get_typed(&stage, "/Sun", "NonboundableLightBase")?.is_none());
        Ok(())
    }
}
