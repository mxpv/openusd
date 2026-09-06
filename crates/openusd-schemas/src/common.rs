//! Low-level building blocks shared across the schema families.
//!
//! The view-gate helpers ([`get_typed`], [`is_typed`], [`is_any_typed`],
//! [`get_typed_in_family`], [`get_with_api`])
//! back the type-gated `get` lookups every trait-view family shares, and the
//! small value reader ([`read_token`]) plus the
//! [`impl_token_value!`] macro cover the decoding that would otherwise be
//! duplicated verbatim. Attribute *authoring* is inlined per family via the
//! [`Attribute`](openusd::usd::Attribute) builder, so no shared authoring
//! helpers live here.

// Each helper is used by at least one schema feature, but typically not
// all — silence the dead-code warning on per-feature builds.
#![allow(dead_code)]

use openusd::Result;

use openusd::sdf::{self, FieldKey, Path};
use openusd::tf;
use openusd::usd::{Prim, Stage, VersionFilter};

/// Read a `token`-valued attribute. A non-token value reads as absent
/// (`token` attributes never resolve to a `Value::String`).
pub(crate) fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<tf::Token>> {
    Ok(stage.field::<tf::Token>(prim.append_property(name)?, FieldKey::Default)?)
}

/// Wrap `path` as a concrete view's `Prim` if the prim is `type_name` or
/// derives from it — the type-gate every typed view's `get` performs, matching
/// how a C++ schema's `Get` validates through [`Prim::is_a`].
///
/// A prim backed by a registered schema is gated on derivation, so a base
/// view matches a derived prim. A prim the registry has no schema for is gated
/// on its authored `typeName` alone, which is what resolves the views while
/// the process registry carries only the core `usd` family.
pub(crate) fn get_typed(
    stage: &Stage,
    path: impl sdf::IntoPath,
    type_name: impl Into<tf::Token>,
) -> Result<Option<Prim>> {
    let prim = stage.prim(path)?;
    Ok(is_typed(&prim, type_name)?.then_some(prim))
}

/// Whether `prim` is `type_name` or derives from it — the gate [`get_typed`]
/// applies, asked of a prim already in hand.
pub(crate) fn is_typed(prim: &Prim, type_name: impl Into<tf::Token>) -> Result<bool> {
    let type_name = type_name.into();
    is_any_typed(prim, &[type_name.as_str()])
}

/// Whether `prim` is any of `type_names`, or derives from one.
///
/// The prim's schema type is resolved once and tested against every candidate,
/// so asking about several types costs no more lookups than asking about one.
// TODO: drop the authored-name arm once every stage's registry carries the
// schema data — it answers for prims whose type the *stage's* registry does not
// know, so a partially registered custom registry still needs it.
pub(crate) fn is_any_typed(prim: &Prim, type_names: &[&str]) -> Result<bool> {
    if let Some(schema_type) = prim.schema_type()? {
        let registry = prim.stage().schema_registry();
        return Ok(type_names
            .iter()
            .any(|name| registry.is_a(&schema_type, &tf::Token::from(*name))));
    }
    let authored = prim.type_name()?;
    Ok(type_names.iter().any(|name| authored.as_deref() == Some(*name)))
}

/// Like [`get_typed`], but matches any version of the schema family `family` —
/// the gate for a view whose schema has shipped under more than one version
/// (`DomeLight`, `DomeLight_1`).
///
/// The version a prim carries is its own business, so the gate asks
/// [`Prim::is_in_family`], which places a prim by its registered schema or, for
/// a type no registered schema backs, by the family its authored `typeName`
/// names.
pub(crate) fn get_typed_in_family(
    stage: &Stage,
    path: impl sdf::IntoPath,
    family: impl Into<tf::Token>,
) -> Result<Option<Prim>> {
    let prim = stage.prim(path)?;
    Ok(prim.is_in_family(family, VersionFilter::All)?.then_some(prim))
}

/// Wrap `path` as an applied-API view's `Prim` if any of `apis` appears in the
/// prim's composed `apiSchemas` — the gate every single-apply API view's `get`
/// performs.
pub(crate) fn get_with_api(stage: &Stage, path: impl sdf::IntoPath, apis: &[impl AsRef<str>]) -> Result<Option<Prim>> {
    let prim = stage.prim(path)?;
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
/// [`Attribute::set`](openusd::usd::Attribute::set) (`attr.set(Axis::X)?`), and
/// `TryFrom` decodes one (these attributes are `token`-valued, so only a
/// `Value::Token` decodes) so [`Attribute::get`](openusd::usd::Attribute::get)
/// extracts it directly (`attr.get::<Axis>()?`). Each enum must expose
/// `fn as_token(self) -> &'static str` and
/// `fn from_token(impl Into<tf::Token>) -> Option<Self>`.
macro_rules! impl_token_value {
    ($($ty:ty),+ $(,)?) => {$(
        impl From<$ty> for $crate::openusd::sdf::Value {
            fn from(value: $ty) -> Self {
                $crate::openusd::sdf::Value::Token(value.as_token().into())
            }
        }

        impl TryFrom<$crate::openusd::sdf::Value> for $ty {
            type Error = $crate::openusd::sdf::CastError;

            fn try_from(value: $crate::openusd::sdf::Value) -> Result<Self, Self::Error> {
                match &value {
                    $crate::openusd::sdf::Value::Token(s) => <$ty>::from_token(s.as_str()),
                    _ => None,
                }
                .ok_or_else(|| $crate::openusd::sdf::CastError::TypeMismatch {
                    target: stringify!($ty),
                    actual: (&value).into(),
                })
            }
        }
    )+};
}

pub(crate) use impl_token_value;

#[cfg(test)]
mod tests {
    use super::*;

    use openusd::Result;
    use openusd::usd::{FamilySource, SchemaRegistryBuilder};

    /// One abstract base with three concrete types under it, two of them
    /// versions of the same family name — the derivation chain and version
    /// suffix the type gates below resolve against.
    const MANIFEST: &str = r#"#usda 1.0

def "NonboundableLightBase"
{
    uniform token schemaKind = "abstractTyped"
}

def "DistantLight"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["NonboundableLightBase"]
}

def "DomeLight"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["NonboundableLightBase"]
}

def "DomeLight_1"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["NonboundableLightBase"]
}
"#;

    const SCHEMATICS: &str = r#"#usda 1.0

class "NonboundableLightBase"
{
}

class DistantLight "DistantLight"
{
}

class DomeLight "DomeLight"
{
}

class DomeLight_1 "DomeLight_1"
{
}
"#;

    /// One of the family's layers, over text.
    fn layer(text: &str) -> openusd::sdf::Layer {
        openusd::sdf::Layer::from_bytes("test", text.as_bytes().to_vec()).expect("the layer parses")
    }

    /// A stage resolving against the miniature family above.
    fn schema_stage() -> Result<Stage> {
        let registry = SchemaRegistryBuilder::empty()
            .family(FamilySource {
                name: "test",
                manifest: &layer(MANIFEST),
                schematics: &layer(SCHEMATICS),
            })
            .expect("test family registers")
            .build()
            .expect("test registry builds");

        Stage::builder().schema_registry(registry).in_memory("anon.usda")
    }

    #[test]
    fn typed_gate_subtype() -> Result<()> {
        let stage = schema_stage()?;
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
    fn family_gate_versions() -> Result<()> {
        let stage = schema_stage()?;
        stage.define_prim("/Old")?.set_type_name("DomeLight")?;
        stage.define_prim("/New")?.set_type_name("DomeLight_1")?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // One gate covers every version the family has shipped under.
        assert!(get_typed_in_family(&stage, "/Old", "DomeLight")?.is_some());
        assert!(get_typed_in_family(&stage, "/New", "DomeLight")?.is_some());
        assert!(get_typed_in_family(&stage, "/Sun", "DomeLight")?.is_none());
        Ok(())
    }

    #[test]
    fn family_gate_no_schema_data() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/New")?.set_type_name("DomeLight_1")?;
        stage.define_prim("/Sun")?.set_type_name("DistantLight")?;

        // With nothing registered the authored name carries its own version
        // suffix, so the family still resolves without listing the versions.
        assert!(get_typed_in_family(&stage, "/New", "DomeLight")?.is_some());
        assert!(get_typed_in_family(&stage, "/Sun", "DomeLight")?.is_none());

        // Only a spelling that could name a schema is placed in the family, so
        // a non-canonical version suffix is not a `DomeLight`.
        stage.define_prim("/Odd")?.set_type_name("DomeLight_01")?;
        assert!(get_typed_in_family(&stage, "/Odd", "DomeLight")?.is_none());
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
