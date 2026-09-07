//! Writing what a flattened layer cannot carry.
//!
//! Flattening a schema library answers what each schema *holds*, and forgets
//! what it *is*: its kind, what it derives from, and the rules governing where
//! it may be applied. C++ keeps those in `plugInfo.json`; this crate keeps them
//! in a manifest layer beside the schematics, which is the pair
//! [`family`](openusd::usd::SchemaRegistryBuilder::family) reads a family from.

use openusd::{sdf, tf};

use crate::GENERATED_BY;
use crate::error::Error;
use crate::model::{Class, Library};

/// The library's schema declarations as one manifest layer.
pub fn write(library: &Library) -> Result<sdf::Layer, Error> {
    let mut layer = sdf::Layer::new_anonymous(format!("{} manifest", library.name));

    layer.edit(|edit| {
        let data = edit.data_mut();
        data.set_field(
            &sdf::Path::abs_root(),
            sdf::FieldKey::Comment.as_str(),
            sdf::Value::String(GENERATED_BY.to_owned()),
        );

        for class in &library.classes {
            write_class(data, class)?;
        }
        Ok(())
    })?;

    Ok(layer)
}

/// One schema's entry.
fn write_class(data: &mut dyn sdf::AbstractData, class: &Class) -> Result<(), sdf::AuthoringError> {
    let path = class.prim_path()?;
    sdf::PrimSpec::new(data, &path, sdf::Specifier::Def, "")?;

    uniform_token(data, &path, "schemaKind", tf::Token::new(class.kind.as_str()))?;

    // What the registry walks `is_a` up to. The root every schema derives from
    // has no base of its own, and a library declaring that root says so by
    // leaving the field off rather than by naming it after itself.
    if let Some(base) = &class.direct_base {
        uniform_tokens(data, &path, "bases", vec![base.clone()])?;
    }

    if let Some(prefix) = &class.metadata.property_namespace_prefix {
        uniform_token(data, &path, "propertyNamespacePrefix", prefix.clone())?;
    }
    for (name, tokens) in [
        ("apiSchemaAutoApplyTo", &class.metadata.auto_apply_to),
        ("apiSchemaCanOnlyApplyTo", &class.metadata.can_only_apply_to),
        ("allowedInstanceNames", &class.metadata.allowed_instance_names),
    ] {
        if !tokens.is_empty() {
            uniform_tokens(data, &path, name, tokens.clone())?;
        }
    }

    write_instance_restrictions(data, &path, class);
    Ok(())
}

/// The per-instance application restrictions a multiple-apply schema declares.
///
/// A dictionary rather than attributes, because an instance name may carry
/// namespaces of its own and a flat attribute name could not be split back out
/// of one unambiguously.
fn write_instance_restrictions(data: &mut dyn sdf::AbstractData, path: &sdf::Path, class: &Class) {
    if class.metadata.instance_restrictions.is_empty() {
        return;
    }

    let instances: sdf::Dictionary = class
        .metadata
        .instance_restrictions
        .iter()
        .map(|(instance, allowed)| {
            let entry = sdf::Dictionary::from([(
                "apiSchemaCanOnlyApplyTo".to_owned(),
                sdf::Value::TokenVec(allowed.clone()),
            )]);
            (instance.to_string(), sdf::Value::Dictionary(entry))
        })
        .collect();

    data.set_field(
        path,
        sdf::FieldKey::CustomData.as_str(),
        sdf::Value::Dictionary(sdf::Dictionary::from([(
            "apiSchemaInstances".to_owned(),
            sdf::Value::Dictionary(instances),
        )])),
    );
}

/// Declares one `uniform token` attribute with its value.
fn uniform_token(
    data: &mut dyn sdf::AbstractData,
    prim: &sdf::Path,
    name: &str,
    value: tf::Token,
) -> Result<(), sdf::AuthoringError> {
    let path = prim.append_property(name)?;
    sdf::AttributeSpec::new(data, &path, sdf::ValueTypeName::TOKEN, sdf::Variability::Uniform, false)?
        .set_default(sdf::Value::Token(value))
}

/// Declares one `uniform token[]` attribute with its value.
fn uniform_tokens(
    data: &mut dyn sdf::AbstractData,
    prim: &sdf::Path,
    name: &str,
    values: Vec<tf::Token>,
) -> Result<(), sdf::AuthoringError> {
    let path = prim.append_property(name)?;
    sdf::AttributeSpec::new(
        data,
        &path,
        sdf::ValueTypeName::TOKEN_ARRAY,
        sdf::Variability::Uniform,
        false,
    )?
    .set_default(sdf::Value::TokenVec(values))
}

#[cfg(test)]
mod tests {
    use openusd::usd;

    use super::*;
    use crate::schematics;
    use crate::tests::read_fixture;

    /// The pair registers as a family, which is the whole contract: what the
    /// two layers say is what a registry answers.
    #[test]
    fn registers_as_a_family() {
        let library = read_fixture("schema.usda").expect("resolves");
        let schematics = schematics::write(&library).expect("writes");
        let manifest = write(&library).expect("writes");

        let registry = usd::SchemaRegistry::builder()
            .family(usd::FamilySource {
                name: &library.name,
                manifest: &manifest,
                schematics: &schematics,
            })
            .expect("the generated pair registers")
            .build()
            .expect("builds");

        let info = |identifier: &str| {
            registry
                .schema_info(&tf::Token::from(identifier))
                .unwrap_or_else(|| panic!("{identifier} is registered"))
        };
        assert_eq!(info("Derived").kind(), usd::SchemaKind::ConcreteTyped);
        assert_eq!(info("Base").kind(), usd::SchemaKind::AbstractTyped);
        assert_eq!(info("MultipleApplyAPI").kind(), usd::SchemaKind::MultipleApplyApi);
        assert_eq!(
            info("MultipleApplyAPI")
                .property_namespace_prefix()
                .map(tf::Token::as_str),
            Some("test")
        );

        assert!(
            registry.is_a(&tf::Token::from("Derived"), &tf::Token::from("Base")),
            "the bases the manifest records are what is_a walks"
        );

        // Every application rule the manifest records, read back the way a
        // caller reads it. The writer and the registry's reader spell these
        // field names on their own sides, so a typo on either would otherwise
        // register a family quietly missing a rule.
        let tokens = |names: &[&str]| names.iter().map(|name| tf::Token::from(*name)).collect::<Vec<_>>();
        let single = info("SingleApplyAPI");
        assert_eq!(single.auto_apply_to(), tokens(&["Derived", "ExternalPluginType"]));
        assert_eq!(single.can_only_apply_to(None), tokens(&["Base", "ExternalPluginType"]));

        let multiple = info("MultipleApplyAPI");
        assert_eq!(multiple.allowed_instance_names(), tokens(&["foo", "bar", "baz"]));
        assert_eq!(
            multiple.can_only_apply_to(None),
            tokens(&["Base", "ExternalPluginType"])
        );
        assert_eq!(
            multiple.can_only_apply_to(Some(&tf::Token::from("foo"))),
            tokens(&["Derived"]),
            "an instance with its own restriction replaces the schema-wide one"
        );
        assert_eq!(
            multiple.can_only_apply_to(Some(&tf::Token::from("baz"))),
            tokens(&["Base", "ExternalPluginType"]),
            "an instance without one falls back to it"
        );
    }

    /// The root every schema derives from derives from nothing itself, and is
    /// an abstract base rather than the API schema a class inheriting nothing
    /// and carrying no type otherwise looks like.
    #[test]
    fn root_declares_itself() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = crate::tests::read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testRoot"
    }
)
{
}

class "SchemaBase" {}
"#,
        )
        .expect("resolves");

        let class = library.classes.first().expect("SchemaBase");
        assert_eq!(class.kind, usd::SchemaKind::AbstractBase);
        assert_eq!(class.direct_base, None);

        let manifest = write(&library).expect("writes");
        let kind = manifest
            .attribute("/SchemaBase.schemaKind")
            .expect("a path")
            .expect("the kind attribute")
            .get::<sdf::Value>(sdf::FieldKey::Default)
            .and_then(sdf::Value::try_as_token);
        assert_eq!(kind.as_ref().map(tf::Token::as_str), Some("abstractBase"));
        assert!(
            manifest.attribute("/SchemaBase.bases").expect("a path").is_none(),
            "the root names no base to walk up to"
        );
    }

    /// A schema that inherits nothing still derives from the root every schema
    /// derives from, and the manifest says so rather than leaving it unsaid.
    #[test]
    fn root_base_is_named() {
        let library = read_fixture("schema.usda").expect("resolves");
        let manifest = write(&library).expect("writes");

        let bases = manifest
            .attribute("/Base.bases")
            .expect("a path")
            .expect("the bases attribute")
            .get::<sdf::Value>(sdf::FieldKey::Default)
            .and_then(sdf::Value::try_as_token_vec)
            .expect("a value");
        assert_eq!(bases, vec![tf::Token::from("Typed")], "Base inherits Typed");
    }
}
