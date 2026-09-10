//! Lowering the model to the declarations a registry takes.
//!
//! This is the contractual half of what the generator produces: a registry
//! built from these declarations has to answer what a registry built from
//! C++'s `generatedSchema.usda` and `plugInfo.json` answers, because a stage
//! composed against them must behave like one composed against upstream's.
//!
//! The emitter writes the same declarations as a `const` table, so this is also
//! what that table is checked against — here against upstream's own generated
//! schema data, and in the crate the table is compiled into against this.
//!
//! Everything comes from the model. Composition was consulted once, when the
//! model was built, so nothing here re-reads a layer or re-resolves a value.

use std::collections::BTreeMap;

use openusd::{sdf, tf, usd};

use crate::model::{Class, Library, Property};

/// Calls `f` with the library's schemas as a declared family.
///
/// Nothing here can fail: the model was checked before it got this far, so
/// lowering is a translation of what it already holds.
///
/// The declarations borrow from `library` and from storage this owns for the
/// length of the call, which is why they arrive through a closure rather than
/// as a value: a `usd::SchemaDecl` is a view over its parts, and nothing here
/// keeps a structure pointing into itself.
pub fn with_family<R>(library: &Library, f: impl FnOnce(&usd::SchemaFamily<'_>) -> R) -> R {
    // Built outermost-last, so each level borrows only from the level before.
    let lists: Vec<Lists<'_>> = library.classes.iter().map(Lists::of).collect();
    let nested: Vec<Nested<'_>> = library
        .classes
        .iter()
        .zip(&lists)
        .map(|(class, lists)| Nested::of(class, lists))
        .collect();

    let decls: Vec<usd::SchemaDecl<'_>> = library
        .classes
        .iter()
        .zip(&lists)
        .zip(&nested)
        .map(|((class, lists), nested)| declare(class, lists, nested))
        .collect();

    f(&usd::SchemaFamily::new(&library.name, &decls))
}

/// One class's name lists and field sets, owned so the declaration can borrow
/// them.
struct Lists<'a> {
    bases: Vec<&'a str>,
    applied_api_schemas: Vec<&'a str>,
    override_property_names: Vec<&'a str>,
    auto_apply_to: Vec<&'a str>,
    can_only_apply_to: Vec<&'a str>,
    allowed_instance_names: Vec<&'a str>,
    fallback_types: Vec<&'a str>,
    /// Each instance restriction's own list, paired up in [`Nested`].
    instances: Vec<(&'a str, Vec<&'a str>)>,
    fields: Vec<usd::Field<'a>>,
    /// One entry per property, in the class's own property order.
    property_fields: Vec<Vec<usd::Field<'a>>>,
}

/// What a declaration borrows from [`Lists`] rather than from the model.
struct Nested<'a> {
    instances: Vec<usd::InstanceRestriction<'a>>,
    properties: Vec<usd::PropertyDecl<'a>>,
}

impl<'a> Lists<'a> {
    fn of(class: &'a Class) -> Self {
        let tokens = |names: &'a [tf::Token]| names.iter().map(tf::Token::as_str).collect();

        Self {
            // What the registry walks `is_a` up to, which is the class's own
            // base and not the chain behind it. The root every schema derives
            // from has none.
            bases: class.direct_base.iter().map(tf::Token::as_str).collect(),
            applied_api_schemas: tokens(&class.applied_api_schemas),
            override_property_names: override_names(class),
            auto_apply_to: tokens(&class.metadata.auto_apply_to),
            can_only_apply_to: tokens(&class.metadata.can_only_apply_to),
            allowed_instance_names: tokens(&class.metadata.allowed_instance_names),
            fallback_types: tokens(&class.metadata.fallback_types),
            instances: class
                .metadata
                .instance_restrictions
                .iter()
                .map(|(instance, allowed)| (instance.as_str(), tokens(allowed)))
                .collect(),
            fields: fields(&class.fields, sdf::SpecType::Prim),
            property_fields: class
                .properties
                .iter()
                .map(|property| fields(&property.fields, property.spec_type))
                .collect(),
        }
    }
}

impl<'a> Nested<'a> {
    fn of(class: &'a Class, lists: &'a Lists<'a>) -> Self {
        Self {
            instances: lists
                .instances
                .iter()
                .map(|(instance, allowed)| (*instance, allowed.as_slice()))
                .collect(),
            properties: class
                .properties
                .iter()
                .zip(&lists.property_fields)
                .map(|(property, fields)| declare_property(property, fields))
                .collect(),
        }
    }
}

/// One class as the schema a registry registers.
fn declare<'a>(class: &'a Class, lists: &'a Lists<'a>, nested: &'a Nested<'a>) -> usd::SchemaDecl<'a> {
    let mut decl = usd::SchemaDecl::new(class.identifier.as_str(), class.kind)
        .bases(&lists.bases)
        .properties(&nested.properties)
        .fields(&lists.fields)
        .applied_api_schemas(&lists.applied_api_schemas)
        .override_property_names(&lists.override_property_names)
        .auto_apply_to(&lists.auto_apply_to)
        .can_only_apply_to(&lists.can_only_apply_to)
        .instance_restrictions(&nested.instances)
        .allowed_instance_names(&lists.allowed_instance_names)
        .fallback_types(&lists.fallback_types);

    if let Some(prefix) = &class.metadata.property_namespace_prefix {
        decl = decl.property_namespace_prefix(prefix.as_str());
    }
    decl
}

/// One property under the name the schematics records it by, which for a
/// multiple-apply schema is the template name.
fn declare_property<'a>(property: &'a Property, fields: &'a [usd::Field<'a>]) -> usd::PropertyDecl<'a> {
    let name = property.schematics_name.as_str();
    let decl = if property.spec_type == sdf::SpecType::Relationship {
        usd::PropertyDecl::relationship(name)
    } else {
        // Validation rejects an attribute whose `typeName` names no registered
        // type, so the spelling is there. Were it not, the empty one it stands
        // in for names no type either, and registering the declaration says so.
        usd::PropertyDecl::attribute(name, property.declared_type_name().unwrap_or_default())
    };

    // Said outright rather than left to whichever way the constructor leans,
    // so the two kinds of property keep the variability the schema authored.
    let decl = decl.fields(fields);
    let decl = match property.variability() {
        sdf::Variability::Uniform => decl.uniform(),
        sdf::Variability::Varying => decl.varying(),
    };
    if property.is_custom() { decl.custom() } else { decl }
}

/// The properties a class restates only to change what a built-in API schema
/// declares. A registration sorts them, the set being what matters.
fn override_names(class: &Class) -> Vec<&str> {
    class
        .override_properties()
        .map(|property| property.schematics_name.as_str())
        .collect()
}

/// A model field map as declaration fields, less what a declaration may not
/// carry on a spec of this type.
///
/// This is the one place the model's field maps are narrowed. They travel whole
/// so validation can see a field it means to reject and the emitter can read
/// the documentation; everything else is carried verbatim, so a field nobody
/// thought to name still survives.
///
/// What a registration would refuse is what is dropped here, asked of the
/// registry rather than listed again. `documentation` is this crate's own
/// choice: a registry would carry it, and the generated views say it instead.
/// Everything else is carried, and a value the emitter has no Rust literal for
/// stops the build rather than being dropped on the way past.
fn fields<'a>(fields: &'a BTreeMap<String, sdf::Value>, spec: sdf::SpecType) -> Vec<usd::Field<'a>> {
    fields
        .iter()
        .filter(|(key, _)| {
            key.as_str() != sdf::FieldKey::Documentation.as_str() && !usd::SchemaRegistry::is_reserved_field(spec, key)
        })
        .map(|(key, value)| usd::Field::borrowed(key, value))
        .collect()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::tests::{read_fixture, read_source};

    /// Prim metadata the vendored corpus never exercises, on a schema and on
    /// one inheriting it.
    const METADATA: &str = r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testMetadata"
    }
)
{
}

class "Typed"
{
}

class "Marked" (
    inherits = </Typed>
    hidden = true
    assetInfo = {
        string version = "1"
    }
    customData = {
        string className = "Marked"
    }
)
{
}

class "Refined" (
    inherits = </Marked>
)
{
}
"#;

    /// The class prims a library's declarations amount to.
    fn declared(library: &Library) -> sdf::Data {
        with_family(library, |family| family.to_data()).expect("the declarations register")
    }

    /// One field of one spec.
    fn field(data: &sdf::Data, path: &str, key: sdf::FieldKey) -> Option<sdf::Value> {
        data.spec(&sdf::path(path).expect("a path"))?.get(key.as_str()).cloned()
    }

    /// The registry a library's declarations build, which is what every rule
    /// they carry is finally read back through.
    fn registry(library: &Library) -> Arc<usd::SchemaRegistry> {
        with_family(library, |family| {
            usd::SchemaRegistryBuilder::empty().register(family).build()
        })
        .expect("the declarations register")
    }

    /// A concrete schema names the prim type it stands for; nothing else does.
    #[test]
    fn concrete_carries_type_name() {
        let library = read_fixture("schema.usda").expect("resolves");
        let data = declared(&library);

        let type_name = |path: &str| {
            field(&data, path, sdf::FieldKey::TypeName)
                .and_then(sdf::Value::try_as_token)
                .map(|token| token.as_str().to_owned())
        };
        assert_eq!(type_name("/Derived").as_deref(), Some("Derived"));
        assert_eq!(type_name("/Base"), None, "an abstract schema is no prim type");
        assert_eq!(type_name("/SingleApplyAPI"), None, "nor is an API schema");
    }

    /// A multiple-apply schema's built-ins are recorded as templates, since it
    /// carries them under whatever instance name it is applied with.
    #[test]
    fn applied_names_templated() {
        let library = read_fixture("schema.usda").expect("resolves");
        let data = declared(&library);

        let applied = field(&data, "/PublicMultipleApplyAPI", sdf::FieldKey::ApiSchemas)
            .and_then(sdf::Value::try_as_token_list_op)
            .expect("the built-in list");
        assert_eq!(
            applied.explicit_items,
            vec![
                tf::Token::from("MultiApplyAPI:__INSTANCE_NAME__"),
                tf::Token::from("BuiltinMultiApplyAPI:__INSTANCE_NAME__:builtin"),
            ]
        );
    }

    /// The fallbacks a stage reaches for when a prim type is gone.
    #[test]
    fn fallback_types_recorded() {
        let library = read_fixture("schema.usda").expect("resolves");
        let data = declared(&library);

        let fallbacks = field(&data, "/", sdf::FieldKey::FallbackPrimTypes)
            .and_then(sdf::Value::try_as_dictionary)
            .expect("the fallback dictionary");
        assert_eq!(
            fallbacks.get("Derived").and_then(sdf::Value::try_as_token_vec_ref),
            Some(&vec![tf::Token::from("OldDerived"), tf::Token::from("OlderDerived")])
        );
    }

    /// Prim metadata is a fallback a registry serves from the schema's
    /// definition, so it reaches the declarations rather than stopping at the
    /// model — on the schema that declared it and on the one that inherits it,
    /// composition having put it on both. The `customData` beside it does not:
    /// it is the generator's own input.
    #[test]
    fn prim_metadata_survives() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(dir.path(), METADATA).expect("resolves");
        let data = declared(&library);

        for identifier in ["Marked", "Refined"] {
            let class = library
                .classes
                .iter()
                .find(|class| class.identifier.as_str() == identifier)
                .expect("the class");
            for key in [sdf::FieldKey::Hidden, sdf::FieldKey::AssetInfo] {
                let carried = field(&data, &format!("/{identifier}"), key);
                assert!(carried.is_some(), "{identifier} lost {}", key.as_str());
                assert_eq!(
                    carried.as_ref(),
                    class.fields.get(key.as_str()),
                    "{identifier}.{} is not what the model carried",
                    key.as_str()
                );
            }
        }

        assert_eq!(
            field(&data, "/Marked", sdf::FieldKey::CustomData),
            None,
            "the generator's own input is not schema data"
        );
        assert_eq!(
            field(&data, "/Marked", sdf::FieldKey::InheritPaths),
            None,
            "a declaration is already flat"
        );
    }

    /// A relationship keeps the variability the schema authored, which is not
    /// the one either kind of property defaults to: a bare `rel` is uniform and
    /// an attribute is varying, so a declaration that leaned on a default would
    /// silently change one of them.
    #[test]
    fn relationship_variability_kept() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testVariability"
    }
)
{
}

class "Typed" {}

class "Bound" (
    inherits = </Typed>
)
{
    rel plain
    varying rel loose
    uniform double fixed = 1
    double free = 1
}
"#,
        )
        .expect("resolves");
        let data = declared(&library);

        let variability = |name: &str| {
            field(&data, &format!("/Bound.{name}"), sdf::FieldKey::Variability).and_then(sdf::Value::try_as_variability)
        };
        assert_eq!(variability("plain"), Some(sdf::Variability::Uniform));
        assert_eq!(variability("loose"), None, "varying is the unauthored spelling");
        assert_eq!(variability("fixed"), Some(sdf::Variability::Uniform));
        assert_eq!(variability("free"), None);
    }

    /// The declarations register as a family, which is the whole contract: what
    /// they say is what a registry answers.
    #[test]
    fn registers_as_a_family() {
        let library = read_fixture("schema.usda").expect("resolves");
        let registry = registry(&library);

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
            "the bases the declarations record are what is_a walks"
        );
        assert_eq!(
            info("Base").bases(),
            vec![tf::Token::from("Typed")],
            "a schema inheriting nothing still derives from the root, and says so"
        );

        // Every application rule the declarations record, read back the way a
        // caller reads it. The lowering and the registry's reader name these on
        // their own sides, so a mistake on either would otherwise register a
        // family quietly missing a rule.
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
        let library = read_source(
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

        let registry = registry(&library);
        let info = registry
            .schema_info(&tf::Token::from("SchemaBase"))
            .expect("SchemaBase is registered");
        assert_eq!(info.kind(), usd::SchemaKind::AbstractBase);
        assert!(info.bases().is_empty(), "the root names no base to walk up to");
    }
}
