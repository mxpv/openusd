//! What the compiled tables carry against the schemas they were generated
//! from.
//!
//! `openusd-build` checks its own lowering against upstream's generated schema
//! data; this checks the other half, which nothing else can see: that the
//! declaration table compiled into this crate says what that lowering says.
//! Between them a schema is followed from its `schema.usda` to what a stage
//! answers, with no step taken on trust.
//!
//! Everything is compared through a registry rather than as text, so a mistake
//! in a generated `Field::make` closure, a dropped application restriction or a
//! kind written as the wrong variant all surface as a difference in what the
//! registry answers.
//!
//! Only the families this build enables are compared, since only those have a
//! table. With no features there is nothing to check and the test passes having
//! checked nothing, which is what running it against a build that generated
//! nothing should mean.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use openusd::usd::{SchemaRegistry, SchemaRegistryBuilder};
use openusd::{sdf, tf, usd};

/// Where the vendored definitions live, which is what the build script reads.
fn schemas() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("schemas")
}

// The generator as the build script configures it, so the model read here is
// the one the compiled tables were generated from.
include!("../families.rs");

/// Everything a registry answers about one schema: how it applies, what it
/// derives from, what may apply it, and every property a prim of it has before
/// anything is authored.
fn described(registry: &SchemaRegistry, identifier: &tf::Token) -> String {
    let info = registry.schema_info(identifier).expect("the schema is registered");
    let instances: Vec<String> = info
        .allowed_instance_names()
        .iter()
        .map(|instance| format!("{instance}={:?}", info.can_only_apply_to(Some(instance))))
        .collect();

    let mut described = format!(
        "{:?} {:?} v{} family={:?} bases={:?} prefix={:?} auto={:?} only={:?} instances={:?} {instances:?}\n",
        info.identifier(),
        info.kind(),
        info.version(),
        info.family(),
        info.bases(),
        info.property_namespace_prefix(),
        info.auto_apply_to(),
        info.can_only_apply_to(None),
        info.allowed_instance_names(),
    );

    let definition = registry
        .concrete_prim_definition(identifier)
        .or_else(|| registry.api_prim_definition(identifier));
    let Some(definition) = definition else {
        return described;
    };

    described += &format!("  applied={:?}\n", definition.applied_api_schemas());
    for name in definition.property_names() {
        let property = definition.property(name).expect("the property is defined");
        described += &format!(
            "  {name} {:?} {:?} {:?} custom={:?} default={:?} fields={:?}\n",
            property.spec_type(),
            property.type_name(),
            property.variability(),
            property.field(sdf::FieldKey::Custom),
            property.fallback(),
            [
                sdf::FieldKey::AllowedTokens,
                sdf::FieldKey::DisplayName,
                sdf::FieldKey::DisplayGroup,
                sdf::FieldKey::Hidden,
            ]
            .map(|key| property.field(key)),
        );
    }
    described
}

/// The class prims a family's declarations amount to: every spec, its type and
/// its fields.
///
/// Fields are keyed rather than kept in the order they were authored, since a
/// registry reads them by name; the order inside one, as `propertyChildren`
/// keeps, is part of the value and compares with it.
type Specs = BTreeMap<String, (sdf::SpecType, BTreeMap<String, sdf::Value>)>;

fn specs(family: &usd::SchemaFamily<'_>) -> Specs {
    family
        .to_data()
        .expect("the declarations build")
        .iter()
        .map(|(path, spec)| {
            let fields = spec.fields.iter().cloned().collect();
            (path.to_string(), (spec.ty, fields))
        })
        .collect()
}

/// The compiled table and the schema it came from carry the same class prims,
/// and register into registries that answer the same for every schema.
#[test]
fn tables_match_their_schemas() {
    let mut from_source = SchemaRegistryBuilder::empty();
    let mut from_tables = SchemaRegistryBuilder::empty();
    let mut identifiers = Vec::new();

    for compiled in openusd_schemas::ALL {
        let library = compiled.name();
        let output = configured(&schemas())
            .build_library(schemas().join(library).join("schema.usda"), openusd_build::Views::Skip)
            .unwrap_or_else(|error| panic!("{library}: {error}"));

        // The data first, which is where a wrong fallback or a dropped piece of
        // metadata shows up against the exact spec that lost it. One lowering
        // serves both it and the registration below.
        let (theirs, registered) = output.with_family(|family| (specs(family), from_source.register(family)));
        from_source = registered;
        let ours = specs(compiled);
        assert_eq!(ours.keys().collect::<Vec<_>>(), theirs.keys().collect::<Vec<_>>());
        for (path, spec) in &theirs {
            assert_eq!(&ours[path], spec, "{library} {path} is not what its schema declares");
        }

        // Every family declares schemas, so an empty table would otherwise
        // compare clean against an empty table. What a build enables is up to
        // its features, so this is each family's own count rather than a number
        // of families.
        assert!(!compiled.schemas().is_empty(), "{library} declares schemas");
        identifiers.extend(compiled.schemas().iter().map(|decl| tf::Token::from(decl.identifier())));
        from_tables = from_tables.register(compiled);
    }

    // Then what a registry makes of them, which is what a stage actually reads:
    // every kind, base, application rule and composed property fallback.
    let from_tables = from_tables.build().expect("the compiled tables compose");
    let from_source = from_source.build().expect("the generated declarations compose");
    for identifier in &identifiers {
        assert_eq!(
            described(&from_tables, identifier),
            described(&from_source, identifier),
            "{identifier} differs"
        );
    }
}
