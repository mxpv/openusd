//! Schema registry build tests over the public API.
//!
//! Each test registers its own miniature family through
//! `usd::SchemaRegistry::builder` and asserts on the definitions the build
//! composes. Unit tests that reach module-private helpers or the shared
//! `cfg(test)` fixture family live with the module in
//! `src/usd/schema_registry.rs`.

use std::sync::Arc;

use openusd::usd::{
    FamilySource, Field, PropertyDecl, SchemaDecl, SchemaFamily, SchemaKind, SchemaRegistry, SchemaRegistryBuilder,
    SchemaRegistryError,
};
use openusd::{sdf, tf};

/// One of a family's layers, over text: how a family stored as `.usda` and
/// read into memory reaches the registry.
fn layer(text: &str) -> sdf::Layer {
    sdf::Layer::from_bytes("test", text.as_bytes().to_vec()).expect("the layer parses")
}

/// A registry assembled for a caller's own family carries the core one too, so
/// handing a custom registry to a stage does not cost it the definitions the
/// same stage had by default. Only [`SchemaRegistryBuilder::empty`] starts
/// from nothing.
#[test]
fn builder_seeds_core_family() {
    let manifest = r#"#usda 1.0

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["Typed"]
}
"#;
    let registry = SchemaRegistry::builder()
        .family(FamilySource {
            name: "widget",
            manifest: &layer(manifest),
            schematics: &layer("#usda 1.0\n\nclass Widget \"Widget\"\n{\n}\n"),
        })
        .build()
        .expect("registry builds");

    // The core schemas are still there, and the custom family's base reaches
    // them — the whole point of seeding.
    assert!(registry.schema_info(&tf::Token::new("CollectionAPI")).is_some());
    assert!(registry.is_a(&tf::Token::new("Widget"), &tf::Token::new("Typed")));
    assert!(registry.is_a(&tf::Token::new("Widget"), &tf::Token::new("SchemaBase")));
}

/// Redeclaring one of the core schemas is the ordinary duplicate error, not a
/// silent replacement.
#[test]
fn seeded_builder_rejects_core_duplicate() {
    let manifest = r#"#usda 1.0

def "CollectionAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
}
"#;
    let error = SchemaRegistry::builder()
        .family(FamilySource {
            name: "mine",
            manifest: &layer(manifest),
            schematics: &layer("#usda 1.0\n\nclass \"CollectionAPI\"\n{\n}\n"),
        })
        .build()
        .expect_err("a core schema cannot be redeclared");
    assert!(format!("{error:#}").contains("CollectionAPI"), "{error:#}");
}

/// Builds a registry from one schema family's manifest and schematics.
fn registry(manifest: &str, schematics: &str) -> Arc<SchemaRegistry> {
    SchemaRegistryBuilder::empty()
        .family(FamilySource {
            name: "test",
            manifest: &layer(manifest),
            schematics: &layer(schematics),
        })
        .build()
        .expect("registry builds")
}

#[test]
fn is_a_unregistered_base() {
    // A family whose bases live in a family that was left out answers the
    // same as registering nothing: the walk could only reach one link of a
    // chain it cannot see, so it reports none of it.
    let manifest = r#"#usda 1.0

def "LightFilter"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["Xformable"]
}
"#;
    let registry = registry(manifest, "#usda 1.0\n\nclass LightFilter \"LightFilter\"\n{\n}\n");

    let filter = tf::Token::new("LightFilter");
    assert!(registry.is_a(&filter, &filter));
    assert!(!registry.is_a(&filter, &tf::Token::new("Xformable")));
    assert!(!registry.is_a(&filter, &tf::Token::new("Imageable")));
}

#[test]
fn built_in_must_be_applied() {
    // A class prim can name anything in `apiSchemas`; only an applied API
    // schema is one, so a typed schema named there contributes nothing and
    // never acquires a definition of its own.
    let manifest = r#"#usda 1.0

def "APISchemaBase"
{
    uniform token schemaKind = "abstractBase"
}

def "Marker"
{
    uniform token schemaKind = "concreteTyped"
}

def "ConfusedAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] bases = ["APISchemaBase"]
}
"#;
    let schematics = r#"#usda 1.0

class "APISchemaBase"
{
}

class Marker "Marker"
{
    float marker:size = 1
}

class "ConfusedAPI" (
    apiSchemas = ["Marker"]
)
{
}
"#;
    let registry = registry(manifest, schematics);

    let confused = registry
        .api_prim_definition(&tf::Token::new("ConfusedAPI"))
        .expect("the API schema is defined");
    assert!(!confused.has_property(&tf::Token::new("marker:size")));
    assert_eq!(confused.applied_api_schemas(), [tf::Token::new("ConfusedAPI")]);
    assert!(registry.api_prim_definition(&tf::Token::new("Marker")).is_none());
}

#[test]
fn is_a_cycle_terminates() {
    let manifest = r#"#usda 1.0

def "Loop"
{
    uniform token schemaKind = "abstractTyped"
    uniform token[] bases = ["Knot"]
}

def "Knot"
{
    uniform token schemaKind = "abstractTyped"
    uniform token[] bases = ["Loop"]
}
"#;
    let registry = registry(manifest, "#usda 1.0\n\nclass \"Loop\"\n{\n}\n\nclass \"Knot\"\n{\n}\n");

    // A manifest is data, so a base cycle must not hang the query.
    assert!(registry.is_a(&tf::Token::new("Loop"), &tf::Token::new("Knot")));
    assert!(!registry.is_a(&tf::Token::new("Loop"), &tf::Token::new("Elsewhere")));
}

#[test]
fn built_ins_reject_template_mismatch() {
    // A single-apply schema including a bare multiple-apply template has to
    // be dropped: the placeholder would survive into a concrete prim.
    let manifest = r#"#usda 1.0

def "APISchemaBase"
{
    uniform token schemaKind = "abstractBase"
}

def "MultiAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
}

def "SingleAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}
"#;
    let schematics = r#"#usda 1.0

class "APISchemaBase"
{
}

class "MultiAPI"
{
    float multi:__INSTANCE_NAME__:value = 1
}

class "SingleAPI" (
    apiSchemas = ["MultiAPI:__INSTANCE_NAME__"]
)
{
}
"#;
    let registry = registry(manifest, schematics);

    let single = registry
        .api_prim_definition(&tf::Token::new("SingleAPI"))
        .expect("SingleAPI");
    assert_eq!(single.applied_api_schemas(), [tf::Token::new("SingleAPI")]);
    assert!(single.property_names().is_empty());
}

#[test]
fn multi_apply_own_family_version_refused() {
    let manifest = r#"#usda 1.0

def "ThingAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
}

def "ThingAPI_2"
{
    uniform token schemaKind = "multipleApplyAPI"
}
"#;
    let schematics = r#"#usda 1.0

class "ThingAPI" (
    apiSchemas = ["ThingAPI_2:__INSTANCE_NAME__"]
)
{
    float thing:__INSTANCE_NAME__:one = 1
}

class "ThingAPI_2"
{
    float thing:__INSTANCE_NAME__:two = 2
}
"#;
    let registry = registry(manifest, schematics);

    // The conflict is caught while building, not left to poison every
    // application of the schema once an instance name is chosen.
    let thing = registry
        .api_prim_definition(&tf::Token::new("ThingAPI"))
        .expect("ThingAPI");
    assert_eq!(
        thing.applied_api_schemas(),
        [tf::Token::new("ThingAPI:__INSTANCE_NAME__")]
    );

    // Applying it still yields the schema's own properties.
    let composed = registry.build_composed_prim_definition(&tf::Token::default(), &[tf::Token::new("ThingAPI:bar")]);
    assert_eq!(
        composed.attribute_fallback(&tf::Token::new("thing:bar:one")),
        Some(sdf::Value::Float(1.0))
    );
}

#[test]
fn built_ins_reject_kind_mismatch() {
    // A single-apply schema wearing a template name has no instance to
    // substitute, so composing it would leave the placeholder in place.
    let manifest = r#"#usda 1.0

def "SingleAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "MultiAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
}
"#;
    let schematics = r#"#usda 1.0

class "SingleAPI"
{
    float single = 1
}

class "MultiAPI" (
    apiSchemas = ["SingleAPI:__INSTANCE_NAME__"]
)
{
    float multi:__INSTANCE_NAME__:value = 2
}
"#;
    let registry = registry(manifest, schematics);

    let multi = registry
        .api_prim_definition(&tf::Token::new("MultiAPI"))
        .expect("MultiAPI");
    assert_eq!(
        multi.applied_api_schemas(),
        [tf::Token::new("MultiAPI:__INSTANCE_NAME__")]
    );
    assert!(!multi.has_property(&tf::Token::new("single")));
}

#[test]
fn built_in_cycle_terminates() {
    let manifest = r#"#usda 1.0

def "FirstAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "SecondAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}
"#;
    let schematics = r#"#usda 1.0

class "FirstAPI" (
    apiSchemas = ["SecondAPI"]
)
{
    float first = 1
}

class "SecondAPI" (
    apiSchemas = ["FirstAPI"]
)
{
    float second = 2
}
"#;
    let registry = registry(manifest, schematics);

    // The mutual inclusion stops where it repeats rather than expanding
    // forever, and each definition is built from its own root, so neither
    // keeps the partial view the other's expansion saw.
    let first = registry
        .api_prim_definition(&tf::Token::new("FirstAPI"))
        .expect("FirstAPI");
    assert!(first.has_property(&tf::Token::new("first")));
    assert!(first.has_property(&tf::Token::new("second")));

    let second = registry
        .api_prim_definition(&tf::Token::new("SecondAPI"))
        .expect("SecondAPI");
    assert!(second.has_property(&tf::Token::new("second")));
    assert!(second.has_property(&tf::Token::new("first")));
}

#[test]
fn unknown_built_in_is_skipped() {
    let manifest = "#usda 1.0\n\ndef \"ThingAPI\"\n{\n    uniform token schemaKind = \"singleApplyAPI\"\n}\n";
    let schematics = r#"#usda 1.0

class "ThingAPI" (
    apiSchemas = ["FromAnotherFamily"]
)
{
    float thing = 1
}
"#;
    // An unregistered built-in does not fail the build.
    let registry = registry(manifest, schematics);

    let thing = registry
        .api_prim_definition(&tf::Token::new("ThingAPI"))
        .expect("ThingAPI");
    assert!(thing.has_property(&tf::Token::new("thing")));
    assert_eq!(thing.applied_api_schemas(), [tf::Token::new("ThingAPI")]);
}

#[test]
fn built_in_own_family_version_refused() {
    let manifest = r#"#usda 1.0

def "ThingAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "ThingAPI_2"
{
    uniform token schemaKind = "singleApplyAPI"
}
"#;
    let schematics = r#"#usda 1.0

class "ThingAPI" (
    apiSchemas = ["ThingAPI_2"]
)
{
    float one = 1
}

class "ThingAPI_2"
{
    float two = 2
}
"#;
    let registry = registry(manifest, schematics);

    // A schema cannot build in a second version of its own family.
    let thing = registry
        .api_prim_definition(&tf::Token::new("ThingAPI"))
        .expect("ThingAPI");
    assert_eq!(thing.applied_api_schemas(), [tf::Token::new("ThingAPI")]);
    assert!(!thing.has_property(&tf::Token::new("two")));
}

#[test]
fn auto_apply_to_typed() {
    let manifest = r#"#usda 1.0

def "MarkerAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["Widget"]
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
    let schematics = r#"#usda 1.0

class "MarkerAPI"
{
    float marker:size = 2
}

class Widget "Widget"
{
    float widget:width = 1
}
"#;
    let registry = registry(manifest, schematics);

    // The type says nothing about the API schema; the API schema says it
    // applies to the type, and that is enough to build it in.
    let widget = registry
        .concrete_prim_definition(&tf::Token::new("Widget"))
        .expect("Widget");
    assert_eq!(widget.applied_api_schemas(), [tf::Token::new("MarkerAPI")]);
    assert_eq!(
        widget.attribute_fallback(&tf::Token::new("marker:size")),
        Some(sdf::Value::Float(2.0))
    );
}

#[test]
fn auto_apply_reaches_derived() {
    let manifest = r#"#usda 1.0

def "MarkerAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["Base"]
}

def "Base"
{
    uniform token schemaKind = "abstractTyped"
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["Base"]
}

def "Gadget"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["Widget"]
}

def "Other"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
    let schematics = r#"#usda 1.0

class "MarkerAPI"
{
    float marker:size = 2
}

class "Base"
{
}

class Widget "Widget"
{
}

class Gadget "Gadget"
{
}

class Other "Other"
{
}
"#;
    let registry = registry(manifest, schematics);

    // A target carries everything below it, however deep, and nothing else.
    let marker = tf::Token::new("marker:size");
    for derived in ["Widget", "Gadget"] {
        let definition = registry
            .concrete_prim_definition(&tf::Token::new(derived))
            .expect("a derived type is defined");
        assert!(definition.has_property(&marker), "{derived} missed the auto-apply");
    }
    let other = registry
        .concrete_prim_definition(&tf::Token::new("Other"))
        .expect("Other");
    assert!(!other.has_property(&marker));
    assert!(other.applied_api_schemas().is_empty());
}

#[test]
fn auto_apply_to_api_schema() {
    let manifest = r#"#usda 1.0

def "MarkerAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["HostAPI"]
}

def "HostAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
    let schematics = r#"#usda 1.0

class "MarkerAPI"
{
    float marker:size = 2
}

class "HostAPI"
{
    float host:name = 1
}

class Widget "Widget" (
    apiSchemas = ["HostAPI"]
)
{
}
"#;
    let registry = registry(manifest, schematics);

    // The auto-apply lands on the API schema, so everything that builds
    // that schema in picks it up too.
    let widget = registry
        .concrete_prim_definition(&tf::Token::new("Widget"))
        .expect("Widget");
    assert_eq!(
        widget.applied_api_schemas(),
        [tf::Token::new("HostAPI"), tf::Token::new("MarkerAPI")]
    );
    assert!(widget.has_property(&tf::Token::new("marker:size")));
}

#[test]
fn auto_apply_after_declared() {
    let manifest = r#"#usda 1.0

def "StrongAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "WeakAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["Widget"]
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
    let schematics = r#"#usda 1.0

class "StrongAPI"
{
    float shared = 1
}

class "WeakAPI"
{
    float shared = 2
}

class Widget "Widget" (
    apiSchemas = ["StrongAPI"]
)
{
}
"#;
    let registry = registry(manifest, schematics);

    // What the class prim declares is stronger than what is applied to it
    // from outside, so the declared schema's fallback wins.
    let widget = registry
        .concrete_prim_definition(&tf::Token::new("Widget"))
        .expect("Widget");
    assert_eq!(
        widget.applied_api_schemas(),
        [tf::Token::new("StrongAPI"), tf::Token::new("WeakAPI")]
    );
    assert_eq!(
        widget.attribute_fallback(&tf::Token::new("shared")),
        Some(sdf::Value::Float(1.0))
    );
}

#[test]
fn auto_apply_newest_version_wins() {
    let manifest = r#"#usda 1.0

def "ThingAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["Widget"]
}

def "ThingAPI_2"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["Widget"]
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
    let schematics = r#"#usda 1.0

class "ThingAPI"
{
    float version = 1
}

class "ThingAPI_2"
{
    float version = 2
    float extra = 0
}

class Widget "Widget"
{
}
"#;
    let registry = registry(manifest, schematics);

    // Reverse dictionary order puts the later version first, and only one
    // version of a family composes, so the earlier one contributes
    // nothing.
    let widget = registry
        .concrete_prim_definition(&tf::Token::new("Widget"))
        .expect("Widget");
    assert_eq!(widget.applied_api_schemas(), [tf::Token::new("ThingAPI_2")]);
    assert_eq!(
        widget.attribute_fallback(&tf::Token::new("version")),
        Some(sdf::Value::Float(2.0))
    );
    assert!(widget.has_property(&tf::Token::new("extra")));
}

#[test]
fn auto_apply_reverse_dict_order() {
    let manifest = r#"#usda 1.0

def "AlphaAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["Widget"]
}

def "BetaAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["Widget"]
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
    let schematics = r#"#usda 1.0

class "AlphaAPI"
{
    float alpha = 1
}

class "BetaAPI"
{
    float beta = 2
}

class Widget "Widget"
{
}
"#;
    let registry = registry(manifest, schematics);

    // Unrelated schemas auto-applying to one target still compose in a
    // fixed order, whatever order they registered in.
    let widget = registry
        .concrete_prim_definition(&tf::Token::new("Widget"))
        .expect("Widget");
    assert_eq!(
        widget.applied_api_schemas(),
        [tf::Token::new("BetaAPI"), tf::Token::new("AlphaAPI")]
    );
}

#[test]
fn auto_apply_multi_target_skipped() {
    let manifest = r#"#usda 1.0

def "MarkerAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["MultiAPI"]
}

def "MultiAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
}
"#;
    let schematics = r#"#usda 1.0

class "MarkerAPI"
{
    float marker:size = 2
}

class "MultiAPI"
{
    float multi:__INSTANCE_NAME__:value = 1
}
"#;
    let registry = registry(manifest, schematics);

    // A multiple-apply schema takes only templates, and an auto-applied
    // name never is one, so the declaration reaches nothing.
    let multi = registry
        .api_prim_definition(&tf::Token::new("MultiAPI"))
        .expect("MultiAPI");
    assert_eq!(
        multi.applied_api_schemas(),
        [tf::Token::new("MultiAPI:__INSTANCE_NAME__")]
    );
    assert!(!multi.has_property(&tf::Token::new("marker:size")));
}

#[test]
fn auto_apply_unregistered_target() {
    let manifest = r#"#usda 1.0

def "MarkerAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["FromAnotherFamily"]
}
"#;
    // An unregistered target does not fail the build.
    let registry = registry(
        manifest,
        "#usda 1.0\n\nclass \"MarkerAPI\"\n{\n    float marker:size = 2\n}\n",
    );

    let marker = registry
        .api_prim_definition(&tf::Token::new("MarkerAPI"))
        .expect("MarkerAPI");
    assert!(marker.has_property(&tf::Token::new("marker:size")));
}

#[test]
fn auto_apply_non_single_ignored() {
    let manifest = r#"#usda 1.0

def "MultiAPI"
{
    uniform token schemaKind = "multipleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["Widget"]
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
    let schematics = r#"#usda 1.0

class "MultiAPI"
{
    float multi:__INSTANCE_NAME__:value = 1
}

class Widget "Widget"
{
}
"#;
    let registry = registry(manifest, schematics);

    // Applying a multiple-apply schema takes an instance name, which a
    // declaration has no way to supply.
    let widget = registry
        .concrete_prim_definition(&tf::Token::new("Widget"))
        .expect("Widget");
    assert!(widget.applied_api_schemas().is_empty());
    assert!(widget.property_names().is_empty());
}

#[test]
fn auto_apply_cycle_terminates() {
    let manifest = r#"#usda 1.0

def "FirstAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["SecondAPI"]
}

def "SecondAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}
"#;
    let schematics = r#"#usda 1.0

class "FirstAPI" (
    apiSchemas = ["SecondAPI"]
)
{
    float first = 1
}

class "SecondAPI"
{
    float second = 2
}
"#;
    let registry = registry(manifest, schematics);

    // One schema declares the other while the other is auto-applied back
    // to it, so the expansion has to stop where it repeats.
    let first = registry
        .api_prim_definition(&tf::Token::new("FirstAPI"))
        .expect("FirstAPI");
    assert!(first.has_property(&tf::Token::new("first")));
    assert!(first.has_property(&tf::Token::new("second")));

    let second = registry
        .api_prim_definition(&tf::Token::new("SecondAPI"))
        .expect("SecondAPI");
    assert!(second.has_property(&tf::Token::new("second")));
    assert!(second.has_property(&tf::Token::new("first")));
}

#[test]
fn auto_apply_cross_family() {
    let core_manifest = "#usda 1.0\n\ndef \"Widget\"\n{\n    uniform token schemaKind = \"concreteTyped\"\n}\n";
    let ext_manifest = r#"#usda 1.0

def "MarkerAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["Widget"]
}
"#;
    let registry = SchemaRegistryBuilder::empty()
        .family(FamilySource {
            name: "core",
            manifest: &layer(core_manifest),
            schematics: &layer("#usda 1.0\n\nclass Widget \"Widget\"\n{\n}\n"),
        })
        .family(FamilySource {
            name: "ext",
            manifest: &layer(ext_manifest),
            schematics: &layer("#usda 1.0\n\nclass \"MarkerAPI\"\n{\n    float marker:size = 2\n}\n"),
        })
        .build()
        .expect("registry builds");

    // The target belongs to a family that knows nothing about the schema
    // reaching into it.
    let widget = registry
        .concrete_prim_definition(&tf::Token::new("Widget"))
        .expect("Widget");
    assert_eq!(widget.applied_api_schemas(), [tf::Token::new("MarkerAPI")]);
    assert!(widget.has_property(&tf::Token::new("marker:size")));
}

#[test]
fn auto_apply_builder_entries() {
    let manifest = r#"#usda 1.0

def "MarkerAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] apiSchemaAutoApplyTo = ["Widget"]
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
}

def "Gadget"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
    let schematics = r#"#usda 1.0

class "MarkerAPI"
{
    float marker:size = 2
}

class Widget "Widget"
{
}

class Gadget "Gadget"
{
}
"#;
    let registry = SchemaRegistryBuilder::empty()
        .auto_apply("MarkerAPI", ["Gadget"])
        .family(FamilySource {
            name: "test",
            manifest: &layer(manifest),
            schematics: &layer(schematics),
        })
        .build()
        .expect("registry builds");

    // A registered declaration adds to what the manifest declares rather
    // than replacing it, and neither side has to be registered when it is
    // made.
    for target in ["Widget", "Gadget"] {
        let definition = registry
            .concrete_prim_definition(&tf::Token::new(target))
            .expect("a target is defined");
        assert_eq!(
            definition.applied_api_schemas(),
            [tf::Token::new("MarkerAPI")],
            "{target}"
        );
    }

    // The merged declaration reads back beside the manifest's own.
    let info = registry.schema_info(&tf::Token::new("MarkerAPI")).expect("MarkerAPI");
    assert_eq!(
        info.auto_apply_to(),
        [tf::Token::new("Widget"), tf::Token::new("Gadget")]
    );
}

#[test]
fn non_canonical_identifier_rejected() {
    let manifest = r#"#usda 1.0

def "Foo_1"
{
    uniform token schemaKind = "abstractBase"
}

def "Foo_01"
{
    uniform token schemaKind = "abstractBase"
}
"#;
    // `Foo_01` parses to the same family and version as `Foo_1`, so letting
    // it register would silently shadow one of the two.
    let error = SchemaRegistryBuilder::empty()
        .family(FamilySource {
            name: "test",
            manifest: &layer(manifest),
            schematics: &layer("#usda 1.0\n"),
        })
        .build()
        .expect_err("a non-canonical identifier is rejected");
    assert!(format!("{error:#}").contains("not a valid identifier"), "{error:#}");
}

#[test]
fn composed_refuses_version_conflict() {
    let manifest = r#"#usda 1.0

def "ThingAPI"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "ThingAPI_2"
{
    uniform token schemaKind = "singleApplyAPI"
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
}
"#;
    let schematics = r#"#usda 1.0

class "ThingAPI"
{
    float version = 1
}

class "ThingAPI_2"
{
    float version = 2
    float extra = 0
}

class Widget "Widget" (
    apiSchemas = ["ThingAPI"]
)
{
}
"#;
    let registry = registry(manifest, schematics);

    let definition =
        registry.build_composed_prim_definition(&tf::Token::new("Widget"), &[tf::Token::new("ThingAPI_2")]);

    // Widget already builds in version 1 of the family, so authoring
    // version 2 contributes nothing at all — not even its own properties.
    assert_eq!(definition.applied_api_schemas(), [tf::Token::new("ThingAPI")]);
    assert_eq!(
        definition.attribute_fallback(&tf::Token::new("version")),
        Some(sdf::Value::Float(1.0))
    );
    assert!(!definition.has_property(&tf::Token::new("extra")));
}

#[test]
fn unknown_kind_rejected() {
    let manifest = "#usda 1.0\n\ndef \"Thing\"\n{\n    uniform token schemaKind = \"bogus\"\n}\n";
    let error = SchemaRegistryBuilder::empty()
        .family(FamilySource {
            name: "test",
            manifest: &layer(manifest),
            schematics: &layer("#usda 1.0\n"),
        })
        .build()
        .expect_err("unknown kind is rejected");
    assert!(format!("{error:#}").contains("Unknown schemaKind"), "{error:#}");
}

#[test]
fn missing_kind_rejected() {
    let manifest = "#usda 1.0\n\ndef \"Thing\"\n{\n}\n";
    let error = SchemaRegistryBuilder::empty()
        .family(FamilySource {
            name: "test",
            manifest: &layer(manifest),
            schematics: &layer("#usda 1.0\n"),
        })
        .build()
        .expect_err("missing kind is rejected");
    assert!(format!("{error:#}").contains("schemaKind is required"), "{error:#}");
}

#[test]
fn duplicate_identifier_rejected() {
    let manifest = "#usda 1.0\n\ndef \"Thing\"\n{\n    uniform token schemaKind = \"abstractBase\"\n}\n";
    let source = FamilySource {
        name: "test",
        manifest: &layer(manifest),
        schematics: &layer("#usda 1.0\n"),
    };
    let error = SchemaRegistryBuilder::empty()
        .family(source)
        .family(FamilySource {
            name: "other",
            ..source
        })
        .build()
        .expect_err("duplicate identifier is rejected");
    assert!(
        format!("{error:#}").contains("Duplicate schema identifier"),
        "{error:#}"
    );
}

/// The declared twin of `LAYERS`, schema for schema and field for field.
static DECLARED: &SchemaFamily<'_> = &SchemaFamily::new(
    "gadget",
    &[
        SchemaDecl::new("Gadget", SchemaKind::ConcreteTyped)
            .bases(&["Typed"])
            .properties(&[
                PropertyDecl::attribute("size", "double").fields(&[Field::new("default", || sdf::Value::Double(2.0))]),
                PropertyDecl::attribute("purpose", "token").uniform().fields(&[
                    Field::token("default", "render"),
                    Field::strings("allowedTokens", &["render", "proxy"]),
                    Field::string("displayGroup", "Shape"),
                ]),
                PropertyDecl::relationship("proxyPrim").uniform(),
                PropertyDecl::relationship("targets"),
            ]),
        SchemaDecl::new("SlotAPI", SchemaKind::MultipleApplyApi)
            .bases(&["APISchemaBase"])
            .property_namespace_prefix("slot")
            .can_only_apply_to(&["Gadget"])
            .instance_restrictions(&[("left", &["Gadget"]), ("right", &[])])
            .allowed_instance_names(&["left", "right"])
            .properties(&[PropertyDecl::attribute("slot:__INSTANCE_NAME__:depth", "int")
                .fields(&[Field::new("default", || sdf::Value::Int(3))])]),
    ],
);

/// The same family as the pair of layers a `generatedSchema.usda` build hands
/// over, which is what the declaration has to agree with.
const LAYERS: (&str, &str) = (
    r#"#usda 1.0

def "Gadget"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["Typed"]
}

def "SlotAPI" (
    customData = {
        dictionary apiSchemaInstances = {
            dictionary left = {
                token[] apiSchemaCanOnlyApplyTo = ["Gadget"]
            }
            dictionary right = {
                token[] apiSchemaCanOnlyApplyTo = []
            }
        }
    }
)
{
    uniform token schemaKind = "multipleApplyAPI"
    uniform token[] bases = ["APISchemaBase"]
    uniform token propertyNamespacePrefix = "slot"
    uniform token[] apiSchemaCanOnlyApplyTo = ["Gadget"]
    uniform token[] allowedInstanceNames = ["left", "right"]
}
"#,
    r#"#usda 1.0

class Gadget "Gadget"
{
    double size = 2
    uniform token purpose = "render" (
        allowedTokens = ["render", "proxy"]
        displayGroup = "Shape"
    )
    rel proxyPrim
    varying rel targets
}

class "SlotAPI"
{
    int slot:__INSTANCE_NAME__:depth = 3
}
"#,
);

/// Everything a registry answers about one schema, for comparing two ways of
/// declaring the same family.
fn described(registry: &SchemaRegistry, identifier: &str) -> String {
    let identifier = tf::Token::from(identifier);
    let info = registry.schema_info(&identifier).expect("the schema is registered");
    let definition = registry
        .concrete_prim_definition(&identifier)
        .or_else(|| registry.api_prim_definition(&identifier))
        .expect("the schema has a definition");

    let mut described = format!(
        "{:?} {:?} bases={:?} prefix={:?} canOnlyApplyTo={:?} instances={:?} allowed={:?}\n",
        info.identifier(),
        info.kind(),
        info.bases(),
        info.property_namespace_prefix(),
        info.can_only_apply_to(None),
        ["left", "right"].map(|name| info.can_only_apply_to(Some(&tf::Token::new(name))).to_vec()),
        info.allowed_instance_names(),
    );
    for name in definition.property_names() {
        let property = definition.property(name).expect("the property is defined");
        described += &format!(
            "  {name} {:?} {:?} {:?} custom={:?} default={:?} allowed={:?} group={:?}\n",
            property.spec_type(),
            property.type_name(),
            property.variability(),
            property.field(sdf::FieldKey::Custom),
            property.fallback(),
            property.field(sdf::FieldKey::AllowedTokens),
            property.field(sdf::FieldKey::DisplayGroup),
        );
    }
    described
}

/// A declared family reaches the registry as the pair of layers would: same
/// kinds, bases, restrictions and property fallbacks, down to a relationship's
/// variability and a per-instance restriction.
#[test]
fn declared_family_matches_layers() {
    let from_layers = SchemaRegistry::builder()
        .family(FamilySource {
            name: "gadget",
            manifest: &layer(LAYERS.0),
            schematics: &layer(LAYERS.1),
        })
        .build()
        .expect("the layers register");
    let from_decls = SchemaRegistry::builder()
        .register(DECLARED)
        .build()
        .expect("the declaration registers");

    for identifier in ["Gadget", "SlotAPI"] {
        assert_eq!(
            described(&from_decls, identifier),
            described(&from_layers, identifier),
            "{identifier} differs"
        );
    }
}

/// A declared family is registered like any other, so a stage resolves its
/// fallbacks and `is_a` walks its bases into the core family.
#[test]
fn declared_family_answers_is_a() {
    let registry = SchemaRegistry::builder()
        .register(DECLARED)
        .build()
        .expect("the declaration registers");

    assert!(registry.is_a(&tf::Token::new("Gadget"), &tf::Token::new("Typed")));
    assert_eq!(
        registry
            .concrete_prim_definition(&tf::Token::new("Gadget"))
            .expect("Gadget")
            .property(&tf::Token::new("size"))
            .expect("size")
            .fallback(),
        Some(sdf::Value::Double(2.0))
    );
}

/// Registering a family twice is refused rather than replacing or merging what
/// the first registration brought.
#[test]
fn duplicate_family_rejected() {
    let error = SchemaRegistry::builder()
        .register(DECLARED)
        .register(DECLARED)
        .build()
        .expect_err("a family cannot be registered twice");

    assert!(
        matches!(&error, SchemaRegistryError::DuplicateFamily { family } if family.as_str() == "gadget"),
        "{error:?}"
    );
}

/// A field the registry derives from the declaration itself is refused, so
/// which of the two won cannot come down to the order they are written in.
#[test]
fn reserved_field_rejected() {
    static RESERVED: &SchemaFamily<'_> = &SchemaFamily::new(
        "reserved",
        &[SchemaDecl::new("Thing", SchemaKind::ConcreteTyped)
            .bases(&["Typed"])
            .properties(&[PropertyDecl::attribute("size", "double").fields(&[Field::token("typeName", "float")])])],
    );

    let error = SchemaRegistry::builder()
        .register(RESERVED)
        .build()
        .expect_err("a derived field cannot be declared");

    assert!(
        matches!(&error, SchemaRegistryError::ReservedField { field, .. } if &**field == "typeName"),
        "{error:?}"
    );
}

/// Registration reports nothing itself, so a failure survives every later call
/// and is the one `build` hands back.
#[test]
fn first_failure_kept() {
    static OTHER: &SchemaFamily<'_> = &SchemaFamily::new(
        "other",
        &[SchemaDecl::new("Other", SchemaKind::ConcreteTyped).bases(&["Typed"])],
    );

    let error = SchemaRegistry::builder()
        .register(DECLARED)
        .register(DECLARED)
        .register(OTHER)
        .build()
        .expect_err("the first failure is kept");

    assert!(
        matches!(error, SchemaRegistryError::DuplicateFamily { .. }),
        "{error:?}"
    );
}

/// A slice registers every family in it, which is what a crate's own list of
/// what it declares amounts to.
#[test]
fn slice_registers_every_family() {
    static FIRST: &SchemaFamily<'_> = &SchemaFamily::new(
        "first",
        &[SchemaDecl::new("First", SchemaKind::ConcreteTyped).bases(&["Typed"])],
    );
    static SECOND: &SchemaFamily<'_> = &SchemaFamily::new(
        "second",
        &[SchemaDecl::new("Second", SchemaKind::ConcreteTyped).bases(&["Typed"])],
    );
    static ALL: &[&SchemaFamily<'_>] = &[FIRST, SECOND];

    let registry = ALL
        .iter()
        .fold(SchemaRegistry::builder(), |builder, family| builder.register(family))
        .build()
        .expect("both register");
    assert!(registry.schema_info(&tf::Token::new("First")).is_some());
    assert!(registry.schema_info(&tf::Token::new("Second")).is_some());
}
