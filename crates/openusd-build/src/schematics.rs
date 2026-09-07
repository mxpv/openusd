//! Writing a library's schema data as a flattened layer.
//!
//! This is the contractual half of what the generator emits: a registry built
//! from it has to answer what a registry built from C++'s `generatedSchema.usda`
//! answers, because a stage composed against these class prims must behave like
//! one composed against upstream's.
//!
//! Everything comes from the model. Composition was consulted once, when the
//! model was built, so nothing here re-reads a layer or re-resolves a value —
//! which is what keeps this writer and the Rust emitter from ever disagreeing
//! about a field.

use std::collections::BTreeMap;

use openusd::{sdf, tf, usd};

use crate::GENERATED_BY;
use crate::error::Error;
use crate::model::{Class, Library, Property};

/// What a class prim's own writer authors, so copying the composed spelling
/// back over it would undo a decision the model already made: the prim type a
/// concrete schema stands for, and the applied list under its templated names.
const CLASS_DECLARATION: &[sdf::FieldKey] = &[sdf::FieldKey::TypeName, sdf::FieldKey::ApiSchemas];

/// What a property spec's constructor authors, and normalizes as it does — the
/// canonical type token, `variability` only where it is uniform, `custom` only
/// where it is set. Copying the composed spelling back would undo that.
const PROPERTY_DECLARATION: &[sdf::FieldKey] = &[
    sdf::FieldKey::TypeName,
    sdf::FieldKey::Variability,
    sdf::FieldKey::Custom,
];

/// Every field naming a spec's children, which is the namespace holding the
/// layer together rather than anything a schema declared.
///
/// The writer creates whatever child specs it means to, so it names their
/// fields itself; copying one in would leave a list of children that are not
/// there. `SchemaRegistry::is_disallowed_field` refuses the four naming a
/// prim's own children, and these are the rest.
const CHILD_NAMES: &[sdf::ChildrenKey] = &[
    sdf::ChildrenKey::ConnectionChildren,
    sdf::ChildrenKey::ExpressionChildren,
    sdf::ChildrenKey::MapperArgChildren,
    sdf::ChildrenKey::MapperChildren,
    sdf::ChildrenKey::RelationshipTargetChildren,
];

/// The library's schemas as one flattened layer.
pub fn write(library: &Library) -> Result<sdf::Layer, Error> {
    let mut layer = sdf::Layer::new_anonymous(format!("{} schematics", library.name));

    layer.edit(|edit| {
        let data = edit.data_mut();
        let root = sdf::Path::abs_root();
        data.set_field(
            &root,
            sdf::FieldKey::Comment.as_str(),
            sdf::Value::String(GENERATED_BY.to_owned()),
        );

        let fallbacks = fallback_prim_types(library);
        if !fallbacks.is_empty() {
            data.set_field(
                &root,
                sdf::FieldKey::FallbackPrimTypes.as_str(),
                sdf::Value::Dictionary(fallbacks),
            );
        }

        for class in &library.classes {
            write_class(data, class)?;
        }
        Ok(())
    })?;

    Ok(layer)
}

/// One schema as the class prim a registry reads it from.
fn write_class(data: &mut dyn sdf::AbstractData, class: &Class) -> Result<(), sdf::AuthoringError> {
    let path = class.prim_path()?;

    // A concrete schema is a prim type, and its class prim carries that type
    // name; every other kind names nothing a prim can be.
    let type_name = match class.kind {
        usd::SchemaKind::ConcreteTyped => class.identifier.as_str(),
        _ => "",
    };
    sdf::PrimSpec::new(data, &path, sdf::Specifier::Class, type_name)?;

    // The rest of what composition left on the class prim: `hidden`,
    // `assetInfo`, `propertyOrder` and anything else the schema declared. A
    // registry serves these as the prim metadata fallbacks of every prim the
    // schema defines, so a writer that dropped them would drop a fallback the
    // schema authored.
    copy_fields(data, &path, &class.fields, CLASS_DECLARATION);

    if !class.applied_api_schemas.is_empty() {
        data.set_field(
            &path,
            sdf::FieldKey::ApiSchemas.as_str(),
            sdf::TokenListOp::explicit(class.applied_api_schemas.clone()).into(),
        );
    }

    let mut overrides: Vec<tf::Token> = class.override_properties().map(|p| p.schematics_name.clone()).collect();
    if !overrides.is_empty() {
        // Sorted, since the set is what matters and a stable order keeps two
        // runs comparable.
        overrides.sort();
        data.set_field(
            &path,
            sdf::FieldKey::CustomData.as_str(),
            sdf::Dictionary::from([(
                "apiSchemaOverridePropertyNames".to_owned(),
                sdf::Value::TokenVec(overrides),
            )])
            .into(),
        );
    }

    for property in &class.properties {
        write_property(data, &path, property)?;
    }
    Ok(())
}

/// One property, under the name the schematics records it by.
fn write_property(
    data: &mut dyn sdf::AbstractData,
    prim: &sdf::Path,
    property: &Property,
) -> Result<(), sdf::AuthoringError> {
    let path = prim.append_property(property.schematics_name.as_str())?;

    if property.spec_type == sdf::SpecType::Relationship {
        sdf::RelationshipSpec::new(data, &path, property.variability(), property.is_custom())?;
    } else {
        // Validation rejected any attribute whose `typeName` names no
        // registered type, so the fallback only keeps this total.
        let type_name = property.type_name().unwrap_or(sdf::ValueTypeName::TOKEN);
        sdf::AttributeSpec::new(data, &path, type_name, property.variability(), property.is_custom())?;
    }

    copy_fields(data, &path, &property.fields, PROPERTY_DECLARATION);
    Ok(())
}

/// Copies a model field map onto a spec, less what a schematics never carries
/// and less the `declared` fields the caller has already authored itself.
///
/// This is the one place the model's field maps are narrowed. They travel whole
/// so validation can see a field it means to reject and the emitter can read
/// the documentation; what a registry would refuse to carry is dropped here,
/// where the output is written, and everything else is copied verbatim — so a
/// field nobody thought to name still survives.
fn copy_fields(
    data: &mut dyn sdf::AbstractData,
    path: &sdf::Path,
    fields: &BTreeMap<String, sdf::Value>,
    declared: &[sdf::FieldKey],
) {
    for (key, value) in fields {
        let carried = key != sdf::FieldKey::Documentation.as_str()
            && !declared.iter().any(|field| field.as_str() == key)
            && !CHILD_NAMES.iter().any(|field| field.as_str() == key)
            && !usd::SchemaRegistry::is_disallowed_field(key);
        if carried {
            data.set_field(path, key, value.clone());
        }
    }
}

/// The concrete schemas a stage falls back to, keyed by the schema they stand
/// in for.
fn fallback_prim_types(library: &Library) -> sdf::Dictionary {
    library
        .classes
        .iter()
        .filter(|class| !class.metadata.fallback_types.is_empty())
        .map(|class| {
            (
                class.identifier.to_string(),
                sdf::Value::TokenVec(class.metadata.fallback_types.clone()),
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;
    use std::collections::BTreeMap;
    use std::path::Path;

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

    /// Upstream's own generated schematics for the same corpus.
    fn baseline() -> sdf::Layer {
        let path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/testUsdGenSchema/baseline/basic/generatedSchema.usda");
        sdf::Layer::open(path.to_string_lossy()).expect("the vendored baseline")
    }

    /// Every spec a layer holds and every field on it, valued.
    ///
    /// Four things are left out, each a place upstream's file and this crate's
    /// differ by design: the `documentation` neither registry reads; the layer
    /// comment, which names whichever generator wrote the file; and the two
    /// children keys, because the two files order properties differently —
    /// upstream keeps the order the schema declared them in, while this crate
    /// takes the composed order, which is `sdf::element_cmp`. Nothing resolves
    /// a value through that order, so it is a divergence rather than a defect.
    fn specs(layer: &sdf::Layer) -> BTreeMap<sdf::Path, BTreeMap<String, sdf::Value>> {
        const APART: [&str; 4] = [
            sdf::FieldKey::Documentation.as_str(),
            sdf::FieldKey::Comment.as_str(),
            sdf::ChildrenKey::PrimChildren.as_str(),
            sdf::ChildrenKey::PropertyChildren.as_str(),
        ];

        let data = layer.data();
        data.spec_paths()
            .into_iter()
            .map(|path| {
                let fields = data
                    .list_fields(&path)
                    .unwrap_or_default()
                    .into_iter()
                    .filter(|field| !APART.contains(&field.as_str()))
                    .filter_map(|field| {
                        let value = data.try_field(&path, &field).ok().flatten().map(Cow::into_owned)?;
                        let value = match field == sdf::FieldKey::CustomData.as_str() {
                            true => emitted_custom_data(value)?,
                            false => value,
                        };
                        Some((field, value))
                    })
                    .collect();
                (path, fields)
            })
            .collect()
    }

    /// A spec's `customData` less the brief user documentation upstream carries
    /// and this crate drops, `None` once nothing else is left in it — an
    /// emptied dictionary meaning the same as an absent one.
    fn emitted_custom_data(value: sdf::Value) -> Option<sdf::Value> {
        let mut custom_data = value.try_as_dictionary()?;
        custom_data.remove("userDocBrief");
        (!custom_data.is_empty()).then_some(sdf::Value::Dictionary(custom_data))
    }

    /// The same schemas, carrying the same properties with the same values, as
    /// upstream generates.
    ///
    /// Compared for what it means rather than byte for byte: the formatting is
    /// ours, and the fields the two files differ over by design are the ones
    /// [`specs`] leaves out.
    #[test]
    fn matches_upstream_specs() {
        let library = read_fixture("schema.usda").expect("resolves");
        let theirs = specs(&baseline());
        let ours = specs(&write(&library).expect("writes"));

        let missing: Vec<&sdf::Path> = theirs.keys().filter(|path| !ours.contains_key(*path)).collect();
        let extra: Vec<&sdf::Path> = ours.keys().filter(|path| !theirs.contains_key(*path)).collect();
        assert!(
            theirs.len() > 100,
            "the baseline should carry the whole corpus: {}",
            theirs.len()
        );
        assert!(missing.is_empty(), "upstream has specs we do not: {missing:?}");
        assert!(extra.is_empty(), "we have specs upstream does not: {extra:?}");

        for (path, fields) in &theirs {
            assert_eq!(&ours[path], fields, "{path} is not what upstream generates");
        }
    }

    /// A concrete schema names the prim type it stands for; nothing else does.
    #[test]
    fn concrete_carries_type_name() {
        let library = read_fixture("schema.usda").expect("resolves");
        let layer = write(&library).expect("writes");

        let type_name = |path: &str| {
            layer
                .prim(path)
                .expect("a path")
                .expect("the class prim")
                .type_name()
                .map(|token| token.to_string())
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
        let layer = write(&library).expect("writes");

        let applied = layer
            .prim("/PublicMultipleApplyAPI")
            .expect("a path")
            .expect("the class prim")
            .api_schemas()
            .expect("built-ins");
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
        let layer = write(&library).expect("writes");

        let fallbacks = layer
            .pseudo_root()
            .expect("the pseudo-root")
            .get::<sdf::Value>(sdf::FieldKey::FallbackPrimTypes)
            .and_then(sdf::Value::try_as_dictionary)
            .expect("a fallback dict");
        assert_eq!(
            fallbacks.get("Derived").and_then(sdf::Value::try_as_token_vec_ref),
            Some(&vec![tf::Token::from("OldDerived"), tf::Token::from("OlderDerived")])
        );
    }

    /// Prim metadata is a fallback a registry serves from the schema's
    /// definition, so it reaches the schematics rather than stopping at the
    /// model — on the schema that declared it and on the one that inherits it,
    /// composition having put it on both.
    #[test]
    fn prim_metadata_survives() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(dir.path(), METADATA).expect("resolves");
        let layer = write(&library).expect("writes");

        let field = |identifier: &str, key: sdf::FieldKey| {
            layer
                .prim(format!("/{identifier}"))
                .expect("a path")
                .expect("the class prim")
                .get::<sdf::Value>(key)
        };
        for identifier in ["Marked", "Refined"] {
            let class = library
                .classes
                .iter()
                .find(|class| class.identifier.as_str() == identifier)
                .expect("the class");
            for key in [sdf::FieldKey::Hidden, sdf::FieldKey::AssetInfo] {
                let carried = field(identifier, key);
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
            field("Marked", sdf::FieldKey::CustomData),
            None,
            "the generator's own input is not schema data"
        );
        assert_eq!(
            field("Marked", sdf::FieldKey::InheritPaths),
            None,
            "a schematics is already flat"
        );
    }

    /// A relationship carries whatever variability the schema declared. The
    /// field is authored only where it is uniform, the reverse of how an
    /// attribute reads, so an unauthored one has to arrive as `varying rel`
    /// rather than as the default an attribute would take.
    #[test]
    fn relationship_variability_kept() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testRelVariability"
    }
)
{
}

class "Typed" {}

class "Held" (
    inherits = </Typed>
) {
    rel plain
    varying rel loose
}
"#,
        )
        .expect("resolves");

        let text = write(&library).expect("writes").export_to_string().expect("exports");
        assert!(
            text.contains(
                "
    rel plain
"
            ),
            "{text}"
        );
        assert!(
            text.contains(
                "
    varying rel loose
"
            ),
            "{text}"
        );
    }
}
