//! Turning what the layers declare into the one model every output reads.
//!
//! Two views meet here, and they answer different questions.
//!
//! [`Stage::flatten`](openusd::usd::Stage::flatten) answers what a schema
//! *effectively holds*: every property it carries, its own and its ancestors',
//! with each field composed. That is what the schematics writes and what an
//! accessor reads, and asking composition for it once is what keeps the Rust
//! emitter and the schematics writer from ever disagreeing.
//!
//! The declarations answer what a schema *says for itself*: which properties
//! it declares, what its `customData` asks the generator for, and where each
//! was written. Flattening cannot answer those — it deliberately forgets which
//! layer an opinion came from — so provenance, accessor naming and the
//! inheritance graph are all read from the declarations instead.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::iter;

use openusd::{sdf, tf, usd};

use crate::error::Error;
use crate::load::{self, CustomData, Declaration, PropertyDeclaration, Source};
use crate::model::{
    API_SCHEMA_OVERRIDE, Base, Class, ForeignClass, Library, Metadata, NON_APPLIED, Property, PropertyApi, SCHEMA_BASE,
    Shape, Site, TYPED, is_root,
};
use crate::names;
use crate::validate::Violation;

/// The `customData` key naming an API schema's kind.
const API_SCHEMA_TYPE: &str = "apiSchemaType";

/// Resolves every class the root layer declares into a [`Library`].
pub fn library(source: &Source) -> Result<Library, Error> {
    // One flattening answers what every class effectively holds; the
    // declarations answer the rest.
    //
    // TODO(perf): flatten only the prims this library generates. Measured over
    // the eleven upstream libraries, this is 80 ms of a 165 ms release run
    // (49%), and most of it composes base-library prims that arrive through
    // `subLayers` and are never read: `usdMedia` flattens 40 declarations to
    // read 2. A paths-scoped flatten — `usd::flatten`'s `write_prim` over the
    // generated declarations alone — would take it to roughly 21 ms.
    let flattened = source.stage.flatten()?;

    // Declarations arrive strongest first, so the first of a name is the one
    // composition resolves to; a sublayer redeclaring a class must not
    // overwrite the root's.
    let mut index: HashMap<&tf::Token, &Declaration> = HashMap::new();
    for declaration in &source.declarations {
        index.entry(&declaration.name).or_insert(declaration);
    }

    let mut classes = Vec::new();
    for declaration in source.declarations.iter().filter(|d| d.generated) {
        classes.push(class(&flattened, &index, declaration)?);
    }

    // What the classes reflect is resolved from the same stage, so a schema
    // this run does not generate can lend its accessors here. One it generates
    // is already among the classes; whether a view exists to reflect from is
    // lowering's question.
    let mut reflected: Vec<Class> = Vec::new();
    for owner in &classes {
        for schema in &owner.metadata.reflected_api_schemas {
            if classes
                .iter()
                .chain(&reflected)
                .any(|class| &class.identifier == schema)
            {
                continue;
            }
            let Some(declaration) = index.get(schema) else {
                return Err(owner.violation(Violation::UnknownReflectedSchema { schema: schema.clone() }));
            };
            reflected.push(class(&flattened, &index, declaration)?);
        }
    }

    // What a class inherits from another library reaches its view through a
    // supertrait, as does whatever that ancestor reflects, so a descendant's
    // method names are checked against both. A schema reflected only there is
    // resolved too; one naming nothing is the declaring library's to report.
    let mut inherited: Vec<Class> = Vec::new();
    let held = |name: &tf::Token, reflected: &[Class], inherited: &[Class]| {
        classes
            .iter()
            .chain(reflected)
            .chain(inherited)
            .any(|class| &class.identifier == name)
    };
    for owner in &classes {
        let foreign = owner
            .bases
            .iter()
            .filter(|base| base.library != source.library && !is_root(&base.identifier));
        for base in foreign {
            if !held(&base.identifier, &reflected, &inherited) {
                inherited.push(class(&flattened, &index, index[&base.identifier])?);
            }
        }
    }
    let mut next = 0;
    while let Some(ancestor) = inherited.get(next) {
        let schemas = ancestor.metadata.reflected_api_schemas.clone();
        for schema in &schemas {
            if let Some(declaration) = index.get(schema)
                && !held(schema, &reflected, &inherited)
            {
                inherited.push(class(&flattened, &index, declaration)?);
            }
        }
        next += 1;
    }

    // Every class another library declares, by name, for documentation to link
    // where prose names one. A class of this library that only a sublayer
    // declares is not among them, having no view anywhere to link to.
    let foreign = source
        .declarations
        .iter()
        .filter(|declaration| declaration.library != source.library)
        .map(|declaration| ForeignClass {
            library: declaration.library.clone(),
            class_name: class_name(declaration),
            upstream_name: upstream_name(declaration),
        })
        .collect();

    Ok(Library {
        name: source.library.clone(),
        use_literal_identifiers: source.use_literal_identifiers,
        skip_code_generation: source.skip_code_generation,
        classes,
        reflected,
        inherited,
        foreign,
        // Asked after the flatten above, which composed every prim and so
        // loaded every layer an arc reaches.
        source_layers: load::watched_layers(&source.stage),
        declared_tokens: source.tokens.clone(),
        metadata: Vec::new(),
    })
}

/// Resolves one class.
fn class(
    flattened: &sdf::Layer,
    index: &HashMap<&tf::Token, &Declaration>,
    declaration: &Declaration,
) -> Result<Class, Error> {
    let bases = chain(index, declaration)?;
    let direct_base = direct_base(&bases, &declaration.name);
    let is_typed = bases.iter().any(|base| base.identifier.as_str() == TYPED);

    // Upstream clears a type name a parent already declares; here one has to be
    // the class's own identifier (`Violation::TypeNameMismatch`), and two
    // classes cannot share that, so there is nothing to clear.
    let (family, version) = usd::SchemaRegistry::parse_schema_family_and_version(&declaration.name);
    let kind = kind(declaration, is_typed)?;
    let metadata = metadata(declaration);
    let properties = properties(flattened, index, declaration, &bases, &metadata, kind)?;

    Ok(Class {
        identifier: declaration.name.clone(),
        family,
        version,
        library: declaration.library.clone(),
        upstream_name: upstream_name(declaration),
        kind,
        is_typed,
        authored_base_count: declaration.bases.len(),
        bases,
        properties,
        applied_api_schemas: applied_api_schemas(flattened, declaration, kind),
        documentation: declaration.documentation.clone(),
        direct_base,
        authored_fields: declaration.fields.clone(),
        fields: composed_fields(flattened, &declaration.origin.path)?,
        authored_type_name: declaration.type_name.clone(),
        api_schemas_op: declaration.api_schemas.clone(),
        metadata,
        origin: declaration.origin.clone(),
    })
}

/// The inheritance chain, nearest first.
///
/// The chain is checked for a cycle as it is walked, so a schema inheriting
/// from itself is a diagnostic rather than a hang.
fn chain(index: &HashMap<&tf::Token, &Declaration>, declaration: &Declaration) -> Result<Vec<Base>, Error> {
    let mut walked: Vec<&Declaration> = Vec::new();
    let mut seen = HashSet::new();
    seen.insert(declaration.name.clone());

    let mut current = declaration;
    while let Some(name) = current.bases.first() {
        let Some(parent) = index.get(name) else {
            return Err(Error::Definition {
                origin: current.origin.describe(),
                violation: Violation::MissingBase { name: name.clone() },
            });
        };

        if !seen.insert(parent.name.clone()) {
            let mut chain: Vec<&str> = walked.iter().map(|base| base.name.as_str()).collect();
            chain.push(parent.name.as_str());
            return Err(Error::Definition {
                origin: declaration.origin.describe(),
                violation: Violation::CyclicInheritance {
                    chain: chain.join(" -> "),
                },
            });
        }

        walked.push(parent);
        current = parent;
    }

    // Each base is classified against what stands behind it, which is the rest
    // of this chain. Building it furthest-first is what carries `Typed` forward:
    // a base is typed exactly when something further back is.
    let mut reaches_typed = false;
    let mut bases: Vec<Base> = walked
        .iter()
        .rev()
        .map(|parent| {
            // An `apiSchemaType` nothing can read is a rule broken by the class
            // that wrote it, which validation reports where that class is
            // generated. A descendant merely inheriting from it reads the kind
            // it can see rather than failing on someone else's declaration.
            let kind = kind(parent, reaches_typed).unwrap_or(usd::SchemaKind::AbstractBase);
            reaches_typed |= parent.name.as_str() == TYPED;
            Base {
                identifier: parent.name.clone(),
                library: parent.library.clone(),
                generated: parent.generated,
                reflected_api_schemas: parent.custom_data.tokens("reflectedAPISchemas"),
                class_name: class_name(parent),
                kind,
            }
        })
        .collect();

    bases.reverse();
    Ok(bases)
}

/// The Rust type name a class is generated under: what its `customData` asked
/// for, or its identifier in proper case.
fn class_name(declaration: &Declaration) -> String {
    declaration
        .custom_data
        .string("className")
        .unwrap_or_else(|| names::proper_case(declaration.name.as_str()))
}

/// What upstream calls a class: its library's prefix before its class name.
fn upstream_name(declaration: &Declaration) -> String {
    format!("{}{}", declaration.prefix, class_name(declaration))
}

/// What kind of schema a class is.
///
/// A schema that is neither typed nor concrete, and is not one of the three
/// roots, is an API schema; `apiSchemaType` then says which of the three kinds,
/// and defaults to single-apply.
fn kind(declaration: &Declaration, is_typed: bool) -> Result<usd::SchemaKind, Error> {
    // A schema is concrete when it carries a type name of its own.
    let is_concrete = declaration.type_name.is_some();
    // The roots are abstract bases. `SchemaBase` is among them: it inherits
    // nothing and carries no type, which is what an API schema looks like from
    // here, and a library declaring it would otherwise register the root every
    // schema derives from as an API schema of its own.
    let is_api = !is_typed && !is_concrete && !is_root(&declaration.name);

    let spelling = declaration.custom_data.string(API_SCHEMA_TYPE);
    if let Some(spelling) = spelling.as_deref() {
        // A typed or concrete class saying this contradicts itself, which
        // `Violation::ApiSchemaTypeOnTyped` reports; the kind it asked for is
        // what the other rules are then read against.
        return match spelling {
            "singleApply" => Ok(usd::SchemaKind::SingleApplyApi),
            "multipleApply" => Ok(usd::SchemaKind::MultipleApplyApi),
            NON_APPLIED => Ok(usd::SchemaKind::NonAppliedApi),
            other => Err(Error::Definition {
                origin: declaration.origin.describe(),
                violation: Violation::UnknownApiSchemaType {
                    spelling: other.to_owned(),
                },
            }),
        };
    }

    Ok(if is_api {
        usd::SchemaKind::SingleApplyApi
    } else if is_concrete {
        usd::SchemaKind::ConcreteTyped
    } else if is_typed {
        usd::SchemaKind::AbstractTyped
    } else {
        usd::SchemaKind::AbstractBase
    })
}

/// A class's `customData`, sorted into what the registry reads and what only
/// this crate reads.
fn metadata(declaration: &Declaration) -> Metadata {
    Metadata {
        property_namespace_prefix: declaration
            .custom_data
            .string("propertyNamespacePrefix")
            .map(|prefix| tf::Token::from(prefix.as_str())),
        auto_apply_to: declaration.custom_data.tokens("apiSchemaAutoApplyTo"),
        can_only_apply_to: declaration.custom_data.tokens("apiSchemaCanOnlyApplyTo"),
        allowed_instance_names: declaration.custom_data.tokens("apiSchemaAllowedInstanceNames"),
        instance_restrictions: declaration.custom_data.instance_restrictions(),
        fallback_types: declaration.custom_data.tokens("fallbackTypes"),
        class_name: class_name(declaration),
        reflected_api_schemas: declaration.custom_data.tokens("reflectedAPISchemas"),
        schema_tokens: declaration.custom_data.token_declarations("schemaTokens"),
    }
}

/// The base a manifest names, which is what the registry walks `is_a` up to.
///
/// A class that inherits nothing still derives from the root every schema
/// derives from — except that root, which derives from nothing and would
/// otherwise be given itself to walk up to.
fn direct_base(bases: &[Base], name: &tf::Token) -> Option<tf::Token> {
    bases
        .first()
        .map(|base| base.identifier.clone())
        .or_else(|| (name.as_str() != SCHEMA_BASE).then(|| tf::Token::new(SCHEMA_BASE)))
}

/// The API schemas applied to every instance of a schema, as composition
/// resolved them and under the names the schematics records them by.
///
/// A multiple-apply schema's built-ins are applied under whatever instance name
/// it is applied with, so they are templated here: `MultiApplyAPI` becomes
/// `MultiApplyAPI:__INSTANCE_NAME__`, and an already-instanced
/// `BuiltinAPI:builtin` becomes `BuiltinAPI:__INSTANCE_NAME__:builtin`. This is
/// the same move [`schematics_name`] makes for a property, made once and in the
/// same place.
fn applied_api_schemas(flattened: &sdf::Layer, declaration: &Declaration, kind: usd::SchemaKind) -> Vec<tf::Token> {
    let applied = flattened
        .prim(&declaration.origin.path)
        .ok()
        .flatten()
        .and_then(|prim| prim.api_schemas())
        .map(|list_op| list_op.flatten())
        .unwrap_or_default();

    if kind != usd::SchemaKind::MultipleApplyApi {
        return applied;
    }
    applied
        .iter()
        .map(|name| {
            let (identifier, instance) = usd::SchemaRegistry::type_name_and_instance(name);
            let instance = instance.as_ref().map_or("", tf::Token::as_str);
            usd::SchemaRegistry::make_multiple_apply_name_template(identifier.as_str(), instance)
        })
        .collect()
}

/// Every property the schema carries, its own and its ancestors'.
///
/// The flattened layer is the authority on what they are: it holds the
/// composed set, in composed order, with every field already resolved. What it
/// cannot say — which class introduced a property, where it was written, and
/// what its `customData` asked for — comes from the declarations.
fn properties(
    flattened: &sdf::Layer,
    index: &HashMap<&tf::Token, &Declaration>,
    declaration: &Declaration,
    bases: &[Base],
    metadata: &Metadata,
    kind: usd::SchemaKind,
) -> Result<Vec<Property>, Error> {
    let Some(prim) = flattened.prim(&declaration.origin.path)? else {
        return Ok(Vec::new());
    };

    let mut properties = Vec::new();
    for name in prim.property_children().unwrap_or_default() {
        let path = declaration.origin.path.append_property(name.as_str())?;
        let Some(shape) = shape_at(flattened, &path)? else {
            continue;
        };

        let local = declaration.properties.iter().find(|p| p.name == name);
        let sites = declaring_sites(flattened, index, declaration, bases, &name)?;
        // A property no declaration carries was found on this class, which is
        // what one reaching the model through composition alone looks like.
        let origin = sites
            .last()
            .map_or_else(|| declaration.origin.clone(), |site| site.origin.clone());
        properties.push(Property {
            schematics_name: schematics_name(&name, metadata, kind),
            api: property_api(declaration, local)?,
            is_local: local.is_some(),
            name,
            shape,
            sites,
            fields: composed_fields(flattened, &path)?,
            origin,
        });
    }

    Ok(properties)
}

/// What the property at `path` is in the flattened layer: the three fields a
/// [`Shape`] is made of, read as `sdf` reads them on a property spec, so the
/// variability is varying and `custom` false where neither is authored. `None`
/// where the path holds no property.
fn shape_at(flattened: &sdf::Layer, path: &sdf::Path) -> Result<Option<Shape>, Error> {
    let data = flattened.data();
    let spec_type = match data.spec_type(path) {
        Some(spec_type @ (sdf::SpecType::Attribute | sdf::SpecType::Relationship)) => spec_type,
        _ => return Ok(None),
    };
    let field = |key: sdf::FieldKey| data.try_field(path, key.as_str());
    Ok(Some(Shape {
        spec_type,
        type_name: field(sdf::FieldKey::TypeName)?.and_then(|value| value.try_as_token_ref().cloned()),
        variability: field(sdf::FieldKey::Variability)?
            .and_then(|value| value.into_owned().get())
            .unwrap_or_default(),
        custom: field(sdf::FieldKey::Custom)?
            .and_then(|value| value.into_owned().get())
            .unwrap_or(false),
    }))
}

/// Every field composition left at a path, whether that is a class prim or one
/// of its properties.
///
/// Nothing is filtered. Validation has to see a field it means to reject, the
/// emitter reads the documentation, and the schematics writer is the one place
/// that drops what a schematics does not carry.
fn composed_fields(flattened: &sdf::Layer, path: &sdf::Path) -> Result<BTreeMap<String, sdf::Value>, Error> {
    let data = flattened.data();
    let mut fields = BTreeMap::new();
    for name in data.list_fields(path).unwrap_or_default() {
        if let Some(value) = data.try_field(path, &name)? {
            fields.insert(name, value.into_owned());
        }
    }
    Ok(fields)
}

/// Every class declaring a property, nearest first, each with what the
/// property composes to there.
///
/// This class comes first where it redeclares the property, then each ancestor
/// that declared it, which is the order their opinions run in. A class
/// redeclaring a property refines what is already there, so the furthest site
/// is the one that introduced it. Each site's [`Shape`] is read where the
/// property composes at that class.
fn declaring_sites(
    flattened: &sdf::Layer,
    index: &HashMap<&tf::Token, &Declaration>,
    declaration: &Declaration,
    bases: &[Base],
    name: &tf::Token,
) -> Result<Vec<Site>, Error> {
    let ancestors = bases.iter().filter_map(|base| index.get(&base.identifier).copied());
    let mut sites = Vec::new();
    for class in iter::once(declaration).chain(ancestors) {
        let Some(property) = class.properties.iter().find(|p| &p.name == name) else {
            continue;
        };
        let path = class.origin.path.append_property(name.as_str())?;
        let Some(shape) = shape_at(flattened, &path)? else {
            continue;
        };
        sites.push(Site {
            class: class.name.clone(),
            is_override: property.custom_data.flag(API_SCHEMA_OVERRIDE).unwrap_or(false),
            shape,
            api_name: api_name(&property.custom_data, name),
            origin: property.origin.clone(),
        });
    }
    Ok(sites)
}

/// The accessor name one declaration of a property asks for.
///
/// An override exists to change a built-in's fallback, not to offer an
/// accessor, so it suppresses one exactly as an empty `apiName` does. Saying
/// nothing asks for the property's own name.
fn api_name(custom_data: &CustomData, name: &tf::Token) -> Option<String> {
    if custom_data.flag(API_SCHEMA_OVERRIDE).unwrap_or(false) {
        return None;
    }
    match custom_data.string("apiName").as_deref() {
        Some("") => None,
        Some(explicit) => Some(explicit.to_owned()),
        None => Some(names::camel_case(name.as_str())),
    }
}

/// What a property's `customData` asks the generator for.
fn property_api(declaration: &Declaration, property: Option<&PropertyDeclaration>) -> Result<PropertyApi, Error> {
    let Some(property) = property else {
        // An inherited property keeps the accessor its own class generates, so
        // this class needs none of its own.
        return Ok(PropertyApi::default());
    };

    // `generated` is the default and asks for nothing; `custom` says the
    // library writes the read accessor itself. Any other spelling names a
    // behaviour that does not exist.
    let custom_get = match property.custom_data.string("apiGetImplementation").as_deref() {
        None | Some("generated") => false,
        Some("custom") => true,
        Some(other) => {
            return Err(Error::Definition {
                origin: declaration.origin.describe(),
                violation: Violation::UnknownApiGetImplementation {
                    spelling: other.to_owned(),
                },
            });
        }
    };

    Ok(PropertyApi { custom_get })
}

/// The name a property is recorded under in the schematics.
///
/// A multiple-apply schema's property is a template, since the instance name
/// is not known until the schema is applied. A property literally named
/// `__INSTANCE_NAME__` is the schema's own, with the empty base name.
fn schematics_name(name: &tf::Token, metadata: &Metadata, kind: usd::SchemaKind) -> tf::Token {
    if kind != usd::SchemaKind::MultipleApplyApi {
        return name.clone();
    }
    let Some(prefix) = &metadata.property_namespace_prefix else {
        return name.clone();
    };

    // The bare placeholder is the schema's own property, and takes the prefix
    // with no base name of its own.
    let placeholder = usd::SchemaRegistry::make_multiple_apply_name_template("", "");
    if name == &placeholder {
        return usd::SchemaRegistry::make_multiple_apply_name_template(prefix.as_str(), "");
    }

    // A schema may write a property in template form itself, which is already
    // the name the schematics wants; templating it again would prefix it twice.
    if usd::SchemaRegistry::is_multiple_apply_name_template(name.as_str()) {
        return name.clone();
    }

    usd::SchemaRegistry::make_multiple_apply_name_template(prefix.as_str(), name.as_str())
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use crate::tests::{read_fixture, read_source};

    /// The whole contrived library resolves, with each class classified from
    /// its metadata and its chain.
    #[test]
    fn contrived_library() {
        let library = read_fixture("schema.usda").expect("resolves");
        assert_eq!(library.name, "usdContrived");

        let kind = |identifier: &str| {
            library
                .classes
                .iter()
                .find(|class| class.identifier.as_str() == identifier)
                .unwrap_or_else(|| panic!("{identifier} is generated"))
                .kind
        };
        assert_eq!(kind("Base"), usd::SchemaKind::AbstractTyped);
        assert_eq!(kind("Derived"), usd::SchemaKind::ConcreteTyped);
        assert_eq!(kind("SingleApplyAPI"), usd::SchemaKind::SingleApplyApi);
        assert_eq!(kind("MultipleApplyAPI"), usd::SchemaKind::MultipleApplyApi);
        assert_eq!(kind("NonAppliedAPI"), usd::SchemaKind::NonAppliedApi);
    }

    /// A multiple-apply schema's properties reach the schematics as templates,
    /// under the namespace prefix the schema declares.
    #[test]
    fn multi_apply_templates() {
        let library = read_fixture("schema.usda").expect("resolves");
        let class = library
            .classes
            .iter()
            .find(|class| class.identifier.as_str() == "MultipleApplyAPI")
            .expect("the multiple-apply schema");

        for property in class.local_properties() {
            let name = property.schematics_name.as_str();
            assert!(
                name.starts_with("test:__INSTANCE_NAME__"),
                "{name} is not under the declared prefix"
            );
        }
    }

    /// A property is named by its own name, not by the path it hangs off, and
    /// that is what its `customData` is looked up under.
    ///
    /// `Path::name` answers `Class.property` for a property path, so taking it
    /// from there leaves every accessor unfound and every name wrong — without
    /// failing anything, since the wrong name is used consistently.
    #[test]
    fn property_names_own() {
        let library = read_fixture("schema.usda").expect("resolves");
        let hairman = library
            .classes
            .iter()
            .find(|class| class.identifier.as_str() == "TestPxHairman")
            .expect("the class carrying the api-name cases");

        let names: Vec<&str> = hairman.local_properties().map(|p| p.name.as_str()).collect();
        assert!(
            names.iter().all(|name| !name.contains('.')),
            "a property carries the prim path: {names:?}"
        );

        let accessor = |name: &str| {
            hairman
                .local_properties()
                .find(|property| property.name.as_str() == name)
                .unwrap_or_else(|| panic!("{name} is declared"))
                .api_name()
        };
        assert_eq!(
            accessor("riStatements:attributes:user:Gofur_GeomOnHairdensity"),
            Some("Gofur_GeomOnHairdensity"),
            "the declared apiName is what the accessor is called"
        );
        assert_eq!(
            accessor("attrWithoutGeneratedAccessorAPI"),
            None,
            "an empty apiName asks for no accessor"
        );
        assert_eq!(accessor("temp"), Some("temp"), "the default is the name itself");
    }

    /// A class that redeclares an inherited property still declares it, so the
    /// accessor its own `customData` asks for is not lost.
    ///
    /// The corpus says what it expects: `overrideBaseTrueDerivedFalse` is an
    /// override in `Base`, which suppresses the accessor, and is declared again
    /// in `Derived` with the override off, which asks for one.
    #[test]
    fn redeclared_stays_local() {
        let library = read_fixture("schema.usda").expect("resolves");
        let derived = library
            .classes
            .iter()
            .find(|class| class.identifier.as_str() == "Derived")
            .expect("the derived class");

        let property = derived
            .local_properties()
            .find(|property| property.name.as_str() == "overrideBaseTrueDerivedFalse")
            .expect("a redeclared property is still declared here");

        assert!(!property.is_override(), "Derived turns the override off");
        assert_eq!(
            property.sites.iter().map(|site| site.is_override).collect::<Vec<_>>(),
            vec![false, true],
            "Derived's own declaration is the strongest, and Base's stands behind it"
        );
        assert_eq!(
            property.api_name(),
            Some("overrideBaseTrueDerivedFalse"),
            "so Derived asks for the accessor Base suppressed"
        );
        assert_eq!(
            property.sites.last().map(|site| site.class.as_str()),
            Some("Base"),
            "while Base is still what introduced it"
        );
    }

    /// A schema another library declares is resolved when a class here
    /// reflects it, and only then: the corpus reflects
    /// `TestReflectedExternalAPI` from its `usd` sublayer, and nothing else
    /// from outside its own layer.
    #[test]
    fn reflected_foreign_resolved() {
        let library = read_fixture("schema.usda").expect("resolves");

        let names: Vec<&str> = library
            .reflected
            .iter()
            .map(|class| class.identifier.as_str())
            .collect();
        assert_eq!(names, vec!["TestReflectedExternalAPI"]);

        let external = &library.reflected[0];
        assert_eq!(external.library, "usd");
        assert_eq!(external.kind, usd::SchemaKind::SingleApplyApi);
        let mut properties: Vec<&str> = external.local_properties().map(|p| p.name.as_str()).collect();
        properties.sort_unstable();
        assert_eq!(
            properties,
            vec![
                "testAttrDuplicate",
                "testAttrExternal",
                "testRelDuplicate",
                "testRelExternal"
            ]
        );
    }

    /// A `customData` list reads whether it was written as tokens or as
    /// strings, which upstream schemas do both of — the vendored corpus writes
    /// `string[] reflectedAPISchemas`.
    #[test]
    fn custom_data_list_spellings() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

over "GLOBAL" (
    customData = {
        string libraryName = "testLists"
    }
)
{
}

class "APISchemaBase" {}

class "StringsAPI" (
    inherits = </APISchemaBase>
    customData = {
        token apiSchemaType = "singleApply"
        string[] apiSchemaCanOnlyApplyTo = ["Shape"]
    }
) {}

class "TokensAPI" (
    inherits = </APISchemaBase>
    customData = {
        token apiSchemaType = "singleApply"
        token[] apiSchemaCanOnlyApplyTo = ["Shape"]
    }
) {}
"#,
        )
        .expect("resolves");
        for identifier in ["StringsAPI", "TokensAPI"] {
            let class = library
                .classes
                .iter()
                .find(|class| class.identifier.as_str() == identifier)
                .unwrap_or_else(|| panic!("{identifier} is generated"));
            assert_eq!(
                class.metadata.can_only_apply_to.len(),
                1,
                "{identifier} lost its restriction"
            );
        }
    }

    /// A class the root layer redeclares resolves through the root's
    /// declaration, not through the weaker one a sublayer left.
    ///
    /// Only the parent lookup can see this: a descendant walking its chain
    /// through the sublayer's `Base` would miss `Typed` and be rejected as a
    /// concrete schema that is not typed.
    #[test]
    fn strongest_declaration_wins() {
        let dir = tempfile::tempdir().expect("tempdir");
        fs::write(
            dir.path().join("sublayer.usda"),
            r#"#usda 1.0

over "GLOBAL" (
    customData = {
        string libraryName = "testStrength"
    }
)
{
}

class "Typed" {}

class "Base" {}
"#,
        )
        .expect("write");

        let schema = dir.path().join("schema.usda");
        fs::write(
            &schema,
            r#"#usda 1.0
(
    subLayers = [
        @sublayer.usda@
    ]
)

over "GLOBAL" (
    customData = {
        string libraryName = "testStrength"
    }
)
{
}

class "Base" (
    inherits = </Typed>
) {}

class Child "Child" (
    inherits = </Base>
) {}
"#,
        )
        .expect("write");

        let (library, _) = crate::configure()
            .search_path(dir.path())
            .read(&schema, &[])
            .expect("the root's Base is the one that counts");
        let child = library
            .classes
            .iter()
            .find(|class| class.identifier.as_str() == "Child")
            .expect("the child class");

        assert!(child.is_typed, "Child reaches Typed through the root's Base");
        assert_eq!(child.kind, usd::SchemaKind::ConcreteTyped);
    }

    /// An inherited property travels with the class that declared it, so the
    /// emitter can tell it from a local one.
    #[test]
    fn inherited_declared_by() {
        let library = read_fixture("schema.usda").expect("resolves");
        let derived = library
            .classes
            .iter()
            .find(|class| class.identifier.as_str() == "Derived")
            .expect("the derived class");

        let inherited: Vec<&str> = derived
            .properties
            .iter()
            .filter_map(|property| property.sites.last())
            .map(|site| site.class.as_str())
            .filter(|declared| *declared != "Derived")
            .collect();
        assert!(
            inherited.contains(&"Base"),
            "Derived carries no property declared by Base: {inherited:?}"
        );
    }
}
