//! The rules a schema has to satisfy to be generated from.
//!
//! Two lists, kept apart because they answer different questions. A schema
//! rule says the definition would not mean what it says — a stage composed
//! against our schematics would behave differently from one composed against
//! C++'s. A generator rule says the Rust we would emit does not compile or is
//! ambiguous. Every rule states that harm; that upstream rejects something is
//! not on its own a reason to.
//!
//! Anything a schema author would want to know that does not make the output
//! wrong is a warning instead, returned for a build script to print.

use std::collections::HashMap;

use openusd::{sdf, tf, usd};

use crate::error::Error;
use crate::model::{API_SCHEMA_BASE, Class, Library, Property, Reflection, SCHEMA_BASE, Shape};

/// A rule a schema broke.
///
/// One variant per rule enforced, not one per upstream check: two upstream
/// checks that mean one thing here share a variant, and a check not kept has
/// none. Tests match variants rather than message text.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Violation {
    /// A base no layer in the stack declares.
    #[error("inherits from `{name}`, which no layer declares")]
    MissingBase {
        /// The name that could not be found.
        name: tf::Token,
    },

    /// An inheritance chain that returns to where it started, which has no
    /// order to generate in.
    #[error("inherits from itself through {chain}")]
    CyclicInheritance {
        /// The cycle, in the order it was walked.
        chain: String,
    },

    /// More than one base. A schema is a single chain, and the registry
    /// resolves `is_a` along one.
    #[error("inherits from {count} classes; a schema has at most one base")]
    MultipleBases {
        /// How many were authored.
        count: usize,
    },

    /// An applied API schema that does not inherit directly from
    /// `APISchemaBase`.
    ///
    /// Applying a schema brings its own properties and the API schemas it
    /// lists, not its bases' — an API schema's inheritance is not walked the
    /// way a typed schema's is — so a chain here would promise properties that
    /// applying never delivers.
    #[error("an applied API schema must inherit directly from APISchemaBase, not from `{base}`")]
    AppliedApiNotRooted {
        /// The base it inherits instead.
        base: tf::Token,
    },

    /// A non-applied API schema on a base that is neither `APISchemaBase` nor
    /// another non-applied API schema, whose properties it would appear to
    /// offer and could never carry.
    #[error("a non-applied API schema inherits APISchemaBase or another non-applied API, not `{base}`")]
    NonAppliedApiNotRooted {
        /// The base it inherits instead.
        base: tf::Token,
    },

    /// A schema inheriting inside its own family, which the registry reads as
    /// one schema at two versions rather than two schemas.
    #[error("inherits from `{base}`, which is the same schema family")]
    InheritsWithinFamily {
        /// The base sharing this schema's family.
        base: tf::Token,
    },

    /// An `apiSchemaType` that is none of the three kinds.
    #[error("unknown apiSchemaType `{spelling}`")]
    UnknownApiSchemaType {
        /// What the schema wrote.
        spelling: String,
    },

    /// Metadata that contradicts the kind of schema it sits on.
    #[error("{key} does not apply to a {kind} schema")]
    KindMismatch {
        /// The key that does not belong, whether the schema wrote it as prim
        /// metadata or under `customData`.
        key: &'static str,
        /// The kind it was found on.
        kind: &'static str,
    },

    /// A concrete schema that is not typed, so a stage could never instantiate
    /// it.
    #[error("a concrete schema must inherit from Typed")]
    ConcreteNotTyped,

    /// A schema that is typed, or carries a type name, and also declares
    /// itself an API schema.
    ///
    /// The two cannot both hold: `apiSchemaType` is what makes a schema an API
    /// schema, and an API schema is never a prim type. Left alone the API
    /// reading wins and the type name never reaches the schematics, so a stage
    /// could no longer instantiate the prim type the schema meant to declare.
    #[error("a typed schema cannot declare apiSchemaType")]
    ApiSchemaTypeOnTyped,

    /// An identifier the registry would refuse to register, and so could never
    /// look up.
    #[error("`{identifier}` is not an allowed schema identifier")]
    DisallowedIdentifier {
        /// The identifier as declared.
        identifier: tf::Token,
    },

    /// A `typeName` that is not the class's own identifier. It reaches the
    /// schematics, so a stage would compose the wrong type.
    #[error("typeName `{authored}` is not the schema's own identifier")]
    TypeNameMismatch {
        /// The authored type name.
        authored: tf::Token,
    },

    /// An `apiSchemas` opinion that is not a prepend. Only a prepend composes
    /// as the class's built-in applied API schemas.
    ///
    /// Which kinds may declare built-ins at all is deliberately not a rule
    /// here: the upstream corpus's own `PublicMultipleApplyAPI` declares them
    /// on a multiple-apply schema, so the shape is legal however it reads.
    #[error("apiSchemas must be authored as a prepend")]
    ApiSchemasNotPrepended,

    /// Two properties that reach one name in the schematics, where one spec
    /// cannot hold both.
    ///
    /// The check is on the resolved name: a multiple-apply schema's property
    /// picks up its namespace prefix and the instance-name template on the way
    /// there, so two names distinct at the source can arrive as one.
    #[error("`{first}` and `{second}` both reach `{name}` in the schematics")]
    DuplicateSchematicsName {
        /// The name they collided on.
        name: tf::Token,
        /// The first property to reach it.
        first: tf::Token,
        /// The second.
        second: tf::Token,
    },

    /// An attribute whose type no registered value type names, leaving its
    /// accessor nothing to read.
    #[error("property `{property}` has unknown type `{type_name}`")]
    UnknownPropertyType {
        /// The property.
        property: tf::Token,
        /// The type as declared.
        type_name: tf::Token,
    },

    /// A multiple-apply schema with properties but no namespace prefix, or a
    /// prefix and no properties. The prefix is what keeps one instance's
    /// properties apart from another's.
    #[error("a multiple-apply schema needs propertyNamespacePrefix exactly when it has properties")]
    MultipleApplyPrefix,

    /// A field the registry would refuse to carry, so it would be silently
    /// dropped rather than mean anything.
    #[error("`{field}` is not a field a schema may declare")]
    DisallowedField {
        /// The field name.
        field: String,
    },

    /// A property this class records as an API schema override that an ancestor
    /// declares outright.
    ///
    /// An override reaches a prim definition only where a built-in API schema
    /// supplies the property, so this would delete the ancestor's property from
    /// the class wherever none does. The other direction is allowed: a class may
    /// make an inherited override a declaration of its own.
    #[error("`{property}` is an API schema override here, but `{class}` declares it outright")]
    OverridesADeclaration {
        /// The property.
        property: tf::Token,
        /// The ancestor declaring it outright.
        class: tf::Token,
    },

    /// A redeclaration that changes what a property is, rather than what it
    /// falls back to.
    ///
    /// An accessor is generated where a property is introduced and every class
    /// below reaches that one, so its creator authors the type, variability and
    /// `custom` composed there. A redeclaration changing any of them would have
    /// that creator author a property the redeclaring class's own definition
    /// contradicts. A fallback is not on the list: changing one is what a
    /// redeclaration is for.
    #[error("`{property}` is {} on `{class}`", redeclared_as(.ours, .theirs))]
    IncompatibleRedeclaration {
        /// The property.
        property: tf::Token,
        /// The ancestor it disagrees with.
        class: tf::Token,
        /// What the property is at the ancestor. Boxed with `ours`, so the
        /// error a build stops on stays as small as every other.
        theirs: Box<Shape>,
        /// What this class made it.
        ours: Box<Shape>,
    },

    /// Two token sources reaching one identifier with different values, where
    /// one constant would have to hold both strings.
    #[error("token `{id}` would hold both \"{first}\" and \"{second}\"")]
    TokenValueCollision {
        /// The identifier they collided on.
        id: String,
        /// The string the first source gave it.
        first: String,
        /// The string the second gave it.
        second: String,
    },

    /// Two classes of one library reaching one Rust name, where one module
    /// cannot hold both.
    ///
    /// The scope is the module: two libraries may each declare a `Sphere`, and
    /// nothing stops them.
    #[error("`{first}` and `{second}` both reach the name {name}")]
    RustNameCollision {
        /// The name they collided on.
        name: String,
        /// The first schema to reach it.
        first: String,
        /// The second.
        second: String,
    },

    /// Two properties reaching one method name, where two methods of one name
    /// — or two traits offering one — make every call ambiguous.
    #[error("`{first}` and `{second}` both reach the method {method}")]
    MethodCollision {
        /// The method they collided on.
        method: String,
        /// The first property to reach it.
        first: tf::Token,
        /// The second.
        second: tf::Token,
    },

    /// A name a schema chose — through `className` or `apiName` — that is not a
    /// Rust identifier, so nothing could be called it.
    #[error("`{name}` is not an identifier, so nothing generated can be called it")]
    NotAnIdentifier {
        /// The name as the schema wrote it.
        name: String,
    },

    /// A class this run does not generate and that belongs to no other library,
    /// so no view of it exists for a descendant to derive from or for a class
    /// to reflect.
    #[error(
        "`{class}` is inherited from or reflected but not generated; declare it in the root layer or in a library of its own"
    )]
    Ungenerated {
        /// The class that has no views.
        class: tf::Token,
    },

    /// A reflected API schema no layer in the stack declares.
    #[error("reflects `{schema}`, which no layer declares")]
    UnknownReflectedSchema {
        /// The name that could not be found.
        schema: tf::Token,
    },

    /// A reflected API schema the class does not apply.
    ///
    /// Reflecting says every prim of this type carries the schema's properties,
    /// which only applying the schema makes true; a reflected accessor would
    /// otherwise reach a property the prim's definition does not have. A
    /// multiple-apply class records its applied schemas as instance-name
    /// templates, which no reflected name matches, so it cannot reflect.
    #[error("`{schema}` is reflected but not applied; add it to `prepend apiSchemas`")]
    ReflectedNotApplied {
        /// The schema reflected without being applied.
        schema: tf::Token,
    },

    /// A class in a library this run does not generate and was not told where
    /// to find, so its views cannot be named: a base to derive from, or a
    /// schema to reflect.
    #[error("`{class}` belongs to the {library} library; name where its views live with Builder::extern_library")]
    UnknownLibrary {
        /// The library declaring the class.
        library: String,
        /// The class that could not be reached.
        class: tf::Token,
    },

    /// A library was told where its views live, but not in a spelling Rust can
    /// read, so nothing can be named through it.
    #[error("the {library} library's views were placed at `{path}`, which is no Rust path")]
    UnreadableLibraryPath {
        /// The library the path was given for.
        library: String,
        /// What was given.
        path: String,
    },

    /// An `apiGetImplementation` that is neither spelling.
    #[error("unknown apiGetImplementation `{spelling}`")]
    UnknownApiGetImplementation {
        /// What the schema wrote.
        spelling: String,
    },

    /// A custom read accessor asked for on a property that has no accessor,
    /// which cannot both be true.
    #[error("`{property}` asks for a custom accessor but generates none")]
    CustomGetWithoutAccessor {
        /// The property.
        property: tf::Token,
    },

    /// An attribute whose type the core reads but gives no constant to declare
    /// it with, so nothing could author the property.
    #[error("`{property}` is a `{type_name}`, which has no value-type constant to declare it with")]
    UnnameableType {
        /// The property.
        property: tf::Token,
        /// The type it was declared as.
        type_name: tf::Token,
    },
}

/// Checks every rule against a resolved library, returning what a schema
/// author should know but that does not make the output wrong.
pub fn check(library: &Library) -> Result<Vec<String>, Error> {
    let mut warnings = Vec::new();

    for class in &library.classes {
        check_identifier(class)?;
        check_kind(class)?;
        check_inheritance(class)?;
        check_fields(class)?;
        check_properties(class)?;
        check_reflection(class, library, &mut warnings)?;
        warnings.extend(conventions(class));
    }

    Ok(warnings)
}

/// The identifier and the type name that reach the registry.
fn check_identifier(class: &Class) -> Result<(), Error> {
    if !usd::SchemaRegistry::is_allowed_schema_identifier(class.identifier.as_str()) {
        return Err(class.violation(Violation::DisallowedIdentifier {
            identifier: class.identifier.clone(),
        }));
    }

    if let Some(authored) = &class.authored_type_name
        && authored != &class.identifier
    {
        return Err(class.violation(Violation::TypeNameMismatch {
            authored: authored.clone(),
        }));
    }

    Ok(())
}

/// Metadata that has to agree with the kind of schema carrying it.
fn check_kind(class: &Class) -> Result<(), Error> {
    let kind = class.kind;
    let metadata = &class.metadata;

    // Auto-apply names one schema to apply, which a multiple-apply schema
    // cannot be without an instance name to apply it under.
    let multiple_apply = kind == usd::SchemaKind::MultipleApplyApi;
    for (mismatched, key) in [
        (
            kind != usd::SchemaKind::SingleApplyApi && !metadata.auto_apply_to.is_empty(),
            "apiSchemaAutoApplyTo",
        ),
        (
            !kind.is_applied_api_schema() && !metadata.can_only_apply_to.is_empty(),
            "apiSchemaCanOnlyApplyTo",
        ),
        (
            !multiple_apply && !metadata.allowed_instance_names.is_empty(),
            "apiSchemaAllowedInstanceNames",
        ),
        (
            !multiple_apply && !metadata.instance_restrictions.is_empty(),
            "apiSchemaInstances",
        ),
        (
            kind != usd::SchemaKind::ConcreteTyped && !metadata.fallback_types.is_empty(),
            "fallbackTypes",
        ),
        // An order names properties as the schema declared them, and a
        // multiple-apply schema's reach the schematics under an instance-name
        // template instead — so the order it asked for would name properties
        // the schema data does not have.
        (
            multiple_apply
                && class
                    .authored_fields
                    .iter()
                    .any(|field| field == sdf::FieldKey::PropertyOrder.as_str()),
            sdf::FieldKey::PropertyOrder.as_str(),
        ),
    ] {
        if mismatched {
            return Err(class.violation(Violation::KindMismatch {
                key,
                kind: kind_name(kind),
            }));
        }
    }

    if kind.is_api_schema() && (class.is_typed || class.authored_type_name.is_some()) {
        return Err(class.violation(Violation::ApiSchemaTypeOnTyped));
    }

    if multiple_apply {
        let has_properties = class.local_properties().next().is_some();
        if has_properties != metadata.property_namespace_prefix.is_some() {
            return Err(class.violation(Violation::MultipleApplyPrefix));
        }
    } else if metadata.property_namespace_prefix.is_some() {
        return Err(class.violation(Violation::KindMismatch {
            key: "propertyNamespacePrefix",
            kind: kind_name(kind),
        }));
    }

    // A concrete schema is one a stage instantiates, which only a typed schema
    // can be.
    if kind == usd::SchemaKind::ConcreteTyped && !class.is_typed {
        return Err(class.violation(Violation::ConcreteNotTyped));
    }

    Ok(())
}

/// The shape of the inheritance chain.
fn check_inheritance(class: &Class) -> Result<(), Error> {
    if class.authored_base_count > 1 {
        return Err(class.violation(Violation::MultipleBases {
            count: class.authored_base_count,
        }));
    }

    // Any ancestor of this schema's own family makes the chain read as one
    // schema at two versions, not as two schemas.
    for base in &class.bases {
        let (family, _) = usd::SchemaRegistry::parse_schema_family_and_version(&base.identifier);
        if family == class.family {
            return Err(class.violation(Violation::InheritsWithinFamily {
                base: base.identifier.clone(),
            }));
        }
    }

    if !class.kind.is_api_schema() {
        return Ok(());
    }

    // A class inheriting nothing is rooted at SchemaBase, which every API
    // schema needs APISchemaBase below. Only the root every schema derives from
    // has no base at all, and naming it is what makes the diagnostic read for a
    // class that claims to be an API schema anyway.
    let base = class.direct_base.clone().unwrap_or_else(|| tf::Token::new(SCHEMA_BASE));
    let inherits_root = base.as_str() == API_SCHEMA_BASE;

    if class.kind.is_applied_api_schema() && !inherits_root {
        return Err(class.violation(Violation::AppliedApiNotRooted { base }));
    }

    // A non-applied API schema may sit on APISchemaBase or on another
    // non-applied one, wherever that base is declared. Only a base that is one
    // counts: an API schema that declares no kind at all is single-apply by
    // default, so silence is not permission.
    if class.kind == usd::SchemaKind::NonAppliedApi && !inherits_root {
        let base_is_non_applied = class
            .bases
            .first()
            .is_some_and(|base| base.kind == usd::SchemaKind::NonAppliedApi);
        if !base_is_non_applied {
            return Err(class.violation(Violation::NonAppliedApiNotRooted { base }));
        }
    }

    Ok(())
}

/// Fields a schematics carries, on the class prim and on every property.
///
/// `inheritPaths`, `customData` and `specifier` are the generator's own input
/// rather than schema data, so they are expected here and never written out.
fn check_fields(class: &Class) -> Result<(), Error> {
    if let Some(field) = disallowed_field(&class.authored_fields) {
        return Err(class.violation(Violation::DisallowedField { field: field.clone() }));
    }

    if let Some(op) = &class.api_schemas_op
        && (op.explicit
            || !op.explicit_items.is_empty()
            || !op.appended_items.is_empty()
            || !op.added_items.is_empty()
            || !op.deleted_items.is_empty()
            || !op.ordered_items.is_empty())
    {
        return Err(class.violation(Violation::ApiSchemasNotPrepended));
    }

    Ok(())
}

/// Every property's type, name and accessor metadata.
fn check_properties(class: &Class) -> Result<(), Error> {
    let mut seen: HashMap<&tf::Token, &tf::Token> = HashMap::new();
    for property in &class.properties {
        if let Some(first) = seen.insert(&property.schematics_name, &property.name) {
            return Err(property.violation(Violation::DuplicateSchematicsName {
                name: property.schematics_name.clone(),
                first: first.clone(),
                second: property.name.clone(),
            }));
        }
    }

    for property in &class.properties {
        if let Some(field) = disallowed_field(property.fields.keys()) {
            return Err(property.violation(Violation::DisallowedField { field: field.clone() }));
        }

        if property.shape.spec_type == sdf::SpecType::Attribute && property.type_name().is_none() {
            let declared = property
                .fields
                .get(sdf::FieldKey::TypeName.as_str())
                .and_then(|value| value.clone().try_as_token())
                .unwrap_or_default();
            return Err(property.violation(Violation::UnknownPropertyType {
                property: property.name.clone(),
                type_name: declared,
            }));
        }

        if property.api.custom_get && !property.has_accessor() {
            return Err(property.violation(Violation::CustomGetWithoutAccessor {
                property: property.name.clone(),
            }));
        }

        // An override reaches a prim definition only where a built-in API
        // schema supplies the property, so a class that turns an inherited
        // declaration into one deletes it from itself wherever none does. The
        // other direction is fine, and a class may make an inherited override
        // a declaration of its own.
        if property.is_override()
            && let Some(site) = property.sites.iter().find(|site| !site.is_override)
        {
            return Err(Error::Definition {
                origin: site.origin.describe(),
                violation: Violation::OverridesADeclaration {
                    property: property.name.clone(),
                    class: site.class.clone(),
                },
            });
        }

        // A redeclaration may change what the property falls back to and
        // nothing else: the accessor a caller reaches is the introducing
        // class's, whose creator authors the shape composed there. Reported
        // against this class's own declaration, which is the one to fix.
        if let Some((mine, weaker)) = property.sites.split_first()
            && mine.class == class.identifier
            && let Some(site) = weaker.iter().find(|site| site.shape != mine.shape)
        {
            return Err(Error::Definition {
                origin: mine.origin.describe(),
                violation: Violation::IncompatibleRedeclaration {
                    property: property.name.clone(),
                    class: site.class.clone(),
                    theirs: Box::new(site.shape.clone()),
                    ours: Box::new(mine.shape.clone()),
                },
            });
        }
    }

    Ok(())
}

/// What comes of the API schemas a class names to reflect: what a schema
/// author should know about the ones set aside, and the one that is wrong.
///
/// The model decides each schema's fate ([`Class::reflections`]); this only
/// phrases it. A schema set aside is a warning, as upstream prints and goes on,
/// and the corpus relies on that: it reflects a multiple-apply schema it
/// applies under an instance name.
fn check_reflection(class: &Class, library: &Library, warnings: &mut Vec<String>) -> Result<(), Error> {
    for reflection in class.reflections(library) {
        match reflection {
            Reflection::Taken { schema, shadowed, .. } => {
                for (property, first) in shadowed {
                    warnings.push(format!(
                        "{}: `{}` of `{}` is not reflected; `{first}` already declares it",
                        class.origin.describe(),
                        property.name,
                        schema.identifier
                    ));
                }
            }
            Reflection::NotSingleApply(schema) => warnings.push(format!(
                "{}: `{}` is a {} schema, so it is not reflected; only a single-apply API schema can be",
                class.origin.describe(),
                schema.identifier,
                kind_name(schema.kind)
            )),
            // Reflecting says every prim of this type carries the schema's
            // properties, which only applying the schema makes true.
            Reflection::NotApplied(schema) => {
                return Err(class.violation(Violation::ReflectedNotApplied {
                    schema: schema.identifier.clone(),
                }));
            }
        }
    }
    Ok(())
}

/// What a schema author should know, where the output is still correct.
fn conventions(class: &Class) -> Vec<String> {
    let mut warnings = Vec::new();
    let ends_in_api = class.family.as_str().ends_with("API");
    let is_api = class.kind.is_api_schema();

    // The registry never reads this, so it is a convention rather than a rule.
    if is_api && !ends_in_api {
        warnings.push(format!(
            "{}: an API schema's name conventionally ends in `API`",
            class.origin.describe()
        ));
    }
    if !is_api && ends_in_api {
        warnings.push(format!(
            "{}: only an API schema's name conventionally ends in `API`",
            class.origin.describe()
        ));
    }
    warnings
}

/// The first field a schematics would refuse to carry, if any.
///
/// The generator's own input is expected and never written out: what a class
/// inherits, its `customData`, its specifier, and the two children keys naming
/// the prims and properties it declares.
///
/// The other children keys are not on that list. A class prim carrying a
/// variant set is a shape the schematics has no way to record, and letting the
/// key through would drop the variant's content without a word.
fn disallowed_field<'a>(fields: impl IntoIterator<Item = &'a String>) -> Option<&'a String> {
    let input = [
        sdf::FieldKey::InheritPaths.as_str(),
        sdf::FieldKey::CustomData.as_str(),
        sdf::FieldKey::Specifier.as_str(),
        sdf::ChildrenKey::PrimChildren.as_str(),
        sdf::ChildrenKey::PropertyChildren.as_str(),
    ];
    fields
        .into_iter()
        .find(|field| !input.contains(&field.as_str()) && usd::SchemaRegistry::is_disallowed_field(field))
}

/// How a redeclaration reads in its diagnostic: the first thing `ours` and
/// `theirs` disagree on, this class's reading first, as in "`double` here and
/// `int`".
fn redeclared_as(ours: &Shape, theirs: &Shape) -> String {
    spelled(ours)
        .into_iter()
        .zip(spelled(theirs))
        .find(|(ours, theirs)| ours != theirs)
        .map_or_else(
            || "as it was".to_owned(),
            |(ours, theirs)| format!("{ours} here and {theirs}"),
        )
}

/// Each thing a redeclaration is held to, as a diagnostic reads it.
fn spelled(shape: &Shape) -> [String; 4] {
    [
        match shape.spec_type {
            sdf::SpecType::Relationship => "a relationship",
            _ => "an attribute",
        }
        .to_owned(),
        shape
            .type_name
            .as_ref()
            .map_or_else(|| "of no type".to_owned(), |name| format!("`{name}`")),
        match shape.variability {
            sdf::Variability::Uniform => "uniform",
            sdf::Variability::Varying => "varying",
        }
        .to_owned(),
        match shape.custom {
            true => "custom",
            false => "not custom",
        }
        .to_owned(),
    ]
}

/// How a schema kind reads in a diagnostic.
fn kind_name(kind: usd::SchemaKind) -> &'static str {
    match kind {
        usd::SchemaKind::AbstractBase => "abstract base",
        usd::SchemaKind::AbstractTyped => "abstract typed",
        usd::SchemaKind::ConcreteTyped => "concrete typed",
        usd::SchemaKind::NonAppliedApi => "non-applied API",
        usd::SchemaKind::SingleApplyApi => "single-apply API",
        usd::SchemaKind::MultipleApplyApi => "multiple-apply API",
    }
}

impl Class {
    /// This class's declaration, with the rule it broke.
    pub(crate) fn violation(&self, violation: Violation) -> Error {
        Error::Definition {
            origin: self.origin.describe(),
            violation,
        }
    }
}

impl Property {
    /// This property's declaration, with the rule it broke.
    pub(crate) fn violation(&self, violation: Violation) -> Error {
        Error::Definition {
            origin: self.origin.describe(),
            violation,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{TAG_API, read_fixture, read_source, schema};

    /// The rule a fixture is rejected for.
    fn violation(name: &str) -> Violation {
        match read_fixture(name) {
            Err(Error::Definition { violation, .. }) => violation,
            Err(other) => panic!("{name} was rejected, but not by a rule: {other}"),
            Ok(_) => panic!("{name} was accepted"),
        }
    }

    /// A multiple-apply schema needs its namespace prefix exactly when it has
    /// properties to put under it.
    #[test]
    fn multiple_apply_prefix() {
        assert!(matches!(violation("schemaFail12.usda"), Violation::MultipleApplyPrefix));
        assert!(matches!(violation("schemaFail13.usda"), Violation::MultipleApplyPrefix));
    }

    /// Metadata that contradicts the kind of schema carrying it.
    #[test]
    fn kind_metadata_mismatch() {
        for (fixture, key) in [
            ("schemaFail14.usda", "propertyNamespacePrefix"),
            ("schemaFail15.usda", "fallbackTypes"),
            ("schemaFail16.usda", "fallbackTypes"),
            ("schemaFail17.usda", "apiSchemaAutoApplyTo"),
            ("schemaFail18.usda", "apiSchemaAutoApplyTo"),
            ("schemaFail24.usda", "propertyOrder"),
        ] {
            match violation(fixture) {
                Violation::KindMismatch { key: found, .. } => assert_eq!(found, key, "{fixture}"),
                other => panic!("{fixture}: {other}"),
            }
        }
    }

    /// Only a prepend composes as a class's built-in applied API schemas.
    #[test]
    fn api_schemas_mode() {
        assert!(matches!(
            violation("schemaFail19.usda"),
            Violation::ApiSchemasNotPrepended
        ));
        assert!(matches!(
            violation("schemaFail20.usda"),
            Violation::ApiSchemasNotPrepended
        ));
    }

    /// A schema inheriting inside its own family reads as one schema at two
    /// versions rather than two schemas.
    #[test]
    fn same_family_base() {
        assert!(matches!(
            violation("schemaFail21.usda"),
            Violation::InheritsWithinFamily { .. }
        ));
    }

    /// An identifier the registry would refuse, and a field a schematics does
    /// not carry.
    #[test]
    fn registry_would_refuse() {
        assert!(matches!(
            violation("schemaFail22.usda"),
            Violation::DisallowedIdentifier { .. }
        ));
        match violation("schemaFail23.usda") {
            Violation::DisallowedField { field } => assert_eq!(field, "kind"),
            other => panic!("{other}"),
        }
    }

    /// A variant set on a class prim is a shape the schematics cannot record,
    /// and the children key naming it is not the generator input the two keys
    /// beside it are — so it is refused rather than quietly dropped along with
    /// everything the variant declares.
    #[test]
    fn variant_set_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        let error = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testVariants"
    }
)
{
}

class "Typed" {}

class "Varied" (
    inherits = </Typed>
) {
    double plain = 1

    variantSet "shading" = {
        "red" {
            double onlyInVariant = 2
        }
    }
}
"#,
        )
        .expect_err("a schema may not vary");

        match error {
            Error::Definition {
                violation: Violation::DisallowedField { field },
                ..
            } => assert_eq!(field, sdf::ChildrenKey::VariantSetChildren.as_str()),
            other => panic!("{other}"),
        }
    }

    /// A composition arc is a field the registry refuses too, and it has to be
    /// caught on the class prim rather than on the composed result: flattening
    /// is what resolves an arc away, so by then there is nothing left to see.
    #[test]
    fn composition_arc_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        let error = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testArc"
    }
)
{
}

class "Typed" {}

class "Specializing" (
    inherits = </Typed>
    specializes = </Typed>
) {}
"#,
        )
        .expect_err("a schema may not compose");

        match error {
            Error::Definition {
                violation: Violation::DisallowedField { field },
                ..
            } => assert_eq!(field, "specializes"),
            other => panic!("{other}"),
        }
    }

    /// The two override schemas the corpus keeps commented out, because
    /// upstream rejects them for the reason this rule states.
    const OVERRIDES: &str = r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testOverrides"
    }
)
{
}

class "Typed" {}

class "Base" (
    inherits = </Typed>
) {
    int plain = 1
}

class "Derived" (
    inherits = </Base>
) {
    int plain = 2 (
        customData = {
            bool apiSchemaOverride = true
        }
    )
}
"#;

    /// A class may not turn a property an ancestor declares outright into an
    /// API schema override, which would delete it from this class wherever no
    /// built-in API schema supplies it.
    #[test]
    fn override_of_a_declaration() {
        let dir = tempfile::tempdir().expect("tempdir");
        let error = read_source(dir.path(), OVERRIDES).expect_err("a class may not delete what it inherits");

        match error {
            Error::Definition {
                violation: Violation::OverridesADeclaration { property, class },
                ..
            } => {
                assert_eq!(property.as_str(), "plain");
                assert_eq!(class.as_str(), "Base");
            }
            other => panic!("{other}"),
        }
    }

    /// The reverse is allowed, and is what the corpus's own
    /// `overrideBaseTrueDerivedFalse` does: a class may make an inherited
    /// override a declaration of its own.
    #[test]
    fn declaration_over_an_override() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testTakenOn"
    }
)
{
}

class "Typed" {}

class "Base" (
    inherits = </Typed>
) {
    int plain = 1 (
        customData = {
            bool apiSchemaOverride = true
        }
    )
}

class "Derived" (
    inherits = </Base>
) {
    int plain = 2
}
"#,
        )
        .expect("a class may take an inherited override on");

        let derived = library
            .classes
            .iter()
            .find(|class| class.identifier.as_str() == "Derived")
            .expect("the derived class");
        assert_eq!(derived.override_properties().count(), 0);
    }

    /// An override travels to a class that says nothing about the property:
    /// the strongest declaration decides, and for a class that redeclares
    /// nothing that is the ancestor's.
    #[test]
    fn override_reaches_a_silent_class() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testInheritedOverride"
    }
)
{
}

class "Typed" {}

class "Base" (
    inherits = </Typed>
) {
    int plain = 1 (
        customData = {
            bool apiSchemaOverride = true
        }
    )
}

class "Derived" (
    inherits = </Base>
) {}
"#,
        )
        .expect("resolves");

        for identifier in ["Base", "Derived"] {
            let class = library
                .classes
                .iter()
                .find(|class| class.identifier.as_str() == identifier)
                .expect("the class");
            let names: Vec<&str> = class.override_properties().map(|p| p.name.as_str()).collect();
            assert_eq!(names, vec!["plain"], "{identifier}");
        }
    }

    /// A base declaring one property, and a class deriving from it that
    /// redeclares the same property.
    fn redeclaring(base: &str, derived: &str) -> String {
        schema(
            "testRedeclare",
            &format!(
                r#"class "Base" (
    inherits = </Typed>
) {{
    {base}
}}

class "Derived" (
    inherits = </Base>
) {{
    {derived}
}}"#
            ),
        )
    }

    /// What a redeclaration was refused for: the ancestor, what the property is
    /// there, and what this class made it.
    fn incompatible(base: &str, derived: &str) -> (String, Shape, Shape) {
        let dir = tempfile::tempdir().expect("tempdir");
        match read_source(dir.path(), &redeclaring(base, derived)).expect_err("the redeclaration changes the property")
        {
            Error::Definition {
                origin,
                violation:
                    Violation::IncompatibleRedeclaration {
                        class, theirs, ours, ..
                    },
            } => {
                assert!(
                    origin.ends_with("/Derived.plain"),
                    "reported against the redeclaration: {origin}"
                );
                (class.to_string(), *theirs, *ours)
            }
            other => panic!("{other}"),
        }
    }

    /// A redeclaration that changes the type, which the introducing class's
    /// creator would go on authoring as it was.
    #[test]
    fn redeclared_type_changes() {
        let (class, theirs, ours) = incompatible("int plain = 1", "double plain = 2");
        assert_eq!(class, "Base");
        assert_eq!(theirs.type_name, Some(tf::Token::new("int")));
        assert_eq!(ours.type_name, Some(tf::Token::new("double")));
    }

    /// Spelling `uniform` on a property the base left varying changes what
    /// composes, and so is refused.
    #[test]
    fn redeclared_adds_uniform() {
        let (_, theirs, ours) = incompatible(r#"token plain = "a""#, r#"uniform token plain = "b""#);
        assert_eq!(theirs.variability, sdf::Variability::Varying);
        assert_eq!(ours.variability, sdf::Variability::Uniform);
    }

    /// So does making an inherited property `custom`.
    #[test]
    fn redeclared_adds_custom() {
        let (_, theirs, ours) = incompatible("int plain = 1", "custom int plain = 2");
        assert!(!theirs.custom);
        assert!(ours.custom);
    }

    /// The diagnostic spells the first thing the two shapes disagree on, this
    /// class's reading first.
    #[test]
    fn redeclared_spelled() {
        let base = Shape {
            spec_type: sdf::SpecType::Attribute,
            type_name: Some(tf::Token::new("int")),
            variability: sdf::Variability::Varying,
            custom: false,
        };
        let typed = Shape {
            type_name: Some(tf::Token::new("double")),
            ..base.clone()
        };
        let uniform = Shape {
            variability: sdf::Variability::Uniform,
            ..base.clone()
        };
        let custom = Shape {
            custom: true,
            ..base.clone()
        };
        let related = Shape {
            spec_type: sdf::SpecType::Relationship,
            type_name: None,
            ..base.clone()
        };

        assert_eq!(redeclared_as(&typed, &base), "`double` here and `int`");
        assert_eq!(redeclared_as(&uniform, &base), "uniform here and varying");
        assert_eq!(redeclared_as(&custom, &base), "custom here and not custom");
        assert_eq!(redeclared_as(&related, &base), "a relationship here and an attribute");
    }

    /// Redeclaring an attribute as a relationship never reaches the rule:
    /// composition refuses a property whose specs disagree on what kind it is
    /// before anything is resolved from the stack.
    #[test]
    fn redeclared_as_rel() {
        let dir = tempfile::tempdir().expect("tempdir");
        let error = read_source(dir.path(), &redeclaring("int plain = 1", "rel plain"))
            .expect_err("the specs disagree on what the property is");
        assert!(
            matches!(&error, Error::Composition { diagnostic, .. } if diagnostic.contains("inconsistent spec types")),
            "{error}"
        );
    }

    /// A different accessor name does not excuse the change: the ancestor's
    /// creator is still reachable on the derived view.
    #[test]
    fn redeclared_renamed_rejected() {
        let (_, theirs, ours) = incompatible(
            "int plain = 1",
            r#"double plain = 2 (
        customData = { string apiName = "other" }
    )"#,
        );
        assert_eq!(theirs.type_name, Some(tf::Token::new("int")));
        assert_eq!(ours.type_name, Some(tf::Token::new("double")));
    }

    /// Changing the fallback is what a redeclaration is for.
    #[test]
    fn redeclared_fallback_only() {
        let dir = tempfile::tempdir().expect("tempdir");
        read_source(
            dir.path(),
            &redeclaring("double3 plain = (1, 1, 1)", "double3 plain = (2, 2, 2)"),
        )
        .expect("a fallback may change");
    }

    /// A redeclaration that leaves `uniform` unspelled composes to uniform
    /// through the base, so the property is what it was and is accepted (see
    /// [`Shape`]).
    #[test]
    fn redeclared_omits_uniform() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            &redeclaring(r#"uniform token plain = "a""#, r#"token plain = "b""#),
        )
        .expect("omitting the keyword changes nothing");

        let derived = library
            .classes
            .iter()
            .find(|class| class.identifier.as_str() == "Derived")
            .expect("the derived class");
        let plain = derived
            .local_properties()
            .find(|property| property.name.as_str() == "plain")
            .expect("the redeclared property");
        assert_eq!(plain.shape.variability, sdf::Variability::Uniform);
    }

    /// A library of the roots and whatever `classes` declare.
    fn reflecting(classes: &str) -> String {
        schema("testReflect", classes)
    }

    /// Reflecting a name nothing declares is a mistake the stack reports, not
    /// a schema quietly left out.
    #[test]
    fn reflected_unknown() {
        let dir = tempfile::tempdir().expect("tempdir");
        let error = read_source(
            dir.path(),
            &reflecting(
                r#"class "Thing" (
    inherits = </Typed>
    customData = { token[] reflectedAPISchemas = ["NowhereAPI"] }
) {}"#,
            ),
        )
        .expect_err("nothing declares it");

        match error {
            Error::Definition {
                violation: Violation::UnknownReflectedSchema { schema },
                ..
            } => assert_eq!(schema.as_str(), "NowhereAPI"),
            other => panic!("{other}"),
        }
    }

    /// Reflecting promises the schema's properties on every prim of the type,
    /// which only applying the schema keeps.
    #[test]
    fn reflected_not_applied() {
        let dir = tempfile::tempdir().expect("tempdir");
        let error = read_source(
            dir.path(),
            &reflecting(&format!(
                r#"{TAG_API}

class "Thing" (
    inherits = </Typed>
    customData = {{ token[] reflectedAPISchemas = ["TagAPI"] }}
) {{}}"#
            )),
        )
        .expect_err("the schema is not applied");

        match error {
            Error::Definition {
                violation: Violation::ReflectedNotApplied { schema },
                ..
            } => assert_eq!(schema.as_str(), "TagAPI"),
            other => panic!("{other}"),
        }
    }

    /// A multiple-apply schema has no one set of properties to take, so it is
    /// set aside with a word rather than refused: the corpus does exactly
    /// this, applying it under an instance name.
    #[test]
    fn reflected_multi_apply_warns() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            &reflecting(
                r#"class "MultiAPI" (
    inherits = </APISchemaBase>
    customData = {
        token apiSchemaType = "multipleApply"
        token propertyNamespacePrefix = "multi"
    }
) {
    int depth = 0
}

class "Thing" (
    inherits = </Typed>
    prepend apiSchemas = ["MultiAPI:foo"]
    customData = { token[] reflectedAPISchemas = ["MultiAPI"] }
) {}"#,
            ),
        )
        .expect("set aside, not refused");
        let warnings = check(&library).expect("set aside, not refused");

        assert!(
            warnings
                .iter()
                .any(|warning| warning.contains("`MultiAPI` is a multiple-apply API schema, so it is not reflected")),
            "{warnings:?}"
        );
        let thing = library.find(&tf::Token::new("Thing")).expect("the class");
        assert!(matches!(
            thing.reflections(&library).as_slice(),
            [Reflection::NotSingleApply(schema)] if schema.identifier.as_str() == "MultiAPI"
        ));
    }

    /// Two reflected schemas declaring one name: the first keeps it, the
    /// second's is set aside with a word, and the class takes the rest.
    #[test]
    fn reflected_duplicate_warns() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            &reflecting(&format!(
                r#"{TAG_API}

class "LabelAPI" (
    inherits = </APISchemaBase>
    customData = {{ token apiSchemaType = "singleApply" }}
) {{
    string label = ""
    int dup = 0
}}

class "Thing" (
    inherits = </Typed>
    prepend apiSchemas = ["TagAPI", "LabelAPI"]
    customData = {{ token[] reflectedAPISchemas = ["TagAPI", "LabelAPI"] }}
) {{}}"#
            )),
        )
        .expect("the first keeps the name");
        let warnings = check(&library).expect("the first keeps the name");

        assert!(
            warnings
                .iter()
                .any(|warning| warning.contains("`dup` of `LabelAPI` is not reflected; `TagAPI` already declares it")),
            "{warnings:?}"
        );

        // Each schema, with the names taken from it and the ones set aside.
        let thing = library.find(&tf::Token::new("Thing")).expect("the class");
        let taken: Vec<String> = thing
            .reflections(&library)
            .iter()
            .map(|reflection| match reflection {
                Reflection::Taken {
                    schema,
                    properties,
                    shadowed,
                } => {
                    let names: Vec<&str> = properties.iter().map(|p| p.name.as_str()).collect();
                    let shadowed: Vec<String> = shadowed
                        .iter()
                        .map(|(p, first)| format!("{} by {first}", p.name))
                        .collect();
                    format!("{} takes {names:?}, shadowed {shadowed:?}", schema.identifier)
                }
                other => panic!("{other:?}"),
            })
            .collect();
        assert_eq!(
            taken,
            vec![
                r#"TagAPI takes ["tag", "dup"], shadowed []"#,
                r#"LabelAPI takes ["label"], shadowed ["dup by TagAPI"]"#,
            ]
        );
    }

    /// A `typeName` reaches the schematics, so it has to be the schema's own.
    #[test]
    fn type_name_mismatch() {
        assert!(matches!(
            violation("schemaFail5.usda"),
            Violation::TypeNameMismatch { .. }
        ));
    }

    /// Only a typed schema can be instantiated, so only a typed schema can be
    /// concrete.
    #[test]
    fn concrete_needs_typed() {
        assert!(matches!(violation("schemaFail6.usda"), Violation::ConcreteNotTyped));
        assert!(matches!(violation("schemaFail7.usda"), Violation::ConcreteNotTyped));
    }

    /// An applied API schema inherits `APISchemaBase` and nothing else, since
    /// applying one brings no base's properties with it.
    ///
    /// Upstream rejects `schemaFail3` and `schemaFail4` for declaring a
    /// property twice, and `schemaFail8` for a family name not ending in
    /// `API`. All three are rejected here as well, by this rule instead: none
    /// of them inherits `APISchemaBase`.
    #[test]
    fn applied_api_base() {
        for fixture in [
            "schemaFail3.usda",
            "schemaFail4.usda",
            "schemaFail8.usda",
            "schemaFail10.usda",
            "schemaFail11.usda",
        ] {
            assert!(
                matches!(violation(fixture), Violation::AppliedApiNotRooted { .. }),
                "{fixture}"
            );
        }
    }

    /// A non-applied API schema cannot inherit an applied one, whose
    /// properties it would appear to offer and could never carry.
    #[test]
    fn non_applied_base() {
        assert!(matches!(
            violation("schemaFail9.usda"),
            Violation::NonAppliedApiNotRooted { .. }
        ));
    }

    /// A typed schema that also calls itself an API schema is rejected rather
    /// than quietly generated as the API schema, which would drop the prim
    /// type it meant to declare.
    #[test]
    fn typed_cannot_be_api() {
        let dir = tempfile::tempdir().expect("tempdir");
        let error = read_source(
            dir.path(),
            r#"#usda 1.0

over "GLOBAL" (
    customData = {
        string libraryName = "testTypedApi"
    }
)
{
}

class "Typed" {}

class Shape "Shape" (
    inherits = </Typed>
    customData = { token apiSchemaType = "singleApply" }
) {}
"#,
        )
        .expect_err("a schema cannot be both");
        assert!(
            matches!(
                error,
                Error::Definition {
                    violation: Violation::ApiSchemaTypeOnTyped,
                    ..
                }
            ),
            "{error}"
        );
    }

    /// A base that declares no kind is single-apply, so a non-applied schema
    /// may not sit on it — saying nothing must not buy what saying
    /// `singleApply` is refused.
    #[test]
    fn silent_base_is_not_non_applied() {
        let dir = tempfile::tempdir().expect("tempdir");
        let error = read_source(
            dir.path(),
            r#"#usda 1.0

over "GLOBAL" (
    customData = {
        string libraryName = "testSilentBase"
    }
)
{
}

class "APISchemaBase" {}

class "SilentAPI" (
    inherits = </APISchemaBase>
) {}

class "NonAppliedAPI" (
    inherits = </SilentAPI>
    customData = { token apiSchemaType = "nonApplied" }
) {}
"#,
        )
        .expect_err("the base is single-apply by default");
        assert!(
            matches!(
                error,
                Error::Definition {
                    violation: Violation::NonAppliedApiNotRooted { .. },
                    ..
                }
            ),
            "{error}"
        );
    }

    /// Two properties of a multiple-apply schema can be distinct at the source
    /// and arrive as one name in the schematics, where one spec cannot hold
    /// both and the second would silently replace the first.
    #[test]
    fn schematics_names_collide() {
        let dir = tempfile::tempdir().expect("tempdir");
        let error = read_source(
            dir.path(),
            r#"#usda 1.0

over "GLOBAL" (
    customData = {
        string libraryName = "testCollide"
    }
)
{
}

class "APISchemaBase" {}

class "CollideAPI" (
    inherits = </APISchemaBase>
    customData = {
        token apiSchemaType = "multipleApply"
        token propertyNamespacePrefix = "test"
    }
) {
    int foo
    int test:__INSTANCE_NAME__:foo
}
"#,
        )
        .expect_err("both properties reach one schematics name");
        assert!(
            matches!(
                error,
                Error::Definition {
                    violation: Violation::DuplicateSchematicsName { .. },
                    ..
                }
            ),
            "{error}"
        );
    }

    /// The upstream failure files this crate accepts, and why.
    ///
    /// Both turn on a name two tokens would reach once converted to a Rust
    /// identifier: an `allowedTokens` value colliding with a library token.
    /// That is a generator rule, which the name stage owes and which nothing
    /// here can check yet. The list is the decision on the record: a file
    /// leaving it means a rule arrived, and a file joining it needs a reason
    /// written here.
    #[test]
    fn accepted_upstream_failures() {
        for fixture in ["schemaFail.usda", "schemaFail2.usda"] {
            assert!(
                read_fixture(fixture).is_ok(),
                "{fixture} is now rejected; move it to a rule test and drop it from this list"
            );
        }
    }

    /// A schema whose name breaks the API-suffix convention is still
    /// generated, and says so. The registry never reads that convention, so
    /// nothing about the output is wrong.
    ///
    /// The upstream corpus keeps the convention throughout, and the one file
    /// that breaks it breaks a rule as well, so this writes its own schema.
    #[test]
    fn suffix_is_a_warning() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

over "GLOBAL" (
    customData = {
        string libraryName = "testConvention"
    }
)
{
}

class "APISchemaBase" {}

class "Applied" (
    inherits = </APISchemaBase>
    customData = { token apiSchemaType = "singleApply" }
) {}
"#,
        )
        .expect("nothing here breaks a rule");
        let warnings = check(&library).expect("nothing here breaks a rule");

        assert!(
            warnings
                .iter()
                .any(|warning| warning.contains("conventionally ends in")),
            "{warnings:?}"
        );
    }
}
