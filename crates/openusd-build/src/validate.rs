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
// TODO: two rules are missing, both comparing names nothing has minted yet. A
// redeclaration that changes a property's type, variability or `custom` flag
// needs each declaring site rather than the composed result the model carries.
// The collisions between Rust identifiers — two tokens reaching one constant,
// two properties reaching one method — belong with the stage that mints them.

use std::collections::HashMap;

use openusd::{sdf, tf, usd};

use crate::error::Error;
use crate::model::{API_SCHEMA_BASE, Class, Library, Property, SCHEMA_BASE};

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

    /// Two token identifiers reaching one Rust constant, which is the same
    /// problem one step later.
    #[error("`{first}` and `{second}` both reach the constant {constant}")]
    TokenConstantCollision {
        /// The constant they collided on.
        constant: String,
        /// The first identifier to reach it.
        first: String,
        /// The second.
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

    /// A base this run does not generate and that belongs to no other library,
    /// so no view of it exists for a descendant to derive from.
    #[error("`{base}` is inherited from but not generated; declare it in the root layer or in a library of its own")]
    UngeneratedBase {
        /// The base that has no views.
        base: tf::Token,
    },

    /// A base in a library this run does not generate and was not told where to
    /// find, so its views cannot be named.
    #[error("`{base}` belongs to the {library} library; name where its views live with Builder::extern_library")]
    UnknownLibrary {
        /// The library declaring the base.
        library: String,
        /// The base that could not be reached.
        base: tf::Token,
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

        if property.spec_type == sdf::SpecType::Attribute && property.type_name().is_none() {
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
    use crate::tests::{read_fixture, read_source};

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
