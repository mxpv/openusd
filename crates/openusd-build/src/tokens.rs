//! The token constants a generated library declares.
//!
//! A schema names things in strings — property names, the values a token
//! attribute admits, the prefix a multiple-apply schema namespaces under — and
//! a generated library declares each of them once, as a constant an application
//! can reach for instead of retyping the string.
//!
//! What a token *means* is its value, which is the name the schematics records.
//! Its identifier is a convenience, and this module shapes it the way every
//! OpenUSD generator does so that `default_`, `modelDrawMode` and
//! `collection_MultipleApplyTemplate_ExpansionRule` are the spellings the
//! OpenUSD documentation gives them. What a back end then calls the constant
//! holding one is the back end's own business, and is decided there.

use std::collections::BTreeMap;

use openusd::{sdf, usd};

use crate::doc;
use crate::error::Error;
use crate::model::{Class, DeclaredToken, Library, Property};
use crate::names;
use crate::validate::Violation;

/// One token a generated library declares.
#[derive(Debug)]
pub struct Token {
    /// The identifier the token is known by.
    pub id: String,
    /// The string it holds, which is what a stage actually reads.
    pub value: String,
    /// What it is for: one entry per source that reached this token, so a name
    /// several schemas share says so.
    pub documentation: Vec<String>,
}

impl Library {
    /// Every token this library declares, in the order they are emitted.
    ///
    /// Sorted by identifier, case-insensitively but stably, with the schema
    /// identifiers last: those name the schemas themselves rather than anything
    /// inside one, and reading them as a group is what a user wants.
    pub fn tokens(&self) -> Result<Vec<Token>, Error> {
        let mut properties = Gathered::default();
        let mut identifiers = Gathered::default();

        for class in &self.classes {
            identifiers.add_schema(class)?;
            properties.add_class(class, self)?;
        }
        for declared in &self.declared_tokens {
            properties.declared(declared, &format!("a token of the {} library", self.name))?;
        }

        // A property that happens to be named after a schema is the schema's
        // token, so it reads with the others of its kind rather than alone
        // among the property names.
        let shared: Vec<Token> = identifiers.0.keys().filter_map(|id| properties.0.remove(id)).collect();
        for token in shared {
            for said in token.documentation {
                identifiers.insert(token.id.clone(), token.value.clone(), &said)?;
            }
        }

        let mut tokens = properties.sorted();
        tokens.extend(identifiers.sorted());
        Ok(tokens)
    }
}

/// The tokens gathered so far, keyed by identifier.
#[derive(Default)]
struct Gathered(BTreeMap<String, Token>);

impl Gathered {
    /// Records one token, merging it with an identical one already gathered.
    ///
    /// Two sources reaching one identifier is ordinary — a property name and an
    /// allowed value often coincide — and both are then said to describe it.
    /// Reaching one identifier with two different *values* is not: a constant
    /// holds one string, and which one it should hold has no answer.
    fn insert(&mut self, id: String, value: String, documentation: &str) -> Result<(), Error> {
        match self.0.get_mut(&id) {
            Some(token) if token.value != value => {
                return Err(Error::Definition {
                    origin: format!("token `{id}`"),
                    violation: Violation::TokenValueCollision {
                        id,
                        first: token.value.clone(),
                        second: value,
                    },
                });
            }
            Some(token) => {
                if !token.documentation.iter().any(|said| said == documentation) {
                    token.documentation.push(documentation.to_owned());
                }
            }
            None => {
                self.0.insert(
                    id.clone(),
                    Token {
                        id,
                        value,
                        documentation: vec![documentation.to_owned()],
                    },
                );
            }
        }
        Ok(())
    }

    /// The tokens naming a schema itself: its identifier, and the family behind
    /// that identifier where the schema carries a version.
    fn add_schema(&mut self, class: &Class) -> Result<(), Error> {
        let name = class.identifier.as_str().to_owned();
        let described = named(class);
        if class.version == 0 {
            let documentation = format!("the schema identifier and family of {described}");
            return self.insert(names::token_id(&name, true), name, &documentation);
        }

        self.insert(
            names::token_id(&name, true),
            name,
            &format!("the schema identifier of {described}"),
        )?;
        let family = class.family.as_str().to_owned();
        self.insert(
            names::token_id(&family, true),
            family,
            &format!("the schema family of {described}"),
        )
    }

    /// Every token one schema's properties and metadata imply.
    ///
    /// Attributes come first and in name order, so that a token several of them
    /// reach is described in an order two runs agree on.
    fn add_class(&mut self, class: &Class, library: &Library) -> Result<(), Error> {
        let literal = library.use_literal_identifiers;
        let described = named(class);

        let mut attributes: Vec<&Property> = class
            .properties
            .iter()
            .filter(|property| property.spec_type == sdf::SpecType::Attribute)
            .collect();
        attributes.sort_by_cached_key(|property| property.name.as_str().to_lowercase());

        for property in attributes {
            self.insert(
                property_id(property),
                property.schematics_name.as_str().to_owned(),
                &described,
            )?;

            // A fallback and the values beside it are described once, by the
            // class that declared them: a class inheriting the property offers
            // no accessor of its own to name them against.
            if property.is_local {
                let fallback = token_fallback(property);
                if let Some(value) = &fallback {
                    let documentation = format!("the fallback of {}", describe(class, property));
                    self.insert(names::token_id(value, literal), value.clone(), &documentation)?;
                }

                for allowed in property.allowed_tokens() {
                    let value = allowed.as_str();
                    // The fallback is already described as the fallback, and an
                    // empty string names no constant.
                    if value.is_empty() || fallback.as_deref() == Some(value) {
                        continue;
                    }
                    let documentation = format!("a value {} admits", describe(class, property));
                    self.insert(names::token_id(value, literal), value.to_owned(), &documentation)?;
                }
            }
        }

        for property in &class.properties {
            if property.spec_type == sdf::SpecType::Relationship {
                self.insert(
                    property_id(property),
                    property.schematics_name.as_str().to_owned(),
                    &described,
                )?;
            }
        }

        for declared in &class.metadata.schema_tokens {
            self.declared(declared, &format!("a token of the {described} schema"))?;
        }

        if let Some(prefix) = &class.metadata.property_namespace_prefix {
            let value = prefix.as_str().to_owned();
            let documentation = format!("the property namespace prefix of {described}");
            self.insert(names::token_id(&value, true), value, &documentation)?;
        }
        Ok(())
    }

    /// One token a schema asked for outright, described as it asked or as what
    /// declared it.
    fn declared(&mut self, declared: &DeclaredToken, fallback: &str) -> Result<(), Error> {
        // What a schema author wrote is prose, and what this crate writes is
        // already Markdown.
        let documentation = match &declared.documentation {
            Some(text) => doc::to_markdown(text, &doc::Symbols::default()),
            None => fallback.to_owned(),
        };
        self.insert(
            names::token_id(&declared.id, true),
            declared.value.clone(),
            &documentation,
        )
    }

    /// The gathered tokens in emission order: case-insensitive first so that
    /// unrelated spellings read together, then case-sensitive so that two
    /// differing only in case keep a stable order.
    fn sorted(self) -> Vec<Token> {
        let mut tokens: Vec<Token> = self.0.into_values().collect();
        tokens.sort_by_cached_key(|token| (token.id.to_lowercase(), token.id.clone()));
        tokens
    }
}

/// The identifier a property's token is known by.
///
/// Camel-cased whatever the library asked for: a namespaced name could not
/// survive as an identifier otherwise, and one spelling for all of them is what
/// keeps them predictable.
///
/// A multiple-apply schema's properties reach the schematics under an
/// instance-name template, and the placeholder is an implementation detail no
/// identifier should carry, so it reads spelled out:
/// `collection:__INSTANCE_NAME__:expansionRule` is known as
/// `collection_MultipleApplyTemplate_ExpansionRule`. Two schemas declaring the
/// bare placeholder are told apart the same way, by the prefix each namespaces
/// under.
fn property_id(property: &Property) -> String {
    let spelled = usd::SchemaRegistry::make_multiple_apply_name_instance(
        property.schematics_name.as_str(),
        "_MultipleApplyTemplate_",
    );
    names::token_id(spelled.as_str(), false)
}

/// A token attribute's fallback, which is a token in its own right. Only a
/// token-typed one: a string that happens to look like a name is a value, not a
/// name.
fn token_fallback(property: &Property) -> Option<String> {
    if property.type_name()? != sdf::ValueTypeName::TOKEN {
        return None;
    }
    let fallback = property.fallback()?.clone().try_as_token()?;
    (!fallback.as_str().is_empty()).then(|| fallback.as_str().to_owned())
}

/// How a property reads in a token's documentation: by the name the schema
/// gave it, which is the one a schema author would recognise.
fn describe(class: &Class, property: &Property) -> String {
    let described = &class.metadata.class_name;
    match property.api_name() {
        Some(api_name) => format!("`{described}.{api_name}`"),
        None => format!("the {} property `{}`", named(class), property.schematics_name),
    }
}

/// How a schema reads in a token's documentation.
///
/// Backticked, because these descriptions become doc comments on the generated
/// constants, and a bare `SlotAPI` there is a `clippy::doc_markdown` finding in
/// the consumer's own build.
fn named(class: &Class) -> String {
    format!("`{}`", class.metadata.class_name)
}

#[cfg(test)]
mod tests {
    use std::sync::LazyLock;

    use super::*;
    use crate::tests::{read_fixture, read_source};

    /// The tokens the contrived corpus declares, by identifier.
    fn corpus() -> &'static [Token] {
        static ONCE: LazyLock<Vec<Token>> = LazyLock::new(|| {
            read_fixture("schema.usda")
                .expect("resolves")
                .tokens()
                .expect("gathers")
        });
        &ONCE
    }

    /// The schema identifiers come last, as a group a reader can take in at
    /// once rather than scattered among the property names.
    #[test]
    fn identifiers_last() {
        let tokens = corpus();
        let position = |id: &str| tokens.iter().position(|token| token.id == id);

        let derived = position("Derived").expect("the Derived identifier");
        let property = position("testAttrOne").expect("a property name");
        assert!(derived > property, "identifiers sort after property names");
    }

    /// A token attribute's fallback is a token, and the values it admits are
    /// tokens, but the fallback is not said twice.
    #[test]
    fn fallback_skips_allowed() {
        let tokens = corpus();
        let token = tokens
            .iter()
            .find(|token| token.value == "VariableTokenDefault")
            .expect("the fallback is a token of its own");
        let said = token.documentation.join(", ");
        assert!(said.contains("the fallback of"), "{said}");
        assert!(
            !said.contains("a value"),
            "the fallback is not also listed as a possible value: {said}"
        );
    }

    /// A property name and the value it admits reach one identifier, and both
    /// say what it is for.
    #[test]
    fn one_id_many_sources() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testShared"
    }
)
{
}

class "Typed" {}

class "Held" (
    inherits = </Typed>
) {
    token mode = "mode" (
        allowedTokens = ["mode", "other"]
    )
}
"#,
        )
        .expect("resolves");

        let tokens = library.tokens().expect("gathers");
        let token = tokens.iter().find(|token| token.id == "mode").expect("one token");
        assert_eq!(token.value, "mode");
        let said = token.documentation.join(", ");
        assert!(said.contains("Held.mode"), "{said}");
        assert!(said.contains("fallback"), "{said}");
    }

    /// One identifier cannot hold two strings, so a schema that asks for it is
    /// rejected rather than given one of them.
    #[test]
    fn one_id_two_values() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testClash"
        dictionary libraryTokens = {
            dictionary mode = {
                string value = "somethingElse"
            }
        }
    }
)
{
}

class "Typed" {}

class "Held" (
    inherits = </Typed>
) {
    token mode = "x"
}
"#,
        )
        .expect("resolves");

        match library.tokens() {
            Err(Error::Definition {
                violation: Violation::TokenValueCollision { id, .. },
                ..
            }) => assert_eq!(id, "mode"),
            other => panic!("{other:?}"),
        }
    }
}
