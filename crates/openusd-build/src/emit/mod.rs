//! The Rust a schema library is generated as.
//!
//! Three steps. [`lower`] settles every Rust decision a schema implies — what
//! each type and trait is called, which traits a view implements, which
//! accessors it offers — [`emitter`] writes those decisions as syntax, and
//! [`render`] lays that syntax out as text. Only the first decides anything, so
//! a name is settled in one place and can be checked for collisions there.
//!
//! The file is written to be included bare into whatever module a consumer
//! chooses, through `openusd::include_schema!`. That is what decides its shape:
//! it carries no `use` block, since one would apply to the module it lands in
//! and could collide with what the consumer already imports, so every path in it
//! is spelled in full.

mod emitter;
mod lower;

use proc_macro2::TokenStream;

use crate::model::Library;
use crate::{Externs, GENERATED_BY, error::Error};

/// The generated views for one library, `schema` naming what they came from.
pub fn emit(model: &Library, externs: &Externs, schema: &str) -> Result<String, Error> {
    let lowered = lower::library(model, externs)?;
    Ok(render(emitter::library(&lowered), schema))
}

/// The tokens as a formatted file, with the header above them.
///
/// Each top-level item is laid out on its own so that a blank line falls
/// between them: `prettyplease` reads a syntax tree, which has no blank lines of
/// its own to keep.
fn render(file: TokenStream, schema: &str) -> String {
    let parsed: syn::File = syn::parse2(file).expect("the emitter writes valid Rust");
    let items: Vec<String> = parsed
        .items
        .into_iter()
        .map(|item| {
            let one = syn::File {
                shebang: None,
                attrs: Vec::new(),
                items: vec![item],
            };
            prettyplease::unparse(&one)
        })
        .collect();

    format!("// {GENERATED_BY}\n// Generated from {schema}.\n\n{}", items.join("\n"))
}

#[cfg(test)]
mod tests {
    use std::sync::LazyLock;

    use super::*;
    use crate::error::Error;
    use crate::tests::read_source;
    use crate::validate::Violation;

    /// A library covering the kinds that emit differently.
    const KINDS: &str = r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testEmit"
    }
)
{
}

class "Typed" {}

class "APISchemaBase" {}

class "Shape" (
    inherits = </Typed>
) {
    color3f color = (1, 1, 1)
}

class Ball "Ball" (
    inherits = </Shape>
) {
    double radius = 1
}

class "TagAPI" (
    inherits = </APISchemaBase>
    customData = {
        token apiSchemaType = "singleApply"
    }
) {
    string tag = ""
}

class "SlotAPI" (
    inherits = </APISchemaBase>
    customData = {
        token apiSchemaType = "multipleApply"
        token propertyNamespacePrefix = "slot"
    }
) {
    int depth = 0
}
"#;

    /// A library whose accessors exercise the shapes that differ.
    const ACCESSORS: &str = r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testAccessors"
    }
)
{
}

class "Typed" {}

class "Held" (
    inherits = </Typed>
) {
    double radius = 1 (
        doc = "The radius."
    )
    uniform token mode = "a" (
        allowedTokens = ["a", "b"]
    )
    custom float temp
    rel target
    int hidden (
        customData = {
            string apiName = ""
        }
    )
}
"#;

    /// What one schema library generates.
    fn emitted(source: &str) -> String {
        let dir = tempfile::tempdir().expect("tempdir");
        let model = read_source(dir.path(), source).expect("resolves");
        emit(&model, &Externs::new(), "schema.usda").expect("emits")
    }

    /// The kinds fixture, emitted once for the tests that read it.
    fn kinds() -> &'static str {
        static ONCE: LazyLock<String> = LazyLock::new(|| emitted(KINDS));
        &ONCE
    }

    /// The accessors fixture, likewise.
    fn accessors() -> &'static str {
        static ONCE: LazyLock<String> = LazyLock::new(|| emitted(ACCESSORS));
        &ONCE
    }

    /// An abstract schema is a trait over the root it derives from, and a
    /// concrete one is a struct plus the trait its own accessors live on.
    #[test]
    fn kinds_take_their_shapes() {
        let text = kinds();
        assert!(text.contains("pub trait Shape: ::openusd::usd::Typed {"), "{text}");
        assert!(text.contains("pub trait BallSchema: Shape {"), "{text}");
        assert!(text.contains("pub struct Ball(::openusd::usd::Prim);"), "{text}");
        assert!(text.contains("impl BallSchema for Ball {}"), "{text}");
        assert!(text.contains("impl Shape for Ball {}"), "{text}");
    }

    /// An abstract schema is no prim type, so it gets no view to construct.
    #[test]
    fn abstract_has_no_view() {
        let text = kinds();
        assert!(!text.contains("pub struct Shape"), "{text}");
    }

    /// A concrete view is a prim type, so it defines and recognises one.
    #[test]
    fn concrete_constructors() {
        let text = kinds();
        assert!(text.contains("stage.define_typed_prim(path, tokens::BALL)?"), "{text}");
        assert!(
            text.contains("prim.is_a(tokens::BALL)?.then_some(Self(prim))"),
            "{text}"
        );
    }

    /// An applied API schema is applied rather than defined, and a
    /// multiple-apply one carries the instance name it was applied under.
    #[test]
    fn applied_constructors() {
        let text = kinds();
        assert!(text.contains("prim.clone().apply_api(tokens::TAG_API)?"), "{text}");
        assert!(text.contains("name: ::openusd::tf::Token,"), "{text}");
        assert!(text.contains("make_applied_name(tokens::SLOT_API"), "{text}");
    }

    /// A multiple-apply schema's properties are templates, so its accessors put
    /// the view's own instance name into one.
    #[test]
    fn instanced_accessors() {
        let text = kinds();
        assert!(
            text.contains("make_multiple_apply_name_instance("),
            "the template is instantiated: {text}"
        );
        assert!(text.contains("tokens::SLOT_MULTIPLE_APPLY_TEMPLATE_DEPTH"), "{text}");
        assert!(text.contains("self.name.as_str()"), "{text}");
    }

    /// The file carries no `use` block, every path being spelled in full, since
    /// it is included into a module it knows nothing about.
    #[test]
    fn no_imports() {
        let text = kinds();
        assert!(!text.contains("\nuse "), "{text}");
    }

    /// Registration embeds both layers, so it touches no filesystem.
    #[test]
    fn register_embeds_layers() {
        let text = kinds();
        assert!(text.contains("pub const LIBRARY_NAME: &str = \"testEmit\";"), "{text}");
        assert!(text.contains("\"testEmit.schematics.usda\""), "{text}");
    }

    /// A reader reaches the property, and the creator declares it with the type
    /// the schema gave it.
    #[test]
    fn attribute_pair() {
        let text = accessors();
        assert!(
            text.contains("fn radius_attr(&self) -> ::openusd::usd::Attribute {"),
            "{text}"
        );
        assert!(text.contains("self.prim().attribute(tokens::RADIUS)"), "{text}");
        assert!(text.contains("::openusd::sdf::ValueTypeName::DOUBLE"), "{text}");
    }

    /// What the schema declared is what the creator authors. Authoring leaves a
    /// property `custom`, so every creator says whether it is one; a uniform
    /// property says that too.
    #[test]
    fn creator_authors_declaration() {
        let text = accessors();
        assert!(text.contains(".set_custom(true)?"), "{text}");
        assert!(text.contains(".set_custom(false)?"), "{text}");
        assert!(
            text.contains(".set_variability(::openusd::sdf::Variability::Uniform)?"),
            "{text}"
        );
    }

    /// A relationship reads as a relationship, not as an attribute.
    #[test]
    fn relationship_pair() {
        let text = accessors();
        assert!(
            text.contains("fn target_rel(&self) -> ::openusd::usd::Relationship {"),
            "{text}"
        );
        assert!(text.contains("create_relationship(tokens::TARGET)?"), "{text}");
    }

    /// An empty `apiName` asks for no accessor, so none is written.
    #[test]
    fn suppressed_has_none() {
        let text = accessors();
        assert!(!text.contains("fn hidden"), "{text}");
    }

    /// The documentation says what the property is, beyond what the schema
    /// wrote about it, and the declaration is the one `sdf` would write.
    #[test]
    fn documents_the_declaration() {
        let text = accessors();
        assert!(text.contains("The radius."), "{text}");
        assert!(text.contains("Declared `double radius = 1.0`."), "{text}");
        assert!(text.contains("Read it with `get::<f64>()`"), "{text}");
        assert!(
            text.contains("Declared `uniform token mode = \"a\"`. One of `a`, `b`."),
            "{text}"
        );
    }

    /// Two token identifiers can reach one Rust constant, which upstream does
    /// on purpose where a schema and a property share a name. The library
    /// declares the pair happily, and the second constant takes an underscore.
    #[test]
    fn two_ids_one_constant() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testConstants"
        dictionary libraryTokens = {
            dictionary drawMode = {
                string value = "a"
            }
            dictionary draw_mode = {
                string value = "b"
            }
        }
    }
)
{
}

class "Typed" {}
"#,
        )
        .expect("the library itself is well formed");

        let text = emit(&library, &Externs::new(), "schema.usda").expect("both are named");
        // `draw_mode` sorts before `drawMode`, so it is the one that keeps the
        // name; both say which string they hold.
        assert!(text.contains("pub const DRAW_MODE: &str = \"b\";"), "{text}");
        assert!(text.contains("pub const DRAW_MODE_: &str = \"a\";"), "{text}");
    }

    /// Two properties of one class can ask for one accessor name, and Rust has
    /// no way to hold both.
    #[test]
    fn two_properties_one_method() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testMethods"
    }
)
{
}

class "Typed" {}

class "Held" (
    inherits = </Typed>
) {
    int one (
        customData = {
            string apiName = "same"
        }
    )
    int two (
        customData = {
            string apiName = "same"
        }
    )
}
"#,
        )
        .expect("the library itself is well formed");

        match emit(&library, &Externs::new(), "schema.usda") {
            Err(Error::Definition {
                violation: Violation::MethodCollision { method, .. },
                ..
            }) => assert_eq!(method, "same_attr"),
            other => panic!("{:?}", other.map(|_| "emitted")),
        }
    }

    /// A schema may call its class anything USD admits, including a word Rust
    /// has taken, which is refused where it is named rather than where it is
    /// written out.
    #[test]
    fn keyword_class_name() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testKeywords"
    }
)
{
}

class "Typed" {}

class "Held" (
    inherits = </Typed>
    customData = {
        string className = "type"
    }
) {
}
"#,
        )
        .expect("the library itself is well formed");

        match emit(&library, &Externs::new(), "schema.usda") {
            Err(Error::Definition {
                violation: Violation::NotAnIdentifier { name },
                ..
            }) => assert_eq!(name, "type"),
            other => panic!("{:?}", other.map(|_| "emitted")),
        }
    }

    /// The schema roots are the core's own traits, so a library that declares
    /// one — as the core `usd` library itself does — generates nothing for it.
    #[test]
    fn roots_are_not_generated() {
        let text = kinds();
        assert!(!text.contains("trait Typed"), "{text}");
        assert!(!text.contains("trait APISchemaBase"), "{text}");
        assert!(
            text.contains("::openusd::usd::Typed"),
            "the core's is what a view answers to: {text}"
        );
    }

    /// The generated file takes three names of its own, and a class that asks
    /// for one is refused where it asks rather than by the consumer's compiler.
    #[test]
    fn class_takes_a_file_name() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testReserved"
    }
)
{
}

class "Typed" {}

class "Held" (
    inherits = </Typed>
    customData = {
        string className = "tokens"
    }
) {
}
"#,
        )
        .expect("the library itself is well formed");

        match emit(&library, &Externs::new(), "schema.usda") {
            Err(Error::Definition {
                violation: Violation::RustNameCollision { name, .. },
                ..
            }) => assert_eq!(name, "tokens"),
            other => panic!("{:?}", other.map(|_| "emitted")),
        }
    }

    /// A legacy type spelling a stage resolves but no constant names is one no
    /// creator could declare, so it is refused rather than declared as a token.
    #[test]
    fn type_without_a_constant() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testTypes"
    }
)
{
}

class "Typed" {}

class "Held" (
    inherits = </Typed>
) {
    Transform placement
}
"#,
        )
        .expect("the type is one a stage resolves");

        match emit(&library, &Externs::new(), "schema.usda") {
            Err(Error::Definition {
                violation: Violation::UnnameableType { property, .. },
                ..
            }) => assert_eq!(property.as_str(), "placement"),
            other => panic!("{:?}", other.map(|_| "emitted")),
        }
    }

    /// A redeclaration reaches the ancestor's accessor, so a hand-written
    /// reader asked for beside it would never be called.
    #[test]
    fn custom_get_on_a_redeclaration() {
        let dir = tempfile::tempdir().expect("tempdir");
        let library = read_source(
            dir.path(),
            r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testShadowed"
    }
)
{
}

class "Typed" {}

class "Held" (
    inherits = </Typed>
) {
    double size = 1
}

class "Deeper" (
    inherits = </Held>
) {
    double size = 2 (
        customData = {
            string apiGetImplementation = "custom"
        }
    )
}
"#,
        )
        .expect("the library itself is well formed");

        match emit(&library, &Externs::new(), "schema.usda") {
            Err(Error::Definition {
                violation: Violation::CustomGetWithoutAccessor { property },
                ..
            }) => assert_eq!(property.as_str(), "size"),
            other => panic!("{:?}", other.map(|_| "emitted")),
        }
    }
}
