//! Lowering a schema library to the Rust it becomes.
//!
//! [`model`](crate::model) says what a schema *is*, in terms no language owns.
//! This says what it is in Rust: what each type and trait is called, which
//! traits a view implements, which accessors it offers and which it inherits,
//! and what constant holds each token. Rendering then writes what this decided
//! and decides nothing itself.
//!
//! Keeping the two apart is what lets a name be settled once. A name minted
//! where it is used is a name minted twice, and the collisions this checks —
//! two tokens reaching one constant, two methods reaching one name, two schemas
//! reaching one type — can only be checked where the names are made.

use std::collections::BTreeMap;

use openusd::{sdf, tf, usd, usda};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;

use crate::generated_file;
use crate::model::{API_SCHEMA_BASE, Base, Class, Library, Property, SCHEMA_BASE, TYPED};
use crate::validate::Violation;
use crate::{Externs, doc, error::Error, names, types};

/// A whole library, ready to render.
pub struct RustLibrary {
    /// The `libraryName` the schema declared.
    pub library: String,
    /// The token constants, in the order they are declared.
    pub tokens: Vec<Constant>,
    /// The schemas, in the order the root layer declares them.
    pub classes: Vec<RustClass>,
    /// The manifest the generated `register` embeds, named as it is written.
    pub manifest_file: String,
    /// The schematics it embeds beside it.
    pub schematics_file: String,
}

/// One token constant.
pub struct Constant {
    /// The constant's name.
    pub name: Ident,
    /// The string it holds.
    pub value: String,
    /// What it is for.
    pub documentation: String,
}

/// One schema as Rust: every name and path settled.
pub struct RustClass {
    /// The view type's name.
    pub name: Ident,
    /// The trait this class's own accessors live on, where it has one. An
    /// applied API schema is never inherited from, so its accessors are
    /// inherent and it has none.
    pub accessor_trait: Option<Ident>,
    /// The trait that trait derives from.
    pub parent: syn::Path,
    /// Every trait the view implements, the schema root it answers to first.
    pub memberships: Vec<syn::Path>,
    /// The `tokens::` constant naming the schema.
    pub constant: TokenStream,
    /// The `usd::SchemaKind` constant the view reports itself as.
    pub kind_constant: syn::Path,
    /// What a prim is viewed through, or `None` for a class no prim can be.
    pub view: Option<View>,
    /// The schema's documentation, converted, where it wrote any.
    pub documentation: Option<String>,
    /// The accessors it emits, in property order.
    pub accessors: Vec<RustAccessor>,
}

/// What a prim is viewed through, which decides the shape of the view and the
/// constructors it carries.
pub enum View {
    /// A prim type: defined at a path, and recognised by what a prim is.
    Concrete,
    /// A view over whatever prim a caller hands it, applied to nothing.
    Plain,
    /// Applied to a prim once, under no instance name.
    SingleApply,
    /// Applied per instance name, which the view carries beside the prim.
    MultipleApply,
}

impl View {
    /// Whether the view carries an instance name beside the prim.
    pub fn is_multiple_apply(&self) -> bool {
        matches!(self, View::MultipleApply)
    }
}

/// One property's accessor pair.
pub struct RustAccessor {
    /// The method that reaches the property.
    pub getter: Ident,
    /// The method that authors it.
    pub creator: Ident,
    /// Whether the library writes the reader by hand, so only the creator is
    /// emitted and the reader's name is left reserved.
    pub custom_get: bool,
    /// Whether the pair is written on the view itself rather than on a trait,
    /// which is what an applied API schema's accessors are: nothing derives
    /// from one, so there is no trait for them to live on.
    pub inherent: bool,
    /// The expression naming the property, which for a multiple-apply schema
    /// instantiates a template with the view's own instance name.
    pub token: TokenStream,
    /// Whether the property holds a value, and what type it is declared with.
    pub kind: PropertyKind,
    /// Whether the creator authors `custom`.
    pub custom: bool,
    /// Whether the creator authors `uniform`.
    pub uniform: bool,
    /// The documentation above the reader.
    pub documentation: String,
}

/// What a property is, which decides what its accessors return and how its
/// creator declares it.
pub enum PropertyKind {
    /// An attribute, declared with the value type it holds.
    Attribute {
        /// The `sdf::ValueTypeName` constant its creator declares it with.
        type_constant: syn::Path,
    },
    /// A relationship, which holds targets rather than a value and so is
    /// declared with no type at all.
    Relationship,
}

/// Lowers a library to Rust, resolving every name it will mint.
pub fn library(model: &Library, externs: &Externs) -> Result<RustLibrary, Error> {
    let tokens = constants(model)?;
    let by_value: BTreeMap<&str, &Ident> = tokens
        .iter()
        .map(|constant| (constant.value.as_str(), &constant.name))
        .collect();

    check_class_names(model)?;
    let classes = model
        .classes
        .iter()
        .filter(|class| !is_root(class.identifier.as_str()))
        .map(|class| lower_class(class, model, externs, &by_value))
        .collect::<Result<_, _>>()?;

    Ok(RustLibrary {
        manifest_file: generated_file(&model.name, "manifest.usda"),
        schematics_file: generated_file(&model.name, "schematics.usda"),
        library: model.name.clone(),
        tokens,
        classes,
    })
}

/// The constant each token is emitted as, checked for two reaching one name.
///
/// Two identifiers that differ only in punctuation or case reach the same
/// screaming-snake constant, and a constant holds one string.
fn constants(model: &Library) -> Result<Vec<Constant>, Error> {
    let mut minted: BTreeMap<String, String> = BTreeMap::new();
    let mut constants = Vec::new();

    for token in model.tokens()? {
        let name = names::screaming_snake(&token.id);
        let origin = format!("token `{}`", token.id);
        if let Some(first) = minted.insert(name.clone(), token.id.clone()) {
            return Err(Error::Definition {
                origin,
                violation: Violation::TokenConstantCollision {
                    constant: name,
                    first,
                    second: token.id,
                },
            });
        }
        constants.push(Constant {
            name: identifier(&name, &origin)?,
            documentation: doc::wrap(&format!("`\"{}\"`: {}.", token.value, token.documentation.join(", "))),
            value: token.value,
        });
    }
    Ok(constants)
}

/// Two schemas of one library reaching one Rust name.
///
/// The scope is this module: two libraries may each have a `Sphere`, and
/// nothing stops them, since a consumer includes each in a module of its own.
fn check_class_names(model: &Library) -> Result<(), Error> {
    // The file takes three names of its own, which a schema may not also take.
    let mut seen: BTreeMap<String, &str> = ["tokens", "register", "LIBRARY_NAME"]
        .map(|name| (name.to_owned(), "the generated file"))
        .into();
    for class in &model.classes {
        if is_root(class.identifier.as_str()) {
            continue;
        }
        let name = &class.metadata.class_name;
        let identifier = class.identifier.as_str();

        // A class brings the trait its own accessors live on, except an applied
        // API schema, which has none: a class called `FooSchema` collides with
        // `Foo`'s trait, but never with `FooAPI`.
        let mut minted = vec![name.clone()];
        if !class.kind.is_applied_api_schema() {
            minted.push(trait_name(class.kind, name));
        }
        for minted in minted {
            if let Some(first) = seen.insert(minted.clone(), identifier)
                && first != identifier
            {
                return Err(class.violation(Violation::RustNameCollision {
                    name: minted,
                    first: first.to_owned(),
                    second: identifier.to_owned(),
                }));
            }
        }
    }
    Ok(())
}

/// One schema's names, paths and accessors.
fn lower_class(
    class: &Class,
    model: &Library,
    externs: &Externs,
    by_value: &BTreeMap<&str, &Ident>,
) -> Result<RustClass, Error> {
    check_methods(class)?;

    // A property the schema asked for no accessor for contributes none, and one
    // an ancestor's trait already offers is reached through that trait.
    let applied = class.kind.is_applied_api_schema();
    let offers = |property: &&Property| applied || !shadows_an_ancestor(class, property);
    for property in class.local_properties().filter(|property| !offers(property)) {
        // The ancestor's accessor is what a caller reaches, and it is generated
        // where the ancestor is: a hand-written reader here would never be
        // called, so the schema is told rather than quietly ignored.
        if property.api.custom_get {
            return Err(property.violation(Violation::CustomGetWithoutAccessor {
                property: property.name.clone(),
            }));
        }
    }
    let accessors = class
        .local_properties()
        .filter(offers)
        .filter_map(|property| named(property.api_name(), property.spec_type).map(|a| (property, a)))
        .map(|(property, accessor)| lower_accessor(class, property, &accessor, by_value))
        .collect::<Result<_, _>>()?;

    // Each base contributes the trait a view derives its accessors from, the
    // first of them being the supertrait of this class's own trait. A root
    // contributes none, being what the chain ends at.
    let inherited = class
        .bases
        .iter()
        .map(|base| base_trait(class, base, model, externs))
        .collect::<Result<Vec<_>, _>>()?;
    let parent = match (class.bases.first(), inherited.first()) {
        (_, Some(Some(path))) => path.clone(),
        (Some(base), _) => root_trait(base.identifier.as_str()),
        (None, _) => syn::parse_quote! { ::openusd::usd::SchemaBase },
    };

    // The root the view answers to, then every ancestor whose accessors it
    // inherits. A class no prim can be implements nothing, having no view.
    let view = view(class.kind);
    let mut memberships: Vec<syn::Path> = view.iter().map(schema_root).collect();
    memberships.extend(inherited.into_iter().flatten());

    let name = &class.metadata.class_name;
    let origin = class.origin.describe();
    Ok(RustClass {
        name: identifier(name, &origin)?,
        accessor_trait: match applied {
            true => None,
            false => Some(identifier(&trait_name(class.kind, name), &origin)?),
        },
        parent,
        memberships,
        constant: constant_of(by_value, &class.identifier),
        kind_constant: kind_constant(class.kind),
        view,
        documentation: class.documentation.as_deref().map(doc::to_markdown),
        accessors,
    })
}

/// One property's accessor pair, named and typed.
fn lower_accessor(
    class: &Class,
    property: &Property,
    accessor: &Accessor,
    by_value: &BTreeMap<&str, &Ident>,
) -> Result<RustAccessor, Error> {
    let named = constant_of(by_value, &property.schematics_name);
    let token = match class.kind.is_multiple_apply_api_schema() {
        true => quote! {
            ::openusd::usd::SchemaRegistry::make_multiple_apply_name_instance(#named, self.name.as_str())
        },
        false => named,
    };

    let kind = match property.spec_type {
        sdf::SpecType::Relationship => PropertyKind::Relationship,
        _ => PropertyKind::Attribute {
            type_constant: value_type(property)?,
        },
    };

    let origin = property.origin.describe();
    Ok(RustAccessor {
        getter: identifier(&accessor.getter, &origin)?,
        creator: identifier(&accessor.creator, &origin)?,
        custom_get: property.api.custom_get,
        inherent: class.kind.is_applied_api_schema(),
        token,
        kind,
        custom: property.is_custom(),
        uniform: property.variability() == sdf::Variability::Uniform
            && property.spec_type != sdf::SpecType::Relationship,
        documentation: documentation(property),
    })
}

/// Whether `name` is one of the schema roots, which are the core's own traits
/// rather than anything a library generates: a layer of this library may still
/// declare one, since that is how a base is there to inherit from.
fn is_root(name: &str) -> bool {
    matches!(name, TYPED | API_SCHEMA_BASE | SCHEMA_BASE)
}

/// The `sdf::ValueTypeName` constant an attribute is declared with.
///
/// A legacy spelling the core reads but names no constant for — `Transform`,
/// `PointIndex` — is a type validation admits, since a stage resolves it, and
/// one no creator could declare. It is refused here, where what the generated
/// code needs is known.
fn value_type(property: &Property) -> Result<syn::Path, Error> {
    let named = property.type_name().and_then(|name| name.constant_ident());
    let Some(constant) = named else {
        return Err(property.violation(Violation::UnnameableType {
            property: property.name.clone(),
            type_name: property.type_name().map(|name| name.as_token()).unwrap_or_default(),
        }));
    };

    let constant = Ident::new(constant, Span::call_site());
    Ok(syn::parse_quote! { ::openusd::sdf::ValueTypeName::#constant })
}

/// The `tokens::` constant holding a value.
///
/// Every property name and every schema identifier reached the token set, so a
/// value that did not is one nothing declared: it is named by its own string,
/// which is still what the schematics recorded.
fn constant_of(by_value: &BTreeMap<&str, &Ident>, value: &tf::Token) -> TokenStream {
    if let Some(name) = by_value.get(value.as_str()) {
        return quote! { tokens::#name };
    }
    let literal = value.as_str();
    quote! { #literal }
}

/// An identifier, checked before it is made.
///
/// A schema names its own class and accessors, through `className` and
/// `apiName`, and a name Rust would not take — one that is no identifier at
/// all, or a word Rust has reserved — has to be reported against the schema
/// that wrote it rather than left to panic where it is written out.
fn identifier(name: &str, origin: &str) -> Result<Ident, Error> {
    if !names::is_rust_identifier(name) {
        return Err(Error::Definition {
            origin: origin.to_owned(),
            violation: Violation::NotAnIdentifier { name: name.to_owned() },
        });
    }
    Ok(Ident::new(name, Span::call_site()))
}

/// The methods one property contributes.
struct Accessor {
    getter: String,
    creator: String,
}

/// The methods an accessor of `api_name` contributes to a property of
/// `spec_type`.
fn named(api_name: Option<&str>, spec_type: sdf::SpecType) -> Option<Accessor> {
    let suffix = match spec_type {
        sdf::SpecType::Relationship => "rel",
        _ => "attr",
    };
    // The suffix is what keeps a method clear of a Rust keyword, so no escaping
    // rule is needed on top of it.
    let getter = format!("{}_{suffix}", names::snake_case(api_name?));
    Some(Accessor {
        creator: format!("create_{getter}"),
        getter,
    })
}

/// Every method name a view reaches a property by, readers and authors alike.
///
/// One pair per class along the chain that named it: each emits its own
/// accessors unless a nearer one already offers them, so together they are what
/// a caller can write. A reader the library writes by hand still occupies its
/// name, so it counts here too.
fn offered(property: &Property) -> impl Iterator<Item = String> {
    property
        .sites
        .iter()
        .filter_map(|site| named(site.api_name.as_deref(), property.spec_type))
        .flat_map(|accessor| [accessor.getter, accessor.creator])
}

/// Whether a redeclaration would offer a method an ancestor's trait already
/// offers, which every call through the chain would then find twice.
///
/// A class redeclaring a property to change its fallback keeps the ancestor's
/// accessor: the two mean the same method, and a supertrait already carries it.
/// A redeclaration that renames it is a different method and is emitted, unless
/// a class between them renamed it the same way — which is why every ancestor
/// site is compared and not only the one that introduced the property.
fn shadows_an_ancestor(class: &Class, property: &Property) -> bool {
    let Some(mine) = named(property.api_name(), property.spec_type) else {
        return false;
    };
    property
        .sites
        .iter()
        .filter(|site| site.class != class.identifier)
        .filter_map(|site| named(site.api_name.as_deref(), property.spec_type))
        .any(|theirs| theirs.getter == mine.getter)
}

/// Two properties reaching one method name, counting every ancestor's.
///
/// A view's methods arrive through a chain of traits, and two supertraits
/// offering one method make every call ambiguous — as do two methods of one name
/// in a single trait. Readers and authors share the namespace, so a property
/// whose reader is called `create_size_attr` collides with `size`'s author.
fn check_methods(class: &Class) -> Result<(), Error> {
    let mut seen: BTreeMap<String, &tf::Token> = BTreeMap::new();
    for property in &class.properties {
        for method in offered(property) {
            if let Some(first) = seen.insert(method.clone(), &property.name)
                && first != &property.name
            {
                return Err(property.violation(Violation::MethodCollision {
                    method,
                    first: first.clone(),
                    second: property.name.clone(),
                }));
            }
        }
    }
    Ok(())
}

/// The trait a class's accessors live on.
///
/// An abstract class is the trait, there being no struct to distinguish it
/// from; anything a prim can be needs a name of its own, so its accessors take
/// the `Schema` suffix.
fn trait_name(kind: usd::SchemaKind, class_name: &str) -> String {
    match kind {
        usd::SchemaKind::AbstractTyped | usd::SchemaKind::AbstractBase => class_name.to_owned(),
        _ => format!("{class_name}Schema"),
    }
}

/// The trait a base contributes to a view that derives from it, or `None` where
/// the base is one of the roots, which have no accessors and are named directly.
fn base_trait(class: &Class, base: &Base, model: &Library, externs: &Externs) -> Result<Option<syn::Path>, Error> {
    let name = base.identifier.as_str();
    if matches!(name, TYPED | API_SCHEMA_BASE | SCHEMA_BASE) {
        return Ok(None);
    }

    let origin = class.origin.describe();
    let inherited = identifier(&trait_name(base.kind, &base.class_name), &origin)?;
    let Some(library) = &base.library else {
        // A base of this library that this run does not generate — one a
        // sublayer declares without a `/GLOBAL` of its own — has no trait for a
        // view to derive from, so naming it would name nothing.
        let generated = model.classes.iter().any(|other| other.identifier == base.identifier);
        return match generated {
            true => Ok(Some(syn::parse_quote! { #inherited })),
            false => Err(class.violation(Violation::UngeneratedBase {
                base: base.identifier.clone(),
            })),
        };
    };

    let unknown = || {
        class.violation(Violation::UnknownLibrary {
            library: library.clone(),
            base: base.identifier.clone(),
        })
    };
    let Some(path) = externs.get(library) else {
        return Err(unknown());
    };
    let path: syn::Path = syn::parse_str(path).map_err(|_| unknown())?;
    Ok(Some(syn::parse_quote! { #path::#inherited }))
}

/// What a prim of this kind is viewed through, or `None` where no prim can be
/// one: an abstract schema is a trait and nothing more.
fn view(kind: usd::SchemaKind) -> Option<View> {
    match kind {
        usd::SchemaKind::AbstractTyped | usd::SchemaKind::AbstractBase => None,
        usd::SchemaKind::ConcreteTyped => Some(View::Concrete),
        usd::SchemaKind::NonAppliedApi => Some(View::Plain),
        usd::SchemaKind::SingleApplyApi => Some(View::SingleApply),
        usd::SchemaKind::MultipleApplyApi => Some(View::MultipleApply),
    }
}

/// The root trait a view answers to: a prim type is one of the typed schemas,
/// and everything else here is something applied to a prim.
fn schema_root(view: &View) -> syn::Path {
    match view {
        View::Concrete => syn::parse_quote! { ::openusd::usd::Typed },
        _ => syn::parse_quote! { ::openusd::usd::APISchemaBase },
    }
}

/// The `usd::SchemaKind` constant a view reports itself as.
fn kind_constant(kind: usd::SchemaKind) -> syn::Path {
    let variant = Ident::new(
        match kind {
            usd::SchemaKind::AbstractBase => "AbstractBase",
            usd::SchemaKind::AbstractTyped => "AbstractTyped",
            usd::SchemaKind::ConcreteTyped => "ConcreteTyped",
            usd::SchemaKind::NonAppliedApi => "NonAppliedApi",
            usd::SchemaKind::SingleApplyApi => "SingleApplyApi",
            usd::SchemaKind::MultipleApplyApi => "MultipleApplyApi",
        },
        Span::call_site(),
    );
    syn::parse_quote! { ::openusd::usd::SchemaKind::#variant }
}

/// The core trait one of the schema roots stands for.
fn root_trait(name: &str) -> syn::Path {
    match name {
        TYPED => syn::parse_quote! { ::openusd::usd::Typed },
        API_SCHEMA_BASE => syn::parse_quote! { ::openusd::usd::APISchemaBase },
        _ => syn::parse_quote! { ::openusd::usd::SchemaBase },
    }
}

/// A property's documentation: what the schema said, then what the property is.
fn documentation(property: &Property) -> String {
    // What the schema wrote arrives wrapped, from `to_markdown`; the sentence
    // about the declaration is this crate's own and is wrapped here, so every
    // line of a doc comment holds to one width.
    let declared = doc::wrap(&declaration(property));
    match property.documentation() {
        Some(text) => format!("{}\n\n{declared}", doc::to_markdown(text)),
        None => declared,
    }
}

/// A property as a schema author would write it, then what it reads back as.
fn declaration(property: &Property) -> String {
    let mut text = format!("Declared `{}`.", declared_as(property));

    let allowed = property.allowed_tokens();
    if !allowed.is_empty() {
        let listed: Vec<String> = allowed.iter().map(|token| format!("`{token}`")).collect();
        text.push_str(&format!(" One of {}.", listed.join(", ")));
    }

    let rust = property
        .type_name()
        .and_then(|name| name.kind())
        .and_then(types::rust_type);
    if let Some(rust) = rust {
        text.push_str(&format!(" Read it with `get::<{rust}>()`."));
    }
    text
}

/// The property's declaration as USD writes one, e.g. `uniform token mode = "a"`.
///
/// Assembled from what the model says rather than read back out of a layer, with
/// the fallback rendered by the `usda` writer so the one value a reader has to
/// trust is spelled the way every USD file spells it.
fn declared_as(property: &Property) -> String {
    let mut text = String::new();
    if property.is_custom() {
        text.push_str("custom ");
    }
    if property.variability() == sdf::Variability::Uniform && property.spec_type != sdf::SpecType::Relationship {
        text.push_str("uniform ");
    }

    if property.spec_type == sdf::SpecType::Relationship {
        text.push_str("rel ");
    } else {
        let spelling = property
            .type_name()
            .map_or_else(|| "token".to_owned(), |name| name.serialization_name().to_string());
        text.push_str(&spelling);
        text.push(' ');
    }
    text.push_str(property.schematics_name.as_str());

    if let Some(fallback) = property.fallback()
        && let Ok(value) = usda::TextWriter::value_to_string(fallback)
    {
        text.push_str(&format!(" = {value}"));
    }
    text
}
