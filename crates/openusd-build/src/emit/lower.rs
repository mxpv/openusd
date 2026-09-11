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

use std::collections::{BTreeMap, BTreeSet};
use std::iter;

use openusd::{sdf, tf, usd, usda};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;

use crate::model::{API_SCHEMA_BASE, Base, Class, Library, Property, TYPED, is_root};
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
    /// The trait this class's own accessors live on, and so where every one of
    /// them is written: as that trait's defaults, or on the view itself when
    /// this is `None`. An applied API schema is never inherited from, so its
    /// accessors are inherent and it has no trait.
    pub accessor_trait: Option<Ident>,
    /// The trait that trait derives from.
    pub parent: syn::Path,
    /// The schema root the view answers to, one per side of the typed / API
    /// split.
    pub root: syn::Path,
    /// The traits carrying the accessors it inherits, which are those of the
    /// classes it is built on, nearest first.
    pub inherited: Vec<syn::Path>,
    /// The `tokens::` constant naming the schema.
    pub constant: TokenStream,
    /// Whether its names need `non_camel_case_types` allowed: a versioned
    /// schema keeps the underscore its identifier carries, and `Cylinder_1` is
    /// no camel-case name.
    pub allows_non_camel_case: bool,
    /// The `usd::SchemaKind` constant the view reports itself as.
    pub kind_constant: syn::Path,
    /// What a prim is viewed through.
    pub view: View,
    /// The schema's documentation, converted, where it wrote any.
    pub documentation: Option<String>,
    /// The accessors it emits, in property order. Where they go is one
    /// decision for the class, which [`accessor_trait`](Self::accessor_trait)
    /// carries: they are that trait's defaults, or inherent when it has none.
    pub accessors: Vec<RustAccessor>,
    /// The API schemas whose properties it offers as its own, each as the
    /// method that views a prim through it.
    pub reflected: Vec<Reflected>,
}

/// An API schema a class reflects: its properties read as the class's own, and
/// the view itself is one method away.
pub struct Reflected {
    /// What the method that views the prim through the schema is called.
    pub accessor: Ident,
    /// The view it returns.
    pub view: Ident,
}

/// What a prim is viewed through, which decides the shape of the view and the
/// constructors it carries.
pub enum View {
    /// A prim type: defined at a path, and recognised by what a prim is.
    Concrete,
    /// A base of prim types: recognised by what a prim is, but naming none a
    /// prim can be defined as.
    Abstract,
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
    let mut lowered = tokens(model)?;
    let by_value: BTreeMap<&str, &Ident> = lowered
        .tokens
        .iter()
        .map(|constant| (constant.value.as_str(), &constant.name))
        .collect();

    check_class_names(model)?;
    // One table for the library, layered under each class's own.
    let library = library_symbols(model);
    lowered.classes = model
        .classes
        .iter()
        .filter(|class| !is_root(&class.identifier))
        .map(|class| lower_class(class, model, externs, &by_value, &library))
        .collect::<Result<_, _>>()?;

    Ok(lowered)
}

/// The tokens alone, for a library that gets no views.
///
/// A separate request rather than a flag on [`library`], because it is held to
/// different rules: what a Rust name would collide with, or which type has no
/// constant to declare it, says nothing about a library whose API is written by
/// hand. Asking for one or the other says which set applies.
pub fn tokens(model: &Library) -> Result<RustLibrary, Error> {
    Ok(RustLibrary {
        library: model.name.clone(),
        tokens: constants(model)?,
        classes: Vec::new(),
    })
}

/// The constant each token is emitted as.
///
/// Two identifiers can reach one screaming-snake name: `points` and the schema
/// `Points` both reach `POINTS`, a pair upstream writes on purpose and keeps
/// apart by case, which a Rust constant cannot. The first one there keeps the
/// name and the next takes a trailing underscore, as a token landing on a
/// reserved word does. The order is the one [`Library::tokens`] fixed —
/// properties by name, schema identifiers last — so a library mints the same
/// constants on every run, and each says in its own documentation what it
/// holds.
fn constants(model: &Library) -> Result<Vec<Constant>, Error> {
    let mut minted: BTreeSet<String> = BTreeSet::new();
    let mut constants = Vec::new();

    for token in model.tokens()? {
        let mut name = names::screaming_snake(&token.id);
        while !minted.insert(name.clone()) {
            name.push('_');
        }

        let origin = format!("token `{}`", token.id);
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
    // The names the file takes for itself, which a schema may not also take:
    // `SCHEMAS` is a value, and so is a view's tuple-struct constructor, so a
    // schema of that name would collide with it. Read from where the emitter
    // writes them, so renaming one cannot leave this stale.
    let mut seen: BTreeMap<String, &str> = super::items::ALL
        .map(|name| (name.to_owned(), "the generated file"))
        .into();
    for class in &model.classes {
        if is_root(&class.identifier) {
            continue;
        }
        let name = &class.metadata.class_name;
        let identifier = class.identifier.as_str();

        // A class brings the trait its own accessors live on, except an applied
        // API schema, which has none: a class called `FooSchema` collides with
        // `Foo`'s trait, but never with `FooAPI`.
        let mut minted = vec![name.clone()];
        if !class.kind.is_applied_api_schema() {
            minted.push(trait_name(name));
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
    library: &doc::Symbols<'_>,
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
    let links = class_symbols(class, model, library);
    let accessors = class
        .local_properties()
        .filter(offers)
        .filter_map(|property| named(property.api_name(), property.spec_type).map(|a| (property, a)))
        .map(|(property, accessor)| lower_accessor(class, property, &accessor, by_value, &links))
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
        (Some(base), _) => root_trait(&base.identifier),
        (None, _) => syn::parse_quote! { ::openusd::usd::SchemaBase },
    };

    // The root the view answers to, then every ancestor whose accessors it
    // inherits.
    let view = view(class.kind);
    let inherited: Vec<syn::Path> = inherited.into_iter().flatten().collect();

    // What a class reflects reads as its own: the properties of an API schema
    // that every prim of this type carries anyway.
    let mut accessors: Vec<RustAccessor> = accessors;
    let mut reflected = Vec::new();
    for schema in &class.metadata.reflected_api_schemas {
        // TODO: reflect a schema another library declares. Its properties are
        // not in this model, so only what this run generates is reflected; a
        // caller reaches the rest by applying that schema to the prim.
        let Some(other) = model.classes.iter().find(|other| &other.identifier == schema) else {
            continue;
        };

        // A reflected accessor is the reflecting class's own, so it goes
        // wherever the rest of them go: nothing here marks it apart.
        let origin = other.origin.describe();
        let reflected_links = class_symbols(other, model, library);
        accessors.extend(
            other
                .local_properties()
                .filter_map(|property| named(property.api_name(), property.spec_type).map(|a| (property, a)))
                .map(|(property, accessor)| lower_accessor(other, property, &accessor, by_value, &reflected_links))
                .collect::<Result<Vec<_>, _>>()?,
        );
        reflected.push(Reflected {
            accessor: identifier(&names::snake_case(&other.metadata.class_name), &origin)?,
            view: identifier(&other.metadata.class_name, &origin)?,
        });
    }
    if !reflected.is_empty() {
        check_reflected(class, &accessors, &reflected)?;
    }

    let name = &class.metadata.class_name;
    let origin = class.origin.describe();
    Ok(RustClass {
        name: identifier(name, &origin)?,
        accessor_trait: match applied {
            true => None,
            false => Some(identifier(&trait_name(name), &origin)?),
        },
        parent,
        root: schema_root(&view),
        inherited,
        constant: constant_of(by_value, &class.identifier),
        allows_non_camel_case: name.contains('_'),
        kind_constant: kind_constant(class.kind),
        view,
        documentation: class
            .documentation
            .as_deref()
            .map(|text| doc::to_markdown(text, &links)),
        accessors,
        reflected,
    })
}

/// One property's accessor pair, named and typed.
fn lower_accessor(
    class: &Class,
    property: &Property,
    accessor: &Accessor,
    by_value: &BTreeMap<&str, &Ident>,
    symbols: &doc::Symbols<'_>,
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
        token,
        kind,
        custom: property.is_custom(),
        uniform: property.variability() == sdf::Variability::Uniform
            && property.spec_type != sdf::SpecType::Relationship,
        documentation: documentation(property, symbols),
    })
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
        let tokens = super::ident(super::items::TOKENS);
        return quote! { #tokens::#name };
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

/// A reflected accessor landing on a name the class already offers.
///
/// The check [`check_methods`] runs is over what a class declares; what it
/// reflects arrives from another class, so the merged set is checked here. The
/// schemas name where each name came from: the class's own declaration, or the
/// schema it reflects.
fn check_reflected(class: &Class, accessors: &[RustAccessor], reflected: &[Reflected]) -> Result<(), Error> {
    // Everything the chain already offers, which is what `check_methods`
    // walked: a reflected name collides with an inherited one as surely as
    // with one the class declares itself.
    let mut seen: BTreeSet<String> = class
        .properties
        .iter()
        .filter(|property| !property.is_local)
        .flat_map(offered)
        .collect();

    for accessor in accessors {
        for method in [&accessor.getter, &accessor.creator] {
            if !seen.insert(method.to_string()) {
                let schemas = reflected.iter().map(|r| r.view.to_string()).collect::<Vec<_>>();
                return Err(class.violation(Violation::MethodCollision {
                    method: method.to_string(),
                    first: class.identifier.clone(),
                    second: tf::Token::from(schemas.join(", ")),
                }));
            }
        }
    }
    Ok(())
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

/// What the C++ names a library's documentation mentions point at here.
///
/// Upstream's prose names upstream's API — `GetExtentAttr()`, `UsdGeomMesh` —
/// and the reader of the generated crate has neither. What this library emits
/// for those is known here, so the two are paired and the documentation reads
/// as links to the Rust that answers.
///
/// This is the half that holds for the whole library: the classes it declares,
/// under both spellings upstream writes them, and the accessors that one class
/// alone declares. A name several classes declare is left to
/// [`class_symbols`], which answers it against the class being documented.
///
/// TODO: a class of another library is named here as plainly as one of this
/// one, and goes unlinked. `Externs` holds where those libraries' views live,
/// so their classes could be paired too.
fn library_symbols(model: &Library) -> doc::Symbols<'static> {
    let mut symbols = doc::Symbols::default();

    let prefix = names::proper_case(&model.name);

    // A name is paired only where one class declares it; `None` marks one that
    // several do, which stays here so a later class cannot revive it.
    let mut accessors: BTreeMap<String, Option<String>> = BTreeMap::new();
    for class in model.classes.iter().filter(|class| !is_root(&class.identifier)) {
        for (cpp, markdown) in accessor_links(class, &prefix) {
            accessors
                .entry(cpp)
                .and_modify(|found| *found = None)
                .or_insert(Some(markdown));
        }
    }
    for (cpp, markdown) in accessors {
        if let Some(markdown) = markdown {
            symbols.insert(cpp, markdown);
        }
    }

    // Upstream names a class by its library and its class name; the same class
    // is that class name alone here. Both spellings appear in its prose, the
    // bare one far more often.
    //
    // TODO: the prefix is `libraryPrefix` where a library declares one, which
    // `load` drops for want of a reader. This is the fallback upstream applies
    // without it (`usdGenSchema._GetLibPrefix`), so a library declaring one
    // would be paired under the wrong spelling.
    for class in &model.classes {
        if is_root(&class.identifier) {
            continue;
        }
        // A view is named where the documentation is, so its own name reaches
        // it and the link needs no path.
        let view = &class.metadata.class_name;
        let link = doc::link(view, None);
        symbols.insert(format!("{prefix}{view}"), link.clone());

        // The bare name is paired only where it is a coined one, which an
        // interior capital is what makes it: upstream writes `PointInstancer`
        // meaning the schema, but `Curves` for a RIB statement and for what
        // Maya calls a NURBS curve, and a word that is ordinary English is
        // ordinary English as often as it is a class.
        if view.chars().skip(1).any(char::is_uppercase) {
            symbols.insert(view.clone(), link);
        }
    }
    symbols
}

/// What those names point at when the documentation is `class`'s own.
///
/// A method name alone is ambiguous across a library: four of `usdGeom`'s
/// shapes declare a `radius`. Documentation on a class means that class's
/// property, so its own chain answers first and nearest wins; what is left
/// falls through to the library, which pairs only unambiguous names.
// TODO(perf): every class re-walks its chain and re-pairs what `library_symbols`
// already paired once, each base found by a scan of the library. The pairs are a
// pure function of the class, so they could be built per class in one pass and
// read here, or built in parallel.
fn class_symbols<'a>(class: &Class, model: &Library, library: &'a doc::Symbols<'a>) -> doc::Symbols<'a> {
    let mut symbols = doc::Symbols::layered(library);
    let prefix = names::proper_case(&model.name);
    let chain = iter::once(class).chain(
        class
            .bases
            .iter()
            .filter_map(|base| model.classes.iter().find(|other| other.identifier == base.identifier)),
    );
    for owner in chain {
        for (cpp, markdown) in accessor_links(owner, &prefix) {
            symbols.insert(cpp, markdown);
        }
    }
    symbols
}

/// Every accessor a class emits, as the C++ names upstream calls it by and the
/// Markdown that links it here.
///
/// A property redeclared to change a fallback contributes none: its accessor is
/// the ancestor's, which that ancestor pairs. Each is paired under its bare
/// name and under the class-qualified one upstream also writes, so a reference
/// naming the class it means is answered by that class.
fn accessor_links<'a>(owner: &'a Class, prefix: &str) -> impl Iterator<Item = (String, String)> + 'a {
    let applied = owner.kind.is_applied_api_schema();
    // An applied API schema writes its accessors on the view; everything else
    // puts them on the trait a view derives them from.
    let qualifier = match applied {
        true => owner.metadata.class_name.clone(),
        false => trait_name(&owner.metadata.class_name),
    };
    let class = owner.metadata.class_name.clone();
    // Upstream qualifies with its own spelling of the class, this crate with its.
    let qualified = format!("{prefix}{class}");

    owner
        .local_properties()
        .filter(move |property| applied || !shadows_an_ancestor(owner, property))
        .filter_map(move |property| {
            let accessor = named(property.api_name(), property.spec_type)?;
            let suffix = match property.spec_type {
                sdf::SpecType::Relationship => "Rel",
                _ => "Attr",
            };
            let name = names::proper_case(property.api_name()?);

            // A reader the library writes by hand is no method of this crate's,
            // so only the creator is paired for it.
            let mut pairs = vec![(format!("Create{name}{suffix}"), accessor.creator)];
            if !property.api.custom_get {
                pairs.push((format!("Get{name}{suffix}"), accessor.getter));
            }

            // Each property's pairs name the class they came from, so the two
            // names travel with them rather than being borrowed per pair.
            let (qualifier, class, qualified) = (qualifier.clone(), class.clone(), qualified.clone());
            Some(pairs.into_iter().flat_map(move |(cpp, method)| {
                let markdown = doc::link(&method, Some(&format!("{qualifier}::{method}")));
                [
                    (format!("{qualified}::{cpp}"), markdown.clone()),
                    (format!("{class}::{cpp}"), markdown.clone()),
                    (cpp, markdown),
                ]
            }))
        })
        .flatten()
}

/// The trait a class's accessors live on.
///
/// The schema's own name belongs to the view a prim is read through, so the
/// trait behind it takes the `Schema` suffix — `Mesh` and `MeshSchema`,
/// `Gprim` and `GprimSchema` — whether the schema is one a prim can be or a
/// base of ones it can.
fn trait_name(class_name: &str) -> String {
    format!("{class_name}Schema")
}

/// The trait a base contributes to a view that derives from it, or `None` where
/// the base is one of the roots, which have no accessors and are named directly.
fn base_trait(class: &Class, base: &Base, model: &Library, externs: &Externs) -> Result<Option<syn::Path>, Error> {
    if is_root(&base.identifier) {
        return Ok(None);
    }

    let origin = class.origin.describe();
    let inherited = identifier(&trait_name(&base.class_name), &origin)?;
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

/// What a prim of this kind is viewed through.
///
/// Every kind names one, so a class carries a view rather than perhaps
/// carrying one: the schema roots are what would have none, and [`is_root`]
/// keeps those from being lowered at all. An abstract base that is not a root
/// is viewed as any unapplied schema is, which is what it is — C++ recognises
/// the two alike, `UsdAPISchemaBase::_IsCompatible` asking nothing of a prim
/// until the schema is one that gets applied to it.
fn view(kind: usd::SchemaKind) -> View {
    match kind {
        usd::SchemaKind::AbstractTyped => View::Abstract,
        usd::SchemaKind::ConcreteTyped => View::Concrete,
        usd::SchemaKind::AbstractBase | usd::SchemaKind::NonAppliedApi => View::Plain,
        usd::SchemaKind::SingleApplyApi => View::SingleApply,
        usd::SchemaKind::MultipleApplyApi => View::MultipleApply,
    }
}

/// The root trait a view answers to: a prim type and a base of prim types are
/// typed schemas, and everything else here is something applied to a prim.
///
/// Every shape names its own side of that split, so adding one is a question
/// asked here.
fn schema_root(view: &View) -> syn::Path {
    match view {
        View::Concrete | View::Abstract => syn::parse_quote! { ::openusd::usd::Typed },
        View::Plain | View::SingleApply | View::MultipleApply => {
            syn::parse_quote! { ::openusd::usd::APISchemaBase }
        }
    }
}

/// The `usd::SchemaKind` constant a view reports itself as, and a declaration
/// records its kind as.
pub(super) fn kind_constant(kind: usd::SchemaKind) -> syn::Path {
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
///
/// Asked of the schema family, as [`is_root`] is, so the name that reaches here
/// answers as the root it spells: a class deriving from a versioned `Typed`
/// reaches [`Typed`](openusd::usd::Typed) like any other.
fn root_trait(name: &tf::Token) -> syn::Path {
    let (family, _) = usd::SchemaRegistry::parse_schema_family_and_version(name);
    match family.as_str() {
        TYPED => syn::parse_quote! { ::openusd::usd::Typed },
        API_SCHEMA_BASE => syn::parse_quote! { ::openusd::usd::APISchemaBase },
        _ => syn::parse_quote! { ::openusd::usd::SchemaBase },
    }
}

/// A property's documentation: what the schema said, then what the property is.
fn documentation(property: &Property, symbols: &doc::Symbols<'_>) -> String {
    // What the schema wrote arrives wrapped, from `to_markdown`; the sentence
    // about the declaration is this crate's own and is wrapped here, so every
    // line of a doc comment holds to one width.
    let declared = doc::wrap(&declaration(property));
    match property.documentation() {
        Some(text) => format!("{}\n\n{declared}", doc::to_markdown(text, symbols)),
        None => declared,
    }
}

/// A property as a schema author would write it, then what it reads back as.
fn declaration(property: &Property) -> String {
    let mut text = format!("Declared `{}`.", declared_as(property));

    let allowed = property.allowed_tokens();
    if !allowed.is_empty() {
        // An allowed value can be the empty string, which upstream
        // `usdRender` writes; an empty code span is no spelling of it, so it
        // reads as the two quotes a schema author would write.
        let listed: Vec<String> = allowed
            .iter()
            .map(|token| match token.as_str().is_empty() {
                true => "`\"\"`".to_owned(),
                false => format!("`{token}`"),
            })
            .collect();
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
