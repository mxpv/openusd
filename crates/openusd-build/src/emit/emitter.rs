//! The Rust a lowered schema library is written as.
//!
//! Everything here reads [`RustLibrary`](super::lower::RustLibrary) and writes
//! Rust. What it decides is what that Rust looks like: which construct carries
//! an accessor, how a call chain is laid out, where a doc comment goes. Those
//! are real decisions, and a wrong one compiles and behaves wrongly — writing
//! syntax is not the same as writing correct code.
//!
//! What it does not do is resolve a name or read a schema. Every identifier,
//! path and membership was settled by [`lower`](super::lower) and arrives
//! already decided, so nothing here can disagree with the rest of the pipeline
//! about what a schema declares or what anything is called. That is the
//! boundary worth relying on; the code it writes is held to its own tests.
//! [`family`](super::family) writes the schema data on the same terms.
//!
//! The output is built as tokens rather than as text. `quote!` writes it in the
//! shape it will take, `syn` parses it back so anything malformed fails here
//! rather than in a consumer's build, and `prettyplease` lays it out without an
//! external formatter. What that buys over writing strings is that an
//! identifier, a path and a string literal are different things, so none can be
//! mistaken for another.
//!
//! Documentation a schema wrote arrives as text and is written one `#[doc]`
//! attribute per line: `prettyplease` writes a value verbatim after the `///`,
//! hence the space each line opens with, and lays a value that holds newlines
//! out as a `/** … */` block instead. What this crate says about the code it
//! writes is a doc comment in the `quote!` itself.

use std::iter;

use openusd::usd;
use proc_macro2::TokenStream;
use quote::quote;

use super::{ident, items};

use super::lower::{
    AccessorTrait, Constant, PropertyKind, Reflected, RustAccessor, RustClass, RustLibrary, kind_constant, schema_root,
};
use crate::doc;

/// The whole generated file: the tokens its schemas name things by, what
/// registers them, and a trait and a view per schema.
pub fn library(library: &RustLibrary, declarations: &TokenStream) -> TokenStream {
    let name = library.library.as_str();
    let constants = library.tokens.iter().map(|constant| {
        let Constant {
            name,
            value,
            documentation,
        } = constant;
        let documentation = documentation.lines().map(|line| format!(" {line}"));
        quote! {
            #(#[doc = #documentation])*
            pub const #name: &str = #value;
        }
    });
    let classes = library.classes.iter().map(|class| {
        let accessors = accessor_trait(class);
        let view = view(class);
        quote! {
            #accessors
            #view
        }
    });

    let tokens = ident(items::TOKENS);
    let library_name = ident(items::LIBRARY_NAME);

    quote! {
        /// The strings these schemas name things by.
        ///
        /// A token's value is what a stage actually reads; the constant is a
        /// name for it, so an application can say what it means instead of
        /// retyping a string.
        pub mod #tokens {
            #(#constants)*
        }

        /// The library these schemas belong to, as their manifest records it.
        pub const #library_name: &str = #name;

        #declarations
        #(#classes)*
    }
}

/// A schema's documentation as the doc comment above its trait and its view,
/// followed by whatever `note` the two say for themselves.
fn documented(class: &RustClass, note: &str) -> TokenStream {
    let own = class.documentation.as_deref().unwrap_or_default();
    // A blank line parts the two, where both have something to say.
    let separator = (!own.is_empty() && !note.is_empty()).then_some("");
    let lines = own
        .lines()
        .chain(separator)
        .chain(note.lines())
        .map(|line| format!(" {line}"));
    quote! { #(#[doc = #lines])* }
}

/// What a view says about where its accessors are, since reaching one means
/// having the trait that declares it in scope.
///
/// The schema's own documentation is upstream's and describes the schema, which
/// the trait and the view share; this is what parts them, and is why a reader
/// landing on either knows which to import.
fn accessor_note(class: &RustClass) -> String {
    // An applied API schema writes its accessors on the view, there being no
    // trait to derive from, so a caller needs nothing else in scope.
    let Some(own) = &class.accessor_trait else {
        return String::new();
    };

    let own = doc::link(&own.name.to_string(), None);
    let inherited: Vec<String> = class.inherited.iter().map(linked).collect();
    let text = match (class.accessors.is_empty(), inherited.is_empty()) {
        // A schema that declares no property and derives from none of its own
        // has nothing to reach, so it says nothing about reaching it.
        (true, true) => return String::new(),
        (true, false) => format!(
            "Its accessors are those of the classes behind it, on {}, which a caller has to have in \
             scope to reach one.",
            listed(&inherited)
        ),
        (false, true) => format!("Its accessors live on {own}, which a caller has to have in scope to reach one."),
        (false, false) => format!(
            "A property is reached through the trait that declares it, which a caller has to have in \
             scope. This schema's own are on {own}; the rest come from the classes behind it, on {}.",
            listed(&inherited)
        ),
    };
    format!("# Accessors\n\n{}", doc::wrap(&text))
}

/// What the trait says for itself, which is what it is for: the accessors a
/// view carries, held apart so that a schema deriving from this one carries
/// them too.
fn trait_note(class: &RustClass) -> String {
    // A trait with no accessor of its own carries nothing to say this about; it
    // is there for a view to derive the ones behind it through.
    if class.accessors.is_empty() {
        return String::new();
    }

    let name = doc::link(&class.name.to_string(), None);
    doc::wrap(&format!(
        "The accessors {name} carries. They live on a trait so that a schema deriving from this one \
         carries them too."
    ))
}

/// A trait as a link, whatever module it came from: the name a reader sees,
/// and the path that reaches it.
fn linked(path: &syn::Path) -> String {
    let name = match path.segments.last() {
        Some(segment) => segment.ident.to_string(),
        None => return String::new(),
    };
    // A trait of this library is named where the view is, so its own name
    // reaches it; one from another module needs the path spelled out.
    if path.segments.len() == 1 && path.leading_colon.is_none() {
        return doc::link(&name, None);
    }

    let leading = match path.leading_colon.is_some() {
        true => "::",
        false => "",
    };
    let full: Vec<String> = path.segments.iter().map(|segment| segment.ident.to_string()).collect();
    doc::link(&name, Some(&format!("{leading}{}", full.join("::"))))
}

/// Names in a sentence, the last joined with `and`.
fn listed(names: &[String]) -> String {
    match names.split_last() {
        Some((last, [])) => last.clone(),
        Some((last, rest)) => format!("{} and {last}", rest.join(", ")),
        None => String::new(),
    }
}

/// The trait a class's own accessors live on.
///
/// Its supertrait is the parent's, so a view reaching for an inherited property
/// finds it without this class restating it, and a class with no accessors of
/// its own still earns a trait: what it offers is everything behind it.
fn accessor_trait(class: &RustClass) -> TokenStream {
    let Some(AccessorTrait { name, parent }) = &class.accessor_trait else {
        return TokenStream::new();
    };
    let documentation = documented(class, &trait_note(class));
    let allow = allow_non_camel_case(class);
    let methods = class.accessors.iter().map(|accessor| method(accessor, false));
    // A reflected schema's own view is one method away, for what it offers
    // beyond its properties.
    let reflected = class.reflected.iter().map(|reflected| {
        let Reflected { accessor, view } = reflected;
        let documentation = format!(" Views the prim through `{view}`, whose properties this schema carries.");
        quote! {
            #[doc = #documentation]
            fn #accessor(&self) -> #view {
                #view::from_prim_unchecked(self.prim().clone())
            }
        }
    });

    quote! {
        #documentation
        #allow
        pub trait #name: #parent {
            #(#reflected)*
            #(#methods)*
        }
    }
}

/// What lets a versioned schema keep the name its identifier gives it.
///
/// `Cylinder_1` is what the registry knows the schema as and what a schema
/// author reads, so the view is called that too rather than being respelled
/// into a camel-case name that matches nothing.
fn allow_non_camel_case(class: &RustClass) -> TokenStream {
    match class.name.to_string().contains('_') {
        true => quote! {
            #[allow(
                non_camel_case_types,
                reason = "the schema's identifier carries its version, and the view is named after it"
            )]
        },
        false => TokenStream::new(),
    }
}

/// The struct a prim is viewed through: what it holds, what reaches the prim
/// inside it, and every trait it implements.
fn view(class: &RustClass) -> TokenStream {
    let name = &class.name;
    let documentation = documented(class, &accessor_note(class));
    let allow = allow_non_camel_case(class);
    let kind = kind_constant(class.kind);
    let constructors = constructors(class);

    // A multiple-apply view carries the instance name it was applied under
    // beside the prim; every other kind is the prim alone.
    let (declaration, prim) = match class.kind.is_multiple_apply_api_schema() {
        true => (
            quote! {
                pub struct #name {
                    prim: ::openusd::usd::Prim,
                    name: ::openusd::tf::Token,
                }
            },
            quote! { &self.prim },
        ),
        false => (quote! { pub struct #name(::openusd::usd::Prim); }, quote! { &self.0 }),
    };

    // An applied API schema is never derived from, so its accessors are written
    // on the view rather than on a trait nothing would implement. A class with
    // a trait puts them all there instead, so this is empty for it.
    let inherent = class
        .accessor_trait
        .is_none()
        .then(|| class.accessors.iter().map(|accessor| method(accessor, true)))
        .into_iter()
        .flatten();
    let own = class.accessor_trait.iter().map(|own| {
        let own = &own.name;
        quote! { impl #own for #name {} }
    });
    let root = schema_root(class.kind);
    let answers_to = iter::once(&root)
        .chain(&class.inherited)
        .map(|path| quote! { impl #path for #name {} });

    quote! {
        #documentation
        #allow
        #[derive(::std::clone::Clone, ::std::fmt::Debug)]
        #declaration

        impl #name {
            #constructors
            #(#inherent)*
        }

        impl ::openusd::usd::SchemaBase for #name {
            const KIND: ::openusd::usd::SchemaKind = #kind;

            fn prim(&self) -> &::openusd::usd::Prim {
                #prim
            }
        }

        impl ::std::ops::Deref for #name {
            type Target = ::openusd::usd::Prim;

            fn deref(&self) -> &Self::Target {
                #prim
            }
        }

        #(#own)*
        #(#answers_to)*
    }
}

/// What views a prim as the schema, and what authors it.
///
/// Every kind is constructed from a prim the same way, by
/// `from_prim_unchecked`, which is what lets a schema that reflects another
/// reach its view without knowing what kind it is. Where a prim can be asked
/// whether it is one, a checked constructor sits beside it.
///
/// A prim type is defined at a path and recognised by what a prim is; a base of
/// prim types is recognised the same way, but defines none, being no type a
/// prim carries. An applied API schema is applied to a prim already there and
/// recognised by what it carries, under an instance name where the schema takes
/// one. Anything else is a view over whatever prim a caller hands it.
fn constructors(class: &RustClass) -> TokenStream {
    let constant = &class.constant;

    match class.kind {
        // Both are recognised by what a prim is, which is one question however
        // far up the chain it is asked: a prim of a type under `Gprim` is a
        // `Gprim`, as one of type `Sphere` is a `Sphere`. Only authoring parts
        // them, a base of prim types naming nothing a prim can be defined as.
        usd::SchemaKind::ConcreteTyped | usd::SchemaKind::AbstractTyped => {
            let define = class.kind.is_concrete().then(|| {
                quote! {
                    /// Defines a prim of this schema at `path` and views it.
                    pub fn define(
                        stage: &::openusd::usd::Stage,
                        path: impl ::openusd::sdf::IntoPath,
                    ) -> ::openusd::Result<Self> {
                        ::std::result::Result::Ok(Self(stage.define_typed_prim(path, #constant)?))
                    }
                }
            });
            quote! {
                /// Views `prim` as this schema without asking whether it is one.
                ///
                /// Unchecked of the schema, not of memory: nothing here is
                /// `unsafe`, and a prim of another type simply answers nothing
                /// for the properties this schema declares.
                /// [`from_prim`](Self::from_prim) is the constructor that asks.
                pub fn from_prim_unchecked(prim: ::openusd::usd::Prim) -> Self {
                    Self(prim)
                }

                #define

                /// Views `prim` as this schema, or `None` where it is not one.
                ///
                /// The stage's registry is what answers, so a prim from a stage
                /// opened without this library's family registered is never one.
                pub fn from_prim(
                    prim: ::openusd::usd::Prim,
                ) -> ::openusd::Result<::std::option::Option<Self>> {
                    ::std::result::Result::Ok(prim.is_a(#constant)?.then_some(Self(prim)))
                }

                /// Views the prim at `path` as this schema, or `None` where it
                /// is not one — [`from_prim`](Self::from_prim) over the prim
                /// `path` names.
                pub fn get(
                    stage: &::openusd::usd::Stage,
                    path: impl ::openusd::sdf::IntoPath,
                ) -> ::openusd::Result<::std::option::Option<Self>> {
                    Self::from_prim(stage.prim(path)?)
                }
            }
        }
        usd::SchemaKind::SingleApplyApi => quote! {
            /// Views `prim` as this schema whether or not it carries it.
            ///
            /// Unchecked of the schema, not of memory: nothing here is
            /// `unsafe`, and a prim that does not carry this schema simply
            /// answers nothing for the properties it declares.
            /// [`from_prim`](Self::from_prim) is the constructor that asks.
            pub fn from_prim_unchecked(prim: ::openusd::usd::Prim) -> Self {
                Self(prim)
            }

            /// Applies the schema to `prim` and views it.
            pub fn apply(prim: &::openusd::usd::Prim) -> ::openusd::Result<Self> {
                ::std::result::Result::Ok(Self(prim.clone().apply_api(#constant)?))
            }

            /// Whether the schema may be applied to `prim`.
            pub fn can_apply(
                prim: &::openusd::usd::Prim,
            ) -> ::std::result::Result<(), ::openusd::usd::ApplyApiError> {
                prim.can_apply_api(#constant)
            }

            /// Views `prim` as this schema, or `None` where it does not carry
            /// it.
            pub fn from_prim(
                prim: ::openusd::usd::Prim,
            ) -> ::openusd::Result<::std::option::Option<Self>> {
                ::std::result::Result::Ok(prim.has_api_schema(#constant)?.then_some(Self(prim)))
            }

            /// Views the prim at `path` as this schema, or `None` where it does
            /// not carry it — [`from_prim`](Self::from_prim) over the prim
            /// `path` names.
            pub fn get(
                stage: &::openusd::usd::Stage,
                path: impl ::openusd::sdf::IntoPath,
            ) -> ::openusd::Result<::std::option::Option<Self>> {
                Self::from_prim(stage.prim(path)?)
            }
        },
        usd::SchemaKind::MultipleApplyApi => quote! {
            /// Views `prim` as this schema applied under `name`, whether or not
            /// it is.
            ///
            /// Unchecked of the schema, not of memory: nothing here is
            /// `unsafe`, and a prim that does not carry this schema under this
            /// name simply answers nothing for the properties it declares.
            /// [`get_instance`](Self::get_instance) is the constructor that
            /// asks.
            pub fn from_prim_unchecked(
                prim: ::openusd::usd::Prim,
                name: impl ::std::convert::Into<::openusd::tf::Token>,
            ) -> Self {
                Self { prim, name: name.into() }
            }

            /// The instance name this view reads its properties under.
            pub fn name(&self) -> &::openusd::tf::Token {
                &self.name
            }

            /// Applies the schema to `prim` under `name` and views it.
            pub fn apply(
                prim: &::openusd::usd::Prim,
                name: impl ::std::convert::Into<::openusd::tf::Token>,
            ) -> ::openusd::Result<Self> {
                let name = name.into();
                let applied =
                    ::openusd::usd::SchemaRegistry::make_applied_name(#constant, name.as_str());
                ::std::result::Result::Ok(Self { prim: prim.clone().apply_api(applied)?, name })
            }

            /// Views `prim` as this schema applied under `name`, or `None`
            /// where it does not carry it.
            pub fn get_instance(
                prim: &::openusd::usd::Prim,
                name: impl ::std::convert::Into<::openusd::tf::Token>,
            ) -> ::openusd::Result<::std::option::Option<Self>> {
                let name = name.into();
                let applied =
                    ::openusd::usd::SchemaRegistry::make_applied_name(#constant, name.as_str());
                let carried = prim.has_api_schema(applied)?;
                ::std::result::Result::Ok(carried.then(|| Self { prim: prim.clone(), name }))
            }

            /// Whether the schema may be applied to `prim` under `name`.
            pub fn can_apply(
                prim: &::openusd::usd::Prim,
                name: &str,
            ) -> ::std::result::Result<(), ::openusd::usd::ApplyApiError> {
                prim.can_apply_api(
                    ::openusd::usd::SchemaRegistry::make_applied_name(#constant, name),
                )
            }

            /// Every instance of this schema applied to `prim`.
            pub fn get_all(prim: &::openusd::usd::Prim) -> ::openusd::Result<::std::vec::Vec<Self>> {
                let mut found = ::std::vec::Vec::new();
                for applied in prim.api_schemas()? {
                    let (schema, instance) =
                        ::openusd::usd::SchemaRegistry::type_name_and_instance(&applied);
                    let mine = instance.filter(|_| schema.as_str() == #constant);
                    if let ::std::option::Option::Some(name) = mine {
                        found.push(Self { prim: prim.clone(), name });
                    }
                }
                ::std::result::Result::Ok(found)
            }
        },
        // An abstract base is no root here — a root is never lowered — so it
        // is viewed as any schema that is applied to nothing is.
        usd::SchemaKind::AbstractBase | usd::SchemaKind::NonAppliedApi => quote! {
            /// Views `prim` as this schema, which any prim can be viewed as.
            ///
            /// Unchecked of the schema, not of memory: nothing here is
            /// `unsafe`. This schema is applied to no prim and names no prim
            /// type, so there is nothing to ask about one — which is why it has
            /// no constructor that asks.
            pub fn from_prim_unchecked(prim: ::openusd::usd::Prim) -> Self {
                Self(prim)
            }
        },
    }
}

/// One property's accessor pair, written where its class puts them:
/// `inherent` on the view itself, otherwise as defaults of its trait.
fn method(accessor: &RustAccessor, inherent: bool) -> TokenStream {
    let RustAccessor {
        getter,
        creator,
        token,
        instanced,
        documentation,
        ..
    } = accessor;

    // A multiple-apply schema's property is named by a template, and the view
    // fills it in with the instance name it carries.
    let token = match instanced {
        true => quote! {
            ::openusd::usd::SchemaRegistry::make_multiple_apply_name_instance(#token, self.name.as_str())
        },
        false => token.clone(),
    };

    let visibility = if inherent {
        quote! { pub }
    } else {
        TokenStream::new()
    };
    // A trait default reaches the prim through `SchemaBase`, which its own
    // supertrait bound brings along. An inherent method cannot: the generated
    // file carries no `use`, so a trait the consumer's module has not imported
    // is not in scope there, however the type implements it. Those reach the
    // prim through the view's own `Deref` instead.
    let prim = if inherent {
        quote! { self }
    } else {
        quote! { self.prim() }
    };

    // The creator authors what the schema declared, not what a bare property
    // would default to: a stage reading either back has no schema to ask.
    let (kind, reader, mut declared) = match &accessor.kind {
        PropertyKind::Relationship => (
            quote! { ::openusd::usd::Relationship },
            quote! { relationship },
            quote! { #prim.create_relationship(#token)? },
        ),
        PropertyKind::Attribute { type_constant } => (
            quote! { ::openusd::usd::Attribute },
            quote! { attribute },
            quote! { #prim.create_attribute(#token, #type_constant)? },
        ),
    };
    // Authoring a property leaves it `custom`, as C++ `CreateAttribute` does,
    // so a schema's own property is the one that has to say it is not.
    let custom = accessor.custom;
    declared = quote! { #declared.set_custom(#custom)? };
    if accessor.uniform {
        declared = quote! { #declared.set_variability(::openusd::sdf::Variability::Uniform)? };
    }

    let documentation = documentation.lines().map(|line| format!(" {line}"));
    let read = if accessor.custom_get {
        TokenStream::new()
    } else {
        quote! {
            #(#[doc = #documentation])*
            #visibility fn #getter(&self) -> #kind {
                #prim.#reader(#token)
            }
        }
    };

    quote! {
        #read

        /// Authors the property as the schema declares it, and returns it.
        #visibility fn #creator(&self) -> ::openusd::Result<#kind> {
            ::std::result::Result::Ok(#declared)
        }
    }
}
