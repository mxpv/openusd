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

use proc_macro2::TokenStream;
use quote::quote;

use super::{ident, items};

use super::lower::{Constant, PropertyKind, Reflected, RustAccessor, RustClass, RustLibrary, View};

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

/// A schema's documentation as the doc comment above its trait and its view.
fn documented(class: &RustClass) -> TokenStream {
    let lines = class
        .documentation
        .iter()
        .flat_map(|text| text.lines())
        .map(|line| format!(" {line}"));
    quote! { #(#[doc = #lines])* }
}

/// The trait a class's own accessors live on.
///
/// Its supertrait is the parent's, so a view reaching for an inherited property
/// finds it without this class restating it, and a class with no accessors of
/// its own still earns a trait: what it offers is everything behind it.
fn accessor_trait(class: &RustClass) -> TokenStream {
    let Some(name) = &class.accessor_trait else {
        return TokenStream::new();
    };
    let parent = &class.parent;
    let documentation = documented(class);
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
                #view::new(self.prim().clone())
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
    match class.allows_non_camel_case {
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
    let shape = &class.view;
    let name = &class.name;
    let documentation = documented(class);
    let allow = allow_non_camel_case(class);
    let kind = &class.kind_constant;
    let constructors = constructors(class, shape);

    // A multiple-apply view carries the instance name it was applied under
    // beside the prim; every other kind is the prim alone.
    let (declaration, prim) = match shape.is_multiple_apply() {
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
    let own = class.accessor_trait.iter().map(|own| quote! { impl #own for #name {} });
    let answers_to = class.memberships.iter().map(|path| quote! { impl #path for #name {} });

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
/// A prim type is defined at a path and recognised by what a prim is; a base of
/// prim types is recognised the same way, but defines none, being no type a
/// prim carries. An applied API schema is applied to a prim already there and
/// recognised by what it carries, under an instance name where the schema takes
/// one. Anything else is a view over whatever prim a caller hands it.
fn constructors(class: &RustClass, shape: &View) -> TokenStream {
    let constant = &class.constant;

    match shape {
        // Both are recognised by what a prim is, which is one question however
        // far up the chain it is asked: a prim of a type under `Gprim` is a
        // `Gprim`, as one of type `Sphere` is a `Sphere`. Only authoring parts
        // them, a base of prim types naming nothing a prim can be defined as.
        View::Concrete | View::Abstract => {
            let define = matches!(shape, View::Concrete).then(|| {
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
                /// Views `prim` as this schema, whatever it is.
                ///
                /// The prim is not checked; [`get`](Self::get) is the constructor
                /// that asks.
                pub fn new(prim: ::openusd::usd::Prim) -> Self {
                    Self(prim)
                }

                #define

                /// Views the prim at `path` as this schema, or `None` where it is
                /// not one.
                ///
                /// The stage's registry is what answers, so a stage opened without
                /// this library's family registered answers `None` for every prim.
                pub fn get(
                    stage: &::openusd::usd::Stage,
                    path: impl ::openusd::sdf::IntoPath,
                ) -> ::openusd::Result<::std::option::Option<Self>> {
                    let prim = stage.prim(path)?;
                    ::std::result::Result::Ok(prim.is_a(#constant)?.then_some(Self(prim)))
                }
            }
        }
        View::SingleApply => quote! {
            /// Views `prim` as this schema, whether or not it carries it.
            pub fn new(prim: ::openusd::usd::Prim) -> Self {
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

            /// Views the prim at `path` as this schema, or `None` where it does
            /// not carry it.
            pub fn get(
                stage: &::openusd::usd::Stage,
                path: impl ::openusd::sdf::IntoPath,
            ) -> ::openusd::Result<::std::option::Option<Self>> {
                let prim = stage.prim(path)?;
                ::std::result::Result::Ok(prim.has_api_schema(#constant)?.then_some(Self(prim)))
            }
        },
        View::MultipleApply => quote! {
            /// Views `prim` as this schema applied under `name`, whether or not
            /// it is.
            pub fn new(prim: ::openusd::usd::Prim, name: impl ::std::convert::Into<::openusd::tf::Token>) -> Self {
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
        View::Plain => quote! {
            /// Views `prim` as this schema.
            pub fn new(prim: ::openusd::usd::Prim) -> Self {
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
        documentation,
        ..
    } = accessor;

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
