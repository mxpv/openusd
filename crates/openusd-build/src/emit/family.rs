//! The declaration table a library's schema data is written as.
//!
//! This reads [`usd::SchemaFamily`] and nothing else. Which constructor carries
//! a value, and how the call chain is laid out, are decided here — and a wrong
//! choice is a table that compiles and registers the wrong thing, which is what
//! `tests/values.rs` compiles the output to catch.
//!
//! What is not decided here is what a schema declares: the declarations arrive
//! settled, and nothing in this module resolves a name or reads a schema again.
//!
//! [`emitter`](super::emitter) writes the views beside it, from the lowered
//! Rust model rather than from these declarations, so neither can reinterpret
//! the other's half.

use openusd::{sdf, tf, usd};
use proc_macro2::TokenStream;
use quote::quote;

use super::{ident, items, lower, value};
use crate::error::Error;

/// This library's schema data, as the declaration table a registry takes.
///
/// The data is the table: nothing is serialized and nothing is parsed back, so
/// registering a family costs the values it builds and no more. What cannot be
/// written as a `const` is the value of a field — only a string, a token and
/// their arrays can be — so anything else arrives as a closure, which a
/// `static` can hold because a non-capturing closure is a function pointer.
pub(super) fn declarations(family: &usd::SchemaFamily<'_>) -> Result<TokenStream, Error> {
    let schemas = family.schemas().iter().map(schema).collect::<Result<Vec<_>, Error>>()?;
    let schemas_const = ident(items::SCHEMAS);
    let library_name = ident(items::LIBRARY_NAME);

    Ok(quote! {
        /// The schemas this library declares, ready to register.
        ///
        /// Hand it to
        /// [`SchemaRegistryBuilder::register`](::openusd::usd::SchemaRegistryBuilder::register):
        /// a stage opened with the resulting registry resolves these schemas'
        /// fallbacks and answers `is_a` along their inheritance, and one opened
        /// without it knows nothing about them, so the typed constructors
        /// answer `None`.
        pub const #schemas_const: &::openusd::usd::SchemaFamily<'static> =
            &::openusd::usd::SchemaFamily::new(#library_name, &[#(#schemas),*]);
    })
}

/// One schema as the declaration a registry reads it from.
fn schema(decl: &usd::SchemaDecl<'_>) -> Result<TokenStream, Error> {
    let identifier = decl.identifier();
    let kind = lower::kind_constant(decl.kind());
    let properties = decl
        .declared_properties()
        .iter()
        .map(|property| self::property(identifier, property))
        .collect::<Result<Vec<_>, Error>>()?;
    let fields = fields(identifier, decl.declared_fields())?;

    let list = |names: &[&str]| (!names.is_empty()).then(|| quote! { &[#(#names),*] });
    let bases = list(decl.declared_bases()).map(|names| quote! { .bases(#names) });
    let applied = list(decl.declared_applied_api_schemas()).map(|names| quote! { .applied_api_schemas(#names) });
    let overrides =
        list(decl.declared_override_property_names()).map(|names| quote! { .override_property_names(#names) });
    let auto_apply = list(decl.declared_auto_apply_to()).map(|names| quote! { .auto_apply_to(#names) });
    let can_only = list(decl.declared_can_only_apply_to()).map(|names| quote! { .can_only_apply_to(#names) });
    let instance_names =
        list(decl.declared_allowed_instance_names()).map(|names| quote! { .allowed_instance_names(#names) });
    let fallbacks = list(decl.declared_fallback_types()).map(|names| quote! { .fallback_types(#names) });

    let prefix = decl
        .declared_property_namespace_prefix()
        .map(|prefix| quote! { .property_namespace_prefix(#prefix) });

    let restrictions = decl.declared_instance_restrictions();
    let restrictions = (!restrictions.is_empty()).then(|| {
        let entries = restrictions.iter().map(|(instance, allowed)| {
            quote! { (#instance, &[#(#allowed),*]) }
        });
        quote! { .instance_restrictions(&[#(#entries),*]) }
    });

    let properties = (!properties.is_empty()).then(|| quote! { .properties(&[#(#properties),*]) });
    let fields = (!fields.is_empty()).then(|| quote! { .fields(&[#(#fields),*]) });

    Ok(quote! {
        ::openusd::usd::SchemaDecl::new(#identifier, #kind)
            #bases
            #prefix
            #applied
            #overrides
            #auto_apply
            #can_only
            #restrictions
            #instance_names
            #fallbacks
            #properties
            #fields
    })
}

/// One property, under the name the schematics records it by.
fn property(schema: &str, decl: &usd::PropertyDecl<'_>) -> Result<TokenStream, Error> {
    let name = decl.name();
    let declaration = if let Some(type_name) = decl.type_name() {
        quote! { ::openusd::usd::PropertyDecl::attribute(#name, #type_name) }
    } else {
        quote! { ::openusd::usd::PropertyDecl::relationship(#name) }
    };
    // Stated either way rather than left to whichever the constructor defaults
    // to: the two kinds of property default differently, and a table reading as
    // correct only because of that would change meaning if either moved.
    let variability = if decl.is_uniform() {
        quote! { .uniform() }
    } else {
        quote! { .varying() }
    };
    let custom = decl.is_custom().then(|| quote! { .custom() });

    let fields = fields(schema, decl.declared_fields())?;
    let fields = (!fields.is_empty()).then(|| quote! { .fields(&[#(#fields),*]) });

    Ok(quote! { #declaration #variability #custom #fields })
}

/// The fields of a class prim or a property.
fn fields(schema: &str, fields: &[usd::Field<'_>]) -> Result<Vec<TokenStream>, Error> {
    fields.iter().map(|field| self::field(schema, field)).collect()
}

/// One field, written through whichever constructor carries its value.
fn field(schema: &str, field: &usd::Field<'_>) -> Result<TokenStream, Error> {
    let name = field.name();
    let value = field.value();
    Ok(match &value {
        sdf::Value::String(text) => quote! { ::openusd::usd::Field::string(#name, #text) },
        sdf::Value::StringVec(texts) => {
            let texts = texts.iter().map(String::as_str);
            quote! { ::openusd::usd::Field::strings(#name, &[#(#texts),*]) }
        }
        sdf::Value::Token(token) => {
            let token = token.as_str();
            quote! { ::openusd::usd::Field::token(#name, #token) }
        }
        sdf::Value::TokenVec(tokens) => {
            let tokens = tokens.iter().map(tf::Token::as_str);
            quote! { ::openusd::usd::Field::tokens(#name, &[#(#tokens),*]) }
        }
        other => {
            let built = value::value_expr(other).map_err(|kind| Error::UnwritableValue {
                schema: schema.to_owned(),
                field: name.to_owned(),
                kind: kind.into(),
            })?;
            quote! { ::openusd::usd::Field::new(#name, || #built) }
        }
    })
}
