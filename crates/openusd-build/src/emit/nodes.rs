//! Views of shader nodes, one per node a shader-definition layer declares.
//!
//! A node is a `Shader` authoring a particular `info:id`, so its view wraps the
//! shade library's `Shader` view and is recognised by that id. What it adds is
//! what the definition knows and a bare `Shader` does not: which inputs and
//! outputs the node takes, their types, and the value a renderer uses for an
//! input nothing authors.

use std::collections::BTreeMap;

use openusd::{tf, usda};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;

use super::lower::{self, Constant};
use super::{emitter, value};
use crate::doc;
use crate::error::Error;
use crate::names;
use crate::shader_defs::{Node, NodeLibrary, Port};
use crate::types;

/// The generated file for `library`, whose `Shader`, `Input` and `Output`
/// views live at `shade`.
pub fn nodes(library: &NodeLibrary, shade: &syn::Path) -> Result<String, Error> {
    // Two prims can name one view, `UsdFoo` and `Foo` alike: both would be
    // `Foo`, and a second definition of it would not compile.
    let mut views: BTreeMap<String, &str> = BTreeMap::new();
    for node in &library.nodes {
        let name = type_name(&node.prim_name);
        if let Some(first) = views.insert(name.clone(), &node.prim_name) {
            return Err(Error::ShaderDefs {
                path: library.path.clone(),
                cause: format!("`{first}` and `{}` would both be the view `{name}`", node.prim_name),
            });
        }
    }

    let tokens = constants(library)?;
    let by_value = lower::by_value(&tokens);
    let views = library
        .nodes
        .iter()
        .map(|node| view(library, node, shade, &by_value))
        .collect::<Result<Vec<_>, _>>()?;

    let tokens = emitter::tokens_module(&tokens);
    let file = quote! {
        #tokens

        #(#views)*
    };
    let source = library.path.file_name().map_or_else(
        || library.path.display().to_string(),
        |name| name.to_string_lossy().into_owned(),
    );
    super::render(file, &source)
}

/// One constant per distinct name the library's nodes use: each node's id and
/// each input and output's base name.
fn constants(library: &NodeLibrary) -> Result<Vec<Constant>, Error> {
    let mut by_value: BTreeMap<&str, String> = BTreeMap::new();
    for node in &library.nodes {
        by_value
            .entry(node.id.as_str())
            .or_insert_with(|| format!("the `info:id` of a `{}` shader", node.prim_name));
        for port in node.inputs.iter().chain(&node.outputs) {
            by_value
                .entry(&port.base_name)
                .or_insert_with(|| "an input or output a shader node declares".to_owned());
        }
    }

    let origin = library.path.display().to_string();
    let mut by_name: BTreeMap<String, &str> = BTreeMap::new();
    by_value
        .into_iter()
        .map(|(value, documentation)| {
            let name = names::screaming_snake(&names::token_id(value, true));
            if let Some(first) = by_name.insert(name.clone(), value) {
                return Err(Error::ShaderDefs {
                    path: library.path.clone(),
                    cause: format!("`{first}` and `{value}` would both be the constant `{name}`"),
                });
            }
            Ok(Constant {
                name: lower::identifier(&name, &origin)?,
                documentation: doc::wrap(&format!("`\"{value}\"`: {documentation}.")),
                value: value.to_owned(),
            })
        })
        .collect()
}

/// One node's view.
fn view(
    library: &NodeLibrary,
    node: &Node,
    shade: &syn::Path,
    by_value: &BTreeMap<&str, &Ident>,
) -> Result<TokenStream, Error> {
    let origin = format!("{}/{}", library.path.display(), node.prim_name);
    let invalid = |cause: String| Error::ShaderDefs {
        path: library.path.clone(),
        cause: format!("{}: {cause}", node.prim_name),
    };
    let name = lower::identifier(&type_name(&node.prim_name), &origin)?;
    let constant = |value: &str| lower::constant_of(by_value, &tf::Token::from(value));
    let id = constant(node.id.as_str());

    // The view's own methods keep their names; a port reaching one of them, or
    // two ports reaching one method, would make one of them unreachable.
    let mut methods: BTreeMap<String, String> = ["shader", "get", "define", "from_shader"]
        .iter()
        .map(|method| ((*method).to_owned(), "the view".to_owned()))
        .collect();
    let mut claim = |method: String, port: &str| match methods.insert(method.clone(), port.to_owned()) {
        Some(first) => Err(invalid(format!(
            "`{first}` and `{port}` would both be read by `{method}`"
        ))),
        None => lower::identifier(&method, &origin),
    };

    let mut accessors = Vec::new();
    let kinds = [
        ("inputs", "input", &node.inputs, quote! { #shade::Input }),
        ("outputs", "output", &node.outputs, quote! { #shade::Output }),
    ];
    for (namespace, kind, ports, handle) in kinds {
        let find = Ident::new(kind, Span::call_site());
        for declared in ports {
            let port = format!("{namespace}:{}", declared.base_name);
            let accessor = claim(format!("{}_{kind}", names::snake_case(&declared.base_name)), &port)?;
            let token = constant(&declared.base_name);
            let documentation = port_documentation(&port, declared);
            let documentation = super::doc_lines(&documentation);
            accessors.push(quote! {
                #(#[doc = #documentation])*
                pub fn #accessor(&self) -> #handle {
                    <#shade::Shader as #shade::Connectable>::#find(&self.0, #token)
                }
            });

            // An input reads back as the type it is declared with; an output
            // is what a connection reads, not a value the node holds.
            let Some(ty) = declared
                .type_name
                .kind()
                .and_then(types::rust_type)
                .filter(|_| kind == "input")
            else {
                continue;
            };
            let reader = claim(names::method_name(&declared.base_name), &port)?;
            // A value of another type is no value of this input, as a schema
            // attribute's typed read skips one, so the definition answers.
            let read = if let Some(fallback) = &declared.fallback {
                let fallback = value::value_expr(fallback)
                    .map_err(|kind| invalid(format!("{port} has a fallback of a kind no value spells: {kind:?}")))?;
                quote! {
                    match self.#accessor().attribute().get::<#ty>()? {
                        ::std::option::Option::Some(value) => ::std::result::Result::Ok(::std::option::Option::Some(value)),
                        ::std::option::Option::None => <#ty as ::std::convert::TryFrom<::openusd::sdf::Value>>::try_from(#fallback)
                            .map(::std::option::Option::Some)
                            .map_err(::std::convert::Into::into),
                    }
                }
            } else {
                quote! { self.#accessor().attribute().get::<#ty>() }
            };
            accessors.push(quote! {
                /// The input's value as the type it is declared with: what the
                /// shader authors, else the value the node's definition gives it.
                pub fn #reader(&self) -> ::openusd::Result<::std::option::Option<#ty>> {
                    #read
                }
            });
        }
    }

    let mut documentation = String::new();
    if let Some(text) = &node.documentation {
        documentation.push_str(&doc::to_markdown(text, &doc::Symbols::default()));
        documentation.push_str("\n\n");
    }
    documentation.push_str(&doc::wrap(&format!(
        "A `Shader` whose `info:id` is `{}`, as the `{}` library defines the node.",
        node.id, library.name
    )));
    let documentation = super::doc_lines(&documentation);

    Ok(quote! {
        #(#[doc = #documentation])*
        #[derive(::std::fmt::Debug, ::std::clone::Clone)]
        pub struct #name(#shade::Shader);

        impl #name {
            /// The `info:id` a shader of this node authors.
            pub const ID: &str = #id;

            /// Views `shader` as this node, or `None` where it authors another
            /// `info:id`.
            pub fn from_shader(shader: #shade::Shader) -> ::openusd::Result<::std::option::Option<Self>> {
                ::std::result::Result::Ok(
                    (shader.id()?.as_deref() == ::std::option::Option::Some(Self::ID)).then_some(Self(shader)),
                )
            }

            /// Views the prim at `path` as this node, or `None` where it is not
            /// a `Shader` of this node's `info:id`.
            pub fn get(
                stage: &::openusd::usd::Stage,
                path: impl ::openusd::sdf::IntoPath,
            ) -> ::openusd::Result<::std::option::Option<Self>> {
                match #shade::Shader::get(stage, path)? {
                    ::std::option::Option::Some(shader) => Self::from_shader(shader),
                    ::std::option::Option::None => ::std::result::Result::Ok(::std::option::Option::None),
                }
            }

            /// Defines a `Shader` at `path` authoring this node's `info:id`,
            /// and views it.
            pub fn define(stage: &::openusd::usd::Stage, path: impl ::openusd::sdf::IntoPath) -> ::openusd::Result<Self> {
                let shader = #shade::Shader::define(stage, path)?;
                shader.create_id_attr()?.set(::openusd::sdf::Value::token(Self::ID))?;
                ::std::result::Result::Ok(Self(shader))
            }

            /// The `Shader` this node is.
            pub fn shader(&self) -> &#shade::Shader {
                &self.0
            }

            #(#accessors)*
        }
    })
}

/// A node's Rust type name: its prim name without the `Usd` prefix every
/// upstream node carries, each `_`-separated part opening with a capital, so
/// `UsdPrimvarReader_float2` is `PrimvarReaderFloat2`.
fn type_name(prim_name: &str) -> String {
    prim_name
        .strip_prefix("Usd")
        .filter(|rest| rest.starts_with(char::is_uppercase))
        .unwrap_or(prim_name)
        .split('_')
        .map(names::proper_case)
        .collect()
}

/// What an input or output's accessor says about it: the definition's own
/// words, then how it is declared.
fn port_documentation(port: &str, declared: &Port) -> String {
    let mut declaration = format!("{} {port}", declared.type_name.serialization_name());
    if let Some(fallback) = &declared.fallback
        && let Ok(text) = usda::TextWriter::value_to_string(fallback)
    {
        declaration.push_str(&format!(" = {text}"));
    }
    let mut text = format!("Declared `{declaration}`.");
    text.push_str(&lower::allowed_values(&declared.allowed_tokens));
    if declared.interface_only {
        text.push_str(" It connects only to an interface input.");
    }
    let declaration = doc::wrap(&text);
    match &declared.documentation {
        Some(prose) => format!("{}\n\n{declaration}", doc::to_markdown(prose, &doc::Symbols::default())),
        None => declaration,
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    /// Two nodes whose prims name one view are refused rather than emitted
    /// twice.
    #[test]
    fn colliding_views_refused() {
        let node = |prim_name: &str, id: &str| Node {
            prim_name: prim_name.to_owned(),
            id: tf::Token::from(id),
            documentation: None,
            inputs: Vec::new(),
            outputs: Vec::new(),
        };
        let library = NodeLibrary {
            name: "testNodes".to_owned(),
            path: PathBuf::from("shaderDefs.usda"),
            layers: Vec::new(),
            nodes: vec![node("UsdFoo", "UsdFoo"), node("Foo", "Foo")],
        };
        match nodes(&library, &syn::parse_quote! { crate::shade }) {
            Err(Error::ShaderDefs { cause, .. }) => assert!(cause.contains("the view `Foo`"), "{cause}"),
            other => panic!("{:?}", other.map(|_| "emitted")),
        }
    }

    /// A node's type name drops the `Usd` prefix and capitalises each part.
    #[test]
    fn node_type_names() {
        assert_eq!(type_name("UsdPreviewSurface"), "PreviewSurface");
        assert_eq!(type_name("UsdUVTexture"), "UVTexture");
        assert_eq!(type_name("UsdPrimvarReader_float2"), "PrimvarReaderFloat2");
        assert_eq!(type_name("UsdTransform2d"), "Transform2d");
        assert_eq!(type_name("Usdish"), "Usdish", "a prefix is only one before a capital");
        assert_eq!(type_name("MyNode"), "MyNode");
    }
}
