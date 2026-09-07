//! Reading what a `schema.usda` declares.
//!
//! Composition stays the composition engine's job: inheritance, sublayers and
//! composed values already have one implementation, and codegen must not grow
//! a second. This module's whole responsibility is to open the stage and
//! extract what its layers *declare*, with the origin of each declaration. It
//! classifies nothing, resolves no inheritance and generates no names —
//! [`resolve`](crate::resolve) does that, over the stage this leaves behind.

use std::collections::{BTreeMap, HashMap};
use std::iter;
use std::path::Path;

use openusd::{ar, sdf, tf, usd};

use crate::Builder;
use crate::error::Error;
use crate::model::Origin;

/// The `/GLOBAL` prim every schema library configures itself through.
const GLOBAL: &str = "/GLOBAL";

/// An opened schema library: the stage its layers compose into, and what those
/// layers declare.
pub struct Source {
    /// The composed stage, which [`resolve`](crate::resolve) reads inheritance
    /// and effective property values from.
    pub stage: usd::Stage,
    /// The `libraryName` the root layer's `/GLOBAL` declares.
    pub library: String,
    /// Whether token identifiers keep the spelling the schema gave them.
    pub use_literal_identifiers: bool,
    /// Whether any layer asked for schema data only, with no Rust.
    pub skip_code_generation: bool,
    /// Every class any layer declares, in root-layer declaration order first.
    pub declarations: Vec<Declaration>,
    /// Every layer read, for a build script to watch.
    pub source_layers: Vec<String>,
}

/// One class prim, as the layer that declares it wrote it.
pub struct Declaration {
    /// The prim's name, which is the schema identifier.
    pub name: tf::Token,
    /// The library whose `/GLOBAL` covers the layer declaring it.
    pub library: String,
    /// Whether the root layer declares it, and so whether this run generates
    /// it. A class from a sublayer can be inherited from but is never
    /// regenerated.
    pub generated: bool,
    /// The names its `inheritPaths` targets, in authored order.
    pub bases: Vec<tf::Token>,
    /// Its `customData`, read but not interpreted.
    pub custom_data: CustomData,
    /// Its authored `typeName`.
    pub type_name: Option<tf::Token>,
    /// Its authored `apiSchemas` list op, whose mode validation checks.
    pub api_schemas: Option<sdf::TokenListOp>,
    /// Its documentation.
    pub documentation: Option<String>,
    /// The properties it declares itself.
    pub properties: Vec<PropertyDeclaration>,
    /// Every field authored on the prim, which validation checks against what
    /// a schematics may carry.
    pub fields: Vec<String>,
    /// Where it was declared.
    pub origin: Origin,
}

/// One property of a class prim, as the layer that declares it wrote it.
///
/// Only its `customData`, which steers the accessor this class generates.
/// Everything else about a property — its type, its fields, where the
/// declaration that wins lives — is a composed question, and
/// [`resolve`](crate::resolve) asks it of the stage.
pub struct PropertyDeclaration {
    /// The property's name, as declared and so without a namespace prefix.
    pub name: tf::Token,
    /// Its `customData`, read but not interpreted.
    pub custom_data: CustomData,
    /// Where it was declared, which a flattened layer no longer records.
    pub origin: Origin,
}

/// Opens `schema` and reads every declaration its layers carry.
///
/// The stage is built on a registry that knows nothing, so a class prim named
/// `Sphere` cannot pick up built-ins from a registry that already knows
/// `Sphere` — what C++ reaches for `USD_DISABLE_PRIM_DEFINITIONS_FOR_USDGENSCHEMA`
/// to get.
pub fn open(builder: &Builder, schema: &Path) -> Result<Source, Error> {
    let resolver = ar::DefaultResolver::with_search_paths(builder.search_paths.clone());
    let registry = usd::SchemaRegistryBuilder::empty()
        .build()
        .map_err(|source| Error::Core(source.into()))?;

    let stage = usd::Stage::builder()
        .resolver(resolver)
        .schema_registry(registry)
        .open(&schema.to_string_lossy())?;

    if let Some(error) = Error::composition(schema, &stage) {
        return Err(error);
    }

    let source_layers = stage.layer_stack();
    let root = stage.root_layer().identifier.clone();

    // The root layer first, so what this run generates leads the list.
    let mut globals = Vec::new();
    for identifier in iter::once(&root).chain(source_layers.iter().filter(|id| **id != root)) {
        let Some(layer) = stage.layer(identifier) else {
            continue;
        };
        globals.push((identifier, read_global(&layer)));
    }

    let skip_code_generation = globals.iter().any(|(_, global)| global.skip_code_generation);
    let use_literal_identifiers = globals.first().is_none_or(|(_, global)| global.use_literal_identifiers);

    // A layer with no `/GLOBAL` of its own belongs to whichever library
    // sublayered it; only its class prims matter.
    let libraries: HashMap<&String, &String> = globals
        .iter()
        .filter_map(|(identifier, global)| Some((*identifier, global.library.as_ref()?)))
        .collect();
    let library = libraries.get(&root).ok_or_else(|| Error::NoLibraryName {
        schema: schema.to_path_buf(),
    })?;

    let mut declarations = Vec::new();
    for (identifier, _) in &globals {
        let Some(layer) = stage.layer(identifier) else {
            continue;
        };
        let owner = libraries.get(identifier).unwrap_or(library);
        declarations.extend(read_classes(&layer, identifier, owner, **identifier == root));
    }

    let library = (*library).clone();
    Ok(Source {
        stage,
        library,
        use_literal_identifiers,
        skip_code_generation,
        declarations,
        source_layers,
    })
}

/// What one layer's `/GLOBAL` prim configures.
struct Global {
    library: Option<String>,
    use_literal_identifiers: bool,
    skip_code_generation: bool,
}

/// Reads a layer's `/GLOBAL` prim.
///
/// The keys that only mean something to the C++ build (`libraryPath`,
/// `libraryPrefix`, `tokensPrefix`, `useExportAPI`) are ignored: there is no
/// C++ build here to name.
fn read_global(layer: &sdf::Layer) -> Global {
    let custom_data = layer
        .prim(GLOBAL)
        .ok()
        .flatten()
        .map(|prim| CustomData::read(prim.get::<sdf::Value>(sdf::FieldKey::CustomData)))
        .unwrap_or_default();

    Global {
        library: custom_data.string("libraryName"),
        use_literal_identifiers: custom_data.flag("useLiteralIdentifier").unwrap_or(true),
        skip_code_generation: custom_data.flag("skipCodeGeneration").unwrap_or(false),
    }
}

/// Reads every class prim one layer declares, in `primChildren` order.
fn read_classes(layer: &sdf::Layer, identifier: &str, library: &str, generated: bool) -> Vec<Declaration> {
    let Some(root) = layer.pseudo_root() else {
        return Vec::new();
    };

    root.prim_children()
        .unwrap_or_default()
        .into_iter()
        .filter_map(|name| {
            let path = sdf::Path::abs_root().append_path(name.as_str()).ok()?;
            let prim = layer.prim(&path).ok().flatten()?;
            if prim.specifier() != Some(sdf::Specifier::Class) {
                return None;
            }

            let origin = Origin {
                layer: identifier.to_owned(),
                path: path.clone(),
            };
            Some(Declaration {
                name,
                library: library.to_owned(),
                generated,
                bases: inherit_names(&prim),
                custom_data: CustomData::read(prim.get::<sdf::Value>(sdf::FieldKey::CustomData)),
                type_name: prim.type_name(),
                api_schemas: prim.api_schemas(),
                documentation: prim.get(sdf::FieldKey::Documentation),
                properties: read_properties(layer, &prim, &path, identifier),
                fields: prim.fields(),
                origin,
            })
        })
        .collect()
}

/// The names a class prim inherits from, in authored order.
///
/// A schema inherits by path (`inherits = </Typed>`), and every target is a
/// root prim, so the name is all that is carried forward.
fn inherit_names(prim: &sdf::PrimSpecRef<'_>) -> Vec<tf::Token> {
    let Some(list_op) = prim.get::<sdf::PathListOp>(sdf::FieldKey::InheritPaths) else {
        return Vec::new();
    };
    list_op
        .iter()
        .filter_map(|target| target.name().map(tf::Token::from))
        .collect()
}

/// Reads the `customData` of every property a class prim declares.
///
/// Unordered: what the emitter and the schematics write follows the composed
/// order [`resolve`](crate::resolve) reads off the stage, where inheritance has
/// been applied.
fn read_properties(
    layer: &sdf::Layer,
    prim: &sdf::PrimSpecRef<'_>,
    prim_path: &sdf::Path,
    identifier: &str,
) -> Vec<PropertyDeclaration> {
    prim.property_children()
        .unwrap_or_default()
        .into_iter()
        .filter_map(|name| {
            let path = prim_path.append_property(name.as_str()).ok()?;
            let custom_data = layer
                .attribute(&path)
                .ok()
                .flatten()
                .map(|attribute| attribute.get::<sdf::Value>(sdf::FieldKey::CustomData))
                .or_else(|| {
                    layer
                        .relationship(&path)
                        .ok()
                        .flatten()
                        .map(|relationship| relationship.get::<sdf::Value>(sdf::FieldKey::CustomData))
                })?;

            Some(PropertyDeclaration {
                name,
                custom_data: CustomData::read(custom_data),
                origin: Origin {
                    layer: identifier.to_owned(),
                    path,
                },
            })
        })
        .collect()
}

/// A `customData` dictionary, read but not interpreted.
///
/// Both a class prim and a property carry one, and the generator asks the same
/// few questions of each.
#[derive(Default)]
pub struct CustomData(sdf::Dictionary);

impl CustomData {
    /// Reads one, empty when the field is absent or holds something else.
    fn read(value: Option<sdf::Value>) -> Self {
        Self(value.and_then(sdf::Value::try_as_dictionary).unwrap_or_default())
    }

    /// One entry as a string, written either as a string or as a token.
    pub fn string(&self, key: &str) -> Option<String> {
        self.0.get(key).and_then(sdf::Value::as_str).map(str::to_owned)
    }

    /// One entry as a boolean.
    pub fn flag(&self, key: &str) -> Option<bool> {
        self.0.get(key).and_then(sdf::Value::try_as_bool_ref).copied()
    }

    /// One entry as a token list, empty when it is absent.
    ///
    /// Written either as `token[]` or as `string[]`: `customData` is untyped
    /// to the generator that reads it, and upstream schemas use both.
    pub fn tokens(&self, key: &str) -> Vec<tf::Token> {
        let Some(value) = self.0.get(key) else {
            return Vec::new();
        };
        if let Some(tokens) = value.try_as_token_vec_ref() {
            return tokens.clone();
        }
        value
            .try_as_string_vec_ref()
            .map(|strings| strings.iter().map(|text| tf::Token::from(text.as_str())).collect())
            .unwrap_or_default()
    }

    /// The per-instance `apiSchemaCanOnlyApplyTo` lists a multiple-apply
    /// schema declares, keyed by instance name.
    ///
    /// An empty list is not recorded, matching what the registry stores when it
    /// reads the manifest this generator writes, so the instance keeps the
    /// schema-wide restriction.
    pub fn instance_restrictions(&self) -> BTreeMap<tf::Token, Vec<tf::Token>> {
        self.0
            .get("apiSchemaInstances")
            .and_then(sdf::Value::try_as_dictionary_ref)
            .into_iter()
            .flatten()
            .filter_map(|(instance, entry)| {
                let allowed = CustomData(entry.try_as_dictionary_ref()?.clone()).tokens("apiSchemaCanOnlyApplyTo");
                (!allowed.is_empty()).then(|| (tf::Token::from(instance.as_str()), allowed))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::error::Error;
    use crate::tests::read_fixture;

    /// A library has to name itself, since one library refers to another by
    /// that name and not by path.
    #[test]
    fn library_name_required() {
        let error = read_fixture("schema_sublayer.usda").expect_err("a sublayer declares no library of its own");
        assert!(matches!(error, Error::NoLibraryName { .. }), "{error}");
    }

    /// A codeless library asks for schema data and no Rust.
    #[test]
    fn codeless_flag() {
        let library = read_fixture("codeless_schema.usda").expect("resolves");
        assert!(library.skip_code_generation);

        let library = read_fixture("schema.usda").expect("resolves");
        assert!(!library.skip_code_generation);
    }

    /// Every layer read is reported, so a build script can watch the sublayers
    /// a schema resolves to and not just the file it was given.
    #[test]
    fn sublayers_reported() {
        let library = read_fixture("schema.usda").expect("resolves");
        assert!(
            library
                .source_layers
                .iter()
                .any(|layer| layer.ends_with("schema_sublayer.usda")),
            "{:?}",
            library.source_layers
        );
    }
}
