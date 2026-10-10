//! Generates Rust schema views from OpenUSD `schema.usda` files, with the
//! metadata fields and kinds a `plugInfo.json` declares beside them.
//!
//! This is the Rust answer to `usdGenSchema`, shaped as a build dependency: a
//! consumer describes its schema libraries in `build.rs`, and the generated
//! views join the crate through
//! [`openusd::include_schema!`](openusd::include_schema).
//!
//! ```no_run
//! // build.rs
//! openusd_build::configure()
//!     .search_path("schemas")
//!     .schema("schemas/usdGeom/schema.usda")
//!     .generate()?;
//! # Ok::<(), openusd_build::Error>(())
//! ```
//!
//! ```ignore
//! // src/lib.rs
//! pub mod geom {
//!     openusd::include_schema!("usdGeom");
//! }
//! ```
//!
//! A library's name comes from the `libraryName` its `schema.usda` declares,
//! not from the path, so the two spellings above name one library.
//!
//! [`Builder::plug_info`] adds what a library's plugin declares, and
//! [`Builder::declaration_family`] generates a plugin that has declarations
//! and no `schema.usda` at all.
//!
//! [`Builder::generate`] reads and checks the schemas it is given and writes
//! one file per library, carrying both the views and the schema data behind
//! them. The data is written as declarations a registry takes directly, so
//! nothing is serialized on the way out and nothing is parsed on the way back
//! in: what a consumer registers is a `const` its compiler has already checked.
//!
//! A registry is handed the whole of it through the `SCHEMAS` each generated
//! library exposes:
//!
//! ```ignore
//! use openusd::usd::SchemaRegistry;
//!
//! let registry = SchemaRegistry::builder().register(geom::SCHEMAS).build()?;
//! ```
//!
//! Fenced `ignore`, as the `include_schema!` example above is: this crate has
//! no build script, so there is no `OUT_DIR` here for the module to come from.

mod error;

mod decl;
mod emit;
mod load;
mod plug_info;
mod resolve;
mod shader_defs;
mod tokens;
mod validate;

mod doc;
mod model;
mod names;
mod types;

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

use openusd::{tf, usd};

use crate::model::Library;

/// Where a library's generated views live, for a base this run does not
/// generate: the library name a schema declares, mapped to the Rust path its
/// views are reachable at.
pub(crate) type Externs = BTreeMap<String, String>;

pub use error::{Error, TokenEnumError};
pub use validate::Violation;

/// What generating one library produced: a schema library, or the family of a
/// plugin that declares no schema.
///
/// The declarations are the contract: a registry built from them answers what
/// a registry built from upstream's own schema data answers. They reach a
/// consumer as the `SCHEMAS` table in [`rust`](Self::rust), and this crate's
/// own callers through [`with_family`](Self::with_family).
#[derive(Debug)]
pub struct Output {
    /// The generated file: this library's tokens and schema data, and its views
    /// unless they were left out.
    pub rust: String,
    /// Whether [`rust`](Self::rust) carries the views: [`Views::Skip`] was
    /// asked for, or the schema declared `skipCodeGeneration`.
    pub views: bool,
    /// What a schema author should know, though the output is still correct.
    pub warnings: Vec<String>,
    /// The model everything above was generated from, and what
    /// [`with_family`](Self::with_family) lends its declarations out of.
    library: model::Library,
    /// The file it was generated from: the schema as configured, or the
    /// `plugInfo.json` of a plugin with no schema.
    source: PathBuf,
}

impl Output {
    /// The library's name: the `libraryName` its schema declared, or the name
    /// of the plugin a declaration family was generated from.
    pub fn library_name(&self) -> &str {
        &self.library.name
    }

    /// Where every layer the schema resolved to was found, which is what a
    /// build script watches. A layer reached through a
    /// [`search_path`](Builder::search_path) is here by the location it was
    /// found at, not the bare relative path the schema asked for.
    pub fn layers(&self) -> &[PathBuf] {
        &self.library.source_layers
    }

    /// Calls `f` with this library's schemas as a declared family — the schema
    /// data itself, and the same declarations the generated table carries.
    ///
    /// A [`usd::SchemaFamily`] is a view over its parts, so it arrives through
    /// a closure rather than as a value: what it borrows lives for the call.
    /// [`usd::SchemaRegistryBuilder::register`] takes it, and
    /// [`usd::SchemaFamily::to_data`] turns it into the class prims a
    /// `generatedSchema.usda` would carry.
    ///
    /// ```no_run
    /// # fn main() -> Result<(), openusd_build::Error> {
    /// let output = openusd_build::configure()
    ///     .build_library("schemas/usdGeom/schema.usda", openusd_build::Views::Generate)?;
    /// let data = output.with_family(|family| family.to_data());
    /// # let _ = data;
    /// # Ok(())
    /// # }
    /// ```
    pub fn with_family<R>(&self, f: impl FnOnce(&usd::SchemaFamily<'_>) -> R) -> R {
        decl::with_family(&self.library, f)
    }
}

/// What generating one shader-node library produced.
#[derive(Debug)]
pub struct NodeOutput {
    /// The generated file: the node views and the tokens naming their ids,
    /// inputs and outputs.
    pub rust: String,
    /// Where every layer the definitions composed from was found.
    layers: Vec<PathBuf>,
}

impl NodeOutput {
    /// Where every layer the definitions composed from was found, which is
    /// what a build script watches.
    pub fn layers(&self) -> &[PathBuf] {
        &self.layers
    }
}

/// Whether a library's views are generated beside its schema data.
///
/// The data is not optional either way: it is what a registry is built from, so
/// a library declining an API still ships what registers it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Views {
    /// Generate the trait and view per schema.
    Generate,
    /// Generate the tokens and the schema data alone, for a library whose API
    /// is written by hand. A schema declaring `skipCodeGeneration` is treated
    /// this way however it was asked for.
    Skip,
}

/// A Rust enum over one token attribute's `allowedTokens`.
///
/// Generation is opt-in and explicit, because a token set is not an identity:
/// two properties can admit the same tokens and mean different things, and two
/// properties meaning the same thing can declare different fallbacks. So the
/// enum is named here and sourced from the one property that defines it.
/// Nothing else is associated with it — a property admitting the same tokens is
/// free to use it or not, and the generated accessors are unchanged either
/// way.
///
/// ```no_run
/// # fn main() -> Result<(), openusd_build::Error> {
/// use openusd_build::TokenEnum;
///
/// openusd_build::configure()
///     .schema("schemas/usdGeom/schema.usda")
///     .token_enum(TokenEnum::new("Purpose", "usdGeom", "Imageable.purpose").with_default())
///     .generate()?;
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct TokenEnum {
    /// The Rust type to generate.
    pub(crate) name: String,
    /// The `libraryName` of the schema declaring the source property.
    pub(crate) library: String,
    /// `Class.property`, naming the declaration the variants come from.
    source: String,
    /// Whether to derive `Default` from the source property's fallback.
    pub(crate) default: bool,
    /// Variant names the caller spelled, by the token each stands for.
    pub(crate) variants: BTreeMap<String, String>,
}

impl TokenEnum {
    /// An enum called `name` over the `allowedTokens` of `source`, a property
    /// of `library` named `Class.property`.
    ///
    /// `Class` is the schema's registered identifier, as the class prim spells
    /// it, not the Rust name its `className` may ask for.
    pub fn new(name: impl Into<String>, library: impl Into<String>, source: impl Into<String>) -> Self {
        TokenEnum {
            name: name.into(),
            library: library.into(),
            source: source.into(),
            default: false,
            variants: BTreeMap::new(),
        }
    }

    /// Derives `Default` from the source property's fallback.
    ///
    /// Off unless asked for: a token set carries no default of its own, and the
    /// corpus shows why — `guideVisibility` falls back to `invisible` where
    /// `proxyVisibility` and `renderVisibility` fall back to `inherited`, all
    /// three admitting the same tokens. So the default is the source
    /// property's, said explicitly, and a source with no token fallback is an
    /// error rather than a guess.
    #[must_use]
    pub fn with_default(mut self) -> Self {
        self.default = true;
        self
    }

    /// Spells the variant for `token` rather than casing it.
    ///
    /// For a token Rust has no name for — an empty spelling, one opening with a
    /// digit — and for two tokens that would otherwise reach one name. Naming a
    /// token the source property does not admit is an error, so an override
    /// cannot quietly do nothing.
    #[must_use]
    pub fn variant(mut self, token: impl Into<String>, variant: impl Into<String>) -> Self {
        self.variants.insert(token.into(), variant.into());
        self
    }

    /// The class and property its variants come from, or the spelling that is
    /// neither.
    pub(crate) fn source(&self) -> Result<(&str, &str), TokenEnumError> {
        self.source
            .split_once('.')
            .filter(|(class, property)| !class.is_empty() && !property.is_empty())
            .ok_or_else(|| TokenEnumError::MalformedSource {
                spelling: self.source.clone(),
            })
    }
}

/// Starts describing what to generate. See [`Builder`].
pub fn configure() -> Builder {
    Builder {
        out_dir: None,
        search_paths: Vec::new(),
        extern_libraries: BTreeMap::new(),
        schemas: Vec::new(),
        token_enums: Vec::new(),
        plug_infos: Vec::new(),
        declaration_families: Vec::new(),
        shader_defs: Vec::new(),
    }
}

/// What to generate, and where.
///
/// Every method takes and returns the builder, so a `build.rs` reads as one
/// expression.
#[derive(Debug)]
pub struct Builder {
    out_dir: Option<PathBuf>,
    search_paths: Vec<PathBuf>,
    extern_libraries: Externs,
    /// Each schema to generate, and whether its views are wanted with it.
    schemas: Vec<(PathBuf, Views)>,
    /// The enums to generate over token properties, in the order declared.
    token_enums: Vec<TokenEnum>,
    /// The `plugInfo.json` files declaring libraries' metadata fields and
    /// kinds.
    plug_infos: Vec<PathBuf>,
    /// The plugins to generate as families of their own, with no schema
    /// library behind them.
    declaration_families: Vec<String>,
    /// The shader-definition layers to generate node views of, each with the
    /// library name its file is written under.
    shader_defs: Vec<(String, PathBuf)>,
}

impl Builder {
    /// Writes generated files to `dir` instead of `OUT_DIR`.
    ///
    /// A build script needs this only when it writes somewhere it also reads
    /// from, such as a checked-in copy; `OUT_DIR` is the ordinary destination,
    /// and where [`openusd::include_schema!`](openusd::include_schema) looks.
    #[must_use]
    pub fn out_dir(mut self, dir: impl Into<PathBuf>) -> Self {
        self.out_dir = Some(dir.into());
        self
    }

    /// Reads what a `plugInfo.json` declares beside its schemas, the way C++
    /// registers it: the metadata fields of each plugin's `SdfMetadata` block
    /// and the kinds of its `Kinds` block.
    ///
    /// Each plugin's declarations belong to the library whose `libraryName`
    /// is the plugin's `Name`. They are registered with that library's
    /// schemas; a field is also named in its `tokens`, and read and written
    /// through extension traits on the handles it applies to
    /// (`AttributeMetadata` and its siblings). A plugin with no schema library
    /// is named with [`declaration_family`](Self::declaration_family), and one
    /// file may hold plugins of both sorts. A plugin that is neither is an
    /// error when [`generate`](Self::generate) runs.
    #[must_use]
    pub fn plug_info(mut self, path: impl Into<PathBuf>) -> Self {
        self.plug_infos.push(path.into());
        self
    }

    /// Generates the plugin called `name` as a family of its own, for a
    /// plugin that declares kinds or metadata fields and has no schema
    /// library. Repeatable.
    ///
    /// The plugin is read from a file [`plug_info`](Self::plug_info) names.
    /// Its file is written as `<name>.rs` and included with
    /// [`openusd::include_schema!`](openusd::include_schema) like a schema
    /// library's, and its `SCHEMAS` registers the declarations and no schema.
    /// A name no configured `plugInfo.json` declares is an error when
    /// [`generate`](Self::generate) runs.
    #[must_use]
    pub fn declaration_family(mut self, name: impl Into<String>) -> Self {
        self.declaration_families.push(name.into());
        self
    }

    /// Generates a view of each shader node the layer at `path` defines, as
    /// `usdShaders`'s `shaderDefs.usda` defines `UsdPreviewSurface` and its
    /// companions.
    ///
    /// Each `def Shader` prim authoring an `info:id` is a node, and its view
    /// wraps the `usdShade` library's `Shader` view, so that library must be
    /// placed with [`extern_library`](Self::extern_library). The file is
    /// written as `<library>.rs` and included with
    /// [`openusd::include_schema!`](openusd::include_schema) like a schema
    /// library's.
    #[must_use]
    pub fn shader_defs(mut self, library: impl Into<String>, path: impl Into<PathBuf>) -> Self {
        self.shader_defs.push((library.into(), path.into()));
        self
    }

    /// Adds a directory that a `schema.usda`'s sublayers resolve through, the
    /// way [`ar::DefaultResolver::with_search_paths`](openusd::ar::DefaultResolver::with_search_paths)
    /// takes them.
    ///
    /// Upstream schemas sublayer each other by bare path
    /// (`subLayers = [@usd/schema.usda@]`), which is what a search path
    /// resolves. Repeatable, and searched in the order given.
    #[must_use]
    pub fn search_path(mut self, dir: impl Into<PathBuf>) -> Self {
        self.search_paths.push(dir.into());
        self
    }

    /// Declares where a library this run does not generate already lives, so
    /// the generated code can name types from it.
    ///
    /// `library` is the `libraryName` that library's `schema.usda` declares and
    /// `rust_path` the module path its views are reachable at, as in
    /// `("usdGeom", "openusd_schemas::geom")`. A class inheriting from, or
    /// reflecting, a schema of a library this run does not generate needs it
    /// declared here; a class of a declared library that a schema's prose names
    /// is linked to where it lives, and one of an undeclared library is left as
    /// prose. The path is to the library's views, so a library generated for
    /// its schema data alone has nothing to declare. Keyed by library name, so
    /// declaring one twice keeps the last.
    #[must_use]
    pub fn extern_library(mut self, library: impl Into<String>, rust_path: impl Into<String>) -> Self {
        self.extern_libraries.insert(library.into(), rust_path.into());
        self
    }

    /// Adds a `schema.usda` to generate a library from. Repeatable.
    #[must_use]
    pub fn schema(mut self, path: impl Into<PathBuf>) -> Self {
        self.schemas.push((path.into(), Views::Generate));
        self
    }

    /// Adds a `schema.usda` to generate schema data from, without its views.
    ///
    /// The generated file still carries the tokens and the declaration table a
    /// registry is built from; what it leaves out is the trait and view per
    /// schema. That is what a crate whose API for these schemas is written by
    /// hand wants: the declarations a registry needs, without a generated set
    /// of views beside its own to collide with.
    ///
    /// A schema that declares `skipCodeGeneration` is treated this way whether
    /// or not it is named here.
    #[must_use]
    pub fn schema_data(mut self, path: impl Into<PathBuf>) -> Self {
        self.schemas.push((path.into(), Views::Skip));
        self
    }

    /// Adds a Rust enum over a token property's `allowedTokens`. Repeatable.
    ///
    /// See [`TokenEnum`] for what it takes and why it is named rather than
    /// derived. The enum joins the generated file of the library its source
    /// property belongs to, beside that library's token constants; a library no
    /// configured enum names generates exactly what it did before.
    ///
    /// An enum whose library this run does not build generates nothing, so one
    /// list of enums describes families that are each behind their own
    /// feature. Naming a library this build neither generates nor declares
    /// with [`extern_library`](Self::extern_library) is an error.
    #[must_use]
    pub fn token_enum(mut self, declared: TokenEnum) -> Self {
        self.token_enums.push(declared);
        self
    }

    /// Generates every configured library.
    ///
    /// Configuring no schemas, shader definitions or declaration families is
    /// not an error and writes nothing: a consumer whose families are
    /// feature-gated generates none of them when its features are off, and its
    /// `build.rs` should not have to know that.
    ///
    /// Otherwise the output directory must be known, from
    /// [`out_dir`](Self::out_dir) or from the `OUT_DIR` a build script runs
    /// with, and is created if it does not exist.
    ///
    /// Each library writes one file, `<library>.rs`, named after the
    /// `libraryName` its `/GLOBAL` declares and included by
    /// [`openusd::include_schema!`](openusd::include_schema). It carries both
    /// the views and the schema data, the latter as the declaration table
    /// [`usd::SchemaRegistryBuilder::register`] takes. A library that asked for
    /// `skipCodeGeneration` writes that file too, carrying its tokens and its
    /// schema data without the views — the data is what a registry is built
    /// from, so a library declining an API still has to ship it.
    ///
    /// Two schemas declaring the same `libraryName` would write one file, and
    /// are refused before anything is written. A file already holding what
    /// this run generates is left untouched, its modification time with it.
    pub fn generate(self) -> Result<(), Error> {
        if self.schemas.is_empty() && self.shader_defs.is_empty() && self.declaration_families.is_empty() {
            return Ok(());
        }

        let out_dir = match &self.out_dir {
            Some(dir) => dir.clone(),
            None => env::var_os("OUT_DIR").map(PathBuf::from).ok_or(Error::NoOutDir)?,
        };
        fs::create_dir_all(&out_dir).map_err(|source| Error::Io {
            path: out_dir.clone(),
            source,
        })?;

        // Every library is generated before any of them is written, so a
        // schema this run refuses leaves the last run's output alone rather
        // than half of it replaced. Each file is then replaced whole (`write`),
        // so a run failing part-way leaves every library as one run or the
        // other wrote it.
        //
        // TODO(rayon): a library is an independent stage open, composition and
        // emission over `&self`, so the families of `openusd-schemas` could
        // build at once. `Output` is what stands in the way: its model holds
        // `sdf::Value`s read from a stage that is neither `Send` nor `Sync`, so
        // a parallel version has to finish with each library inside the worker
        // and return the generated text alone.
        let plugins = self.plugins()?;
        let mut outputs = self
            .schemas
            .iter()
            .map(|(schema, views)| self.build(schema, *views, &plugins))
            .collect::<Result<Vec<_>, Error>>()?;
        for family in &self.declaration_families {
            outputs.push(self.declare(family, &plugins)?);
        }

        // A library this run builds, or one declared so a view can name it: an
        // enum naming anything else matches nothing, ever. A family behind
        // a feature that is off is still declared, so this does not catch
        // one that is simply switched off.
        let known: BTreeSet<&str> = outputs
            .iter()
            .map(Output::library_name)
            .chain(self.extern_libraries.keys().map(String::as_str))
            .collect();
        if let Some(declared) = self
            .token_enums
            .iter()
            .find(|declared| !known.contains(declared.library.as_str()))
        {
            return Err(Error::TokenEnum {
                name: declared.name.clone(),
                cause: TokenEnumError::UnknownLibrary {
                    library: declared.library.clone(),
                },
            });
        }

        // Every plugin a `plugInfo.json` declares is one of the libraries or
        // declaration families built here.
        for plugin in &plugins {
            if !outputs.iter().any(|output| output.library_name() == plugin.name) {
                return Err(Error::UnknownPlugin {
                    plugin: plugin.name.clone(),
                    path: plugin.path.clone(),
                });
            }
        }

        let nodes = self
            .shader_defs
            .iter()
            .map(|(library, path)| Ok((library.as_str(), path.as_path(), self.build_shader_defs(library, path)?)))
            .collect::<Result<Vec<_>, Error>>()?;

        // One file per library name, so two libraries of one name would write
        // the same file.
        let mut destinations: BTreeMap<&str, &Path> = BTreeMap::new();
        let named = outputs
            .iter()
            .map(|output| (output.library_name(), output.source.as_path()))
            .chain(nodes.iter().map(|(library, path, _)| (*library, *path)));
        for (library, source) in named {
            if let Some(first) = destinations.insert(library, source) {
                return Err(Error::DuplicateLibrary {
                    library: library.to_owned(),
                    first: first.to_path_buf(),
                    second: source.to_path_buf(),
                });
            }
        }

        // A field or a kind is declared once. Two plugins of one name are one
        // library, so a repeat between them names that library twice.
        let fields = declared_twice(&outputs, |library| {
            library.metadata.iter().map(|field| field.name.as_str()).collect()
        });
        if let Some((field, first, second)) = fields {
            return Err(Error::DuplicateMetadataField { field, first, second });
        }
        let kinds = declared_twice(&outputs, |library| {
            library.kinds.iter().map(|kind| kind.name.as_str()).collect()
        });
        if let Some((kind, first, second)) = kinds {
            return Err(Error::DuplicateKind { kind, first, second });
        }
        for (library, _, output) in &nodes {
            write(&out_dir.join(format!("{library}.rs")), &output.rust)?;
            for layer in output.layers() {
                println!("cargo:rerun-if-changed={}", layer.display());
            }
        }

        for output in &outputs {
            for warning in &output.warnings {
                println!("cargo:warning={warning}");
            }

            write(&out_dir.join(format!("{}.rs", output.library_name())), &output.rust)?;

            // Every layer the schema composed from, so an edit to a sublayer
            // regenerates as surely as an edit to the file named here. Naming
            // any of them switches off cargo's own "rerun if the package
            // changed" default, which is why the whole stack is named and not
            // the configured paths alone.
            for layer in output.layers() {
                println!("cargo:rerun-if-changed={}", layer.display());
            }
        }
        Ok(())
    }

    /// Generates one schema library, writing nothing.
    ///
    /// The whole pipeline, for a caller that wants the result rather than the
    /// files: [`generate`](Self::generate) runs this over every schema
    /// [`schema`](Self::schema) named and writes what comes back. The schema is
    /// named here instead, so that list has no bearing on this call.
    /// A schema asking for `skipCodeGeneration` gets no views whatever `views`
    /// says.
    pub fn build_library(&self, schema: impl AsRef<Path>, views: Views) -> Result<Output, Error> {
        self.build(schema.as_ref(), views, &self.plugins()?)
    }

    /// Generates the declaration-only family of the plugin called `family`,
    /// writing nothing: the file [`generate`](Self::generate) writes for a
    /// name [`declaration_family`](Self::declaration_family) gave.
    pub fn build_declarations(&self, family: &str) -> Result<Output, Error> {
        self.declare(family, &self.plugins()?)
    }

    /// Generates the family of what the plugins called `family` declare, with
    /// no schema library behind it.
    fn declare(&self, family: &str, plugins: &[plug_info::Plugin]) -> Result<Output, Error> {
        // The name is the generated file's, and what `include_schema!` is
        // given, so it has to be one a path and a Rust string both take whole.
        if !tf::is_valid_identifier(family) {
            return Err(Error::InvalidDeclarationFamily {
                family: family.to_owned(),
            });
        }
        let Some(plugin) = plugins.iter().find(|plugin| plugin.name == family) else {
            return Err(Error::UnknownDeclarationFamily {
                family: family.to_owned(),
            });
        };
        let mut library = Library::declarations(family);
        library.take_declarations(plugins);
        let warnings = validate::check(&library)?;
        // The traits a metadata field is read through are emitted with the
        // views, so the views are asked for.
        self.emit(library, warnings, &plugin.path, Views::Generate)
    }

    /// Generates the file of a library read from `source`.
    fn emit(&self, library: Library, warnings: Vec<String>, source: &Path, views: Views) -> Result<Output, Error> {
        // Named by file rather than by path: the header reaches whatever the
        // consumer generates into, and an absolute path would differ on every
        // machine that built it.
        let named = source.file_name().unwrap_or(source.as_os_str());
        let rust = emit::emit(
            &library,
            &self.extern_libraries,
            &named.to_string_lossy(),
            views,
            &self.token_enums,
        )?;
        Ok(Output {
            rust,
            views: views == Views::Generate,
            warnings,
            library,
            source: source.to_path_buf(),
        })
    }

    /// Every plugin the configured `plugInfo.json` files declare, each file
    /// read once.
    fn plugins(&self) -> Result<Vec<plug_info::Plugin>, Error> {
        let mut plugins = Vec::new();
        for path in &self.plug_infos {
            plugins.extend(plug_info::read(path)?);
        }
        Ok(plugins)
    }

    /// Generates the views of the shader nodes the layer at `path` defines,
    /// writing nothing: the file [`generate`](Self::generate) writes for a
    /// library [`shader_defs`](Self::shader_defs) named.
    pub fn build_shader_defs(&self, library: &str, path: impl AsRef<Path>) -> Result<NodeOutput, Error> {
        let path = path.as_ref();
        let shade = self.extern_libraries.get("usdShade").ok_or_else(|| Error::ShaderDefs {
            path: path.to_path_buf(),
            cause: "a node's view wraps `usdShade`'s `Shader`, and no extern_library places usdShade".to_owned(),
        })?;
        let shade: syn::Path = syn::parse_str(shade).map_err(|_| Error::ShaderDefs {
            path: path.to_path_buf(),
            cause: format!("usdShade is placed at `{shade}`, which is not a Rust path"),
        })?;
        let library = shader_defs::read(self, library, path)?;
        let rust = emit::nodes(&library, &shade)?;
        Ok(NodeOutput {
            rust,
            layers: library.layers,
        })
    }

    /// Reads, checks and generates one library.
    fn build(&self, schema: &Path, views: Views, plugins: &[plug_info::Plugin]) -> Result<Output, Error> {
        let (library, warnings) = self.read(schema, plugins)?;
        let views = match library.skip_code_generation {
            true => Views::Skip,
            false => views,
        };
        self.emit(library, warnings, schema, views)
    }

    /// Reads one schema into the model every output is generated from, with
    /// whatever a schema author should know about it.
    ///
    /// The three stages behind it stay separate: [`load`] extracts what the
    /// layers declare, [`resolve`] consults composition once and keeps the
    /// answers, and [`validate`] checks the rules. What validation finds that
    /// does not make the output wrong travels back beside the model, so a
    /// caller reading the result in memory sees it as well as a build log does.
    fn read(&self, schema: &Path, plugins: &[plug_info::Plugin]) -> Result<(Library, Vec<String>), Error> {
        let source = load::open(self, schema)?;
        let mut library = resolve::library(&source)?;

        library.take_declarations(plugins);

        // Prim indices are built on demand, so a diagnostic a class's own
        // composition raises exists only once resolve has read that class.
        // Asking again here is what catches those.
        Error::composition(schema, &source.stage).map_or(Ok(()), Err)?;

        let warnings = validate::check(&library)?;
        Ok((library, warnings))
    }
}

/// The first name two of `outputs` both declare, with the library declaring
/// it first and the one declaring it again. `names` lists what one library
/// declares.
fn declared_twice<'a>(
    outputs: &'a [Output],
    names: impl Fn(&'a Library) -> Vec<&'a str>,
) -> Option<(String, String, String)> {
    let mut declared: BTreeMap<&str, &str> = BTreeMap::new();
    for output in outputs {
        for name in names(&output.library) {
            if let Some(first) = declared.insert(name, output.library_name()) {
                return Some((name.to_owned(), first.to_owned(), output.library_name().to_owned()));
            }
        }
    }
    None
}

/// Writes one generated file, naming the path in anything that goes wrong.
///
/// A file already holding `contents` is left untouched, so whatever watches
/// its modification time — rustc's incremental cache, an editor — sees
/// nothing change when the same text is regenerated. Anything else is written
/// beside the destination and renamed onto it, which replaces the file whole:
/// an interrupted run leaves the previous file or the new one, never a
/// truncated one.
fn write(path: &Path, contents: &str) -> Result<(), Error> {
    if fs::read(path).is_ok_and(|current| current == contents.as_bytes()) {
        return Ok(());
    }

    let mut staged = path.as_os_str().to_owned();
    staged.push(format!(".tmp-{}", process::id()));
    let staged = PathBuf::from(staged);
    let written = fs::write(&staged, contents).map_err(|source| Error::Io {
        path: staged.clone(),
        source,
    });
    let replaced = written.and_then(|()| {
        fs::rename(&staged, path).map_err(|source| Error::Io {
            path: path.to_path_buf(),
            source,
        })
    });
    if replaced.is_err() {
        // Nothing to report beyond the failure itself, which is the one a
        // contributor needs; a stale staging file only costs disk space.
        let _ = fs::remove_file(&staged);
    }
    replaced
}

#[cfg(test)]
mod tests {

    use super::*;

    use std::time::{Duration, SystemTime};

    use openusd::sdf;

    /// Resolves one file of the vendored upstream corpus, which every module's
    /// tests read.
    pub(crate) fn read_fixture(name: &str) -> Result<Library, Error> {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/testUsdGenSchema");
        configure()
            .search_path(&dir)
            .read(&dir.join(name), &[])
            .map(|(library, _)| library)
    }

    /// Resolves a schema a test writes for itself, for a case the vendored
    /// corpus does not reach.
    pub(crate) fn read_source(dir: &Path, source: &str) -> Result<Library, Error> {
        fs::write(dir.join("schema.usda"), source).expect("writes the schema");
        configure()
            .read(&dir.join("schema.usda"), &[])
            .map(|(library, _)| library)
    }

    /// A schema library called `library`: the roots, and whatever `classes`
    /// declare.
    pub(crate) fn schema(library: &str, classes: &str) -> String {
        format!(
            r#"#usda 1.0

def "GLOBAL" (
    customData = {{
        string libraryName = "{library}"
    }}
)
{{
}}

class "Typed" {{}}

class "APISchemaBase" {{}}

{classes}
"#
        )
    }

    /// A single-apply API schema for a class to reflect, declaring `dup` among
    /// its properties for a second reflected schema to collide with.
    pub(crate) const TAG_API: &str = r#"class "TagAPI" (
    inherits = </APISchemaBase>
    customData = { token apiSchemaType = "singleApply" }
) {
    string tag = ""
    int dup = 0
}"#;

    /// An API schema whose name breaks the suffix convention, which is a
    /// warning rather than a rule: the registry never reads the spelling.
    const MISSING_SUFFIX: &str = r#"#usda 1.0

def "GLOBAL" (
    customData = {
        string libraryName = "testWarn"
    }
)
{
}

class "APISchemaBase"
{
}

class "MissingSuffix" (
    inherits = </APISchemaBase>
    customData = {
        token apiSchemaType = "singleApply"
    }
)
{
}
"#;

    /// A convention warning reaches the caller that asked for the library, not
    /// only the build log a `generate` run prints to.
    #[test]
    fn build_library_reports_warnings() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("schema.usda");
        fs::write(&path, MISSING_SUFFIX).expect("writes the schema");

        let output = configure().build_library(&path, Views::Generate).expect("builds");
        let warnings = &output.warnings;
        assert_eq!(warnings.len(), 1, "{warnings:?}");
        assert!(warnings[0].contains("conventionally ends in `API`"), "{warnings:?}");
    }

    /// A run with nothing configured writes nothing and needs no destination,
    /// which is the state a consumer's build script is in when every schema
    /// family it can generate is behind a feature that is off.
    #[test]
    fn no_schemas_writes_nothing() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out = dir.path().join("generated");

        configure().out_dir(&out).generate().expect("nothing to do");

        assert!(!out.exists(), "a run with no schemas creates no output directory");
    }

    /// The destination is created on demand, since `OUT_DIR` exists but a
    /// caller's own path need not.
    #[test]
    fn out_dir_created() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out = dir.path().join("nested/generated");

        // The corpus reflects a schema of its `usd` sublayer library, whose
        // views the generated code has to be able to name.
        let schema = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/testUsdGenSchema/schema.usda");
        configure()
            .out_dir(&out)
            .search_path(schema.parent().expect("a parent"))
            .extern_library("usd", "::openusd::usd")
            .schema(&schema)
            .generate()
            .expect("generates");

        assert!(out.is_dir(), "the output directory is created if it is missing");
    }

    /// `MISSING_SUFFIX` written to `dir`, and the library it declares.
    fn missing_suffix(dir: &Path) -> PathBuf {
        let path = dir.join("schema.usda");
        fs::write(&path, MISSING_SUFFIX).expect("writes the schema");
        path
    }

    /// What `generate` writes is what `build_library` hands back, with no
    /// staging file left beside it.
    #[test]
    fn generated_file_written() {
        let dir = tempfile::tempdir().expect("tempdir");
        let schema = missing_suffix(dir.path());
        let out = dir.path().join("generated");

        configure().out_dir(&out).schema(&schema).generate().expect("generates");

        let expected = configure()
            .build_library(&schema, Views::Generate)
            .expect("builds")
            .rust;
        let written = fs::read_to_string(out.join("testWarn.rs")).expect("reads the output");
        assert_eq!(written, expected);
        let names: Vec<_> = fs::read_dir(&out)
            .expect("lists the output")
            .map(|entry| entry.expect("an entry").file_name())
            .collect();
        assert_eq!(names, vec!["testWarn.rs"], "nothing else is left behind");
    }

    /// Regenerating the same text leaves the file as it was, modification
    /// time included; different text replaces it.
    #[test]
    fn unchanged_file_untouched() {
        let dir = tempfile::tempdir().expect("tempdir");
        let schema = missing_suffix(dir.path());
        let out = dir.path().join("generated");
        let file = out.join("testWarn.rs");
        let generate = || configure().out_dir(&out).schema(&schema).generate();

        generate().expect("generates");
        let long_ago = SystemTime::UNIX_EPOCH + Duration::from_secs(1_000_000);
        fs::File::options()
            .write(true)
            .open(&file)
            .and_then(|written| written.set_modified(long_ago))
            .expect("backdates the output");

        generate().expect("regenerates");
        let modified = || {
            fs::metadata(&file)
                .and_then(|meta| meta.modified())
                .expect("reads mtime")
        };
        assert_eq!(modified(), long_ago, "the same text is not written again");

        let changed = MISSING_SUFFIX.replace(
            "class \"MissingSuffix\" (",
            "class \"MissingSuffix\" (\n    doc = \"Changed.\"",
        );
        fs::write(&schema, changed).expect("edits the schema");
        generate().expect("regenerates");
        assert_ne!(modified(), long_ago, "different text replaces the file");
        assert!(fs::read_to_string(&file).expect("reads").contains("Changed."));
    }

    /// Two schemas declaring one `libraryName` would write one file, so the
    /// run refuses before writing either.
    #[test]
    fn duplicate_library_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        let [first, second] = ["a", "b"].map(|name| {
            let own = dir.path().join(name);
            fs::create_dir(&own).expect("creates a schema directory");
            missing_suffix(&own)
        });
        let out = dir.path().join("generated");

        let error = configure()
            .out_dir(&out)
            .schema(&first)
            .schema(&second)
            .generate()
            .expect_err("both declare testWarn");

        match error {
            Error::DuplicateLibrary {
                library,
                first: named_first,
                second: named_second,
            } => {
                assert_eq!(library, "testWarn");
                assert_eq!((named_first, named_second), (first, second));
            }
            other => panic!("{other}"),
        }
        assert!(!out.join("testWarn.rs").exists(), "nothing is written");
    }

    /// A `plugInfo.json` declaring `field` for the plugin `plugin`, written
    /// to `dir`.
    fn plug_info(dir: &Path, plugin: &str, field: &str) -> PathBuf {
        let path = dir.join(format!("{plugin}-{field}.json"));
        let text = format!(
            r#"{{"Plugins": [{{"Name": "{plugin}", "Info": {{"SdfMetadata": {{"{field}": {{"type": "token"}}}}}}}}]}}"#
        );
        fs::write(&path, text).expect("writes the plugInfo");
        path
    }

    /// A `plugInfo.json` holding the schema library `testWarn`'s plugin and
    /// the plugin `siteKinds`, which declares kinds and has no schema library.
    fn mixed_plug_info(dir: &Path) -> PathBuf {
        let path = dir.join("mixed.json");
        fs::write(
            &path,
            r#"{"Plugins": [
                {"Name": "testWarn", "Info": {
                    "SdfMetadata": {"role": {"type": "token"}},
                    "Kinds": {"prop": {"baseKind": "component"}}
                }},
                {"Name": "siteKinds", "Info": {"Kinds": {
                    "chargroup": {"baseKind": "assembly"},
                    "site_root": {}
                }}}
            ]}"#,
        )
        .expect("writes the plugInfo");
        path
    }

    /// The kinds `output`'s family declares, each with its base.
    fn declared_kinds(output: &Output) -> Vec<(String, Option<String>)> {
        output.with_family(|family| {
            family
                .declared_kinds()
                .iter()
                .map(|kind| (kind.name().to_owned(), kind.declared_base().map(str::to_owned)))
                .collect()
        })
    }

    /// One file holds a schema library's plugin and a declaration-only one,
    /// and each reaches its own generated file.
    #[test]
    fn mixed_plugins_generate() {
        let dir = tempfile::tempdir().expect("tempdir");
        let schema = missing_suffix(dir.path());
        let info = mixed_plug_info(dir.path());
        let out = dir.path().join("generated");

        configure()
            .out_dir(&out)
            .schema(&schema)
            .plug_info(&info)
            .declaration_family("siteKinds")
            .generate()
            .expect("generates both");

        let library = fs::read_to_string(out.join("testWarn.rs")).expect("the schema library is written");
        assert!(
            library.contains(r#"::openusd::kind::Decl::new("prop").base("component")"#),
            "{library}"
        );
        let family = fs::read_to_string(out.join("siteKinds.rs")).expect("the declaration family is written");
        assert!(
            family.contains(r#"::openusd::kind::Decl::new("chargroup").base("assembly")"#),
            "{family}"
        );
        assert!(
            family.contains(r#"::openusd::kind::Decl::new("site_root")"#),
            "{family}"
        );
        assert!(!family.contains("prop"), "{family}");
    }

    /// A run with no schema at all still writes its declaration families.
    #[test]
    fn declarations_alone_generate() {
        let dir = tempfile::tempdir().expect("tempdir");
        let info = mixed_plug_info(dir.path());
        let out = dir.path().join("generated");

        // Naming the file alone asks for nothing, as configuring no schema does.
        configure()
            .out_dir(&out)
            .plug_info(&info)
            .generate()
            .expect("nothing to do");
        assert!(!out.exists(), "nothing is written");

        let error = configure()
            .out_dir(&out)
            .plug_info(&info)
            .declaration_family("siteKinds")
            .generate()
            .expect_err("testWarn has no schema library here");
        assert!(
            matches!(&error, Error::UnknownPlugin { plugin, .. } if plugin == "testWarn"),
            "{error}"
        );

        let kinds = dir.path().join("kinds.json");
        fs::write(
            &kinds,
            r#"{"Plugins": [{"Name": "siteKinds", "Info": {"Kinds": {"chargroup": {"baseKind": "assembly"}}}}]}"#,
        )
        .expect("writes the plugInfo");
        configure()
            .out_dir(&out)
            .plug_info(&kinds)
            .declaration_family("siteKinds")
            .generate()
            .expect("generates the family");
        assert!(out.join("siteKinds.rs").exists());
    }

    /// A declaration family carries its plugin's kinds and watches its file.
    #[test]
    fn declaration_family_kinds() {
        let dir = tempfile::tempdir().expect("tempdir");
        let info = mixed_plug_info(dir.path());

        let output = configure()
            .plug_info(&info)
            .build_declarations("siteKinds")
            .expect("builds");
        assert_eq!(output.library_name(), "siteKinds");
        assert_eq!(output.layers(), [info]);
        assert_eq!(
            declared_kinds(&output),
            [
                ("chargroup".to_owned(), Some("assembly".to_owned())),
                ("site_root".to_owned(), None)
            ]
        );
        output.with_family(|family| assert!(family.schemas().is_empty()));
    }

    /// A declaration family's name is its file's, so one that is no
    /// identifier is refused before anything is written.
    #[test]
    fn declaration_family_name_checked() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out = dir.path().join("generated");
        for name in ["../kinds", "site/kinds", "my-kinds", ""] {
            let error = configure()
                .out_dir(&out)
                .plug_info(mixed_plug_info(dir.path()))
                .declaration_family(name)
                .generate()
                .expect_err("not an identifier");
            assert!(
                matches!(&error, Error::InvalidDeclarationFamily { family } if family == name),
                "{error}"
            );
        }
        let written = fs::read_dir(&out).expect("the output directory").count();
        assert_eq!(written, 0, "nothing is written");
        assert!(!dir.path().join("kinds.rs").exists(), "nor beside it");
    }

    /// A declaration family no configured file declares a plugin for would
    /// write an empty file, so generation stops.
    #[test]
    fn unknown_declaration_family_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        let schema = missing_suffix(dir.path());

        let error = configure()
            .out_dir(dir.path().join("generated"))
            .schema(&schema)
            .plug_info(mixed_plug_info(dir.path()))
            .declaration_family("siteKindz")
            .generate()
            .expect_err("no plugin is called siteKindz");
        assert!(
            matches!(&error, Error::UnknownDeclarationFamily { family } if family == "siteKindz"),
            "{error}"
        );
    }

    /// One kind declared by two plugins would be refused by the registry, so
    /// generation refuses it first.
    #[test]
    fn duplicate_kind_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        let schema = missing_suffix(dir.path());
        let info = dir.path().join("twice.json");
        fs::write(
            &info,
            r#"{"Plugins": [
                {"Name": "testWarn", "Info": {"Kinds": {"prop": {"baseKind": "component"}}}},
                {"Name": "siteKinds", "Info": {"Kinds": {"prop": {}}}}
            ]}"#,
        )
        .expect("writes the plugInfo");

        let error = configure()
            .out_dir(dir.path().join("generated"))
            .schema(&schema)
            .plug_info(&info)
            .declaration_family("siteKinds")
            .generate()
            .expect_err("both declare prop");
        assert!(
            matches!(&error, Error::DuplicateKind { kind, .. } if kind == "prop"),
            "{error}"
        );
    }

    /// A plugin named after no library this run builds declares fields that
    /// would reach nothing, so generation stops.
    #[test]
    fn unknown_plugin_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        let schema = missing_suffix(dir.path());
        let info = plug_info(dir.path(), "testElsewhere", "role");

        let error = configure()
            .out_dir(dir.path().join("generated"))
            .schema(&schema)
            .plug_info(&info)
            .generate()
            .expect_err("no library is called testElsewhere");
        assert!(
            matches!(&error, Error::UnknownPlugin { plugin, path } if plugin == "testElsewhere" && path == &info),
            "{error}"
        );
    }

    /// A plugin's fields reach the library named after it: its schema data
    /// registers them, and the file is watched with the layers it read.
    #[test]
    fn plugin_fields_reach_library() {
        let dir = tempfile::tempdir().expect("tempdir");
        let schema = missing_suffix(dir.path());
        let info = plug_info(dir.path(), "testWarn", "role");

        let output = configure()
            .plug_info(&info)
            .build_library(&schema, Views::Generate)
            .expect("builds");
        assert!(output.layers().contains(&info), "{:?}", output.layers());
        let names: Vec<String> = output.with_family(|family| {
            family
                .declared_metadata()
                .iter()
                .map(|field| field.name().to_owned())
                .collect()
        });
        assert_eq!(names, vec!["role"]);
    }

    /// A list default is written into the declaration table as the value it
    /// decodes to, array and tuple alike.
    #[test]
    fn list_defaults_emitted() {
        let dir = tempfile::tempdir().expect("tempdir");
        let schema = missing_suffix(dir.path());
        let info = dir.path().join("plugInfo.json");
        fs::write(
            &info,
            r#"{"Plugins": [{"Name": "testWarn", "Info": {"SdfMetadata": {
                "weights": {"type": "double[]", "default": [0.0, 1.0], "appliesTo": "layers"},
                "up": {"type": "float3", "default": [0, 1, 0], "appliesTo": "layers"}
            }}}]}"#,
        )
        .expect("writes the plugInfo");

        let output = configure()
            .plug_info(&info)
            .build_library(&schema, Views::Generate)
            .expect("builds");
        let fallbacks: Vec<Option<sdf::Value>> = output.with_family(|family| {
            family
                .declared_metadata()
                .iter()
                .map(usd::MetadataDecl::declared_fallback)
                .collect()
        });
        assert!(
            fallbacks.contains(&Some(sdf::Value::DoubleVec(vec![0.0, 1.0]))),
            "{fallbacks:?}"
        );
        assert!(output.rust.contains(".fallback(||"), "{}", output.rust);
    }

    /// One field declared by two libraries would be refused by the registry,
    /// so generation refuses it first.
    #[test]
    fn duplicate_field_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        let first = missing_suffix(dir.path());
        let second_dir = dir.path().join("other");
        fs::create_dir(&second_dir).expect("creates a schema directory");
        let second = second_dir.join("schema.usda");
        fs::write(&second, MISSING_SUFFIX.replace("testWarn", "testOther")).expect("writes the schema");

        let error = configure()
            .out_dir(dir.path().join("generated"))
            .schema(&first)
            .schema(&second)
            .plug_info(plug_info(dir.path(), "testWarn", "role"))
            .plug_info(plug_info(dir.path(), "testOther", "role"))
            .generate()
            .expect_err("both declare role");
        assert!(
            matches!(&error, Error::DuplicateMetadataField { field, .. } if field == "role"),
            "{error}"
        );
    }

    /// Every layer a node library composes from is watched, a sublayer
    /// included, so an edit to any of them regenerates.
    #[test]
    fn shader_def_sublayers_watched() {
        let dir = tempfile::tempdir().expect("tempdir");
        let base = dir.path().join("base.usda");
        fs::write(
            &base,
            "#usda 1.0\n\ndef Shader \"UsdBase\"\n{\n    uniform token info:id = \"UsdBase\"\n}\n",
        )
        .expect("writes the sublayer");
        let root = dir.path().join("shaderDefs.usda");
        fs::write(&root, "#usda 1.0\n(\n    subLayers = [@./base.usda@]\n)\n").expect("writes the root");

        let output = configure()
            .extern_library("usdShade", "crate::shade")
            .build_shader_defs("testNodes", &root)
            .expect("generates");
        let watched: Vec<_> = output
            .layers()
            .iter()
            .map(|layer| layer.file_name().expect("a file").to_owned())
            .collect();
        assert_eq!(watched, vec!["shaderDefs.usda", "base.usda"]);
        assert!(output.rust.contains("pub struct Base("), "{}", output.rust);
    }

    /// A node taking its ports from a referenced layer watches that layer
    /// too, since the generated interface is read from it.
    #[test]
    fn shader_def_references_watched() {
        let dir = tempfile::tempdir().expect("tempdir");
        fs::write(
            dir.path().join("base.usda"),
            "#usda 1.0\n\ndef Shader \"Base\"\n{\n    float inputs:gain = 1\n}\n",
        )
        .expect("writes the referenced layer");
        let root = dir.path().join("shaderDefs.usda");
        fs::write(
            &root,
            "#usda 1.0\n\ndef Shader \"UsdGain\" (\n    references = @./base.usda@</Base>\n)\n{\n    uniform token info:id = \"UsdGain\"\n}\n",
        )
        .expect("writes the root");

        let output = configure()
            .extern_library("usdShade", "crate::shade")
            .build_shader_defs("testNodes", &root)
            .expect("generates");
        assert!(output.rust.contains("pub fn gain_input("), "{}", output.rust);
        let watched: Vec<_> = output
            .layers()
            .iter()
            .map(|layer| layer.file_name().expect("a file").to_owned())
            .collect();
        assert_eq!(watched, vec!["shaderDefs.usda", "base.usda"]);
    }

    /// A node referencing a layer that is not there fails generation rather
    /// than emitting the interface without what the layer would have given it.
    #[test]
    fn shader_def_missing_reference_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path().join("shaderDefs.usda");
        fs::write(
            &root,
            "#usda 1.0\n\ndef Shader \"UsdGain\" (\n    references = @./missing.usda@</Base>\n)\n{\n    uniform token info:id = \"UsdGain\"\n}\n",
        )
        .expect("writes the root");

        let error = configure()
            .extern_library("usdShade", "crate::shade")
            .build_shader_defs("testNodes", &root)
            .expect_err("the reference resolves to nothing");
        assert!(matches!(error, Error::Composition { .. }), "{error}");
    }

    /// A run configuring only shader definitions still generates them.
    #[test]
    fn shader_defs_alone_generated() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out = dir.path().join("generated");
        let defs = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/nodes/shaderDefs.usda");

        configure()
            .out_dir(&out)
            .extern_library("usdShade", "crate::shade")
            .shader_defs("tinyNodes", &defs)
            .generate()
            .expect("generates");
        assert!(out.join("tinyNodes.rs").is_file(), "the node library is written");
    }

    /// With schemas to build and nowhere to put them, generation stops rather
    /// than guessing.
    #[test]
    fn missing_out_dir_reported() {
        let error = configure()
            .schema("schemas/usdGeom/schema.usda")
            .generate()
            .expect_err("this crate has no build script, so its tests run without OUT_DIR set");

        assert!(matches!(error, Error::NoOutDir), "{error}");
    }

    /// A repeated option accumulates, except an extern library, which is keyed
    /// by library name and keeps the last declaration.
    ///
    /// Nothing reads either yet; they are what the generator will be given.
    #[test]
    fn repeated_options() {
        let builder = configure()
            .schema("schemas/usdGeom/schema.usda")
            .schema("schemas/usdLux/schema.usda")
            .extern_library("usdGeom", "crate::geom")
            .extern_library("usdGeom", "openusd_schemas::geom");

        assert_eq!(builder.schemas.len(), 2);
        assert_eq!(
            builder.extern_libraries.get("usdGeom").map(String::as_str),
            Some("openusd_schemas::geom")
        );
    }
}
