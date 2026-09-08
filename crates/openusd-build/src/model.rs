//! What the generator knows about a schema library, between reading it and
//! emitting from it.
//!
//! Every output reads this and nothing else. Composition is consulted once,
//! while [`Library`] is built, so the Rust emitter and the schematics writer
//! cannot come to different conclusions about one field — and so a schema is
//! read once however many files it produces.

use std::collections::BTreeMap;
use std::path::PathBuf;

use openusd::{sdf, tf, usd};

pub use crate::load::DeclaredToken;

/// The base every typed schema reaches. A schema that reaches it is one a
/// prim's `typeName` can name.
pub const TYPED: &str = "Typed";

/// The base every applied API schema inherits directly.
pub const API_SCHEMA_BASE: &str = "APISchemaBase";

/// The root every schema derives from, which a class inheriting nothing still
/// reaches and the manifest names for it.
pub const SCHEMA_BASE: &str = "SchemaBase";

/// The `customData` key a property sets to say it exists only to change a
/// built-in API schema's declaration, rather than to declare one of its own.
pub const API_SCHEMA_OVERRIDE: &str = "apiSchemaOverride";

/// The `apiSchemaType` an API schema declares to say it is never applied.
///
/// Saying nothing is not the same: an API schema that declares no kind is
/// single-apply, so only this spelling makes one non-applied.
pub const NON_APPLIED: &str = "nonApplied";

/// One schema library: what a single `schema.usda` and its sublayers declare.
#[derive(Debug)]
pub struct Library {
    /// The `libraryName` its `/GLOBAL` prim declares, which names the library
    /// wherever one library refers to another. Not the file's directory.
    pub name: String,
    /// Whether token identifiers keep the spelling the schema gave them
    /// (`useLiteralIdentifier`, default true).
    pub use_literal_identifiers: bool,
    /// Whether the library asked for schema data only, with no Rust
    /// (`skipCodeGeneration`).
    pub skip_code_generation: bool,
    /// The classes to generate, in the order the root layer declares them.
    ///
    /// A class a sublayer declares is not here. What a view can inherit from is
    /// therefore a class of this layer, one of the schema roots, or a class of
    /// a library that declares its own `libraryName` and generates its own
    /// views; anything else is reported as an ungenerated base.
    pub classes: Vec<Class>,
    /// Where every layer read was found, for a build script to watch.
    pub source_layers: Vec<PathBuf>,
    /// The tokens the library asks for outright, beyond what its schemas imply.
    pub declared_tokens: Vec<DeclaredToken>,
}

/// One schema: a class prim in the root layer, and everything generation needs
/// to know about it.
#[derive(Debug)]
pub struct Class {
    /// The registered identifier, which is the class prim's name.
    pub identifier: tf::Token,
    /// The identifier with any version suffix removed.
    pub family: tf::Token,
    /// The version its identifier's suffix names; 0 when it has none.
    pub version: u32,
    /// What kind of schema it is, which decides what the emitter writes and
    /// what the manifest records.
    pub kind: usd::SchemaKind,
    /// The inheritance chain, nearest first. Empty for a class that inherits
    /// nothing, whose implicit root is `SchemaBase`.
    pub bases: Vec<Base>,
    /// Every property the schema carries, its own and its ancestors', in the
    /// order the schematics writes them. Each records the class that declared
    /// it, so the emitter can take the local ones.
    pub properties: Vec<Property>,
    /// The API schemas applied to every instance of this schema, under the
    /// names the schematics records them by. A multiple-apply schema carries
    /// its built-ins under whatever instance name it is applied with, so those
    /// are templates rather than plain identifiers.
    pub applied_api_schemas: Vec<tf::Token>,
    /// The schema's own documentation, as the schema wrote it.
    pub documentation: Option<String>,
    /// Whether `Typed` is among its ancestors, which is what makes a schema
    /// instantiable.
    pub is_typed: bool,
    /// How many bases the class authored, which is at most one in a schema the
    /// generator can represent.
    pub authored_base_count: usize,
    /// The base the registry walks `is_a` up to: the class's own, or the root
    /// every schema derives from for a class that inherits nothing. `None` only
    /// on that root itself, which derives from nothing.
    pub direct_base: Option<tf::Token>,
    /// Every field authored on the class prim, by name.
    ///
    /// Kept apart from [`fields`](Self::fields) because flattening resolves
    /// composition away: a `references` or `variantSets` opinion is gone from
    /// the composed map, and validation has to see what the schema wrote to
    /// reject it.
    pub authored_fields: Vec<String>,
    /// Every field composition left on the class prim, its own and its
    /// ancestors'.
    ///
    /// These are the prim metadata a registry serves as fallbacks from the
    /// schema's definition — `hidden`, `assetInfo`, `propertyOrder` — so they
    /// travel whole exactly as a property's fields do, and the schematics
    /// writer is the one place that narrows them.
    pub fields: BTreeMap<String, sdf::Value>,
    /// The `typeName` as authored, before a parent declaring the same one
    /// clears it.
    pub authored_type_name: Option<tf::Token>,
    /// The `apiSchemas` list op as authored, whose mode validation checks.
    pub api_schemas_op: Option<sdf::TokenListOp>,
    /// What its `customData` asked for.
    pub metadata: Metadata,
    /// Where it was declared.
    pub origin: Origin,
}

/// A class this one inherits from.
#[derive(Debug, Clone)]
pub struct Base {
    /// The identifier it is registered under.
    pub identifier: tf::Token,
    /// The library declaring it, when that is not the library being generated.
    /// Its views live in another crate or module, reached through the
    /// `extern_library` mapping.
    pub library: Option<String>,
    /// The class name it declares (`className`), defaulting to its identifier
    /// in proper case. What a generator makes of it is the generator's own.
    pub class_name: String,
    /// What kind of schema it is, classified against what stands behind it.
    pub kind: usd::SchemaKind,
}

/// A class's `customData`, with what the registry reads kept apart from what
/// only this crate reads.
///
/// The first group is runtime meaning: it reaches the manifest and decides how
/// a stage composes and what `can_apply` answers. The second is generator
/// convention, and steers the Rust alone.
#[derive(Debug, Default)]
pub struct Metadata {
    /// The namespace every property of a multiple-apply schema sits under.
    pub property_namespace_prefix: Option<tf::Token>,
    /// Schemas this API schema is applied to automatically.
    pub auto_apply_to: Vec<tf::Token>,
    /// The only schemas this API schema may be applied to.
    pub can_only_apply_to: Vec<tf::Token>,
    /// The only instance names a multiple-apply schema admits.
    pub allowed_instance_names: Vec<tf::Token>,
    /// Per-instance overrides of [`can_only_apply_to`](Self::can_only_apply_to).
    pub instance_restrictions: BTreeMap<tf::Token, Vec<tf::Token>>,
    /// The concrete schemas a stage falls back to for this type.
    pub fallback_types: Vec<tf::Token>,

    /// The Rust type name, which defaults to the identifier in proper case.
    pub class_name: String,
    /// Single-apply API schemas whose accessors this class re-emits.
    ///
    // TODO: nothing reads this yet. Re-emitting a reflected schema's accessors
    // as delegates on the reflecting class is the missing feature.
    #[allow(dead_code)]
    pub reflected_api_schemas: Vec<tf::Token>,
    /// The tokens this schema asks for outright, beyond what its properties
    /// imply.
    pub schema_tokens: Vec<DeclaredToken>,
}

/// One property of a schema.
///
/// The authored fields travel whole, in [`fields`](Self::fields): validation
/// has to see a field it means to reject, the emitter reads the documentation,
/// and the schematics writer is the one place that drops what a schematics
/// does not carry. The accessors below are typed reads over that map, so no
/// two consumers can disagree about a value.
#[derive(Debug)]
pub struct Property {
    /// The name the schema declared, without a namespace prefix.
    pub name: tf::Token,
    /// The name the schematics records. For a multiple-apply schema this is
    /// the template `prefix:__INSTANCE_NAME__:name`.
    pub schematics_name: tf::Token,
    /// Whether it is an attribute or a relationship.
    pub spec_type: sdf::SpecType,
    /// Every class declaring it, nearest first: this class where it redeclares
    /// the property, then each ancestor that declared it.
    ///
    /// The composed result cannot say which class asked for what, and two
    /// questions need to know. The strongest site decides what the property is,
    /// and a rule about a redeclaration compares that against the weaker ones.
    pub sites: Vec<Site>,
    /// Whether this class declares it in its own layer, which a redeclaration
    /// does as much as a first declaration.
    ///
    /// A redeclaration is both a declaration and an inheritance: an ancestor
    /// introduced the property, and this class still declares it — to change
    /// its fallback, or to ask for the accessor the ancestor suppressed.
    pub is_local: bool,
    /// What its `customData` asked the generator for.
    pub api: PropertyApi,
    /// Every field authored on it, composed over the layers that declare it.
    pub fields: BTreeMap<String, sdf::Value>,
    /// Where it was declared.
    pub origin: Origin,
}

/// One class's declaration of a property.
#[derive(Debug)]
pub struct Site {
    /// The class that declared it.
    pub class: tf::Token,
    /// Whether that declaration asked for `apiSchemaOverride`.
    pub is_override: bool,
    /// The accessor name that declaration asked for, or `None` where it asked
    /// for none.
    ///
    /// A class redeclaring an ancestor's property has to know what the ancestor
    /// called it, and the ancestor may be declared in a library this run does
    /// not generate — so the name travels with the site rather than being
    /// looked up on a class that may not be here.
    pub api_name: Option<String>,
    /// Where it was written.
    pub origin: Origin,
}

/// A property's `customData`, which steers its accessor and nothing else.
#[derive(Debug, Default)]
pub struct PropertyApi {
    /// Whether the library supplies the read accessor by hand
    /// (`apiGetImplementation = "custom"`), so the emitter writes everything
    /// but that one method and leaves its name free.
    pub custom_get: bool,
}

/// Where something was declared, so a diagnostic names the file a contributor
/// has to open.
#[derive(Debug, Clone)]
pub struct Origin {
    /// The layer that declared it.
    pub layer: String,
    /// Its path in that layer.
    pub path: sdf::Path,
}

impl Class {
    /// Where the schema data records it, which is also where the registry looks
    /// for it: a root prim named by the identifier.
    pub fn prim_path(&self) -> Result<sdf::Path, sdf::PathParseError> {
        sdf::Path::abs_root().append_path(self.identifier.as_str())
    }

    /// The properties this class declares itself, in schematics order,
    /// including any it redeclares.
    pub fn local_properties(&self) -> impl Iterator<Item = &Property> {
        self.properties.iter().filter(|property| property.is_local)
    }

    /// The properties this schema declares only to override a built-in API
    /// schema's, which reach the schematics and get no accessor.
    pub fn override_properties(&self) -> impl Iterator<Item = &Property> {
        self.properties.iter().filter(|property| property.is_override())
    }
}

impl Property {
    /// One authored field, decoded. `None` when it is unauthored or holds
    /// another type.
    ///
    /// The defaults the accessors below apply are the ones `sdf` applies to
    /// the same fields on a property spec; this reads them off the composed
    /// map instead, which is where the schematics writer needs them.
    fn field<T: TryFrom<sdf::Value>>(&self, key: sdf::FieldKey) -> Option<T> {
        self.fields.get(key.as_str())?.clone().get()
    }

    /// An attribute's declared type. `None` for a relationship, and for an
    /// attribute whose `typeName` names no registered type — which validation
    /// rejects, since an accessor would have no type to read. Unlike every
    /// other reader in the workspace this resolves through
    /// `ValueTypeName::find`, so an unregistered spelling stays visible rather
    /// than becoming an unregistered type name.
    pub fn type_name(&self) -> Option<sdf::ValueTypeName> {
        let name: tf::Token = self.field(sdf::FieldKey::TypeName)?;
        sdf::ValueTypeName::find(name.as_str())
    }

    /// Whether the property may only be authored at the default time, which
    /// USD leaves varying unless a schema says otherwise.
    pub fn variability(&self) -> sdf::Variability {
        self.field(sdf::FieldKey::Variability).unwrap_or_default()
    }

    /// Whether the schema declared it `custom`, which its creator authors.
    pub fn is_custom(&self) -> bool {
        self.field(sdf::FieldKey::Custom).unwrap_or(false)
    }

    /// The fallback a stage resolves when nothing is authored.
    pub fn fallback(&self) -> Option<&sdf::Value> {
        self.fields.get(sdf::FieldKey::Default.as_str())
    }

    /// The values a token attribute admits, which the tokens module emits and
    /// the accessor's documentation lists.
    ///
    /// Read as tokens or as strings: `allowedTokens` is `token[]` in the schema
    /// SDF declares, but the text parser types the metadata it does not know
    /// from the values it sees, so a list of quoted names arrives as strings.
    ///
    /// TODO: type it in the parser instead, which would let this be one read.
    pub fn allowed_tokens(&self) -> Vec<tf::Token> {
        let Some(value) = self.fields.get(sdf::FieldKey::AllowedTokens.as_str()) else {
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

    /// The property's own documentation, as the schema wrote it.
    pub fn documentation(&self) -> Option<&str> {
        self.fields
            .get(sdf::FieldKey::Documentation.as_str())?
            .try_as_string_ref()
            .map(String::as_str)
    }

    /// The accessor's name before Rust casing, or `None` where this class
    /// asked for no accessor — an `apiName` of `""`, an override, or a
    /// property it only inherits.
    ///
    /// The strongest site is this class's own declaration exactly where it has
    /// one, which is what [`is_local`](Self::is_local) says.
    pub fn api_name(&self) -> Option<&str> {
        let site = self.sites.first()?;
        self.is_local.then_some(site.api_name.as_deref()).flatten()
    }

    /// Whether an accessor is emitted for it at all.
    pub fn has_accessor(&self) -> bool {
        self.api_name().is_some()
    }

    /// Whether the schematics records it among the class's API schema override
    /// property names.
    ///
    /// The strongest declaration decides: this class's where it redeclares the
    /// property, the nearest ancestor's otherwise. An override therefore
    /// reaches a class that says nothing about the property at all.
    pub fn is_override(&self) -> bool {
        self.sites.first().is_some_and(|site| site.is_override)
    }
}

impl Origin {
    /// Names the declaration the way a diagnostic should: the layer, then the
    /// path inside it.
    pub fn describe(&self) -> String {
        format!("{}{}", self.layer, self.path)
    }
}
