//! What a schema family declares, in the form a linked crate can hold.
//!
//! A registry needs two things from a family: how each schema applies and what
//! it derives from, and the properties a prim of that schema has before
//! anything is authored. [`family`] reads both out of a pair of layers, which
//! is what C++ installs beside a plugin. A crate that knows its schemas at
//! compile time has no file to open, so it declares them here instead, and
//! [`register`] builds the same data from the declaration.
//!
//! [`family`]: super::SchemaRegistryBuilder::family
//! [`register`]: super::SchemaRegistryBuilder::register
//!
//! Every builder is a `const fn`, so a whole family is one `static` and costs
//! nothing to construct:
//!
//! ```
//! use openusd::usd::{Field, PropertyDecl, SchemaDecl, SchemaFamily, SchemaKind};
//!
//! static SPHERES: &SchemaFamily<'_> = &SchemaFamily::new(
//!     "mySpheres",
//!     &[SchemaDecl::new("Ball", SchemaKind::ConcreteTyped)
//!         .bases(&["Typed"])
//!         .properties(&[
//!             PropertyDecl::attribute("radius", "double")
//!                 .fields(&[Field::new("default", || 1.0_f64.into())]),
//!             PropertyDecl::attribute("visibility", "token").fields(&[
//!                 Field::token("default", "inherited"),
//!                 Field::tokens("allowedTokens", &["inherited", "invisible"]),
//!             ]),
//!             PropertyDecl::relationship("proxyPrim"),
//!         ])],
//! );
//! ```
//!
//! The declaration is borrowed for the length of the call: a registration takes
//! what it needs into the registry's own storage, so a family built on the
//! stack may be dropped as soon as it is registered.

use crate::sdf;

use super::SchemaKind;

/// One multiple-apply instance name, and the only schemas that instance may be
/// applied to. An instance no restriction names keeps the schema-wide one.
pub type InstanceRestriction<'a> = (&'a str, &'a [&'a str]);

/// One schema family, as [`SchemaRegistryBuilder::register`] takes it.
///
/// [`SchemaRegistryBuilder::register`]: super::SchemaRegistryBuilder::register
///
/// The name is the family every schema in it belongs to, matching the
/// `libraryName` a `schema.usda` declares (`usdGeom`), and is what a
/// registration failure is reported against.
#[derive(Debug, Clone, Copy)]
pub struct SchemaFamily<'a> {
    pub(super) name: &'a str,
    pub(super) schemas: &'a [SchemaDecl<'a>],
}

/// One schema: how it applies, what it derives from, and what a prim of it has
/// before anything is authored.
///
/// Everything a manifest carries is a field here, and everything a schematics
/// class prim carries is either [`properties`](Self::properties),
/// [`fields`](Self::fields), or derived: the `typeName` of a concrete schema
/// is its identifier, its `apiSchemas` list comes from
/// [`applied_api_schemas`](Self::applied_api_schemas), and its `customData`
/// from [`override_property_names`](Self::override_property_names).
#[derive(Debug, Clone, Copy)]
pub struct SchemaDecl<'a> {
    pub(super) identifier: &'a str,
    pub(super) kind: SchemaKind,
    pub(super) bases: &'a [&'a str],
    pub(super) properties: &'a [PropertyDecl<'a>],
    pub(super) fields: &'a [Field<'a>],
    pub(super) applied_api_schemas: &'a [&'a str],
    pub(super) override_property_names: &'a [&'a str],
    pub(super) property_namespace_prefix: Option<&'a str>,
    pub(super) auto_apply_to: &'a [&'a str],
    pub(super) can_only_apply_to: &'a [&'a str],
    pub(super) instance_restrictions: &'a [InstanceRestriction<'a>],
    pub(super) allowed_instance_names: &'a [&'a str],
    pub(super) fallback_types: &'a [&'a str],
}

/// One property of a schema, under the name the schematics records it by — for
/// a multiple-apply schema that is the template name, prefix and all.
///
/// Variability and `custom` are authored as given, so a `uniform` relationship
/// stays uniform and a `custom` attribute stays custom.
#[derive(Debug, Clone, Copy)]
pub struct PropertyDecl<'a> {
    pub(super) name: &'a str,
    pub(super) kind: PropertyKind<'a>,
    pub(super) variability: sdf::Variability,
    pub(super) custom: bool,
    pub(super) fields: &'a [Field<'a>],
}

/// Whether a [`PropertyDecl`] declares an attribute, and under what type name,
/// or a relationship.
#[derive(Debug, Clone, Copy)]
pub(super) enum PropertyKind<'a> {
    Attribute(&'a str),
    Relationship,
}

/// One field on a class prim or a property, and the value it carries.
///
/// [`string`](Self::string), [`strings`](Self::strings),
/// [`token`](Self::token) and [`tokens`](Self::tokens) are the shapes a `const`
/// can hold, and between them they cover a fallback token, an `allowedTokens`
/// list and the display metadata a schema carries. Anything else — a number, a
/// vector, a dictionary — arrives through [`make`](Self::make), which a
/// `static` can hold because a non-capturing closure is a function pointer, or
/// through [`borrowed`](Self::borrowed) when the caller already holds the
/// value.
#[derive(Debug, Clone, Copy)]
pub struct Field<'a> {
    pub(super) name: &'a str,
    value: FieldValue<'a>,
}

/// What a [`Field`] holds. Private: a caller writes one of `Field`'s
/// constructors, and only the registry reads it back.
#[derive(Debug, Clone, Copy)]
enum FieldValue<'a> {
    Str(&'a str),
    Strings(&'a [&'a str]),
    Token(&'a str),
    Tokens(&'a [&'a str]),
    Built(fn() -> sdf::Value),
    Ref(&'a sdf::Value),
}

impl<'a> SchemaFamily<'a> {
    /// A family called `name` declaring `schemas`.
    pub const fn new(name: &'a str, schemas: &'a [SchemaDecl<'a>]) -> Self {
        Self { name, schemas }
    }

    /// The family name every schema in it belongs to.
    pub const fn name(&self) -> &'a str {
        self.name
    }

    /// The schemas it declares.
    pub const fn schemas(&self) -> &'a [SchemaDecl<'a>] {
        self.schemas
    }
}

impl<'a> SchemaDecl<'a> {
    /// A schema called `identifier` applying as `kind`, deriving from nothing
    /// and declaring no properties.
    pub const fn new(identifier: &'a str, kind: SchemaKind) -> Self {
        Self {
            identifier,
            kind,
            bases: &[],
            properties: &[],
            fields: &[],
            applied_api_schemas: &[],
            override_property_names: &[],
            property_namespace_prefix: None,
            auto_apply_to: &[],
            can_only_apply_to: &[],
            instance_restrictions: &[],
            allowed_instance_names: &[],
            fallback_types: &[],
        }
    }

    /// The schemas this one directly derives from, nearest first, by schema
    /// identifier. A base may belong to a family registered separately.
    pub const fn bases(mut self, bases: &'a [&'a str]) -> Self {
        self.bases = bases;
        self
    }

    /// The properties a prim of this schema has, in the order the schema
    /// declares them.
    pub const fn properties(mut self, properties: &'a [PropertyDecl<'a>]) -> Self {
        self.properties = properties;
        self
    }

    /// Metadata the class prim carries, which a registry serves as the prim
    /// metadata fallback of every prim of this schema.
    pub const fn fields(mut self, fields: &'a [Field<'a>]) -> Self {
        self.fields = fields;
        self
    }

    /// The API schemas this schema builds in, which a prim of it has applied
    /// without authoring them.
    pub const fn applied_api_schemas(mut self, schemas: &'a [&'a str]) -> Self {
        self.applied_api_schemas = schemas;
        self
    }

    /// The properties this schema restates only to change what an API schema
    /// it includes declares, rather than to declare its own.
    pub const fn override_property_names(mut self, names: &'a [&'a str]) -> Self {
        self.override_property_names = names;
        self
    }

    /// The namespace every property of a multiple-apply schema sits under.
    pub const fn property_namespace_prefix(mut self, prefix: &'a str) -> Self {
        self.property_namespace_prefix = Some(prefix);
        self
    }

    /// The schemas this API schema applies itself to, each carrying everything
    /// derived from it.
    pub const fn auto_apply_to(mut self, targets: &'a [&'a str]) -> Self {
        self.auto_apply_to = targets;
        self
    }

    /// The only schemas this API schema may be applied to. An empty list
    /// places no restriction.
    pub const fn can_only_apply_to(mut self, targets: &'a [&'a str]) -> Self {
        self.can_only_apply_to = targets;
        self
    }

    /// Per-instance overrides of
    /// [`can_only_apply_to`](Self::can_only_apply_to), each pairing an
    /// instance name with the only schemas that instance may be applied to.
    /// An instance the list does not name keeps the schema-wide restriction.
    pub const fn instance_restrictions(mut self, restrictions: &'a [InstanceRestriction<'a>]) -> Self {
        self.instance_restrictions = restrictions;
        self
    }

    /// The instance names a multiple-apply schema may be applied under. An
    /// empty list allows any name.
    pub const fn allowed_instance_names(mut self, names: &'a [&'a str]) -> Self {
        self.allowed_instance_names = names;
        self
    }

    /// The concrete schemas a stage falls back to for a prim of this type it
    /// does not know, strongest first.
    pub const fn fallback_types(mut self, types: &'a [&'a str]) -> Self {
        self.fallback_types = types;
        self
    }

    /// What the schema is called, which is what a registry looks it up by.
    pub const fn identifier(&self) -> &'a str {
        self.identifier
    }

    /// How the schema applies to a prim.
    pub const fn kind(&self) -> SchemaKind {
        self.kind
    }

    /// What [`bases`](Self::bases) declared.
    pub const fn declared_bases(&self) -> &'a [&'a str] {
        self.bases
    }

    /// What [`properties`](Self::properties) declared.
    pub const fn declared_properties(&self) -> &'a [PropertyDecl<'a>] {
        self.properties
    }

    /// What [`fields`](Self::fields) declared.
    pub const fn declared_fields(&self) -> &'a [Field<'a>] {
        self.fields
    }

    /// What [`applied_api_schemas`](Self::applied_api_schemas) declared.
    pub const fn declared_applied_api_schemas(&self) -> &'a [&'a str] {
        self.applied_api_schemas
    }

    /// What [`override_property_names`](Self::override_property_names)
    /// declared.
    pub const fn declared_override_property_names(&self) -> &'a [&'a str] {
        self.override_property_names
    }

    /// What [`property_namespace_prefix`](Self::property_namespace_prefix)
    /// declared.
    pub const fn declared_property_namespace_prefix(&self) -> Option<&'a str> {
        self.property_namespace_prefix
    }

    /// What [`auto_apply_to`](Self::auto_apply_to) declared.
    pub const fn declared_auto_apply_to(&self) -> &'a [&'a str] {
        self.auto_apply_to
    }

    /// What [`can_only_apply_to`](Self::can_only_apply_to) declared.
    pub const fn declared_can_only_apply_to(&self) -> &'a [&'a str] {
        self.can_only_apply_to
    }

    /// What [`instance_restrictions`](Self::instance_restrictions) declared.
    pub const fn declared_instance_restrictions(&self) -> &'a [InstanceRestriction<'a>] {
        self.instance_restrictions
    }

    /// What [`allowed_instance_names`](Self::allowed_instance_names) declared.
    pub const fn declared_allowed_instance_names(&self) -> &'a [&'a str] {
        self.allowed_instance_names
    }

    /// What [`fallback_types`](Self::fallback_types) declared.
    pub const fn declared_fallback_types(&self) -> &'a [&'a str] {
        self.fallback_types
    }
}

impl<'a> PropertyDecl<'a> {
    /// An attribute of the given type, varying and not custom.
    ///
    /// `type_name` is the type as a schema spells it (`double`, `float3[]`,
    /// `token`); a spelling [`sdf::ValueTypeName::find`] does not know is a
    /// registration error rather than a type of its own, since an attribute
    /// whose type nothing recognizes has no value a caller could read.
    // TODO: take a `sdf::ValueTypeName` and let the compiler check it, once one
    // can appear in a `const`. It cannot today: its unregistered form holds a
    // `tf::Token`, whose shared spelling is an `Arc<str>`, and a value with
    // drop glue is not promoted out of a `static` initializer. Interning shared
    // tokens (the `TODO(perf)` in `tf.rs`) or exposing a `Copy` handle for the
    // registered types would settle it and retire
    // `SchemaRegistryError::UnknownValueType` with it.
    pub const fn attribute(name: &'a str, type_name: &'a str) -> Self {
        Self {
            name,
            kind: PropertyKind::Attribute(type_name),
            variability: sdf::Variability::Varying,
            custom: false,
            fields: &[],
        }
    }

    /// A relationship, uniform and not custom.
    ///
    /// Uniform because that is what a bare `rel foo` means in a layer, where
    /// `varying rel foo` is the opt-out — so a family transcribed from a
    /// `generatedSchema.usda` means the same thing written either way.
    pub const fn relationship(name: &'a str) -> Self {
        Self {
            name,
            kind: PropertyKind::Relationship,
            variability: sdf::Variability::Uniform,
            custom: false,
            fields: &[],
        }
    }

    /// Declares the property `uniform`, so it may not vary over time.
    pub const fn uniform(mut self) -> Self {
        self.variability = sdf::Variability::Uniform;
        self
    }

    /// Declares the property `varying`, which an attribute already is.
    pub const fn varying(mut self) -> Self {
        self.variability = sdf::Variability::Varying;
        self
    }

    /// Declares the property `custom`, as a schema does for one it defines
    /// without claiming it.
    pub const fn custom(mut self) -> Self {
        self.custom = true;
        self
    }

    /// The property's fields: its `default` fallback, its `allowedTokens`, and
    /// whatever else the schema authored on it.
    pub const fn fields(mut self, fields: &'a [Field<'a>]) -> Self {
        self.fields = fields;
        self
    }

    /// The name the schematics records it by.
    pub const fn name(&self) -> &'a str {
        self.name
    }

    /// An attribute's declared type as the schema spells it, and `None` for a
    /// relationship.
    pub const fn type_name(&self) -> Option<&'a str> {
        match self.kind {
            PropertyKind::Attribute(type_name) => Some(type_name),
            PropertyKind::Relationship => None,
        }
    }

    /// Whether the property was declared `uniform`.
    pub const fn is_uniform(&self) -> bool {
        matches!(self.variability, sdf::Variability::Uniform)
    }

    /// Whether the property was declared `custom`.
    pub const fn is_custom(&self) -> bool {
        self.custom
    }

    /// The kind of spec this property is authored as.
    pub const fn spec_type(&self) -> sdf::SpecType {
        match self.kind {
            PropertyKind::Attribute(_) => sdf::SpecType::Attribute,
            PropertyKind::Relationship => sdf::SpecType::Relationship,
        }
    }

    /// What [`fields`](Self::fields) declared.
    pub const fn declared_fields(&self) -> &'a [Field<'a>] {
        self.fields
    }
}

impl<'a> Field<'a> {
    /// A `string`-valued field, as `displayName` and `displayGroup` are.
    pub const fn string(name: &'a str, text: &'a str) -> Self {
        Self {
            name,
            value: FieldValue::Str(text),
        }
    }

    /// A `token`-valued field, as a token attribute's `default` is.
    pub const fn token(name: &'a str, token: &'a str) -> Self {
        Self {
            name,
            value: FieldValue::Token(token),
        }
    }

    /// A `string[]`-valued field, which is how a text layer reads the bracketed
    /// list of an `allowedTokens`.
    pub const fn strings(name: &'a str, texts: &'a [&'a str]) -> Self {
        Self {
            name,
            value: FieldValue::Strings(texts),
        }
    }

    /// A `token[]`-valued field.
    pub const fn tokens(name: &'a str, tokens: &'a [&'a str]) -> Self {
        Self {
            name,
            value: FieldValue::Tokens(tokens),
        }
    }

    /// A field of any type, built when the family is registered. This is what
    /// a `static` declaration uses for a value no other constructor covers,
    /// since a non-capturing closure is a function pointer and so `const`.
    pub const fn new(name: &'a str, value: fn() -> sdf::Value) -> Self {
        Self {
            name,
            value: FieldValue::Built(value),
        }
    }

    /// A field of any type, borrowed from a caller that already holds the
    /// value — what a program declaring a family it computed at run time uses.
    pub const fn borrowed(name: &'a str, value: &'a sdf::Value) -> Self {
        Self {
            name,
            value: FieldValue::Ref(value),
        }
    }

    /// The field's name.
    pub const fn name(&self) -> &'a str {
        self.name
    }

    /// The value this field carries.
    ///
    /// Which constructor wrote it is not recorded: the value is the whole of
    /// what a field means, and its own type says which shape it took.
    pub fn value(&self) -> sdf::Value {
        match self.value {
            FieldValue::Str(text) => sdf::Value::String(text.to_owned()),
            FieldValue::Strings(texts) => sdf::Value::StringVec(texts.iter().map(|text| (*text).to_owned()).collect()),
            FieldValue::Token(token) => sdf::Value::token(token),
            FieldValue::Tokens(tokens) => sdf::Value::token_vec(tokens.iter().copied()),
            FieldValue::Built(build) => build(),
            FieldValue::Ref(value) => value.clone(),
        }
    }
}
