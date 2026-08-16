//! What a schema declares: its properties, their fallback values, and the API
//! schemas it includes.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use anyhow::{Result, bail};

use crate::{sdf, tf};

use super::{SchemaInfo, SchemaRegistry, Schematics, schema_registry};

/// The properties and metadata a prim of some type has before anything is
/// authored (C++ `UsdPrimDefinition`).
///
/// A definition owns no values. Each property name maps to the schematics
/// store and path that declares it, so reading a fallback is a field read
/// against data the registry already holds. That makes a definition cheap to
/// clone — token maps and `Arc` handles — which is what
/// [`SchemaRegistry::build_composed_prim_definition`](super::SchemaRegistry::build_composed_prim_definition)
/// relies on.
///
/// Definitions come from [`SchemaRegistry`](super::SchemaRegistry): one per
/// registered concrete type and applied API schema, plus composed ones built
/// on demand for a prim's particular type and `apiSchemas` list.
#[derive(Debug, Clone, Default)]
pub struct PrimDefinition {
    /// Where each property is declared. The empty token maps to the class
    /// prim itself, so prim metadata and property fields resolve through one
    /// path — the same trick C++ uses.
    prop_map: HashMap<tf::Token, LayerAndPath>,
    properties: Vec<tf::Token>,
    applied_api_schemas: Vec<tf::Token>,
    /// Fields written during composition, when a property's value could not be
    /// referenced from a schematics store unchanged. Allocated only if some
    /// property needs it.
    composed: Option<sdf::Data>,
}

/// A property of a [`PrimDefinition`], borrowed from the store that declares
/// it.
#[derive(Debug, Clone, Copy)]
pub struct DefProperty<'a> {
    definition: &'a PrimDefinition,
    entry: &'a LayerAndPath,
}

/// Where one property (or the class prim itself) is declared.
#[derive(Debug, Clone)]
struct LayerAndPath {
    store: DefStore,
    /// The schematics whose class prim this entry's value came from, kept even
    /// when the value was copied into the composed store, so a fallback can say
    /// where it was authored. Which contribution a composed entry names is
    /// [`value_origin`]'s decision.
    schematics: Arc<Schematics>,
    path: sdf::Path,
}

/// Which store a [`LayerAndPath`] resolves against.
#[derive(Debug, Clone)]
enum DefStore {
    /// A registered family's schematics, shared with the registry.
    Schematics,
    /// The owning definition's own [`PrimDefinition::composed`] store. Cloning
    /// a definition clones that store with it, so the clone's entries resolve
    /// against the clone's own copy.
    Composed,
}

/// One schema's contribution to a composed property.
#[derive(Debug, Clone, Copy)]
struct Contribution<'a> {
    /// The spec that schema declares for the property.
    spec: &'a sdf::SpecData,
    /// The schematics the spec was read from.
    origin: &'a Arc<Schematics>,
}

/// One version per (schema family, instance name) composed so far. Applying two
/// versions of the same family to the same instance is a conflict.
pub(super) type FamilyVersions = HashMap<(tf::Token, Option<tf::Token>), u32>;

/// The name under which a definition holds its class prim's own metadata.
const PRIM_METADATA: tf::Token = tf::Token::new("");

/// The prim every composed property spec hangs off inside
/// [`PrimDefinition::composed`]. Only the owning definition reads that store,
/// so one fixed name suffices.
const COMPOSED_PRIM: &str = "ComposedProperties";

impl PrimDefinition {
    /// The properties this definition declares, in definition order.
    pub fn property_names(&self) -> &[tf::Token] {
        &self.properties
    }

    /// Whether `name` is declared here.
    pub fn has_property(&self, name: &tf::Token) -> bool {
        self.prop_map.contains_key(name)
    }

    /// The API schemas that contribute to this definition, strongest first.
    ///
    /// An applied API schema's own definition lists itself first, matching
    /// C++; a typed schema's lists its built-ins.
    pub fn applied_api_schemas(&self) -> &[tf::Token] {
        &self.applied_api_schemas
    }

    /// Whether this definition declares nothing at all — the answer for a
    /// typeless prim, or one whose type the registry does not know.
    pub fn is_empty(&self) -> bool {
        self.prop_map.is_empty() && self.applied_api_schemas.is_empty()
    }

    /// Looks up one property.
    pub fn property(&self, name: &tf::Token) -> Option<DefProperty<'_>> {
        // The empty name addresses the class prim internally; it is not a
        // property, so it must not be reachable this way.
        if name.as_str().is_empty() {
            return None;
        }
        self.entry(name)
    }

    /// Reads a prim-level metadata field the schema declares, such as
    /// `documentation` (C++ `GetMetadata`).
    ///
    /// Fields that cannot mean anything as a fallback read back `None`; see
    /// [`SchemaRegistry::is_disallowed_field`](super::SchemaRegistry::is_disallowed_field).
    pub fn metadata(&self, field: impl AsRef<str>) -> Option<&sdf::Value> {
        self.entry(&PRIM_METADATA)?.field(field)
    }

    /// The fallback value of an attribute this definition declares
    /// (C++ `UsdPrimDefinition::GetAttributeFallbackValue`).
    ///
    /// A relationship, an attribute with no declared default, and a default
    /// authored as a value block all read back `None` — a schema cannot block
    /// a value that has no weaker opinion to block.
    pub fn attribute_fallback(&self, name: &tf::Token) -> Option<sdf::Value> {
        self.property(name)?.attribute_fallback()
    }

    /// Looks up an entry by name, including the class prim under
    /// [`PRIM_METADATA`].
    fn entry(&self, name: &tf::Token) -> Option<DefProperty<'_>> {
        self.prop_map.get(name).map(|entry| DefProperty {
            definition: self,
            entry,
        })
    }

    /// Builds the definition of one schema from its class prim in a family's
    /// schematics.
    ///
    /// `applied_name` is the name an applied API schema contributes under —
    /// its identifier, or its instance-name template when it is a
    /// multiple-apply schema — and seeds
    /// [`applied_api_schemas`](Self::applied_api_schemas), which every applied
    /// API schema's definition starts with. `overrides` names the properties
    /// the class prim declares only to override a built-in's; they are not
    /// installed here, and are composed over the built-in once it contributes.
    pub(super) fn from_class_prim(
        schematics: &Arc<Schematics>,
        identifier: &tf::Token,
        applied_name: Option<tf::Token>,
        overrides: &[tf::Token],
    ) -> Result<PrimDefinition> {
        let path = sdf::Path::abs_root().append_path(identifier.as_str())?;
        if schematics.data().spec(&path).is_none() {
            bail!(
                "No class prim for schema {identifier} in the schematics of family {}",
                schematics.family()
            );
        }

        // Only a schema that applies whole contributes prim metadata. A
        // multiple-apply schema is a template applied under an instance name,
        // and its class prim describes the template, not the prims using it.
        let contributes_metadata = applied_name
            .as_ref()
            .is_none_or(|name| schema_registry::split_instance_name(name).1.is_none());

        let mut definition = PrimDefinition {
            applied_api_schemas: applied_name.into_iter().collect(),
            ..PrimDefinition::default()
        };

        if contributes_metadata {
            let entry = LayerAndPath {
                store: DefStore::Schematics,
                schematics: schematics.clone(),
                path: path.clone(),
            };
            definition.prop_map.insert(PRIM_METADATA, entry);
        }

        let overrides: HashSet<&tf::Token> = overrides.iter().collect();
        for name in child_names(schematics.data(), &path, sdf::ChildrenKey::PropertyChildren) {
            if overrides.contains(&name) {
                continue;
            }
            let entry = LayerAndPath {
                store: DefStore::Schematics,
                schematics: schematics.clone(),
                path: path.append_property(name.as_str())?,
            };
            definition.prop_map.insert(name.clone(), entry);
            definition.properties.push(name);
        }

        definition.apply_property_order();
        Ok(definition)
    }

    /// Composes a weaker API schema's definition into this one
    /// (C++ `_ComposeWeakerAPIPrimDefinition`).
    ///
    /// `instance` names the instance a multiple-apply schema is contributing
    /// under; its property and built-in names have the instance substituted for
    /// the placeholder. `seen` carries the versions already composed, and the
    /// whole contribution is refused — including the built-ins the weaker
    /// definition brings — if any of them would apply a second version of a
    /// family to the same instance.
    pub(super) fn compose_weaker_api(
        &mut self,
        weaker: &PrimDefinition,
        instance: Option<&tf::Token>,
        infos: &HashMap<tf::Token, SchemaInfo>,
        seen: &mut FamilyVersions,
    ) {
        let names: Vec<tf::Token> = match instance {
            Some(instance) => weaker
                .applied_api_schemas
                .iter()
                .map(|name| schema_registry::make_instance_name(name, instance))
                .collect(),
            None => weaker.applied_api_schemas.clone(),
        };

        if self.append_api_schemas(names, infos, seen) {
            self.compose_properties_from(weaker, instance);
        }
    }

    /// Appends applied-schema names, rejecting the whole batch if any would
    /// conflict with a version already composed.
    fn append_api_schemas(
        &mut self,
        names: Vec<tf::Token>,
        infos: &HashMap<tf::Token, SchemaInfo>,
        seen: &mut FamilyVersions,
    ) -> bool {
        let start = self.applied_api_schemas.len();
        let mut added = Vec::with_capacity(names.len());

        for name in names {
            let (identifier, instance) = schema_registry::split_instance_name(&name);
            let Some(info) = infos.get(&identifier) else {
                continue;
            };
            let key = (info.family().clone(), instance);

            match seen.get(&key) {
                None => {
                    seen.insert(key.clone(), info.version());
                    self.applied_api_schemas.push(name);
                    added.push(key);
                }
                Some(&version) if version == info.version() => {}
                Some(_) => {
                    self.applied_api_schemas.truncate(start);
                    for key in added {
                        seen.remove(&key);
                    }
                    return false;
                }
            }
        }
        true
    }

    /// Copies a weaker definition's properties in, composing fields into any
    /// this definition already declares
    /// (C++ `_ComposePropertiesFromPrimDef`).
    fn compose_properties_from(&mut self, weaker: &PrimDefinition, instance: Option<&tf::Token>) {
        let mut names: Vec<&tf::Token> = weaker.prop_map.keys().collect();
        names.sort_by(|a, b| sdf::element_cmp(a, b));

        for name in names {
            let instanced = match instance {
                Some(instance) => schema_registry::make_instance_name(name, instance),
                None => name.clone(),
            };
            self.add_or_compose_property(instanced, weaker, &weaker.prop_map[name]);
        }
    }

    /// Installs one property from a weaker definition, or composes its fields
    /// into the existing one (C++ `_AddOrComposeProperty`).
    ///
    /// `entry` is where `weaker` declares the property; it is installed as-is
    /// when it points at shared schematics, so the common case copies nothing.
    fn add_or_compose_property(&mut self, name: tf::Token, weaker: &PrimDefinition, entry: &LayerAndPath) {
        // Prim metadata composed into a definition that has none of its own
        // starts from a blank spec, since a weaker schema's prim metadata is
        // only ever a fill-in.
        let is_metadata = name == PRIM_METADATA;
        if is_metadata && !self.prop_map.contains_key(&PRIM_METADATA) {
            let weak = weaker.snapshot(entry);
            let weak = Contribution {
                spec: &weak,
                origin: &entry.schematics,
            };
            if let Some(composed) = self.materialize(&name, None, weak) {
                self.prop_map.insert(PRIM_METADATA, composed);
            }
            return;
        }

        let Some(existing) = self.prop_map.get(&name) else {
            let installed = match entry.store {
                DefStore::Schematics => entry.clone(),
                DefStore::Composed => {
                    match self.write_composed(&name, &weaker.snapshot(entry), entry.schematics.clone()) {
                        Some(installed) => installed,
                        None => return,
                    }
                }
            };
            self.prop_map.insert(name.clone(), installed);
            if !is_metadata {
                self.properties.push(name);
            }
            return;
        };

        // The existing entry borrows `self`, which `materialize` takes
        // mutably, so its origin is taken by value here.
        let strong_origin = existing.schematics.clone();
        let strong_spec = self.snapshot(existing);
        let weak_spec = weaker.snapshot(entry);
        let strong = Contribution {
            spec: &strong_spec,
            origin: &strong_origin,
        };
        let weak = Contribution {
            spec: &weak_spec,
            origin: &entry.schematics,
        };
        if let Some(composed) = self.materialize(&name, Some(strong), weak) {
            self.prop_map.insert(name, composed);
        }
    }

    /// Composes a class prim's override property over the definition it
    /// overrides (C++ `_ComposeOverAndReplaceExistingProperty`).
    ///
    /// The override's own fields win, the overridden definition fills in the
    /// rest, and variability stays the overridden property's — an override may
    /// change a fallback but not whether the property can animate. An override
    /// of a property no definition declares, or one whose type disagrees, is
    /// ignored.
    pub(super) fn compose_override(&mut self, name: &tf::Token, schematics: &Arc<Schematics>, class_prim: &sdf::Path) {
        let Some(existing) = self.prop_map.get(name) else {
            return;
        };
        let Ok(path) = class_prim.append_property(name.as_str()) else {
            return;
        };

        let mut composed = read_spec(schematics.data(), &path);
        let defined = self.snapshot(existing);
        if !types_match(&composed, &defined) {
            return;
        }
        let origin = value_origin(
            Some(Contribution {
                spec: &composed,
                origin: schematics,
            }),
            Contribution {
                spec: &defined,
                origin: &existing.schematics,
            },
        );

        let variability = defined
            .get(sdf::FieldKey::Variability.as_str())
            .cloned()
            .unwrap_or(sdf::Value::Variability(sdf::Variability::default()));

        for (field, value) in defined.fields {
            if !composed.contains(&field) {
                composed.add(field, value);
            }
        }
        composed.add(sdf::FieldKey::Variability, variability);

        if let Some(installed) = self.write_composed(name, &composed, origin) {
            self.prop_map.insert(name.clone(), installed);
        }
    }

    /// Composes the fields a weaker spec contributes over a stronger one,
    /// materializing the result when there is anything to add
    /// (C++ `_CreateComposedPrimOrPropertyIfNeeded`).
    ///
    /// Each contribution arrives with the schematics that authored it, so the
    /// materialized spec can still say where its value was declared.
    ///
    /// Returns `None` when the weaker spec contributes nothing, leaving the
    /// existing entry untouched.
    fn materialize(
        &mut self,
        name: &tf::Token,
        strong: Option<Contribution<'_>>,
        weak: Contribution<'_>,
    ) -> Option<LayerAndPath> {
        let merged = compose_fields(strong.map(|strong| strong.spec), weak.spec)?;
        let origin = value_origin(strong, weak);

        let mut composed = match strong {
            Some(strong) => strong.spec.clone(),
            None => sdf::SpecData::new(weak.spec.ty),
        };
        for (field, value) in merged {
            composed.add(field, value);
        }
        self.write_composed(name, &composed, origin)
    }

    /// Writes a spec into this definition's composed store, creating the store
    /// on first use, and returns the entry that reaches it.
    ///
    /// `origin` is the schematics the written spec stands for, which
    /// [`value_origin`] picks from the contributors that made it.
    fn write_composed(
        &mut self,
        name: &tf::Token,
        spec: &sdf::SpecData,
        origin: Arc<Schematics>,
    ) -> Option<LayerAndPath> {
        let path = composed_path(name)?;
        let composed = self.composed.get_or_insert_with(sdf::Data::default);
        *composed.create_spec(path.clone(), spec.ty) = spec.clone();

        Some(LayerAndPath {
            store: DefStore::Composed,
            schematics: origin,
            path,
        })
    }

    /// Takes an owned copy of what one of this definition's entries declares.
    fn snapshot(&self, entry: &LayerAndPath) -> sdf::SpecData {
        match self.store_of(entry) {
            Some(store) => read_spec(store, &entry.path),
            None => sdf::SpecData::new(sdf::SpecType::default()),
        }
    }

    /// The store one of this definition's entries resolves against.
    fn store_of<'a>(&'a self, entry: &'a LayerAndPath) -> Option<&'a sdf::Data> {
        match entry.store {
            DefStore::Schematics => Some(entry.schematics.data()),
            DefStore::Composed => self.composed.as_ref(),
        }
    }

    /// Puts [`properties`](Self::property_names) in their final order once every
    /// tier has contributed: element order, then the class prim's
    /// `propertyOrder` (C++ sorts and re-applies the order per composed tier;
    /// the result only has to hold at the end).
    pub(super) fn finish_composition(&mut self) {
        self.properties.sort_by(|a, b| sdf::element_cmp(a, b));
        self.apply_property_order();
    }

    /// Reorders [`properties`](Self::property_names) by the class prim's
    /// `propertyOrder` metadata (C++ `_ApplyPropertyOrder`).
    fn apply_property_order(&mut self) {
        let Some(order) = self
            .metadata(sdf::FieldKey::PropertyOrder)
            .and_then(|value| value.clone().try_as_token_vec())
        else {
            return;
        };
        sdf::apply_ordering(&mut self.properties, &order);
    }
}

impl<'a> DefProperty<'a> {
    /// Whether this is an attribute or a relationship.
    pub fn spec_type(&self) -> sdf::SpecType {
        self.store()
            .and_then(|store| store.spec(&self.entry.path))
            .map_or_else(sdf::SpecType::default, |spec| spec.ty)
    }

    /// Reads one of the property's fields, borrowed from the store that
    /// declares it.
    ///
    /// Fields that cannot mean anything as a fallback read back `None`; see
    /// [`SchemaRegistry::is_disallowed_field`](super::SchemaRegistry::is_disallowed_field).
    pub fn field(&self, name: impl AsRef<str>) -> Option<&'a sdf::Value> {
        let name = name.as_ref();
        if SchemaRegistry::is_disallowed_field(name) {
            return None;
        }
        self.store()?.spec(&self.entry.path)?.get(name)
    }

    /// The property's declared value type, as its `typeName` token.
    pub fn type_name(&self) -> Option<tf::Token> {
        self.field(sdf::FieldKey::TypeName)?.clone().try_as_token()
    }

    /// Whether the property may vary over time. Attributes are varying unless
    /// the schema declares otherwise; relationships are uniform, which is what
    /// `SdfRelationshipSpec` declares and what schematics therefore omit.
    pub fn variability(&self) -> sdf::Variability {
        if let Some(declared) = self
            .field(sdf::FieldKey::Variability)
            .and_then(|value| value.clone().try_as_variability())
        {
            return declared;
        }
        match self.spec_type() {
            sdf::SpecType::Relationship => sdf::Variability::Uniform,
            _ => sdf::Variability::default(),
        }
    }

    /// This property's fallback value when it is an attribute
    /// (C++ `UsdPrimDefinition::GetAttributeFallbackValue`).
    ///
    /// A relationship reads back `None`: only an attribute carries a value.
    pub fn attribute_fallback(&self) -> Option<sdf::Value> {
        if self.spec_type() != sdf::SpecType::Attribute {
            return None;
        }
        self.fallback()
    }

    /// The property's fallback value, with a value block read as no value.
    pub fn fallback(&self) -> Option<sdf::Value> {
        match self.field(sdf::FieldKey::Default)?.clone() {
            sdf::Value::ValueBlock | sdf::Value::None => None,
            value => Some(value),
        }
    }

    /// The schematics that authored this property's fallback value — where a
    /// relative asset path in it is anchored.
    ///
    /// Named for the fallback alone because that is all it answers for: a
    /// property composed from more than one schema can take another field from
    /// another family, which this does not report — and where no contributor
    /// authored a fallback at all, it names one arbitrarily.
    pub fn fallback_source(&self) -> &'a Schematics {
        &self.entry.schematics
    }

    /// The store this property's fields live in.
    fn store(&self) -> Option<&'a sdf::Data> {
        self.definition.store_of(self.entry)
    }
}

/// Which contribution a composed spec stands for: the one that authored its
/// `default`, since that is the one field a fallback value read returns and so
/// the only one whose anchor is observable.
///
/// With neither side authoring a `default` there is no value to anchor, and the
/// stronger contributor stands for the spec — or the weaker one when it is the
/// sole contribution, as it is for a prim-metadata fill-in.
///
/// TODO: per-field provenance. One origin per spec can answer for one field, so
/// a composed spec taking its `default` from one family and an asset-valued
/// metadatum from another cannot anchor both; an origin recorded per field in
/// the composed store would, and would let a schema metadatum anchor too.
fn value_origin(strong: Option<Contribution<'_>>, weak: Contribution<'_>) -> Arc<Schematics> {
    let authors_default = |spec: &sdf::SpecData| spec.contains(sdf::FieldKey::Default.as_str());
    match strong {
        Some(strong) if authors_default(strong.spec) => strong.origin.clone(),
        _ if authors_default(weak.spec) => weak.origin.clone(),
        Some(strong) => strong.origin.clone(),
        None => weak.origin.clone(),
    }
}

/// Copies a spec out of a store, keeping only the fields that can mean
/// something as a fallback (C++ composes off `Property::ListMetadataFields`,
/// which applies the same filter).
///
/// Dropping them here rather than on read keeps them out of the composed store
/// entirely, so a property whose only weaker contribution is a disallowed field
/// keeps its zero-copy schematics entry.
fn read_spec(data: &sdf::Data, path: &sdf::Path) -> sdf::SpecData {
    let mut spec = data
        .spec(path)
        .cloned()
        .unwrap_or_else(|| sdf::SpecData::new(sdf::SpecType::default()));
    spec.fields
        .retain(|(field, _)| !SchemaRegistry::is_disallowed_field(field));
    spec
}

/// The child names a spec lists under `key`, in authored order.
pub(super) fn child_names(data: &sdf::Data, path: &sdf::Path, key: sdf::ChildrenKey) -> Vec<tf::Token> {
    data.spec(path)
        .and_then(|spec| spec.get(key.as_str()))
        .and_then(|value| value.clone().try_as_token_vec())
        .unwrap_or_default()
}

/// The fields a weaker spec contributes over a stronger one, or `None` when it
/// contributes nothing.
///
/// A field the stronger spec already declares is kept, except for
/// `propertyOrder` and dictionary-valued fields, which merge: order entries
/// append after the stronger ones without duplicating, dictionaries compose
/// recursively. Documentation never comes from a weaker schema, and neither
/// does a property's `custom` flag.
fn compose_fields(strong: Option<&sdf::SpecData>, weak: &sdf::SpecData) -> Option<Vec<(String, sdf::Value)>> {
    if strong.is_some_and(|strong| !types_match(strong, weak)) {
        return None;
    }
    let composing_prim = weak.ty == sdf::SpecType::Prim;

    let mut merged = Vec::new();
    for (field, weak_value) in &weak.fields {
        let mergeable = field == sdf::FieldKey::PropertyOrder.as_str() || weak_value.is_dictionary();
        if !mergeable && strong.is_some_and(|strong| strong.contains(field)) {
            continue;
        }
        if field == sdf::FieldKey::Documentation.as_str()
            || (!composing_prim && field == sdf::FieldKey::Custom.as_str())
        {
            continue;
        }

        let strong_value = strong.filter(|_| mergeable).and_then(|strong| strong.get(field));
        merged.push((field.clone(), merge_over(strong_value, weak_value.clone())));
    }

    (!merged.is_empty()).then_some(merged)
}

/// Merges a weaker value under a stronger one of the same field.
///
/// Token arrays concatenate without duplicating, dictionaries compose
/// recursively, and anything else keeps the weaker value — the caller only
/// reaches those cases for fields the stronger spec does not declare.
fn merge_over(strong: Option<&sdf::Value>, weak: sdf::Value) -> sdf::Value {
    match (strong, weak) {
        (Some(sdf::Value::TokenVec(strong)), sdf::Value::TokenVec(weak)) => {
            let mut merged = strong.clone();
            for token in weak {
                if !merged.contains(&token) {
                    merged.push(token);
                }
            }
            sdf::Value::TokenVec(merged)
        }
        (Some(sdf::Value::Dictionary(strong)), sdf::Value::Dictionary(weak)) => {
            let mut merged = strong.clone();
            sdf::dictionary_over(&mut merged, weak);
            sdf::Value::Dictionary(merged)
        }
        (_, weak) => weak,
    }
}

/// Whether two specs are the same kind of thing, so their fields may compose.
///
/// Attributes must additionally agree on their value type: a schema cannot
/// redeclare an inherited property as a different type.
fn types_match(strong: &sdf::SpecData, weak: &sdf::SpecData) -> bool {
    match strong.ty {
        sdf::SpecType::Prim => weak.ty == sdf::SpecType::Prim,
        sdf::SpecType::Relationship => weak.ty == sdf::SpecType::Relationship,
        _ => {
            weak.ty == sdf::SpecType::Attribute
                && strong.get(sdf::FieldKey::TypeName.as_str()) == weak.get(sdf::FieldKey::TypeName.as_str())
        }
    }
}

/// Where a name's composed spec lives inside a definition's own store.
fn composed_path(name: &tf::Token) -> Option<sdf::Path> {
    let prim = sdf::Path::abs_root().append_path(COMPOSED_PRIM).ok()?;
    match name.as_str().is_empty() {
        true => Some(prim),
        false => prim.append_property(name.as_str()).ok(),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::usd::SchemaRegistry;
    use crate::{sdf, tf};

    /// A family whose concrete `Thing` includes `WeakAPI` and shares property
    /// and prim metadata with it, so each merge rule has something to bite on.
    const MERGE_MANIFEST: &str = r#"#usda 1.0

def "APISchemaBase"
{
    uniform token schemaKind = "abstractBase"
}

def "WeakAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] bases = ["APISchemaBase"]
}

def "Thing"
{
    uniform token schemaKind = "concreteTyped"
}
"#;

    const MERGE_SCHEMATICS: &str = r#"#usda 1.0

class "APISchemaBase"
{
}

class "WeakAPI" (
    documentation = "weak prim docs"
    assetInfo = {
        string only_weak = "weak"
        string both = "weak"
        dictionary nested = {
            string only_weak = "weak"
            string both = "weak"
        }
    }
)
{
    reorder properties = ["shared", "only_weak"]
    float shared = 1 (
        documentation = "weak property docs"
        displayGroup = "weak group"
        assetInfo = {
            string only_weak = "weak"
            string both = "weak"
        }
    )
    token mismatched = "weak"
    float only_weak = 3
}

class Thing "Thing" (
    apiSchemas = ["WeakAPI"]
    documentation = "strong prim docs"
    assetInfo = {
        string both = "strong"
        dictionary nested = {
            string both = "strong"
        }
    }
)
{
    reorder properties = ["mismatched"]
    float shared (
        documentation = "strong property docs"
        assetInfo = {
            string both = "strong"
        }
    )
    float mismatched = 2
}
"#;

    fn merge_registry() -> Arc<SchemaRegistry> {
        SchemaRegistry::test_family(MERGE_MANIFEST, MERGE_SCHEMATICS)
    }

    #[test]
    fn typed_properties_and_fallbacks() {
        let registry = SchemaRegistry::test_registry();
        let distant = registry
            .concrete_prim_definition(&tf::Token::new("DistantLight"))
            .expect("DistantLight");

        assert!(distant.has_property(&tf::Token::new("inputs:angle")));
        assert_eq!(
            distant.attribute_fallback(&tf::Token::new("inputs:angle")),
            Some(sdf::Value::Float(0.53))
        );
        assert_eq!(distant.attribute_fallback(&tf::Token::new("nonexistent")), None);
    }

    #[test]
    fn built_ins_expand_transitively() {
        let registry = SchemaRegistry::test_registry();
        let distant = registry
            .concrete_prim_definition(&tf::Token::new("DistantLight"))
            .expect("DistantLight");

        // DistantLight includes LightAPI, which in turn includes an instance of
        // CollectionAPI, so all three tiers' properties are present.
        assert_eq!(
            distant.property_names(),
            [
                tf::Token::new("collection:lightLink:expansionRule"),
                tf::Token::new("collection:lightLink:includeRoot"),
                tf::Token::new("collection:lightLink:includes"),
                tf::Token::new("inputs:angle"),
                tf::Token::new("inputs:intensity"),
                tf::Token::new("light:shaderId"),
            ]
        );
        assert_eq!(
            distant.applied_api_schemas(),
            [tf::Token::new("LightAPI"), tf::Token::new("CollectionAPI:lightLink")]
        );
    }

    #[test]
    fn template_instantiated_by_built_in() {
        let registry = SchemaRegistry::test_registry();
        let light = registry
            .api_prim_definition(&tf::Token::new("LightAPI"))
            .expect("LightAPI");

        // The multiple-apply template contributes under its instance name, and
        // its fallbacks come along.
        assert_eq!(
            light.attribute_fallback(&tf::Token::new("collection:lightLink:expansionRule")),
            Some(sdf::Value::token("expandPrims"))
        );
        assert!(!light.has_property(&tf::Token::new("collection:__INSTANCE_NAME__:expansionRule")));
        assert_eq!(
            light.applied_api_schemas(),
            [tf::Token::new("LightAPI"), tf::Token::new("CollectionAPI:lightLink")]
        );
    }

    #[test]
    fn multi_apply_lists_its_template() {
        let registry = SchemaRegistry::test_registry();
        let collection = registry
            .api_prim_definition(&tf::Token::new("CollectionAPI"))
            .expect("CollectionAPI");

        assert_eq!(
            collection.applied_api_schemas(),
            [tf::Token::new("CollectionAPI:__INSTANCE_NAME__")]
        );
    }

    #[test]
    fn override_beats_built_in_fallback() {
        let registry = SchemaRegistry::test_registry();
        let distant = registry
            .concrete_prim_definition(&tf::Token::new("DistantLight"))
            .expect("DistantLight");
        let light = registry
            .api_prim_definition(&tf::Token::new("LightAPI"))
            .expect("LightAPI");

        // DistantLight declares `inputs:intensity` only as an override, so its
        // 50000 has to arrive through LightAPI's property.
        assert_eq!(
            light.attribute_fallback(&tf::Token::new("inputs:intensity")),
            Some(sdf::Value::Float(1.0))
        );
        assert_eq!(
            distant.attribute_fallback(&tf::Token::new("inputs:intensity")),
            Some(sdf::Value::Float(50000.0))
        );
        assert_eq!(
            distant.attribute_fallback(&tf::Token::new("light:shaderId")),
            Some(sdf::Value::token("DistantLight"))
        );
    }

    #[test]
    fn override_supplies_missing_fallback() {
        let registry = SchemaRegistry::test_registry();
        let collection = registry
            .api_prim_definition(&tf::Token::new("CollectionAPI"))
            .expect("CollectionAPI");
        let distant = registry
            .concrete_prim_definition(&tf::Token::new("DistantLight"))
            .expect("DistantLight");

        // CollectionAPI declares `includeRoot` with no fallback; LightAPI's
        // override supplies one, and it survives down to the concrete type.
        assert_eq!(
            collection.attribute_fallback(&tf::Token::new("collection:__INSTANCE_NAME__:includeRoot")),
            None
        );
        assert_eq!(
            distant.attribute_fallback(&tf::Token::new("collection:lightLink:includeRoot")),
            Some(sdf::Value::Bool(true))
        );
    }

    #[test]
    fn override_keeps_defined_variability() {
        let registry = SchemaRegistry::test_registry();
        let distant = registry
            .concrete_prim_definition(&tf::Token::new("DistantLight"))
            .expect("DistantLight");

        // The overridden `inputs:intensity` is varying on LightAPI, and an
        // override cannot change that.
        let intensity = distant
            .property(&tf::Token::new("inputs:intensity"))
            .expect("intensity");
        assert_eq!(intensity.variability(), sdf::Variability::Varying);
        assert_eq!(intensity.type_name(), Some(tf::Token::new("float")));

        let include_root = distant
            .property(&tf::Token::new("collection:lightLink:includeRoot"))
            .expect("includeRoot");
        assert_eq!(include_root.variability(), sdf::Variability::Uniform);
    }

    #[test]
    fn api_definition_lists_itself() {
        let registry = SchemaRegistry::test_registry();
        let light = registry
            .api_prim_definition(&tf::Token::new("LightAPI"))
            .expect("LightAPI");

        assert_eq!(light.applied_api_schemas()[0], tf::Token::new("LightAPI"));
        assert_eq!(
            light.attribute_fallback(&tf::Token::new("inputs:intensity")),
            Some(sdf::Value::Float(1.0))
        );
    }

    #[test]
    fn multi_apply_keeps_templates() {
        let registry = SchemaRegistry::test_registry();
        let collection = registry
            .api_prim_definition(&tf::Token::new("CollectionAPI"))
            .expect("CollectionAPI");

        let expansion = tf::Token::new("collection:__INSTANCE_NAME__:expansionRule");
        assert!(collection.has_property(&expansion));
        assert_eq!(
            collection.attribute_fallback(&expansion),
            Some(sdf::Value::token("expandPrims"))
        );

        // Declared with no default, so there is no fallback to report.
        assert_eq!(
            collection.attribute_fallback(&tf::Token::new("collection:__INSTANCE_NAME__:includeRoot")),
            None
        );
    }

    #[test]
    fn relationship_has_no_fallback() {
        let registry = SchemaRegistry::test_registry();
        let collection = registry
            .api_prim_definition(&tf::Token::new("CollectionAPI"))
            .expect("CollectionAPI");

        let includes = tf::Token::new("collection:__INSTANCE_NAME__:includes");
        let property = collection.property(&includes).expect("includes");
        assert_eq!(property.spec_type(), sdf::SpecType::Relationship);
        assert_eq!(collection.attribute_fallback(&includes), None);
    }

    #[test]
    fn property_type_and_variability() {
        let registry = SchemaRegistry::test_registry();
        let collection = registry
            .api_prim_definition(&tf::Token::new("CollectionAPI"))
            .expect("CollectionAPI");

        let expansion = collection
            .property(&tf::Token::new("collection:__INSTANCE_NAME__:expansionRule"))
            .expect("expansionRule");
        assert_eq!(expansion.type_name(), Some(tf::Token::new("token")));
        assert_eq!(expansion.variability(), sdf::Variability::Uniform);

        let light = registry
            .api_prim_definition(&tf::Token::new("LightAPI"))
            .expect("LightAPI");
        let intensity = light.property(&tf::Token::new("inputs:intensity")).expect("intensity");
        assert_eq!(intensity.type_name(), Some(tf::Token::new("float")));
        assert_eq!(intensity.variability(), sdf::Variability::Varying);
    }

    #[test]
    fn abstract_and_unknown_have_no_definition() {
        let registry = SchemaRegistry::test_registry();

        // Abstract types are not instantiable, so they have no concrete
        // definition; neither does a type the registry never heard of.
        assert!(
            registry
                .concrete_prim_definition(&tf::Token::new("NonboundableLightBase"))
                .is_none()
        );
        assert!(registry.concrete_prim_definition(&tf::Token::new("Bogus")).is_none());
        assert!(registry.empty_prim_definition().is_empty());
    }

    #[test]
    fn weaker_fills_in_missing_fields() {
        let registry = merge_registry();
        let thing = registry
            .concrete_prim_definition(&tf::Token::new("Thing"))
            .expect("Thing");

        // `Thing.shared` declares no fallback of its own, so WeakAPI's fills in,
        // and so does the display group it never mentions.
        assert_eq!(
            thing.attribute_fallback(&tf::Token::new("shared")),
            Some(sdf::Value::Float(1.0))
        );
        let shared = thing.property(&tf::Token::new("shared")).expect("shared");
        assert_eq!(
            shared.field(sdf::FieldKey::DisplayGroup),
            Some(&sdf::Value::String("weak group".into()))
        );
    }

    #[test]
    fn documentation_never_from_weaker() {
        let registry = merge_registry();
        let thing = registry
            .concrete_prim_definition(&tf::Token::new("Thing"))
            .expect("Thing");

        let shared = thing.property(&tf::Token::new("shared")).expect("shared");
        assert_eq!(
            shared.field(sdf::FieldKey::Documentation),
            Some(&sdf::Value::String("strong property docs".into()))
        );
        assert_eq!(
            thing.metadata(sdf::FieldKey::Documentation),
            Some(&sdf::Value::String("strong prim docs".into()))
        );
    }

    #[test]
    fn dictionaries_merge_recursively() {
        let registry = merge_registry();
        let thing = registry
            .concrete_prim_definition(&tf::Token::new("Thing"))
            .expect("Thing");

        let shared = thing.property(&tf::Token::new("shared")).expect("shared");
        let asset_info = shared
            .field(sdf::FieldKey::AssetInfo)
            .expect("assetInfo")
            .clone()
            .try_as_dictionary()
            .expect("dictionary");
        assert_eq!(asset_info["both"], sdf::Value::String("strong".into()));
        assert_eq!(asset_info["only_weak"], sdf::Value::String("weak".into()));

        let prim_data = thing
            .metadata(sdf::FieldKey::AssetInfo)
            .expect("assetInfo")
            .clone()
            .try_as_dictionary()
            .expect("dictionary");
        assert_eq!(prim_data["both"], sdf::Value::String("strong".into()));
        let nested = prim_data["nested"].clone().try_as_dictionary().expect("nested");
        assert_eq!(nested["both"], sdf::Value::String("strong".into()));
        assert_eq!(nested["only_weak"], sdf::Value::String("weak".into()));
    }

    #[test]
    fn mismatched_types_do_not_merge() {
        let registry = merge_registry();
        let thing = registry
            .concrete_prim_definition(&tf::Token::new("Thing"))
            .expect("Thing");

        // WeakAPI declares `mismatched` as a token; Thing's float declaration
        // wins whole rather than absorbing fields from a different type.
        let mismatched = thing.property(&tf::Token::new("mismatched")).expect("mismatched");
        assert_eq!(mismatched.type_name(), Some(tf::Token::new("float")));
        assert_eq!(
            thing.attribute_fallback(&tf::Token::new("mismatched")),
            Some(sdf::Value::Float(2.0))
        );
    }

    #[test]
    fn property_order_appends_weaker() {
        let registry = merge_registry();
        let thing = registry
            .concrete_prim_definition(&tf::Token::new("Thing"))
            .expect("Thing");

        // Thing orders `mismatched` first and WeakAPI orders `shared` before
        // `only_weak`; the weaker order appends after the stronger one.
        assert_eq!(
            thing.property_names(),
            [
                tf::Token::new("mismatched"),
                tf::Token::new("shared"),
                tf::Token::new("only_weak"),
            ]
        );
    }

    #[test]
    fn disallowed_fields_are_not_fallbacks() {
        let registry = SchemaRegistry::test_registry();
        let distant = registry
            .concrete_prim_definition(&tf::Token::new("DistantLight"))
            .expect("DistantLight");

        // A class prim is a prim spec, so it carries fields that describe the
        // declaration rather than the prims using it. Those never read back.
        assert!(distant.metadata(sdf::FieldKey::Specifier).is_none());
        assert!(distant.metadata(sdf::FieldKey::CustomData).is_none());
        assert!(distant.metadata(sdf::ChildrenKey::PropertyChildren).is_none());

        // What the schema genuinely states about itself still does.
        assert!(distant.metadata(sdf::FieldKey::ApiSchemas).is_some());
    }

    #[test]
    fn prim_metadata_is_not_a_property() {
        let registry = SchemaRegistry::test_registry();
        let distant = registry
            .concrete_prim_definition(&tf::Token::new("DistantLight"))
            .expect("DistantLight");

        assert!(distant.property(&tf::Token::default()).is_none());
        assert!(distant.metadata(sdf::FieldKey::ApiSchemas).is_some());
    }
}
