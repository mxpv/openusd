//! The `MaterialBindingAPI` view (C++ `UsdShadeMaterialBindingAPI`).
//!
//! Per `usdShade/schema.usda`, the purpose / collection of a binding is encoded
//! in the *name* of the binding relationship (the token count gives the role):
//!
//! - `material:binding` — direct, all-purpose (2 tokens)
//! - `material:binding:<purpose>` — direct, purpose-restricted (3)
//! - `material:binding:collection:<name>` — collection, all-purpose (4)
//! - `material:binding:collection:<purpose>:<name>` — collection,
//!   purpose-restricted (5)
//!
//! A direct binding rel has one target (the Material); a collection binding has
//! two (the collection path + the Material). The optional `bindMaterialAs`
//! metadata on the rel records binding strength.
//!
//! [`DirectBinding`] and [`CollectionBinding`] each read one relationship.
//! [`MaterialBindingAPI::resolve_binding`] walks a prim and its ancestors for
//! the binding that wins, answering a [`ResolvedBinding`], over a
//! [`BindingCache`] one resolution shares with the next.

use std::collections::HashMap;
use std::iter;

use openusd::Result;
use openusd::sdf;
use openusd::usd::{CollectionAPI, MembershipQuery, Prim, Relationship, SchemaBase, Stage};

use crate::SchemaError;
use crate::geom::{ElementType, FamilyType, Imageable, Subset, subset};

use super::tokens::{
    ALL_PURPOSE, BIND_MATERIAL_AS, FULL, MATERIAL_BIND, MATERIAL_BINDING, MATERIAL_BINDING_COLLECTION, PREVIEW,
    WEAKER_THAN_DESCENDANTS,
};
use super::{BindingStrength, Material, MaterialBindingAPI, RelationshipMetadata};

/// The purposes UsdShade names, all-purpose first (C++ `GetMaterialPurposes`).
/// A binding may be restricted to any token; these are the two a renderer asks
/// for and the fallback both resolve to.
pub const MATERIAL_PURPOSES: [&str; 3] = [ALL_PURPOSE, PREVIEW, FULL];

impl MaterialBindingAPI {
    /// Whether `name` is a property this schema owns: `material:binding` or a
    /// name namespaced under it. C++ `CanContainPropertyName` accepts any
    /// name starting with `material:binding`, `material:bindingX` included.
    pub fn owns_property(name: &str) -> bool {
        name.strip_prefix(MATERIAL_BINDING)
            .is_some_and(|rest| rest.is_empty() || rest.starts_with(':'))
    }

    /// The direct binding relationship for `purpose`, authored or not (C++
    /// `GetDirectBindingRel`): `material:binding` for [`ALL_PURPOSE`], else
    /// `material:binding:<purpose>`.
    pub fn direct_binding_rel(&self, purpose: &str) -> Relationship {
        self.relationship(direct_binding_rel_name(purpose))
    }

    /// The collection binding relationship named `binding_name` for
    /// `purpose`, authored or not (C++ `GetCollectionBindingRel`).
    pub fn collection_binding_rel(&self, binding_name: &str, purpose: &str) -> Relationship {
        self.relationship(collection_binding_rel_name(binding_name, purpose))
    }

    /// The authored collection binding relationships for `purpose`, in
    /// property order, whatever each targets (C++ `GetCollectionBindingRels`).
    pub fn collection_binding_rels(&self, purpose: &str) -> Result<Vec<Relationship>> {
        Ok(self
            .authored_relationships_in_namespace(&collection_binding_rel_name("", purpose))?
            .into_iter()
            .filter(|rel| binding_purpose(rel.name()) == purpose)
            .collect())
    }

    /// The direct binding for `purpose`, where its relationship binds a
    /// material (C++ `GetDirectBinding`).
    pub fn direct_binding(&self, purpose: &str) -> Result<Option<DirectBinding>> {
        DirectBinding::new(self.direct_binding_rel(purpose))
    }

    /// The collection bindings for `purpose` in property order, the order
    /// resolution tries them in, keeping those whose relationship names a
    /// collection and a material (C++ `GetCollectionBindings`).
    pub fn collection_bindings(&self, purpose: &str) -> Result<Vec<CollectionBinding>> {
        self.collection_binding_rels(purpose)?
            .into_iter()
            .filter_map(|rel| CollectionBinding::new(rel).transpose())
            .collect()
    }

    /// Author an all-purpose direct binding (`material:binding`) targeting
    /// `material` at the fallback strength (C++
    /// `UsdShadeMaterialBindingAPI::Bind`).
    pub fn bind(&self, material: impl sdf::IntoPath) -> Result<&Self> {
        self.bind_for_purpose(ALL_PURPOSE, material, None)
    }

    /// Author a direct binding for `purpose` targeting `material`
    /// (`material:binding:<purpose>`, or `material:binding` when `purpose` is
    /// [`ALL_PURPOSE`]), with `strength` authored as [`set_binding_strength`]
    /// authors it (C++ `Bind`).
    pub fn bind_for_purpose(
        &self,
        purpose: &str,
        material: impl sdf::IntoPath,
        strength: Option<BindingStrength>,
    ) -> Result<&Self> {
        let rel =
            self.author_relationship_targets(&direct_binding_rel_name(purpose), [sdf::try_into_path(material)?])?;
        set_binding_strength(rel, strength)?;
        Ok(self)
    }

    /// Author a collection binding of `material` to `collection` for
    /// `purpose`, named `binding_name` on this prim, with `strength` authored
    /// as [`set_binding_strength`] authors it (C++ `Bind`, the collection
    /// overload). The relationship targets the collection path then the
    /// material path.
    ///
    /// An empty `binding_name` takes the collection's name with any namespace
    /// stripped. A name that is not one plain identifier is refused, since the
    /// relationship's token count is what tells its role.
    pub fn bind_collection(
        &self,
        binding_name: &str,
        collection: &CollectionAPI,
        material: impl sdf::IntoPath,
        purpose: &str,
        strength: Option<BindingStrength>,
    ) -> Result<&Self, SchemaError> {
        if !binding_name.is_empty() && !sdf::Path::is_valid_identifier(binding_name) {
            return Err(SchemaError::InvalidBindingName {
                name: binding_name.to_string(),
            });
        }
        let binding_name = if binding_name.is_empty() {
            let name = collection.name().as_str();
            name.rsplit_once(':').map_or(name, |(_, last)| last)
        } else {
            binding_name
        };
        let rel = self.author_relationship_targets(
            &collection_binding_rel_name(binding_name, purpose),
            [collection.collection_path()?, sdf::try_into_path(material)?],
        )?;
        set_binding_strength(rel, strength)?;
        Ok(self)
    }

    /// Block the direct binding for `purpose` with an explicit empty target
    /// list on the edit target, which hides any binding a weaker layer authors
    /// (C++ `UnbindDirectBinding`). The schema stays applied.
    pub fn unbind_direct(&self, purpose: &str) -> Result<&Self> {
        self.relationship_builder(direct_binding_rel_name(purpose))
            .custom(false)
            .block_targets()
            .build()?;
        Ok(self)
    }

    /// Block the collection binding named `binding_name` for `purpose`, as
    /// [`unbind_direct`](Self::unbind_direct) blocks a direct one (C++
    /// `UnbindCollectionBinding`). A binding authored without a name is named
    /// after its collection.
    pub fn unbind_collection(&self, binding_name: &str, purpose: &str) -> Result<&Self> {
        self.relationship_builder(collection_binding_rel_name(binding_name, purpose))
            .custom(false)
            .block_targets()
            .build()?;
        Ok(self)
    }

    /// Block every direct and collection binding relationship on this prim
    /// (C++ `UnbindAllBindings`).
    pub fn unbind_all(&self) -> Result<&Self> {
        for rel in self.relationships()? {
            if Self::owns_property(rel.name()) {
                rel.block_targets()?;
            }
        }
        Ok(self)
    }

    /// Include `prim` in the collection the binding named `binding_name` for
    /// `purpose` targets (C++ `AddPrimToBindingCollection`). Where no such
    /// binding names an applied collection, nothing changes.
    pub fn add_to_binding_collection(
        &self,
        prim: impl sdf::IntoPath,
        binding_name: &str,
        purpose: &str,
    ) -> Result<&Self> {
        if let Some(collection) = self.bound_collection(binding_name, purpose)? {
            collection.include_path(prim)?;
        }
        Ok(self)
    }

    /// Exclude `prim` from the collection the binding named `binding_name` for
    /// `purpose` targets (C++ `RemovePrimFromBindingCollection`). Where no such
    /// binding names an applied collection, nothing changes.
    pub fn remove_from_binding_collection(
        &self,
        prim: impl sdf::IntoPath,
        binding_name: &str,
        purpose: &str,
    ) -> Result<&Self> {
        if let Some(collection) = self.bound_collection(binding_name, purpose)? {
            collection.exclude_path(prim)?;
        }
        Ok(self)
    }

    /// The binding that wins material resolution for `purpose` over this prim
    /// and its ancestors (C++ `ComputeBoundMaterial`, together with the
    /// relationship it hands back through `bindingRel`).
    ///
    /// A restricted purpose is resolved over the whole ancestor chain before
    /// the all-purpose bindings are, so a restricted binding on any ancestor
    /// outranks an all-purpose one on a closer prim. Within one purpose, a
    /// binding on a closer prim wins over one on an ancestor unless the
    /// ancestor's is `strongerThanDescendants`, in which case the topmost such
    /// ancestor wins. At one prim, a collection binding whose collection holds
    /// this prim beats the direct binding, and collection bindings are tried in
    /// property order. A collection with no `CollectionAPI` applied on the
    /// stage binds nothing. Bindings count whether or not the schema is applied
    /// to the prim carrying them, which is the C++ `supportLegacyBindings`
    /// default.
    ///
    /// The winner is committed by its target path, so the answer stands even
    /// where no `Material` prim is there to read (see [`ResolvedBinding`]).
    /// `cache` carries what the walk computes to the next call; hand one cache
    /// to every resolution over a subtree.
    pub fn resolve_binding(&self, purpose: &str, cache: &mut BindingCache) -> Result<Option<ResolvedBinding>> {
        let stage = self.stage();
        let queried = self.path();
        let chain: Vec<Prim> = self.prim().ancestors().collect();
        let StageCache {
            bindings,
            queries,
            strengths,
        } = cache.stages.entry(stage.clone()).or_default();
        for pass in purpose_passes(purpose) {
            let mut winner: Option<ResolvedBinding> = None;
            for current in &chain {
                let at = cached(bindings, current.path(), || BindingsAtPrim::gather(current))?;
                // Whether the winner was set at this prim, where a collection
                // binding outranks the direct one.
                let mut won_here = false;
                if let Some(direct) = at.direct.iter().find(|direct| direct.purpose() == pass)
                    && (winner.is_none()
                        || *cached(strengths, direct.rel.path(), || direct.strength())?
                            == BindingStrength::StrongerThanDescendants)
                {
                    winner = Some(ResolvedBinding::of(&direct.rel, &direct.material_path));
                    won_here = true;
                }
                for binding in at.collections.iter().filter(|binding| binding.purpose() == pass) {
                    let query = cached(queries, &binding.collection_path, || {
                        binding.collection()?.map(|c| c.membership_query()).transpose()
                    })?;
                    if !query.as_ref().is_some_and(|query| query.is_included(queried)) {
                        continue;
                    }
                    if winner.is_some()
                        && !won_here
                        && *cached(strengths, binding.rel.path(), || binding.strength())?
                            != BindingStrength::StrongerThanDescendants
                    {
                        continue;
                    }
                    winner = Some(ResolvedBinding::of(&binding.rel, &binding.material_path));
                    break;
                }
            }
            if winner.is_some() {
                return Ok(winner);
            }
        }
        Ok(None)
    }

    /// The `Material` bound to this prim for `purpose`, resolved as
    /// [`resolve_binding`](Self::resolve_binding) resolves it (C++
    /// `ComputeBoundMaterial`). `None` where nothing is bound and where the
    /// winning binding names no `Material` prim the stage holds; the resolved
    /// binding tells the two apart.
    pub fn bound_material(&self, purpose: &str) -> Result<Option<Material>> {
        match self.resolve_binding(purpose, &mut BindingCache::default())? {
            Some(resolved) => resolved.material(),
            None => Ok(None),
        }
    }

    /// Resolve the binding of each of `prims` for `purpose` over one shared
    /// cache (C++ `ComputeBoundMaterials`), answering in the same order.
    ///
    /// TODO(rayon): each prim resolves independently over the shared cache,
    /// which C++ runs under `WorkParallelForN`; the cache would need to admit
    /// concurrent fills.
    pub fn resolve_bindings(prims: &[Prim], purpose: &str) -> Result<Vec<Option<ResolvedBinding>>> {
        let mut cache = BindingCache::default();
        prims
            .iter()
            .map(|prim| Self::from_prim_unchecked(prim.clone()).resolve_binding(purpose, &mut cache))
            .collect()
    }

    /// Define the subset named `name` under the prim, in the `materialBind`
    /// family, indexing the `indices` of `element_type` (C++
    /// `CreateMaterialBindSubset`); a subset of that name defined already is
    /// the one authored on, as [`Subset::create`] authors it. The family's
    /// type becomes [`FamilyType::NonOverlapping`] where none is authored or
    /// it is unrestricted, under which one element could be bound to two
    /// materials; any other authored token stays, one naming no type
    /// included.
    pub fn create_subset(&self, name: &str, element_type: ElementType, indices: &[i32]) -> Result<Subset> {
        let authored = subset::family_type_token(self.prim(), MATERIAL_BIND)?;
        let unrestricted = authored.is_none_or(|token| token.as_str() == FamilyType::Unrestricted.as_token());
        let family_type = unrestricted.then_some(FamilyType::NonOverlapping);
        Subset::create(
            &self.imageable(),
            name,
            element_type,
            indices,
            MATERIAL_BIND,
            family_type,
        )
    }

    /// The subsets of the `materialBind` family under the prim, of every
    /// element type (C++ `GetMaterialBindSubsets`).
    pub fn subsets(&self) -> Result<Vec<Subset>> {
        Subset::in_family(&self.imageable(), None, Some(MATERIAL_BIND))
    }

    /// The type of the `materialBind` family of subsets under the prim (C++
    /// `GetMaterialBindSubsetsFamilyType`).
    pub fn subset_family_type(&self) -> Result<FamilyType> {
        Subset::family_type(&self.imageable(), MATERIAL_BIND)
    }

    /// Author the type of the `materialBind` family of subsets under the
    /// prim (C++ `SetMaterialBindSubsetsFamilyType`).
    /// [`FamilyType::Unrestricted`] is refused: one element in two subsets
    /// would be bound to two materials.
    pub fn set_subset_family_type(&self, family_type: FamilyType) -> Result<&Self, SchemaError> {
        if family_type == FamilyType::Unrestricted {
            return Err(SchemaError::UnrestrictedBindFamily {
                prim: self.prim().path().clone(),
            });
        }
        Subset::set_family_type(&self.imageable(), MATERIAL_BIND, family_type)?;
        Ok(self)
    }

    /// The applied collection the binding named `binding_name` for `purpose`
    /// targets.
    fn bound_collection(&self, binding_name: &str, purpose: &str) -> Result<Option<CollectionAPI>> {
        match CollectionBinding::new(self.collection_binding_rel(binding_name, purpose))? {
            Some(binding) => binding.collection(),
            None => Ok(None),
        }
    }

    /// The prim as the imageable its subsets are defined under, viewed
    /// without a check, as C++ `UsdGeomImageable geom(GetPrim())` views it.
    fn imageable(&self) -> Imageable {
        Imageable::from_prim_unchecked(self.prim().clone())
    }
}

/// A direct binding relationship, `material:binding` or
/// `material:binding:<purpose>`, read as one (C++
/// `UsdShadeMaterialBindingAPI::DirectBinding`).
#[derive(Clone)]
pub struct DirectBinding {
    rel: Relationship,
    material_path: sdf::Path,
}

impl DirectBinding {
    /// Read `rel` as a direct binding: `Some` when its forwarded targets are
    /// exactly one prim path, which is the material it binds (C++ `IsBound`).
    pub fn new(rel: Relationship) -> Result<Option<Self>> {
        let targets = rel.forwarded_targets()?;
        let material_path = match targets.as_slice() {
            [target] if target.is_prim() => target.clone(),
            _ => return Ok(None),
        };
        Ok(Some(Self { rel, material_path }))
    }

    /// The binding relationship.
    pub fn rel(&self) -> &Relationship {
        &self.rel
    }

    /// The purpose the relationship's name restricts the binding to, or
    /// [`ALL_PURPOSE`] (C++ `GetMaterialPurpose`).
    pub fn purpose(&self) -> &str {
        binding_purpose(self.rel.name())
    }

    /// The bound material's prim path (C++ `GetMaterialPath`).
    pub fn material_path(&self) -> &sdf::Path {
        &self.material_path
    }

    /// The bound `Material`, or `None` where the stage holds no `Material`
    /// prim at the path: the prim is missing, outside the population mask, or
    /// of another type (C++ `GetMaterial`).
    pub fn material(&self) -> Result<Option<Material>> {
        Material::get(self.rel.stage(), self.material_path.clone())
    }

    /// The binding's `bindMaterialAs` strength.
    pub fn strength(&self) -> Result<BindingStrength> {
        binding_strength(&self.rel)
    }
}

/// A collection binding relationship, `material:binding:collection:<name>` or
/// `material:binding:collection:<purpose>:<name>`, read as one (C++
/// `UsdShadeMaterialBindingAPI::CollectionBinding`).
#[derive(Clone)]
pub struct CollectionBinding {
    rel: Relationship,
    collection_path: sdf::Path,
    material_path: sdf::Path,
}

impl CollectionBinding {
    /// Read `rel` as a collection binding: `Some` when it is named as one and
    /// its forwarded targets are exactly two, one a prim path (the material)
    /// and the other not (the collection), in either order (C++ `IsValid`).
    pub fn new(rel: Relationship) -> Result<Option<Self>> {
        if !is_collection_binding_name(rel.name()) {
            return Ok(None);
        }
        let targets = rel.forwarded_targets()?;
        let (collection_path, material_path) = match targets.as_slice() {
            [collection, material] | [material, collection] if material.is_prim() && !collection.is_prim() => {
                (collection.clone(), material.clone())
            }
            _ => return Ok(None),
        };
        Ok(Some(Self {
            rel,
            collection_path,
            material_path,
        }))
    }

    /// Whether `rel` is named as a collection binding, whatever it targets
    /// (C++ `IsCollectionBindingRel`).
    pub fn is_binding_rel(rel: &Relationship) -> bool {
        is_collection_binding_name(rel.name())
    }

    /// The binding relationship.
    pub fn rel(&self) -> &Relationship {
        &self.rel
    }

    /// The purpose the relationship's name restricts the binding to, or
    /// [`ALL_PURPOSE`].
    pub fn purpose(&self) -> &str {
        binding_purpose(self.rel.name())
    }

    /// The bound collection's path, a `collection:<name>` property path (C++
    /// `GetCollectionPath`).
    pub fn collection_path(&self) -> &sdf::Path {
        &self.collection_path
    }

    /// The bound material's prim path (C++ `GetMaterialPath`).
    pub fn material_path(&self) -> &sdf::Path {
        &self.material_path
    }

    /// The bound collection, or `None` where the stage holds no
    /// `CollectionAPI` applied under that name on that prim (C++
    /// `GetCollection`, which is valid for an applied instance only).
    pub fn collection(&self) -> Result<Option<CollectionAPI>> {
        let Some((prim, name)) = CollectionAPI::instance_at_path(&self.collection_path) else {
            return Ok(None);
        };
        CollectionAPI::from_prim(&self.rel.stage().prim(prim)?, name)
    }

    /// The bound `Material`, or `None` where the stage holds no `Material`
    /// prim at the path (C++ `GetMaterial`).
    pub fn material(&self) -> Result<Option<Material>> {
        Material::get(self.rel.stage(), self.material_path.clone())
    }

    /// The binding's `bindMaterialAs` strength.
    pub fn strength(&self) -> Result<BindingStrength> {
        binding_strength(&self.rel)
    }
}

/// The binding material resolution selects for a prim, and the material it
/// names (C++ `ComputeBoundMaterial`'s material together with its
/// `bindingRel` out-parameter).
///
/// Resolution commits to the winning binding by its target path, so the record
/// exists whether or not the stage holds a `Material` there. `material_path`
/// names what was bound either way.
#[derive(Clone)]
pub struct ResolvedBinding {
    rel: Relationship,
    material_path: sdf::Path,
}

impl ResolvedBinding {
    fn of(rel: &Relationship, material_path: &sdf::Path) -> Self {
        Self {
            rel: rel.clone(),
            material_path: material_path.clone(),
        }
    }

    /// The winning binding relationship, direct or collection.
    pub fn rel(&self) -> &Relationship {
        &self.rel
    }

    /// The prim path the winning binding targets as its material.
    pub fn material_path(&self) -> &sdf::Path {
        &self.material_path
    }

    /// The `Material` at the target path, or `None` where the stage holds no
    /// `Material` prim there: the prim is missing, outside the population
    /// mask, or of another type.
    pub fn material(&self) -> Result<Option<Material>> {
        Material::get(self.rel.stage(), self.material_path.clone())
    }
}

/// What material resolutions share (C++ `BindingsCache` and
/// `CollectionQueryCache`): the bindings authored at each prim, the membership
/// query of each collection they bind, and each binding's strength, kept per
/// stage instance.
///
/// Over a subtree, resolutions read the same ancestors and evaluate the same
/// collections; one cache handed to each
/// [`resolve_binding`](MaterialBindingAPI::resolve_binding) computes them
/// once, for any purpose asked and any stage resolved. Nothing evicts an
/// entry: start a new cache after editing bindings or collections.
#[derive(Default)]
pub struct BindingCache {
    /// Entries are keyed by path, which stages share, so each stage has its
    /// own.
    stages: HashMap<Stage, StageCache>,
}

/// A [`BindingCache`]'s entries for one stage.
#[derive(Default)]
struct StageCache {
    bindings: sdf::PathMap<BindingsAtPrim>,
    /// By collection path; `None` where the collection is not applied.
    queries: sdf::PathMap<Option<MembershipQuery>>,
    /// By binding relationship path.
    strengths: sdf::PathMap<BindingStrength>,
}

/// The bindings authored on one prim, each kind in property order (C++
/// `BindingsAtPrim`, which gathers for one purpose; here a pass picks its
/// purpose out at read time).
struct BindingsAtPrim {
    direct: Vec<DirectBinding>,
    collections: Vec<CollectionBinding>,
}

impl BindingsAtPrim {
    fn gather(prim: &Prim) -> Result<Self> {
        let mut direct = Vec::new();
        let mut collections = Vec::new();
        for name in prim.authored_property_names()? {
            if is_collection_binding_name(&name) {
                collections.extend(CollectionBinding::new(prim.relationship(name))?);
            } else if is_direct_binding_name(&name) {
                direct.extend(DirectBinding::new(prim.relationship(name))?);
            }
        }
        Ok(Self { direct, collections })
    }
}

/// The `bindMaterialAs` strength of a binding relationship,
/// [`BindingStrength::WeakerThanDescendants`] where none is authored (C++
/// `GetMaterialBindingStrength`).
pub fn binding_strength(rel: &Relationship) -> Result<BindingStrength> {
    Ok(rel
        .bind_material_as()?
        .and_then(BindingStrength::from_token)
        .unwrap_or_default())
}

/// Author `strength` as the `bindMaterialAs` of a binding relationship (C++
/// `SetMaterialBindingStrength`). `Some` authors the strength as given. `None`
/// is the fallback (C++ `fallbackStrength`): `weakerThanDescendants` is then
/// written only over an authored opinion that says otherwise.
pub fn set_binding_strength(rel: Relationship, strength: Option<BindingStrength>) -> Result<Relationship> {
    match strength {
        Some(strength) => Ok(rel.set_metadata(BIND_MATERIAL_AS, strength)?),
        None if rel
            .bind_material_as()?
            .is_some_and(|authored| authored != WEAKER_THAN_DESCENDANTS) =>
        {
            Ok(rel.set_metadata(BIND_MATERIAL_AS, BindingStrength::WeakerThanDescendants)?)
        }
        None => Ok(rel),
    }
}

/// The entry of `map` at `key`, computed by `fill` on first request.
fn cached<'m, V>(map: &'m mut sdf::PathMap<V>, key: &sdf::Path, fill: impl FnOnce() -> Result<V>) -> Result<&'m V> {
    if !map.contains_key(key) {
        map.insert(key.clone(), fill()?);
    }
    Ok(map.get(key).expect("inserted above"))
}

/// The direct binding relationship name for `purpose` (C++
/// `_GetDirectBindingRelName`).
fn direct_binding_rel_name(purpose: &str) -> String {
    if purpose == ALL_PURPOSE {
        MATERIAL_BINDING.to_string()
    } else {
        format!("{MATERIAL_BINDING}:{purpose}")
    }
}

/// The collection binding relationship name for `binding_name` under
/// `purpose` (C++ `_GetCollectionBindingRelName`).
fn collection_binding_rel_name(binding_name: &str, purpose: &str) -> String {
    if purpose == ALL_PURPOSE {
        format!("{MATERIAL_BINDING_COLLECTION}:{binding_name}")
    } else {
        format!("{MATERIAL_BINDING_COLLECTION}:{purpose}:{binding_name}")
    }
}

/// Whether `name` is a direct binding relationship name: `material:binding`
/// or `material:binding:<purpose>`.
fn is_direct_binding_name(name: &str) -> bool {
    name.strip_prefix(MATERIAL_BINDING)
        .is_some_and(|rest| rest.is_empty() || rest.strip_prefix(':').is_some_and(|purpose| !purpose.contains(':')))
}

/// Whether `name` is a collection binding relationship name, one under
/// `material:binding:collection` (C++ `IsCollectionBindingRel`).
fn is_collection_binding_name(name: &str) -> bool {
    name.strip_prefix(MATERIAL_BINDING_COLLECTION)
        .is_some_and(|rest| rest.starts_with(':'))
}

/// The purpose a binding relationship's name restricts it to, or
/// [`ALL_PURPOSE`]: the third token of a direct name, the fourth of a
/// collection name. A collection name with tokens beyond its fifth is read
/// as C++ resolution gathers it, restricted to its fourth token; C++
/// `GetCollectionBindingRels` lists such a name as all-purpose instead.
fn binding_purpose(rel_name: &str) -> &str {
    if let Some(rest) = rel_name
        .strip_prefix(MATERIAL_BINDING_COLLECTION)
        .and_then(|rest| rest.strip_prefix(':'))
    {
        return rest.split_once(':').map_or(ALL_PURPOSE, |(purpose, _)| purpose);
    }
    rel_name
        .strip_prefix(MATERIAL_BINDING)
        .and_then(|rest| rest.strip_prefix(':'))
        .filter(|purpose| !purpose.contains(':'))
        .unwrap_or(ALL_PURPOSE)
}

/// The purposes a query for `purpose` tries, in order: the purpose itself,
/// then the all-purpose fallback where that is another.
fn purpose_passes(purpose: &str) -> impl Iterator<Item = &str> {
    iter::once(purpose).chain((purpose != ALL_PURPOSE).then_some(ALL_PURPOSE))
}

#[cfg(test)]
mod tests {
    use super::*;

    use openusd::usd::{StagePopulationMask, apply_collection};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    #[test]
    fn direct_all_purpose_roundtrip() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
        Material::define(&stage, "/World/Mat")?;
        MaterialBindingAPI::apply(&stage.prim("/World/Mesh")?)?.bind("/World/Mat")?;

        let binding = MaterialBindingAPI::get(&stage, "/World/Mesh")?.expect("MaterialBindingAPI");
        let direct = binding.direct_binding("")?.expect("all-purpose binding");
        assert_eq!(direct.rel().name(), MATERIAL_BINDING);
        assert_eq!(direct.purpose(), ALL_PURPOSE);
        assert_eq!(direct.material_path().as_str(), "/World/Mat");
        assert_eq!(direct.strength()?, BindingStrength::WeakerThanDescendants);
        assert_eq!(direct.material()?.expect("a Material").path().as_str(), "/World/Mat");
        Ok(())
    }

    /// The sphere of the C++ test: material-bind subsets are defined with
    /// their family typed `nonOverlapping`, a partition is kept once asked
    /// for, each subset binds a material of its own, and `unrestricted` is
    /// refused.
    #[test]
    fn material_bind_subsets() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            "#usda 1.0\ndef Mesh \"Mesh\"\n{\n    int[] faceVertexCounts = [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]\n}\ndef Material \"Mat1\"\n{\n}\ndef Material \"Mat2\"\n{\n}\n",
        )?;
        let binding = MaterialBindingAPI::apply(&stage.prim("/Mesh")?)?;
        let geom = binding.imageable();
        assert!(binding.subsets()?.is_empty());

        let first = binding.create_subset("subset1", ElementType::Face, &[0, 1, 2, 3])?;
        binding.create_subset("subset2", ElementType::Face, &[4, 5, 6, 7, 8, 9, 10, 11])?;
        assert_eq!(binding.subset_family_type()?, FamilyType::NonOverlapping);
        assert!(Subset::validate_family(&geom, ElementType::Face, MATERIAL_BIND)?.is_empty());

        binding.set_subset_family_type(FamilyType::Partition)?;
        assert!(!Subset::validate_family(&geom, ElementType::Face, MATERIAL_BIND)?.is_empty());
        let third = binding.create_subset("subset3", ElementType::Face, &[12, 13, 14, 15])?;
        assert_eq!(binding.subset_family_type()?, FamilyType::Partition);
        assert!(Subset::validate_family(&geom, ElementType::Face, MATERIAL_BIND)?.is_empty());
        assert_eq!(binding.subsets()?.len(), 3);

        MaterialBindingAPI::apply(first.prim())?.bind("/Mat1")?;
        MaterialBindingAPI::apply(third.prim())?.bind("/Mat2")?;
        let bound = MaterialBindingAPI::get(&stage, third.path().clone())?.expect("applied");
        assert_eq!(bound.bound_material("")?.expect("bound").path().as_str(), "/Mat2");

        let refused = binding.set_subset_family_type(FamilyType::Unrestricted);
        assert!(matches!(refused, Err(SchemaError::UnrestrictedBindFamily { prim }) if prim.as_str() == "/Mesh"));
        Ok(())
    }

    #[test]
    fn purpose_binding_with_strength() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        stage.define_prim("/Mat")?.set_type_name("Material")?;
        MaterialBindingAPI::apply(&stage.prim("/Mesh")?)?.bind_for_purpose(
            "preview",
            "/Mat",
            Some(BindingStrength::StrongerThanDescendants),
        )?;

        let binding = MaterialBindingAPI::get(&stage, "/Mesh")?.expect("MaterialBindingAPI");
        let preview = binding.direct_binding("preview")?.expect("preview binding");
        assert_eq!(preview.rel().name(), "material:binding:preview");
        assert_eq!(preview.purpose(), "preview");
        assert_eq!(preview.material_path().as_str(), "/Mat");
        assert_eq!(preview.strength()?, BindingStrength::StrongerThanDescendants);
        // The all-purpose binding wasn't authored.
        assert!(binding.direct_binding("")?.is_none());
        Ok(())
    }

    /// The fallback strength is authored only over an opinion that says
    /// otherwise; an explicit strength is authored as given.
    #[test]
    fn strength_authored_sparsely() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        let binding = MaterialBindingAPI::apply(&stage.prim("/Mesh")?)?;
        binding.bind("/MatA")?;
        let rel = binding.direct_binding_rel("");
        assert!(rel.bind_material_as()?.is_none(), "the fallback is left unauthored");

        binding.bind_for_purpose("", "/MatA", Some(BindingStrength::StrongerThanDescendants))?;
        assert_eq!(binding_strength(&rel)?, BindingStrength::StrongerThanDescendants);

        binding.bind_for_purpose("", "/MatB", None)?;
        assert_eq!(rel.bind_material_as()?.as_deref(), Some(WEAKER_THAN_DESCENDANTS));
        assert_eq!(binding_strength(&rel)?, BindingStrength::WeakerThanDescendants);

        let rel = binding.direct_binding_rel("preview");
        binding.bind_for_purpose("preview", "/MatA", Some(BindingStrength::WeakerThanDescendants))?;
        assert_eq!(rel.bind_material_as()?.as_deref(), Some(WEAKER_THAN_DESCENDANTS));
        Ok(())
    }

    #[test]
    fn collection_binding_roundtrip() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        Material::define(&stage, "/Set/Mat")?;
        let metal = apply_collection(&stage, "/Set", "metal")?;
        let binding = MaterialBindingAPI::apply(&stage.prim("/Set")?)?;
        binding.bind_collection("metalBits", &metal, "/Set/Mat", "", None)?;
        // No name: the collection's own.
        binding.bind_collection("", &metal, "/Set/Mat", "preview", None)?;

        let binding = MaterialBindingAPI::get(&stage, "/Set")?.expect("MaterialBindingAPI");
        let all = binding.collection_bindings("")?;
        let [bound] = all.as_slice() else {
            panic!("one all-purpose collection binding, not {}", all.len());
        };
        assert_eq!(bound.rel().name(), "material:binding:collection:metalBits");
        assert_eq!(bound.purpose(), ALL_PURPOSE);
        assert_eq!(bound.collection_path().as_str(), "/Set.collection:metal");
        assert_eq!(bound.material_path().as_str(), "/Set/Mat");
        assert_eq!(
            bound.collection()?.expect("an applied collection").name().as_str(),
            "metal"
        );
        assert!(bound.material()?.is_some());
        assert!(CollectionBinding::is_binding_rel(bound.rel()));
        assert!(!CollectionBinding::is_binding_rel(&binding.direct_binding_rel("")));

        let preview = binding.collection_bindings("preview")?;
        assert_eq!(preview.len(), 1);
        assert_eq!(preview[0].rel().name(), "material:binding:collection:preview:metal");
        assert_eq!(preview[0].purpose(), "preview");
        Ok(())
    }

    /// A binding name that is not one identifier would change the
    /// relationship's token count, so it is refused.
    #[test]
    fn invalid_binding_name_refused() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        let metal = apply_collection(&stage, "/Set", "metal")?;
        let binding = MaterialBindingAPI::apply(&stage.prim("/Set")?)?;
        for name in ["metal:bits", "metal bits", "1metal"] {
            let refused = binding.bind_collection(name, &metal, "/Set/Mat", "", None);
            assert!(matches!(refused, Err(SchemaError::InvalidBindingName { name: refused }) if refused == name));
        }
        assert!(binding.collection_binding_rels("")?.is_empty());
        Ok(())
    }

    /// The relationships are listed by purpose whatever they target; the
    /// bindings keep only those naming a collection and a material.
    #[test]
    fn collection_rels_by_purpose() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let set = stage.define_prim("/Set")?;
        set.author_relationship_targets("material:binding:collection:dangling", ["/Nothing"])?;
        set.author_relationship_targets("material:binding:collection:full:tight", ["/Set.collection:a", "/Mat"])?;
        set.author_relationship_targets("material:binding:collection:loose", ["/Set.collection:b", "/Mat"])?;
        let binding = MaterialBindingAPI::from_prim_unchecked(set);

        let names = |rels: Vec<Relationship>| rels.into_iter().map(|rel| rel.name().to_string()).collect::<Vec<_>>();
        assert_eq!(
            names(binding.collection_binding_rels("")?),
            [
                "material:binding:collection:dangling",
                "material:binding:collection:loose"
            ]
        );
        assert_eq!(
            names(binding.collection_binding_rels("full")?),
            ["material:binding:collection:full:tight"]
        );
        assert!(binding.collection_binding_rels("preview")?.is_empty());

        let all = binding.collection_bindings("")?;
        assert_eq!(all.len(), 1, "the dangling relationship is no binding");
        assert_eq!(all[0].rel().name(), "material:binding:collection:loose");
        Ok(())
    }

    #[test]
    fn property_name_ownership() {
        assert!(MaterialBindingAPI::owns_property("material:binding"));
        assert!(MaterialBindingAPI::owns_property("material:binding:preview"));
        assert!(MaterialBindingAPI::owns_property("material:binding:collection:full:x"));
        assert!(!MaterialBindingAPI::owns_property("material:bindingStrength"));
        assert!(!MaterialBindingAPI::owns_property("material"));
        assert_eq!(MATERIAL_PURPOSES, ["", "preview", "full"]);

        assert_eq!(binding_purpose("material:binding"), "");
        assert_eq!(binding_purpose("material:binding:preview"), "preview");
        assert_eq!(binding_purpose("material:binding:collection:x"), "");
        assert_eq!(binding_purpose("material:binding:collection:full:x"), "full");
        assert_eq!(binding_purpose("material:binding:collection:full:x:y"), "full");
        assert_eq!(binding_purpose("material:binding:a:b"), "");
    }

    /// A direct binding is one forwarded prim-path target; a collection
    /// binding two targets of which one is a prim path, in either order.
    #[test]
    fn binding_target_shapes() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let set = stage.define_prim("/Set")?;
        Material::define(&stage, "/Mat")?;
        let binding = MaterialBindingAPI::from_prim_unchecked(set.clone());

        set.author_relationship_targets("material:binding", ["/Mat", "/Other"])?;
        assert!(binding.direct_binding("")?.is_none(), "two targets bind nothing");
        set.author_relationship_targets("material:binding", ["/Set.collection:a"])?;
        assert!(binding.direct_binding("")?.is_none(), "a property target binds nothing");
        set.author_relationship_targets("material:binding", ["/Mat", "/Set.collection:a"])?;
        assert!(
            CollectionBinding::new(binding.direct_binding_rel(""))?.is_none(),
            "a direct name is no collection binding, whatever its targets"
        );

        // Forwarded through another relationship.
        set.author_relationship_targets("via", ["/Mat"])?;
        set.author_relationship_targets("material:binding", ["/Set.via"])?;
        assert_eq!(
            binding.direct_binding("")?.expect("forwarded").material_path().as_str(),
            "/Mat"
        );

        set.author_relationship_targets("material:binding:collection:swapped", ["/Mat", "/Set.collection:a"])?;
        let swapped = CollectionBinding::new(binding.collection_binding_rel("swapped", ""))?.expect("either order");
        assert_eq!(swapped.collection_path().as_str(), "/Set.collection:a");
        assert_eq!(swapped.material_path().as_str(), "/Mat");

        set.author_relationship_targets("material:binding:collection:prims", ["/Mat", "/Other"])?;
        assert!(CollectionBinding::new(binding.collection_binding_rel("prims", ""))?.is_none());
        Ok(())
    }

    /// `Material` prims at `paths`, for bindings to target.
    fn materials(stage: &Stage, paths: &[&str]) -> Result {
        for path in paths {
            Material::define(stage, *path)?;
        }
        Ok(())
    }

    fn bound(stage: &Stage, prim: &str, purpose: &str) -> Option<String> {
        MaterialBindingAPI::from_prim_unchecked(stage.prim(prim).unwrap())
            .bound_material(purpose)
            .unwrap()
            .map(|material| material.path().as_str().to_string())
    }

    /// The target path of a resolved binding, for comparing resolutions.
    fn target(resolved: Option<ResolvedBinding>) -> Option<String> {
        resolved.map(|resolved| resolved.material_path().as_str().to_string())
    }

    #[test]
    fn closer_binding_wins() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        materials(&stage, &["/MatA", "/MatB"])?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/Mesh")?.set_type_name("Mesh")?;
        MaterialBindingAPI::apply(&stage.prim("/Set")?)?.bind("/MatA")?;

        // Inherited from the ancestor.
        assert_eq!(bound(&stage, "/Set/Mesh", ""), Some("/MatA".to_string()));

        // A binding on the closer prim wins (both weakerThanDescendants).
        MaterialBindingAPI::apply(&stage.prim("/Set/Mesh")?)?.bind("/MatB")?;
        assert_eq!(bound(&stage, "/Set/Mesh", ""), Some("/MatB".to_string()));
        // The ancestor itself still resolves to its own binding.
        assert_eq!(bound(&stage, "/Set", ""), Some("/MatA".to_string()));
        // Unbound prim → None.
        assert_eq!(bound(&stage, "/Other", ""), None);
        Ok(())
    }

    /// A binding to a prim that is not a `Material` commits the resolution,
    /// as in C++: the binding is reported, the material is not, and no weaker
    /// purpose is consulted.
    #[test]
    fn non_material_target() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        materials(&stage, &["/MatAll"])?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        stage.define_prim("/NotAMaterial")?.set_type_name("Scope")?;
        let binding = MaterialBindingAPI::apply(&stage.prim("/Mesh")?)?;
        binding.bind("/MatAll")?;
        binding.bind_for_purpose("preview", "/NotAMaterial", None)?;

        let resolved = binding
            .resolve_binding("preview", &mut BindingCache::default())?
            .expect("the preview binding wins");
        assert_eq!(resolved.rel().name(), "material:binding:preview");
        assert_eq!(resolved.material_path().as_str(), "/NotAMaterial");
        assert!(resolved.material()?.is_none());
        assert_eq!(bound(&stage, "/Mesh", "preview"), None);
        assert_eq!(bound(&stage, "/Mesh", ""), Some("/MatAll".to_string()));
        Ok(())
    }

    /// A binding whose target the stage does not hold is still the winning
    /// binding.
    #[test]
    fn dangling_target() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        let binding = MaterialBindingAPI::apply(&stage.prim("/Mesh")?)?;
        binding.bind("/Looks/Missing")?;

        let resolved = binding
            .resolve_binding("", &mut BindingCache::default())?
            .expect("a winning binding");
        assert_eq!(resolved.rel().path().as_str(), "/Mesh.material:binding");
        assert_eq!(resolved.material_path().as_str(), "/Looks/Missing");
        assert!(resolved.material()?.is_none());
        assert!(binding.bound_material("")?.is_none());
        Ok(())
    }

    /// The scene of issue 161: a stage populated under a mask that leaves the
    /// bound material out still reports the binding and its target.
    #[test]
    fn masked_target_keeps_binding() -> Result {
        const SCENE: &str = r#"#usda 1.0
def Xform "scene" {
    def Mesh "pCube1" (prepend apiSchemas = ["MaterialBindingAPI"]) {
        rel material:binding = </scene/Looks/mat>
    }
    def Scope "Looks" { def Material "mat" {} }
}
"#;
        let mask = StagePopulationMask::new(["/scene/pCube1"]).expect("a prim path");
        let (_dir, stage) = crate::tests::from_usda_with(SCENE, |builder| builder.mask(mask))?;

        let binding = MaterialBindingAPI::get(&stage, "/scene/pCube1")?.expect("MaterialBindingAPI");
        let resolved = binding
            .resolve_binding("full", &mut BindingCache::default())?
            .expect("the binding wins whether or not its target is populated");
        assert_eq!(resolved.rel().path().as_str(), "/scene/pCube1.material:binding");
        assert_eq!(resolved.material_path().as_str(), "/scene/Looks/mat");
        assert!(resolved.material()?.is_none(), "the material is outside the mask");
        assert!(binding.bound_material("full")?.is_none());

        let direct = binding.direct_binding("")?.expect("read straight off the relationship");
        assert_eq!(direct.material_path().as_str(), "/scene/Looks/mat");
        assert!(direct.material()?.is_none());
        Ok(())
    }

    #[test]
    fn stronger_ancestor_wins() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        materials(&stage, &["/MatStrong", "/MatWeak"])?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/Mesh")?.set_type_name("Mesh")?;
        // Ancestor binding is stronger; closer binding is the default weak.
        MaterialBindingAPI::apply(&stage.prim("/Set")?)?.bind_for_purpose(
            "",
            "/MatStrong",
            Some(BindingStrength::StrongerThanDescendants),
        )?;
        MaterialBindingAPI::apply(&stage.prim("/Set/Mesh")?)?.bind("/MatWeak")?;

        // The stronger ancestor wins despite the closer binding.
        assert_eq!(bound(&stage, "/Set/Mesh", ""), Some("/MatStrong".to_string()));
        Ok(())
    }

    #[test]
    fn restricted_purpose_preferred() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        materials(&stage, &["/MatAll", "/MatPreview"])?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        let binding = MaterialBindingAPI::apply(&stage.prim("/Mesh")?)?;
        binding.bind("/MatAll")?; // all-purpose
        binding.bind_for_purpose("preview", "/MatPreview", None)?;

        // Restricted purpose preferred over the all-purpose binding.
        assert_eq!(bound(&stage, "/Mesh", "preview"), Some("/MatPreview".to_string()));
        // A purpose with no restricted binding falls back to all-purpose.
        assert_eq!(bound(&stage, "/Mesh", "full"), Some("/MatAll".to_string()));
        Ok(())
    }

    #[test]
    fn restricted_ancestor_wins() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        materials(&stage, &["/MatPreview", "/MatAll"])?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/Mesh")?.set_type_name("Mesh")?;
        // Restricted "preview" binding on the ancestor; the queried prim carries
        // only an all-purpose binding.
        MaterialBindingAPI::apply(&stage.prim("/Set")?)?.bind_for_purpose("preview", "/MatPreview", None)?;
        MaterialBindingAPI::apply(&stage.prim("/Set/Mesh")?)?.bind("/MatAll")?;

        // The restricted purpose is resolved across the whole chain first, so
        // the ancestor's "preview" binding outranks the closer all-purpose one.
        assert_eq!(bound(&stage, "/Set/Mesh", "preview"), Some("/MatPreview".to_string()));
        // An unrestricted query still gets the closer all-purpose binding.
        assert_eq!(bound(&stage, "/Set/Mesh", ""), Some("/MatAll".to_string()));
        Ok(())
    }

    /// Build `/Set` with a `metal` collection including `/Set/A`, and a
    /// collection binding to `/MatMetal`, plus a direct binding to `/MatDir`.
    fn collection_scene() -> Result<Stage> {
        let stage = crate::tests::stage("anon.usda")?;
        materials(&stage, &["/MatDir", "/MatMetal"])?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/A")?.set_type_name("Mesh")?;
        stage.define_prim("/Set/B")?.set_type_name("Mesh")?;
        let metal = apply_collection(&stage, "/Set", "metal")?;
        metal.include_path("/Set/A")?;
        let binding = MaterialBindingAPI::apply(&stage.prim("/Set")?)?;
        binding.bind("/MatDir")?;
        binding.bind_collection("metalBits", &metal, "/MatMetal", "", None)?;
        Ok(stage)
    }

    #[test]
    fn collection_beats_direct() -> Result {
        let stage = collection_scene()?;
        // /Set/A is a collection member → the collection binding wins over direct.
        assert_eq!(bound(&stage, "/Set/A", ""), Some("/MatMetal".to_string()));
        // /Set/B is not a member → falls back to the inherited direct binding.
        assert_eq!(bound(&stage, "/Set/B", ""), Some("/MatDir".to_string()));

        let resolved = MaterialBindingAPI::from_prim_unchecked(stage.prim("/Set/A")?)
            .resolve_binding("", &mut BindingCache::default())?
            .expect("bound");
        assert_eq!(
            resolved.rel().path().as_str(),
            "/Set.material:binding:collection:metalBits"
        );
        Ok(())
    }

    /// A weak collection binding on an ancestor does not displace a closer
    /// winner, while a stronger one does.
    #[test]
    fn ancestor_collection_strength() -> Result {
        let stage = collection_scene()?;
        materials(&stage, &["/MatLeaf"])?;
        MaterialBindingAPI::apply(&stage.prim("/Set/A")?)?.bind("/MatLeaf")?;
        assert_eq!(bound(&stage, "/Set/A", ""), Some("/MatLeaf".to_string()));

        let set = MaterialBindingAPI::get(&stage, "/Set")?.expect("MaterialBindingAPI");
        set_binding_strength(
            set.collection_binding_rel("metalBits", ""),
            Some(BindingStrength::StrongerThanDescendants),
        )?;
        assert_eq!(bound(&stage, "/Set/A", ""), Some("/MatMetal".to_string()));
        Ok(())
    }

    /// Editing the bound collection through the binding moves prims between
    /// the collection's material and the direct fallback.
    #[test]
    fn binding_collection_edits() -> Result {
        let stage = collection_scene()?;
        let binding = MaterialBindingAPI::get(&stage, "/Set")?.expect("MaterialBindingAPI");
        binding.add_to_binding_collection("/Set/B", "metalBits", "")?;
        assert_eq!(bound(&stage, "/Set/B", ""), Some("/MatMetal".to_string()));
        binding.remove_from_binding_collection("/Set/B", "metalBits", "")?;
        assert_eq!(bound(&stage, "/Set/B", ""), Some("/MatDir".to_string()));
        // A binding name nothing is bound under edits nothing.
        binding.add_to_binding_collection("/Set/B", "plasticBits", "")?;
        assert_eq!(bound(&stage, "/Set/B", ""), Some("/MatDir".to_string()));
        Ok(())
    }

    /// A collection binding whose collection has no `CollectionAPI` applied
    /// binds nothing, whatever `includes` says.
    #[test]
    fn unapplied_collection_skipped() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        materials(&stage, &["/MatDir", "/MatGhost"])?;
        let set = stage.define_prim("/Set")?;
        stage.define_prim("/Set/A")?.set_type_name("Mesh")?;
        set.author_relationship_targets("collection:ghost:includes", ["/Set/A"])?;
        set.author_relationship_targets(
            "material:binding:collection:ghostBits",
            ["/Set.collection:ghost", "/MatGhost"],
        )?;
        let binding = MaterialBindingAPI::apply(&set)?;
        binding.bind("/MatDir")?;

        let ghost = &binding.collection_bindings("")?[0];
        assert!(ghost.collection()?.is_none());
        assert_eq!(bound(&stage, "/Set/A", ""), Some("/MatDir".to_string()));

        apply_collection(&stage, "/Set", "ghost")?;
        assert_eq!(bound(&stage, "/Set/A", ""), Some("/MatGhost".to_string()));
        Ok(())
    }

    #[test]
    fn collection_native_order() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        materials(&stage, &["/MatSecond", "/MatFirst"])?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/A")?.set_type_name("Mesh")?;
        // Two collections that both include /Set/A.
        let first = apply_collection(&stage, "/Set", "first")?;
        first.include_path("/Set/A")?;
        let second = apply_collection(&stage, "/Set", "second")?;
        second.include_path("/Set/A")?;
        // Author binding "aaa" (collection `second`) before "zzz" (collection
        // `first`) — native *property* order, not target order, decides.
        let binding = MaterialBindingAPI::apply(&stage.prim("/Set")?)?;
        binding.bind_collection("aaa", &second, "/MatSecond", "", None)?;
        binding.bind_collection("zzz", &first, "/MatFirst", "", None)?;

        // `aaa` precedes `zzz` in native property order, so its collection
        // binding (to `/MatSecond`) is the one tested and wins — even though its
        // collection `second` was authored after `first`.
        assert_eq!(bound(&stage, "/Set/A", ""), Some("/MatSecond".to_string()));
        Ok(())
    }

    /// One cache over a subtree answers as fresh caches do, for both the
    /// per-call and the batch entry points, and for more than one purpose.
    #[test]
    fn cache_shared_over_subtree() -> Result {
        let stage = collection_scene()?;
        MaterialBindingAPI::get(&stage, "/Set")?
            .expect("MaterialBindingAPI")
            .bind_for_purpose("preview", "/MatMetal", None)?;
        let prims = [stage.prim("/Set/A")?, stage.prim("/Set/B")?, stage.prim("/Set")?];
        let mut cache = BindingCache::default();
        for purpose in ["", "preview", "full"] {
            let shared: Vec<Option<String>> = prims
                .iter()
                .map(|prim| {
                    MaterialBindingAPI::from_prim_unchecked(prim.clone())
                        .resolve_binding(purpose, &mut cache)
                        .map(target)
                })
                .collect::<openusd::Result<_>>()?;
            let fresh: Vec<Option<String>> = prims
                .iter()
                .map(|prim| bound(&stage, prim.path().as_str(), purpose))
                .collect();
            assert_eq!(shared, fresh, "purpose {purpose:?}");
            let batch: Vec<Option<String>> = MaterialBindingAPI::resolve_bindings(&prims, purpose)?
                .into_iter()
                .map(target)
                .collect();
            assert_eq!(batch, fresh, "purpose {purpose:?}");
        }
        assert_eq!(
            MaterialBindingAPI::resolve_bindings(&prims, "preview")?
                .into_iter()
                .map(target)
                .collect::<Vec<_>>(),
            vec![Some("/MatMetal".to_string()); 3]
        );
        Ok(())
    }

    /// Prims of two stages at one path keep their own stage's bindings
    /// through one cache and one batch.
    #[test]
    fn cache_partitioned_by_stage() -> Result {
        let mut stages = Vec::new();
        for material in ["/MatOne", "/MatTwo"] {
            let stage = crate::tests::stage("anon.usda")?;
            materials(&stage, &[material])?;
            stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
            MaterialBindingAPI::apply(&stage.prim("/Mesh")?)?.bind(material)?;
            stages.push(stage);
        }
        let prims = [stages[0].prim("/Mesh")?, stages[1].prim("/Mesh")?];

        let mut cache = BindingCache::default();
        for (prim, material) in prims.iter().zip(["/MatOne", "/MatTwo"]) {
            let resolved = MaterialBindingAPI::from_prim_unchecked(prim.clone())
                .resolve_binding("", &mut cache)?
                .expect("bound");
            assert_eq!(resolved.material_path().as_str(), material);
            assert!(resolved.rel().stage() == prim.stage());
        }
        let batch: Vec<Option<String>> = MaterialBindingAPI::resolve_bindings(&prims, "")?
            .into_iter()
            .map(target)
            .collect();
        assert_eq!(batch, [Some("/MatOne".to_string()), Some("/MatTwo".to_string())]);
        Ok(())
    }

    /// Unbinding blocks a binding a weaker layer authors.
    #[test]
    fn unbind_blocks_weaker_layer() -> Result {
        let (_dir, stage) = crate::tests::layered(&[(
            "weak.usda",
            r#"
def Material "MatWeak" {}
def Xform "Set" (prepend apiSchemas = ["MaterialBindingAPI"]) {
    rel material:binding = </MatWeak>
    def Mesh "Mesh" {}
}
"#,
        )])?;
        assert_eq!(bound(&stage, "/Set/Mesh", ""), Some("/MatWeak".to_string()));

        let binding = MaterialBindingAPI::get(&stage, "/Set")?.expect("MaterialBindingAPI");
        binding.unbind_direct("")?;
        assert!(binding.direct_binding("")?.is_none());
        assert!(binding.direct_binding_rel("").targets()?.is_empty());
        assert_eq!(bound(&stage, "/Set/Mesh", ""), None);
        Ok(())
    }

    #[test]
    fn unbind_all_bindings() -> Result {
        let stage = collection_scene()?;
        let binding = MaterialBindingAPI::get(&stage, "/Set")?.expect("MaterialBindingAPI");
        binding.bind_for_purpose("preview", "/MatDir", None)?;
        binding.unbind_all()?;

        assert!(binding.direct_binding("")?.is_none());
        assert!(binding.direct_binding("preview")?.is_none());
        assert!(binding.collection_bindings("")?.is_empty());
        assert_eq!(bound(&stage, "/Set/A", ""), None);
        assert_eq!(bound(&stage, "/Set/A", "preview"), None);

        // Each relationship was blocked, not removed, so unbinding one again
        // authors nothing new.
        let rel = binding.collection_binding_rel("metalBits", "");
        assert!(rel.is_defined()?);
        assert!(rel.targets()?.is_empty());
        let authored = stage.prim("/Set")?.authored_relationships()?.len();
        binding.unbind_collection("metalBits", "")?;
        assert_eq!(stage.prim("/Set")?.authored_relationships()?.len(), authored);
        Ok(())
    }

    #[test]
    fn strength_read_through_metadata() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = stage.define_prim("/Mesh")?;
        let rel = mesh.author_relationship_targets("material:binding", ["/Mat"])?;
        assert_eq!(binding_strength(&rel)?, BindingStrength::WeakerThanDescendants);
        let rel = rel.set_metadata(BIND_MATERIAL_AS, BindingStrength::StrongerThanDescendants)?;
        assert_eq!(binding_strength(&rel)?, BindingStrength::StrongerThanDescendants);
        // An unrecognized token reads as the fallback, and the fallback
        // request overwrites it.
        let rel = rel.set_metadata(BIND_MATERIAL_AS, sdf::Value::token("sideways"))?;
        assert_eq!(binding_strength(&rel)?, BindingStrength::WeakerThanDescendants);
        let rel = set_binding_strength(rel, None)?;
        assert_eq!(rel.bind_material_as()?.as_deref(), Some(WEAKER_THAN_DESCENDANTS));
        Ok(())
    }
}
