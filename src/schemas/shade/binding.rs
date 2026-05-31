//! `MaterialBindingAPI` authoring + reading.
//!
//! Per `usdShade/schema.usda`, the purpose / collection of a binding is
//! encoded in the *name* of the binding relationship (token count gives
//! the role):
//!
//! - `material:binding` — direct, all-purpose (2 tokens)
//! - `material:binding:<purpose>` — direct, purpose-restricted (3)
//! - `material:binding:collection:<name>` — collection, all-purpose (4)
//! - `material:binding:collection:<purpose>:<name>` — collection,
//!   purpose-restricted (5)
//!
//! A direct binding rel has one target (the Material); a collection
//! binding has two (the collection path + the Material). The optional
//! `bindMaterialAs` metadata on the rel records binding strength.

use std::collections::hash_map::Entry;
use std::collections::HashMap;

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::usd::{is_collection_api_path, Collection, MembershipQuery, Prim, Relationship, Stage};

use super::tokens::{
    API_MATERIAL_BINDING, META_BIND_MATERIAL_AS, PURPOSE_ALL, REL_MATERIAL_BINDING, REL_MATERIAL_BINDING_COLLECTION,
};
use super::types::BindingStrength;

/// The direct-binding relationship name for `purpose`. All-purpose
/// (empty) → `material:binding`; otherwise `material:binding:<purpose>`.
fn direct_binding_rel(purpose: &str) -> String {
    if purpose == PURPOSE_ALL {
        REL_MATERIAL_BINDING.to_string()
    } else {
        format!("{REL_MATERIAL_BINDING}:{purpose}")
    }
}

/// The collection-binding relationship name for `purpose` + `name`.
fn collection_binding_rel(purpose: &str, name: &str) -> String {
    if purpose == PURPOSE_ALL {
        format!("{REL_MATERIAL_BINDING_COLLECTION}:{name}")
    } else {
        format!("{REL_MATERIAL_BINDING_COLLECTION}:{purpose}:{name}")
    }
}

/// Apply `MaterialBindingAPI` and author an all-purpose **direct**
/// binding (`material:binding`) on `prim` targeting `material`.
/// Mirrors C++ `UsdShadeMaterialBindingAPI::Bind`.
pub fn bind_material(stage: &Stage, prim: impl Into<Path>, material: impl Into<Path>) -> Result<()> {
    bind_material_for_purpose(
        stage,
        prim,
        PURPOSE_ALL,
        material,
        BindingStrength::WeakerThanDescendants,
    )
}

/// Apply `MaterialBindingAPI` and author a **direct** binding for an
/// explicit `purpose` (`material:binding:<purpose>`, or
/// `material:binding` when `purpose` is
/// [`PURPOSE_ALL`](super::tokens::PURPOSE_ALL)). `strength` is written
/// as `bindMaterialAs` only when stronger than the default
/// `weakerThanDescendants` (which the spec leaves unauthored).
pub fn bind_material_for_purpose(
    stage: &Stage,
    prim: impl Into<Path>,
    purpose: &str,
    material: impl Into<Path>,
    strength: BindingStrength,
) -> Result<()> {
    let prim = Prim::new(stage, prim.into());
    stage.override_prim(prim.path().clone())?;
    prim.clone().add_applied_schema(API_MATERIAL_BINDING)?;
    let rel = prim.author_relationship_targets(&direct_binding_rel(purpose), [material.into()])?;
    apply_binding_strength(stage, rel, strength)?;
    Ok(())
}

/// Apply `MaterialBindingAPI` and author a **collection** binding named
/// `binding_name` on `prim`. The relationship targets the `collection`
/// path then the `material` path, per the spec's two-target convention.
pub fn bind_material_collection(
    stage: &Stage,
    prim: impl Into<Path>,
    binding_name: &str,
    collection: impl Into<Path>,
    material: impl Into<Path>,
    purpose: &str,
    strength: BindingStrength,
) -> Result<()> {
    let prim = Prim::new(stage, prim.into());
    stage.override_prim(prim.path().clone())?;
    prim.clone().add_applied_schema(API_MATERIAL_BINDING)?;
    let rel = prim.author_relationship_targets(
        &collection_binding_rel(purpose, binding_name),
        [collection.into(), material.into()],
    )?;
    apply_binding_strength(stage, rel, strength)?;
    Ok(())
}

/// Author `bindMaterialAs` on a freshly-bound relationship. Mirrors C++
/// `UsdShadeMaterialBindingAPI::SetMaterialBindingStrength`: the default
/// `weakerThanDescendants` is left unauthored unless a different opinion
/// already composes (from a weaker layer or a prior binding), in which
/// case it is authored explicitly to override that stale opinion.
fn apply_binding_strength(stage: &Stage, rel: Relationship, strength: BindingStrength) -> Result<()> {
    let needs_write = strength != BindingStrength::WeakerThanDescendants
        || composed_strength(stage, rel.path())? != BindingStrength::WeakerThanDescendants;
    if needs_write {
        rel.set_metadata(META_BIND_MATERIAL_AS, Value::Token(strength.as_token().to_string()))?;
    }
    Ok(())
}

/// Composed `bindMaterialAs` strength on a binding relationship, falling
/// back to the spec default when unauthored.
fn composed_strength(stage: &Stage, rel: &Path) -> Result<BindingStrength> {
    Ok(match stage.field::<Value>(rel.clone(), META_BIND_MATERIAL_AS)? {
        Some(Value::Token(t)) => BindingStrength::from_token(&t).unwrap_or_default(),
        _ => BindingStrength::default(),
    })
}

/// Read the directly-bound Material for `purpose`
/// ([`PURPOSE_ALL`](super::tokens::PURPOSE_ALL) for the fallback
/// binding). Returns `None` when no such binding is authored.
pub fn read_direct_binding(stage: &Stage, prim: &Path, purpose: &str) -> Result<Option<Path>> {
    let rel = prim.append_property(&direct_binding_rel(purpose))?;
    Ok(stage.relationship_targets(&rel)?.into_iter().next())
}

/// Read a collection binding `(collection, material)` for
/// `binding_name` + `purpose`. Returns `None` when not authored or the
/// relationship doesn't carry the expected two targets.
pub fn read_collection_binding(
    stage: &Stage,
    prim: &Path,
    binding_name: &str,
    purpose: &str,
) -> Result<Option<(Path, Path)>> {
    let rel = prim.append_property(&collection_binding_rel(purpose, binding_name))?;
    let targets = stage.relationship_targets(&rel)?;
    Ok(match targets.as_slice() {
        [collection, material] => Some((collection.clone(), material.clone())),
        _ => None,
    })
}

/// Read the `bindMaterialAs` strength on the direct binding for
/// `purpose`. Returns the spec default
/// ([`BindingStrength::WeakerThanDescendants`]) when unauthored.
pub fn read_binding_strength(stage: &Stage, prim: &Path, purpose: &str) -> Result<BindingStrength> {
    let rel = prim.append_property(&direct_binding_rel(purpose))?;
    composed_strength(stage, &rel)
}

/// Resolve the material bound to `prim` for `purpose`, walking `prim` and
/// its ancestors (spec §15 / `UsdShadeMaterialBindingAPI::ComputeBoundMaterial`).
///
/// A restricted purpose (`purpose != ""`) is resolved across the whole
/// ancestor chain before falling back to all-purpose, so a restricted binding
/// on any ancestor outranks an all-purpose binding on a closer prim. Within a
/// single purpose, a binding on a closer prim wins over one on an ancestor
/// unless the ancestor binding is `strongerThanDescendants` (the topmost such
/// ancestor then wins). At a single prim, a collection-based binding whose
/// collection includes `prim` beats a direct binding, and collection bindings
/// resolve in native property order.
pub fn compute_bound_material(stage: &Stage, prim: &Path, purpose: &str) -> Result<Option<Path>> {
    // Cache each collection's membership query across the namespace walk.
    let mut cache: HashMap<Path, Option<MembershipQuery>> = HashMap::new();
    for pur in purpose_fallbacks(purpose) {
        if let Some(material) = bound_material_for_single_purpose(stage, prim, pur, &mut cache)? {
            return Ok(Some(material));
        }
    }
    Ok(None)
}

/// Resolve the bound material for one concrete `purpose` by walking `prim` and
/// its ancestors. The closest binding wins unless a `strongerThanDescendants`
/// ancestor overrides it (the topmost such ancestor then wins).
fn bound_material_for_single_purpose(
    stage: &Stage,
    prim: &Path,
    purpose: &str,
    cache: &mut HashMap<Path, Option<MembershipQuery>>,
) -> Result<Option<Path>> {
    let mut winner: Option<Path> = None;
    let mut current = Some(prim.clone());
    while let Some(p) = current {
        if !p.is_abs_root() {
            if let Some((material, strength)) = winning_binding_at(stage, &p, prim, purpose, cache)? {
                if winner.is_none() || strength == BindingStrength::StrongerThanDescendants {
                    winner = Some(material);
                }
            }
        }
        current = p.parent();
    }
    Ok(winner)
}

/// The binding that wins at a single prim `p` for a concrete `purpose`, as
/// `(material, strength)`. A collection binding whose collection includes
/// `queried` beats the direct binding, in native property order.
fn winning_binding_at(
    stage: &Stage,
    p: &Path,
    queried: &Path,
    purpose: &str,
    cache: &mut HashMap<Path, Option<MembershipQuery>>,
) -> Result<Option<(Path, BindingStrength)>> {
    // Collection bindings beat direct, in native property order.
    for (collection, material, strength) in collection_bindings_on(stage, p, purpose)? {
        if is_collection_member(stage, &collection, queried, cache)? {
            return Ok(Some((material, strength)));
        }
    }
    if let Some(material) = read_direct_binding(stage, p, purpose)? {
        return Ok(Some((material, read_binding_strength(stage, p, purpose)?)));
    }
    Ok(None)
}

/// The collection bindings authored on `p` for `purpose`, as
/// `(collection, material, strength)`, in native property order.
fn collection_bindings_on(stage: &Stage, p: &Path, purpose: &str) -> Result<Vec<(Path, Path, BindingStrength)>> {
    let prefix = format!("{REL_MATERIAL_BINDING_COLLECTION}:");
    let mut out = Vec::new();
    for name in stage.prim_properties(p.clone())? {
        let Some(rest) = name.strip_prefix(&prefix) else {
            continue;
        };
        // `rest` is `<purpose>:<name>` (restricted) or `<name>` (all-purpose),
        // classified by token count to mirror C++ `_GetMaterialPurpose`: only a
        // single-colon remainder is purpose-restricted; a plain name or any
        // deeper-namespaced name is all-purpose.
        let binding_purpose = match rest.split(':').collect::<Vec<_>>().as_slice() {
            [pur, _name] => *pur,
            _ => PURPOSE_ALL,
        };
        if binding_purpose != purpose {
            continue;
        }
        let rel = p.append_property(&name)?;
        if let [collection, material] = stage.relationship_targets(&rel)?.as_slice() {
            out.push((collection.clone(), material.clone(), composed_strength(stage, &rel)?));
        }
    }
    Ok(out)
}

/// Whether `queried` is a member of the collection at `collection_path`,
/// caching the result by collection path. A path that is not a collection
/// identity caches `None` and is never a member.
fn is_collection_member(
    stage: &Stage,
    collection_path: &Path,
    queried: &Path,
    cache: &mut HashMap<Path, Option<MembershipQuery>>,
) -> Result<bool> {
    let query = match cache.entry(collection_path.clone()) {
        Entry::Occupied(e) => e.into_mut(),
        Entry::Vacant(e) => {
            let query = match is_collection_api_path(collection_path) {
                Some((prim, name)) => Some(Collection::new(prim, name).compute_membership_query(stage)?),
                None => None,
            };
            e.insert(query)
        }
    };
    Ok(query.as_ref().is_some_and(|q| q.is_path_included(queried)))
}

/// Purposes to try in preference order: a restricted purpose first, then the
/// all-purpose fallback (spec §15 — restricted preferred over all-purpose).
fn purpose_fallbacks(purpose: &str) -> Vec<&str> {
    if purpose == PURPOSE_ALL {
        vec![PURPOSE_ALL]
    } else {
        vec![purpose, PURPOSE_ALL]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn direct_all_purpose_binding_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
        stage.define_prim("/World/Mat")?.set_type_name("Material")?;
        bind_material(&stage, sdf::path("/World/Mesh")?, sdf::path("/World/Mat")?)?;

        assert!(stage.has_api_schema(&sdf::path("/World/Mesh")?, "MaterialBindingAPI")?);
        assert_eq!(
            read_direct_binding(&stage, &sdf::path("/World/Mesh")?, "")?.map(|p| p.as_str().to_string()),
            Some("/World/Mat".to_string()),
        );
        assert_eq!(
            read_binding_strength(&stage, &sdf::path("/World/Mesh")?, "")?,
            BindingStrength::WeakerThanDescendants,
        );
        Ok(())
    }

    #[test]
    fn purpose_binding_with_strength() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        stage.define_prim("/Mat")?.set_type_name("Material")?;
        bind_material_for_purpose(
            &stage,
            sdf::path("/Mesh")?,
            "preview",
            sdf::path("/Mat")?,
            BindingStrength::StrongerThanDescendants,
        )?;

        assert_eq!(
            stage.spec_type("/Mesh.material:binding:preview")?,
            Some(sdf::SpecType::Relationship),
        );
        assert_eq!(
            read_direct_binding(&stage, &sdf::path("/Mesh")?, "preview")?.map(|p| p.as_str().to_string()),
            Some("/Mat".to_string()),
        );
        assert_eq!(
            read_binding_strength(&stage, &sdf::path("/Mesh")?, "preview")?,
            BindingStrength::StrongerThanDescendants,
        );
        // The all-purpose binding wasn't authored.
        assert!(read_direct_binding(&stage, &sdf::path("/Mesh")?, "")?.is_none());
        Ok(())
    }

    #[test]
    fn bind_without_predefine() -> Result<()> {
        // Binding a prim that has no spec on the edit target yet must
        // still apply the API and author the relationship — `bind_*`
        // creates the `over` itself.
        let stage = Stage::builder().in_memory("anon.usda")?;
        bind_material(&stage, sdf::path("/World/Mesh")?, sdf::path("/World/Mat")?)?;

        assert!(stage.has_api_schema(&sdf::path("/World/Mesh")?, "MaterialBindingAPI")?);
        assert_eq!(
            read_direct_binding(&stage, &sdf::path("/World/Mesh")?, "")?.map(|p| p.as_str().to_string()),
            Some("/World/Mat".to_string()),
        );
        Ok(())
    }

    #[test]
    fn rebind_overrides_strength() -> Result<()> {
        // Rebinding with the default strength must clear a previously
        // authored stronger opinion, not silently leave it composing.
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        bind_material_for_purpose(
            &stage,
            sdf::path("/Mesh")?,
            "",
            sdf::path("/MatA")?,
            BindingStrength::StrongerThanDescendants,
        )?;
        bind_material_for_purpose(
            &stage,
            sdf::path("/Mesh")?,
            "",
            sdf::path("/MatB")?,
            BindingStrength::WeakerThanDescendants,
        )?;

        assert_eq!(
            read_binding_strength(&stage, &sdf::path("/Mesh")?, "")?,
            BindingStrength::WeakerThanDescendants,
        );
        Ok(())
    }

    #[test]
    fn collection_binding_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/Mat")?.set_type_name("Material")?;
        bind_material_collection(
            &stage,
            sdf::path("/Set")?,
            "metalBits",
            sdf::path("/Set.collection:metal")?,
            sdf::path("/Set/Mat")?,
            "",
            BindingStrength::WeakerThanDescendants,
        )?;

        let (collection, material) =
            read_collection_binding(&stage, &sdf::path("/Set")?, "metalBits", "")?.expect("collection binding");
        assert_eq!(collection.as_str(), "/Set.collection:metal");
        assert_eq!(material.as_str(), "/Set/Mat");
        Ok(())
    }

    fn bound(stage: &Stage, prim: &str, purpose: &str) -> Option<String> {
        compute_bound_material(stage, &sdf::path(prim).unwrap(), purpose)
            .unwrap()
            .map(|p| p.as_str().to_string())
    }

    #[test]
    fn closer_binding_wins() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/Mesh")?.set_type_name("Mesh")?;
        bind_material(&stage, sdf::path("/Set")?, sdf::path("/MatA")?)?;

        // Inherited from the ancestor.
        assert_eq!(bound(&stage, "/Set/Mesh", ""), Some("/MatA".to_string()));

        // A binding on the closer prim wins (both weakerThanDescendants).
        bind_material(&stage, sdf::path("/Set/Mesh")?, sdf::path("/MatB")?)?;
        assert_eq!(bound(&stage, "/Set/Mesh", ""), Some("/MatB".to_string()));
        // The ancestor itself still resolves to its own binding.
        assert_eq!(bound(&stage, "/Set", ""), Some("/MatA".to_string()));
        // Unbound prim → None.
        assert_eq!(bound(&stage, "/Other", ""), None);
        Ok(())
    }

    #[test]
    fn stronger_ancestor_wins() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/Mesh")?.set_type_name("Mesh")?;
        // Ancestor binding is stronger; closer binding is the default weak.
        bind_material_for_purpose(
            &stage,
            sdf::path("/Set")?,
            "",
            sdf::path("/MatStrong")?,
            BindingStrength::StrongerThanDescendants,
        )?;
        bind_material(&stage, sdf::path("/Set/Mesh")?, sdf::path("/MatWeak")?)?;

        // The stronger ancestor wins despite the closer binding.
        assert_eq!(bound(&stage, "/Set/Mesh", ""), Some("/MatStrong".to_string()));
        Ok(())
    }

    #[test]
    fn restricted_purpose_preferred() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        bind_material(&stage, sdf::path("/Mesh")?, sdf::path("/MatAll")?)?; // all-purpose
        bind_material_for_purpose(
            &stage,
            sdf::path("/Mesh")?,
            "preview",
            sdf::path("/MatPreview")?,
            BindingStrength::WeakerThanDescendants,
        )?;

        // Restricted purpose preferred over the all-purpose binding.
        assert_eq!(bound(&stage, "/Mesh", "preview"), Some("/MatPreview".to_string()));
        // A purpose with no restricted binding falls back to all-purpose.
        assert_eq!(bound(&stage, "/Mesh", "full"), Some("/MatAll".to_string()));
        Ok(())
    }

    #[test]
    fn restricted_ancestor_wins() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/Mesh")?.set_type_name("Mesh")?;
        // Restricted "preview" binding on the ancestor; the queried prim
        // carries only an all-purpose binding.
        bind_material_for_purpose(
            &stage,
            sdf::path("/Set")?,
            "preview",
            sdf::path("/MatPreview")?,
            BindingStrength::WeakerThanDescendants,
        )?;
        bind_material(&stage, sdf::path("/Set/Mesh")?, sdf::path("/MatAll")?)?;

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
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/A")?.set_type_name("Mesh")?;
        stage.define_prim("/Set/B")?.set_type_name("Mesh")?;
        let coll = crate::usd::apply_collection(&stage, sdf::path("/Set")?, "metal")?;
        coll.include_path(&stage, sdf::path("/Set/A")?)?;
        bind_material(&stage, sdf::path("/Set")?, sdf::path("/MatDir")?)?;
        bind_material_collection(
            &stage,
            sdf::path("/Set")?,
            "metalBits",
            sdf::path("/Set.collection:metal")?,
            sdf::path("/MatMetal")?,
            "",
            BindingStrength::WeakerThanDescendants,
        )?;
        Ok(stage)
    }

    #[test]
    fn collection_beats_direct() -> Result<()> {
        let stage = collection_scene()?;
        // /Set/A is a collection member → the collection binding wins over direct.
        assert_eq!(bound(&stage, "/Set/A", ""), Some("/MatMetal".to_string()));
        // /Set/B is not a member → falls back to the inherited direct binding.
        assert_eq!(bound(&stage, "/Set/B", ""), Some("/MatDir".to_string()));
        Ok(())
    }

    #[test]
    fn collection_native_order() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Set")?.set_type_name("Xform")?;
        stage.define_prim("/Set/A")?.set_type_name("Mesh")?;
        // Two collections that both include /Set/A.
        for c in ["first", "second"] {
            let coll = crate::usd::apply_collection(&stage, sdf::path("/Set")?, c)?;
            coll.include_path(&stage, sdf::path("/Set/A")?)?;
        }
        // Author binding "aaa" (collection `second`) before "zzz" (collection
        // `first`) — native *property* order, not target order, decides.
        bind_material_collection(
            &stage,
            sdf::path("/Set")?,
            "aaa",
            sdf::path("/Set.collection:second")?,
            sdf::path("/MatSecond")?,
            "",
            BindingStrength::WeakerThanDescendants,
        )?;
        bind_material_collection(
            &stage,
            sdf::path("/Set")?,
            "zzz",
            sdf::path("/Set.collection:first")?,
            sdf::path("/MatFirst")?,
            "",
            BindingStrength::WeakerThanDescendants,
        )?;

        // `aaa` precedes `zzz` in native property order, so its collection
        // binding (to `/MatSecond`) is the one tested and wins — even though
        // its collection `second` was authored after `first`.
        assert_eq!(bound(&stage, "/Set/A", ""), Some("/MatSecond".to_string()));
        Ok(())
    }
}
