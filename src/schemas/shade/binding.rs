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

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::usd::{Prim, Relationship, Stage};

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
/// A binding on a closer prim wins over one on an ancestor, **unless** the
/// ancestor binding is `strongerThanDescendants` (the topmost such ancestor
/// then wins). A restricted-purpose binding (`purpose != ""`) is preferred
/// over an all-purpose one at the same prim.
///
/// Currently resolves **direct** bindings; collection-based bindings are
/// added on top in a following commit (they take precedence at a prim once
/// supported).
pub fn compute_bound_material(stage: &Stage, prim: &Path, purpose: &str) -> Result<Option<Path>> {
    let mut winner: Option<Path> = None;
    let mut current = Some(prim.clone());
    while let Some(p) = current {
        if !p.is_abs_root() {
            if let Some((material, strength)) = winning_binding_at(stage, &p, prim, purpose)? {
                // Closest binding wins by default; a `strongerThanDescendants`
                // ancestor overrides it (so the topmost such ancestor wins).
                if winner.is_none() || strength == BindingStrength::StrongerThanDescendants {
                    winner = Some(material);
                }
            }
        }
        current = p.parent();
    }
    Ok(winner)
}

/// The binding that wins at a single prim `p` for `purpose`, as
/// `(material, strength)`. A restricted-purpose binding is preferred over an
/// all-purpose one. `queried` is the prim that collection membership is
/// tested against (used once collection bindings are supported).
fn winning_binding_at(
    stage: &Stage,
    p: &Path,
    queried: &Path,
    purpose: &str,
) -> Result<Option<(Path, BindingStrength)>> {
    let _ = queried;
    for pur in purpose_fallbacks(purpose) {
        if let Some(material) = read_direct_binding(stage, p, pur)? {
            return Ok(Some((material, read_binding_strength(stage, p, pur)?)));
        }
    }
    Ok(None)
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
    fn bound_material_inherits_then_closer_wins() -> Result<()> {
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
    fn stronger_than_descendants_ancestor_overrides_closer() -> Result<()> {
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
    fn restricted_purpose_preferred_then_falls_back() -> Result<()> {
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
}
