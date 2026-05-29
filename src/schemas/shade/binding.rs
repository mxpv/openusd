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

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

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
    prim.clone().add_applied_schema(API_MATERIAL_BINDING)?;
    let rel = prim.author_relationship_targets(&direct_binding_rel(purpose), [material.into()])?;
    if strength != BindingStrength::WeakerThanDescendants {
        rel.set_metadata(
            META_BIND_MATERIAL_AS,
            crate::sdf::Value::Token(strength.as_token().to_string()),
        )?;
    }
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
    prim.clone().add_applied_schema(API_MATERIAL_BINDING)?;
    let rel = prim.author_relationship_targets(
        &collection_binding_rel(purpose, binding_name),
        [collection.into(), material.into()],
    )?;
    if strength != BindingStrength::WeakerThanDescendants {
        rel.set_metadata(
            META_BIND_MATERIAL_AS,
            crate::sdf::Value::Token(strength.as_token().to_string()),
        )?;
    }
    Ok(())
}

/// Read the directly-bound Material for `purpose`
/// ([`PURPOSE_ALL`](super::tokens::PURPOSE_ALL) for the fallback
/// binding). Returns `None` when no such binding is authored.
pub fn read_direct_binding(stage: &Stage, prim: &Path, purpose: &str) -> Result<Option<Path>> {
    let rel = prim.append_property(&direct_binding_rel(purpose))?;
    Ok(read_rel_targets(stage, &rel)?.into_iter().next())
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
    let targets = read_rel_targets(stage, &rel)?;
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
    Ok(match stage.field::<crate::sdf::Value>(rel, META_BIND_MATERIAL_AS)? {
        Some(crate::sdf::Value::Token(t)) => BindingStrength::from_token(&t).unwrap_or_default(),
        _ => BindingStrength::default(),
    })
}

fn read_rel_targets(stage: &Stage, rel: &Path) -> Result<Vec<Path>> {
    use crate::sdf::Value;
    Ok(match stage.field::<Value>(rel.clone(), "targetPaths")? {
        Some(Value::PathListOp(op)) => op.flatten(),
        Some(Value::PathVec(v)) => v,
        _ => Vec::new(),
    })
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
}
