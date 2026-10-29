//! The physics material bound to a prim: what a collider is weighed with
//! and what the parser reports for it (C++ `_GetMaterialBinding` in
//! parseUtils.cpp and the material step of `ComputeMassProperties`).

use openusd::usd::SchemaBase;

use crate::SchemaError;
use crate::shade::MaterialBindingAPI;

use super::{MATERIAL_PURPOSE, MaterialAPI};

impl MaterialAPI {
    /// The physics material `binding` resolves for the [`MATERIAL_PURPOSE`]:
    /// the bound `Material` where it carries `PhysicsMaterialAPI`, and `None`
    /// where nothing is bound or the bound material does not (C++
    /// `_GetMaterialBinding` followed by `HasAPI<UsdPhysicsMaterialAPI>`).
    pub fn bound(binding: &MaterialBindingAPI) -> Result<Option<MaterialAPI>, SchemaError> {
        let Some(material) = binding.bound_material(MATERIAL_PURPOSE, true)? else {
            return Ok(None);
        };
        Ok(MaterialAPI::from_prim(material.prim().clone())?)
    }
}

#[cfg(test)]
mod tests {
    use openusd::usd::SchemaBase;

    use super::{MATERIAL_PURPOSE, MaterialAPI, MaterialBindingAPI};
    use crate::SchemaError;
    use crate::shade::Material;

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// Nothing bound, a bound material without `PhysicsMaterialAPI`, and one
    /// with it.
    #[test]
    fn bound_material_api() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let binding = MaterialBindingAPI::apply(&stage.define_prim("/cube")?)?;
        assert!(MaterialAPI::bound(&binding)?.is_none());

        let plain = Material::define(&stage, "/plain")?;
        binding.bind_for_purpose(MATERIAL_PURPOSE, plain.path().clone(), None)?;
        assert!(MaterialAPI::bound(&binding)?.is_none());

        let physics = Material::define(&stage, "/physics")?;
        MaterialAPI::apply(physics.prim())?;
        binding.bind_for_purpose(MATERIAL_PURPOSE, physics.path().clone(), None)?;
        let bound = MaterialAPI::bound(&binding)?.expect("the physics material is bound");
        assert_eq!(bound.path(), physics.path());
        Ok(())
    }
}
