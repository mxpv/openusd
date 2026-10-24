//! What a `UsdVolVolume` binds its fields through, which is a relationship per
//! field rather than a property the schema declares.

use std::collections::BTreeMap;

use openusd::Result;
use openusd::sdf;
use openusd::usd::{Property, Relationship, SchemaBase};

use super::Volume;
use crate::{SchemaError, namespaced};

/// The namespace a field relationship is named under: a field is bound as
/// `field:<name>`, one relationship per field, which is why the prefix carries
/// the namespace delimiter that the generated `field` token does not.
pub const FIELD_NAMESPACE: &str = "field:";

impl Volume {
    /// The relationship binding the field called `name`, whether or not it is
    /// authored (C++ `UsdPrim::GetRelationship` over the namespaced name).
    /// `name` is the field name, with or without the `field:` namespace:
    /// `"density"` and `"field:density"` name one relationship.
    pub fn field_rel(&self, name: &str) -> Relationship {
        self.relationship(namespaced(FIELD_NAMESPACE, name).as_ref())
    }

    /// Bind field `name` to `target`, authoring the `field:<name>`
    /// relationship as a custom one whose only target is `target` (C++
    /// `UsdVolVolume::CreateFieldRelationship`). Targets an earlier call
    /// authored are replaced.
    ///
    /// `target` is a prim or a property directly on one, absolute or relative
    /// to this volume, and need not exist; any other path is
    /// [`SchemaError::FieldTarget`]. A name with nothing after the namespace
    /// is [`SchemaError::EmptyFieldName`]. Neither error authors anything.
    pub fn create_field_rel(self, name: &str, target: impl sdf::IntoPath) -> Result<Self, SchemaError> {
        let name = namespaced(FIELD_NAMESPACE, name);
        if name == FIELD_NAMESPACE {
            return Err(SchemaError::EmptyFieldName);
        }
        let target = sdf::try_into_path(target)?;
        if !target.is_prim() && !target.is_prim_property() {
            return Err(SchemaError::FieldTarget { path: target });
        }
        self.relationship_builder(name.as_ref())
            .custom(true)
            .set_targets([target])
            .build()?;
        Ok(self)
    }

    /// `true` when a relationship binds field `name`, even one that is
    /// blocked or has no targets (C++ `UsdVolVolume::HasFieldRelationship`).
    pub fn has_field_rel(&self, name: &str) -> Result<bool> {
        self.field_rel(name).is_defined()
    }

    /// The prim field `name` is bound to: the relationship's forwarded target
    /// when there is exactly one and it is a prim path, `None` otherwise (C++
    /// `UsdVolVolume::GetFieldPath`).
    pub fn field_path(&self, name: &str) -> Result<Option<sdf::Path>> {
        Ok(bound_prim(self.field_rel(name).forwarded_targets()?))
    }

    /// Block the binding of field `name` with an explicit empty target list on
    /// the edit target, which hides the targets weaker layers author (C++
    /// `UsdVolVolume::BlockFieldRelationship`). `false`, with nothing
    /// authored, when no relationship binds the field.
    pub fn block_field_rel(&self, name: &str) -> Result<bool> {
        let rel = self.field_rel(name);
        if !rel.is_defined()? {
            return Ok(false);
        }
        rel.block_targets()?;
        Ok(true)
    }

    /// The volume's fields, each keyed by its relationship's base name
    /// (`field:a:b` keys as `b`) and bound as [`field_path`](Self::field_path)
    /// binds one; a relationship that binds no single prim is left out (C++
    /// `UsdVolVolume::GetFieldPaths`). Of two relationships with one base
    /// name, the one `Prim::relationships_in_namespace` lists first is kept.
    pub fn field_paths(&self) -> Result<BTreeMap<String, sdf::Path>> {
        let mut fields = BTreeMap::new();
        for rel in self.prim().relationships_in_namespace(FIELD_NAMESPACE)? {
            if let Some(target) = bound_prim(rel.forwarded_targets()?) {
                fields.entry(rel.base_name().to_string()).or_insert(target);
            }
        }
        Ok(fields)
    }
}

/// The target when `targets` holds exactly one and it is a prim path, `None`
/// for any other list.
fn bound_prim(targets: Vec<sdf::Path>) -> Option<sdf::Path> {
    let [target]: [sdf::Path; 1] = targets.try_into().ok()?;
    target.is_prim().then_some(target)
}

#[cfg(test)]
mod tests {
    use super::*;

    use openusd::Result;
    use openusd::sdf;

    use crate::vol::Volume;

    #[test]
    fn volume_fields_roundtrip() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        Volume::define(&stage, "/V")?
            .create_field_rel("density", sdf::path("/V/density")?)?
            .create_field_rel("temperature", sdf::path("/V/temperature")?)?;

        let v = Volume::get(&stage, "/V")?.expect("Volume");
        assert!(v.has_field_rel("density")?);
        assert_eq!(
            v.field_paths()?,
            BTreeMap::from([
                ("density".to_string(), sdf::path("/V/density")?),
                ("temperature".to_string(), sdf::path("/V/temperature")?),
            ]),
        );
        Ok(())
    }

    #[test]
    fn create_field_rejects_empty() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let volume = Volume::define(&stage, "/V")?;
        for name in ["", FIELD_NAMESPACE] {
            let result = volume.clone().create_field_rel(name, sdf::path("/V/density")?);
            assert!(matches!(result, Err(SchemaError::EmptyFieldName)), "{name:?}");
        }
        Ok(())
    }

    #[test]
    fn field_name_namespaced() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let volume = Volume::define(&stage, "/V")?.create_field_rel("field:x", "/V/x")?;
        assert_eq!(volume.field_rel("x").path(), volume.field_rel("field:x").path());
        assert!(volume.has_field_rel("x")?);
        assert_eq!(volume.field_path("x")?, Some(sdf::path("/V/x")?));
        Ok(())
    }

    #[test]
    fn field_base_name_key() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let volume = Volume::define(&stage, "/V")?.create_field_rel("a:b", "/V/b")?;
        assert_eq!(
            volume.field_paths()?,
            BTreeMap::from([("b".to_string(), sdf::path("/V/b")?)])
        );
        Ok(())
    }

    #[test]
    fn field_multiple_targets() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let volume = Volume::define(&stage, "/V")?.create_field_rel("density", "/V/a")?;
        volume.field_rel("density").add_target("/V/b")?;
        assert_eq!(volume.field_path("density")?, None);
        assert!(volume.field_paths()?.is_empty());
        Ok(())
    }
}
