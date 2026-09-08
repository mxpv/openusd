//! What a `UsdVolVolume` binds its fields through, which is a relationship per
//! field rather than a property the schema declares.

use openusd::Result;
use openusd::sdf;
use openusd::usd::{Relationship, SchemaBase};

use super::Volume;
use crate::SchemaError;

/// The namespace a field relationship is named under: a field is bound as
/// `field:<name>`, one relationship per field, which is why the prefix carries
/// the namespace delimiter that the generated `field` token does not.
pub const FIELD_NAMESPACE: &str = "field:";

impl Volume {
    /// The `field:<name>` relationship binding the field called `name`, whether
    /// or not it is authored (C++ `UsdVolVolume::GetFieldRelationship`). `name`
    /// is the bare field name, without the `field:` namespace.
    pub fn field_rel(&self, name: &str) -> Relationship {
        self.relationship(format!("{FIELD_NAMESPACE}{name}"))
    }

    /// Bind field `name` to the field prim at `target`, authoring the
    /// `field:<name>` relationship (C++ `UsdVolVolume::CreateFieldRelationship`).
    /// `name` must be non-empty, otherwise the property name would end in a
    /// colon (`field:`), which is not a valid USD property name.
    pub fn create_field_relationship(self, name: &str, target: impl sdf::IntoPath) -> Result<Self, SchemaError> {
        if name.is_empty() {
            return Err(SchemaError::EmptyFieldName);
        }
        self.create_relationship(format!("{FIELD_NAMESPACE}{name}"))?
            .set_custom(false)?
            .add_target(target)?;
        Ok(self)
    }

    /// `true` when a `field:<name>` relationship is authored on this volume
    /// (C++ `UsdVolVolume::HasFieldRelationship`).
    pub fn has_field_relationship(&self, name: &str) -> Result<bool> {
        let rel = self.path().append_property(format!("{FIELD_NAMESPACE}{name}"))?;
        Ok(!self.stage().relationship(rel)?.targets()?.is_empty())
    }

    /// The volume's `(field name, target prim path)` bindings, sorted by field
    /// name (C++ `UsdVolVolume::GetFieldPaths`).
    pub fn field_paths(&self) -> Result<Vec<(String, sdf::Path)>> {
        let mut fields = Vec::new();
        for name in self.stage().prim(self.path().clone())?.authored_property_names()? {
            let Some(field_name) = name.strip_prefix(FIELD_NAMESPACE) else {
                continue;
            };
            let rel = self.path().append_property(&name)?;
            if let Some(target) = self.stage().relationship(rel)?.targets()?.into_iter().next() {
                fields.push((field_name.to_string(), target));
            }
        }
        fields.sort();
        Ok(fields)
    }
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
            .create_field_relationship("density", sdf::path("/V/density")?)?
            .create_field_relationship("temperature", sdf::path("/V/temperature")?)?;

        let v = Volume::get(&stage, "/V")?.expect("Volume");
        assert!(v.has_field_relationship("density")?);
        assert_eq!(
            v.field_paths()?,
            vec![
                ("density".to_string(), sdf::path("/V/density")?),
                ("temperature".to_string(), sdf::path("/V/temperature")?),
            ],
        );
        Ok(())
    }

    #[test]
    fn create_field_rejects_empty() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let result = Volume::define(&stage, "/V")?.create_field_relationship("", sdf::path("/V/density")?);
        assert!(result.is_err());
        Ok(())
    }
}
