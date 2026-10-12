//! What `UsdGeomModelAPI` answers beyond its own properties.

use openusd::usd::{self, SchemaBase};
use openusd::{Result, gf, sdf};

use super::{Extent, ModelAPI, Purpose, tokens};
use crate::SchemaError;

impl ModelAPI {
    /// The `extentsHint` attribute, which caches the model's extent for each
    /// purpose (C++ `UsdGeomModelAPI::GetExtentsHintAttr`). No schema
    /// declares it. It is defined only where a layer authors it.
    pub fn extents_hint_attr(&self) -> usd::Attribute {
        self.attribute(tokens::EXTENTS_HINT)
    }

    /// The extents cached on the model at `time` (C++
    /// `UsdGeomModelAPI::GetExtentsHint`). A `time` of `None` reads the
    /// default value.
    ///
    /// The extents are those of the purposes in [`Purpose::ORDERED`], in
    /// that order. The list holds one extent at least and may stop before
    /// the last purpose: a model with no geometry of the trailing purposes
    /// authors no extent for them.
    ///
    /// The answer is `None` where the attribute reads no value, or holds
    /// fewer than the two corners of one extent.
    ///
    /// C++ answers the attribute's array of corners as authored. This
    /// answers the extents `UsdGeomBBoxCache` takes from that array: each
    /// two corners are one extent, a corner left over at the end is dropped,
    /// and so are the extents past the last purpose.
    ///
    /// # Example
    ///
    /// ```
    /// use openusd::gf;
    /// use openusd::usd::{self, SchemaBase};
    /// use openusd_schemas::geom;
    ///
    /// let stage = usd::Stage::builder()
    ///     .schema_registry(openusd_schemas::schema_registry())
    ///     .in_memory("scene.usda")?;
    /// let model = geom::ModelAPI::apply(geom::Xform::define(&stage, "/Model")?.prim())?;
    /// assert_eq!(model.extents_hint_at(None)?, None);
    ///
    /// // The default purpose alone.
    /// let extent = [gf::vec3f(-1.0, -1.0, -1.0), gf::vec3f(1.0, 1.0, 1.0)];
    /// model.set_extents_hint(&[extent], None)?;
    /// assert_eq!(model.extents_hint_at(None)?, Some(vec![extent]));
    /// # Ok::<(), openusd_schemas::SchemaError>(())
    /// ```
    pub fn extents_hint_at(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<Option<Vec<Extent>>> {
        let corners: Option<Vec<gf::Vec3f>> = self.extents_hint_attr().get_at(time)?;
        let extents = corners.as_deref().map(|corners| corners.as_chunks().0);
        Ok(extents
            .filter(|extents| !extents.is_empty())
            .map(|extents| extents[..extents.len().min(Purpose::ORDERED.len())].to_vec()))
    }

    /// Author `extents` as the model's extents hint at `time` (C++
    /// `UsdGeomModelAPI::SetExtentsHint`), creating the `float3[]` attribute
    /// where nothing declares it. A `time` of `None` authors the default
    /// value.
    ///
    /// `extents` are those of the purposes in [`Purpose::ORDERED`], in that
    /// order, from the first to the last one the model has geometry of. An
    /// empty list, or one with more extents than there are purposes, is
    /// [`SchemaError::ExtentsHintCount`].
    pub fn set_extents_hint(
        &self,
        extents: &[Extent],
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<usd::Attribute, SchemaError> {
        let max = Purpose::ORDERED.len();
        if extents.is_empty() || extents.len() > max {
            return Err(SchemaError::ExtentsHintCount {
                prim: self.path().clone(),
                found: extents.len(),
                max,
            });
        }
        Ok(self
            .attribute_builder(tokens::EXTENTS_HINT, sdf::ValueTypeName::FLOAT3_ARRAY)
            .custom(false)
            .set_at(extents.as_flattened().to_vec(), time)
            .build()?)
    }
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, sdf};

    use crate::SchemaError;
    use crate::geom::extent::tests::extent;
    use crate::geom::{ModelAPI, Xform};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    fn model(stage: &usd::Stage) -> Result<ModelAPI> {
        Ok(ModelAPI::apply(Xform::define(stage, "/Model")?.prim())?)
    }

    /// A hint reads back as authored, from a `float3[]` attribute that is
    /// not custom, at the default time and at a sample.
    #[test]
    fn hint_round_trip() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let model = model(&stage)?;
        assert!(!model.extents_hint_attr().is_defined()?);
        assert_eq!(model.extents_hint_at(None)?, None);

        let default = [extent([-1.0; 3], [1.0; 3]), extent([0.0; 3], [2.0; 3])];
        let attr = model.set_extents_hint(&default, None)?;
        assert_eq!(attr.path(), model.extents_hint_attr().path());
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::FLOAT3_ARRAY));
        assert!(!attr.is_custom()?);
        assert_eq!(model.extents_hint_at(None)?, Some(default.to_vec()));

        let time = usd::TimeCode::new(4.0);
        let sampled = [extent([-3.0; 3], [3.0; 3])];
        model.set_extents_hint(&sampled, time)?;
        assert_eq!(model.extents_hint_at(time)?, Some(sampled.to_vec()));
        assert_eq!(model.extents_hint_at(None)?, Some(default.to_vec()));
        Ok(())
    }

    /// A hint holds an extent for one purpose at least and for each purpose
    /// at most; any other count authors nothing.
    #[test]
    fn hint_count_refused() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let model = model(&stage)?;
        let unit = extent([0.0; 3], [1.0; 3]);
        for count in [0, 5] {
            let refused = model.set_extents_hint(&vec![unit; count], None);
            assert!(
                matches!(refused, Err(SchemaError::ExtentsHintCount { found, .. }) if found == count),
                "{refused:?}"
            );
        }
        assert!(!model.extents_hint_attr().is_defined()?);

        model.set_extents_hint(&[unit; 4], None)?;
        assert_eq!(model.extents_hint_at(None)?, Some(vec![unit; 4]));
        Ok(())
    }

    /// An odd corner and the extents past the fourth are dropped from a
    /// hint authored with them. A hint with fewer than two corners, or a
    /// blocked one, reads as none.
    #[test]
    fn hint_malformed() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let model = model(&stage)?;
        let unit = extent([0.0; 3], [1.0; 3]);
        let attr = model.set_extents_hint(&[unit], None)?;
        let attr = attr.set(vec![unit[0], unit[1], gf::vec3f(5.0, 5.0, 5.0)])?;
        assert_eq!(model.extents_hint_at(None)?, Some(vec![unit]));

        let attr = attr.set(vec![gf::vec3f(1.0, 1.0, 1.0); 11])?;
        assert_eq!(
            model.extents_hint_at(None)?,
            Some(vec![[gf::vec3f(1.0, 1.0, 1.0); 2]; 4])
        );

        for corners in [0, 1] {
            attr.clone().set(vec![unit[0]; corners])?;
            assert_eq!(model.extents_hint_at(None)?, None);
        }

        attr.block()?;
        assert_eq!(model.extents_hint_at(None)?, None);
        Ok(())
    }
}
