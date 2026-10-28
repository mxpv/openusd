//! What `UsdGeomModelAPI` answers beyond its own properties: the extents a
//! model caches, the mode it is drawn in, and the constraint targets it
//! publishes.

use openusd::usd::{self, SchemaBase};
use openusd::{Result, gf, sdf, tf, vt};

use super::constraint_target::holds_matrix;
use super::{
    BBoxCache, Boundable, ConstraintTarget, DrawMode, Extent, ModelAPI, Purpose, declared_type, extent, nearest, tokens,
};
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

    /// The extents to cache on the model at the time of `cache`, as
    /// [`set_extents_hint`](Self::set_extents_hint) takes them (C++
    /// `UsdGeomModelAPI::ComputeExtentsHint`).
    ///
    /// They are the model's untransformed bound for each purpose in
    /// [`Purpose::ORDERED`], as an axis-aligned extent, up to the last
    /// purpose the model has geometry of. A model with none has one extent,
    /// the corners of [`gf::Range3d::EMPTY`].
    ///
    /// A model that is itself boundable takes the extent its type computes
    /// for every purpose, by the cache's extent functions, and the one
    /// empty extent where its type computes none.
    ///
    /// The cache answers with its own options, and should not be one that
    /// bounds models by their hints, which would answer the hint the model
    /// holds. Its included purposes play no part and are left as they are,
    /// where C++ leaves the last purpose included.
    ///
    /// # Example
    ///
    /// ```
    /// use openusd::usd::{self, SchemaBase};
    /// use openusd::gf;
    /// use openusd_schemas::geom::{self, Purpose};
    ///
    /// let stage = usd::Stage::builder()
    ///     .schema_registry(openusd_schemas::schema_registry())
    ///     .in_memory("scene.usda")?;
    /// let model = geom::ModelAPI::apply(geom::Xform::define(&stage, "/Model")?.prim())?;
    /// geom::Sphere::define(&stage, "/Model/Ball")?;
    ///
    /// let mut cache = geom::BBoxCache::new(None, [Purpose::Default]);
    /// let extents = model.compute_extents_hint(&mut cache)?;
    /// assert_eq!(extents, [[gf::vec3f(-1.0, -1.0, -1.0), gf::vec3f(1.0, 1.0, 1.0)]]);
    /// model.set_extents_hint(&extents, None)?;
    /// # Ok::<(), openusd_schemas::SchemaError>(())
    /// ```
    pub fn compute_extents_hint(&self, cache: &mut BBoxCache) -> Result<Vec<Extent>, SchemaError> {
        if Boundable::from_prim(self.prim().clone())?.is_some() {
            let extent = cache.context().shape_extent(self.prim(), cache.time(), None)?;
            return Ok(match extent {
                Some(extent) => vec![extent; Purpose::ORDERED.len()],
                None => vec![extent::EMPTY],
            });
        }

        let ranges = cache.purpose_ranges(self.prim())?;
        let bounded = ranges
            .iter()
            .rposition(|range| !range.is_empty())
            .map_or(1, |last| last + 1);
        Ok(ranges[..bounded].iter().map(|range| Extent::from(*range)).collect())
    }

    /// The mode the prim is drawn in (C++
    /// `UsdGeomModelAPI::ComputeModelDrawMode`): the `model:drawMode` of
    /// the nearest model at or above it that has one other than
    /// `inherited`, or [`DrawMode::Default`] where there is none.
    ///
    /// Only a [model](usd::Prim::is_model) decides a draw mode, so a
    /// `model:drawMode` on any other prim plays no part, and neither does
    /// the pseudo-root. A token that names no draw mode decides
    /// [`DrawMode::Default`], where C++ answers the token.
    ///
    /// `parent` is the draw mode computed for the prim's parent, where a
    /// walk has it: it answers for a prim that decides none of its own,
    /// with no prim above looked at. A walk over many prims passes it. With
    /// none, each call reads `model:drawMode` on every prim above up to the
    /// pseudo-root.
    ///
    /// # Example
    ///
    /// ```
    /// use openusd::usd::{self, SchemaBase};
    /// use openusd_schemas::geom::{self, DrawMode};
    ///
    /// let stage = usd::Stage::builder()
    ///     .schema_registry(openusd_schemas::schema_registry())
    ///     .in_memory("scene.usda")?;
    /// let set = geom::Xform::define(&stage, "/Set")?.prim().clone().set_kind("group")?;
    /// let chair = geom::Xform::define(&stage, "/Set/Chair")?.prim().clone().set_kind("component")?;
    /// let set = geom::ModelAPI::apply(&set)?;
    /// let chair = geom::ModelAPI::apply(&chair)?;
    /// assert_eq!(chair.compute_model_draw_mode(None)?, DrawMode::Default);
    ///
    /// // The set's mode reaches the models beneath it.
    /// set.model_draw_mode_attr().set(DrawMode::Bounds)?;
    /// assert_eq!(chair.compute_model_draw_mode(None)?, DrawMode::Bounds);
    /// # Ok::<(), openusd_schemas::SchemaError>(())
    /// ```
    pub fn compute_model_draw_mode(&self, parent: impl Into<Option<DrawMode>>) -> Result<DrawMode> {
        if let Some(parent) = parent.into() {
            return Ok(decided_draw_mode(self.prim())?.unwrap_or(parent));
        }
        let decided = nearest(self.prim(), |prim| Ok(Some(prim)), decided_draw_mode)?;
        Ok(decided.unwrap_or(DrawMode::Default))
    }

    /// The constraint target named `name`, the attribute
    /// `constraintTargets:<name>` (C++
    /// `UsdGeomModelAPI::GetConstraintTarget`), or `None` where the prim
    /// has [none](ConstraintTarget::is_valid) by that name.
    pub fn constraint_target(&self, name: &str) -> Result<Option<ConstraintTarget>> {
        ConstraintTarget::from_attribute(self.attribute(ConstraintTarget::attr_name(name)))
    }

    /// The constraint target named `name`, created as the `matrix4d`
    /// attribute `constraintTargets:<name>` where the prim has no attribute
    /// of that name (C++ `UsdGeomModelAPI::CreateConstraintTarget`).
    ///
    /// Only a [model](usd::Prim::is_model) has constraint targets, so any
    /// other prim is [`SchemaError::ConstraintTargetOffModel`], and a
    /// property of that name that is no matrix-valued attribute is
    /// [`SchemaError::ConstraintTargetType`]. Neither authors anything.
    /// C++ answers a target that is not valid in both cases, and creates
    /// the attribute on a prim that is not a model.
    pub fn create_constraint_target(&self, name: &str) -> Result<ConstraintTarget, SchemaError> {
        if !self.prim().is_model()? {
            return Err(SchemaError::ConstraintTargetOffModel {
                prim: self.path().clone(),
            });
        }
        let attr_name = ConstraintTarget::attr_name(name);
        let attr = self.attribute(attr_name.clone());
        match declared_type(&attr)? {
            Some(type_name) if holds_matrix(&type_name) => Ok(ConstraintTarget::new(attr)),
            Some(type_name) => Err(SchemaError::ConstraintTargetType {
                attribute: attr.path().clone(),
                type_name: type_name.as_token(),
            }),
            // A relationship has the name and declares no type.
            None if self.prim().relationship(attr_name.clone()).is_defined()? => {
                Err(SchemaError::ConstraintTargetType {
                    attribute: attr.path().clone(),
                    type_name: tf::Token::default(),
                })
            }
            None => {
                let builder = self.attribute_builder(attr_name, sdf::ValueTypeName::MATRIX4D);
                Ok(ConstraintTarget::new(builder.custom(false).build()?))
            }
        }
    }

    /// The constraint targets of the prim, in the order of its attributes
    /// (C++ `UsdGeomModelAPI::GetConstraintTargets`). A prim that is not a
    /// model has none.
    pub fn constraint_targets(&self) -> Result<Vec<ConstraintTarget>> {
        let prim = self.prim();
        if !prim.is_model()? {
            return Ok(Vec::new());
        }
        let mut targets = Vec::new();
        for attribute in prim.attributes()? {
            if ConstraintTarget::is_shaped(&attribute)? {
                targets.push(ConstraintTarget::new(attribute));
            }
        }
        Ok(targets)
    }
}

/// The draw mode `prim` decides for itself and the prims beneath it: its
/// `model:drawMode` where that is other than `inherited` and the prim is a
/// model below the pseudo-root.
fn decided_draw_mode(prim: &usd::Prim) -> Result<Option<DrawMode>> {
    if prim.path().is_abs_root() {
        return Ok(None);
    }
    // A value that is no token decides nothing, as an attribute with no
    // value does.
    let value = prim.attribute(tokens::MODEL_DRAW_MODE).get::<vt::Value>()?;
    let Some(token) = value.and_then(|value| value.try_as_token()) else {
        return Ok(None);
    };
    let mode = DrawMode::from_token(token).unwrap_or(DrawMode::Default);
    // Few prims author a mode, and those alone are asked whether they are
    // models, which reads the kind of every prim above.
    Ok((mode != DrawMode::Inherited && prim.is_model()?).then_some(mode))
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, sdf};

    use crate::SchemaError;
    use crate::geom::extent::tests::extent;
    use crate::geom::{BBoxCache, Cube, DrawMode, ExtentFn, ModelAPI, PointInstancer, Purpose, Sphere, Xform, tokens};

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

    /// The extents computed for a model are its bound for each purpose, up
    /// to the last one it has geometry of, and a cache that reads them back
    /// as a hint bounds the model as one that bounds its geometry.
    #[test]
    fn computed_hint_per_purpose() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Model" (kind = "component")
{
    double3 xformOp:translate = (100, 0, 0)
    uniform token[] xformOpOrder = ["xformOp:translate"]

    def Sphere "Ball" {}

    def Cube "Shell"
    {
        uniform token purpose = "render"
        double size = 10
    }
}

def Xform "Guides" (kind = "component")
{
    def Cube "Guide"
    {
        uniform token purpose = "guide"
    }
}

def Xform "Empty" (kind = "component") {}
"#,
        )?;
        let empty = crate::geom::extent::EMPTY;
        let model = |path: &str| -> Result<ModelAPI> { Ok(ModelAPI::from_prim_unchecked(stage.prim(path)?)) };
        let mut cache = BBoxCache::new(None, [Purpose::Proxy, Purpose::Guide]);

        // The model's own transform plays no part.
        let extents = model("/Model")?.compute_extents_hint(&mut cache)?;
        assert_eq!(extents, [extent([-1.0; 3], [1.0; 3]), extent([-5.0; 3], [5.0; 3])]);
        assert_eq!(cache.included_purposes(), [Purpose::Proxy, Purpose::Guide]);

        // Purposes before the last one with geometry keep their place.
        let guides = model("/Guides")?.compute_extents_hint(&mut cache)?;
        assert_eq!(guides, [empty, empty, empty, extent([-1.0; 3], [1.0; 3])]);
        assert_eq!(model("/Empty")?.compute_extents_hint(&mut cache)?, [empty]);

        model("/Model")?.set_extents_hint(&extents, None)?;
        let prim = stage.prim("/Model")?;
        let mut hinted = BBoxCache::new(None, [Purpose::Default, Purpose::Render]).with_extents_hint(true);
        let mut plain = BBoxCache::new(None, [Purpose::Default, Purpose::Render]);
        assert_eq!(
            hinted.world_bound(&prim)?.aligned_range(),
            plain.world_bound(&prim)?.aligned_range()
        );
        Ok(())
    }

    /// A model that is itself boundable takes the extent its type computes
    /// for every purpose, by the functions of the cache asked, and one
    /// empty extent where its type computes none.
    #[test]
    fn computed_hint_boundable() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mut cache = BBoxCache::new(None, [Purpose::Default]);
        let ball = Sphere::define(&stage, "/Ball")?;
        let model = ModelAPI::from_prim_unchecked(ball.prim().clone());
        let extents = model.compute_extents_hint(&mut cache)?;
        assert_eq!(extents, [extent([-1.0; 3], [1.0; 3]); 4]);

        let cube: ExtentFn = |_prim, _time, transform, _context| Ok(Some(Cube::extent_from(6.0, transform)));
        let mut extents = crate::extent_registry().clone();
        extents.register(tokens::SPHERE, cube);
        let mut cache = cache.with_extents(extents);
        let extents = model.compute_extents_hint(&mut cache)?;
        assert_eq!(extents, [extent([-3.0; 3], [3.0; 3]); 4]);

        let bare = PointInstancer::define(&stage, "/Bare")?;
        let extents = ModelAPI::from_prim_unchecked(bare.prim().clone()).compute_extents_hint(&mut cache)?;
        assert_eq!(extents, [crate::geom::extent::EMPTY]);
        Ok(())
    }

    /// A prim is drawn in the mode of the nearest model at or above it that
    /// has one other than `inherited`. A prim that is no model decides
    /// none, and the mode handed in for the parent stands in for the prims
    /// above.
    #[test]
    fn draw_mode_nearest_model() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "World" (kind = "group")
{
    uniform token model:drawMode = "bounds"

    def Xform "Set" (kind = "group")
    {
        def Xform "Chair" (kind = "component") {}

        def Xform "Table" (kind = "component")
        {
            uniform token model:drawMode = "cards"
        }

        def Xform "Lamp" (kind = "component")
        {
            uniform token model:drawMode = "inherited"
        }

        def Xform "Sketch" (kind = "component")
        {
            uniform token model:drawMode = "sketch"
        }

        def Xform "Mistyped" (kind = "component")
        {
            custom string model:drawMode = "cards"
        }

        def Xform "Loose"
        {
            uniform token model:drawMode = "origin"

            def Xform "Under" {}
        }
    }
}

def Xform "Plain" (kind = "component")
{
    def Xform "Geom" {}
}
"#,
        )?;
        let mode = |path: &str, parent: Option<DrawMode>| -> Result<DrawMode> {
            let model = ModelAPI::from_prim_unchecked(stage.prim(path)?);
            Ok(model.compute_model_draw_mode(parent)?)
        };
        assert_eq!(mode("/World", None)?, DrawMode::Bounds);
        assert_eq!(mode("/World/Set", None)?, DrawMode::Bounds);
        assert_eq!(mode("/World/Set/Chair", None)?, DrawMode::Bounds);
        assert_eq!(mode("/World/Set/Table", None)?, DrawMode::Cards);
        assert_eq!(mode("/World/Set/Lamp", None)?, DrawMode::Bounds);
        assert_eq!(mode("/World/Set/Sketch", None)?, DrawMode::Default);
        // A mode that is no token is passed over.
        assert_eq!(mode("/World/Set/Mistyped", None)?, DrawMode::Bounds);
        // A prim that is no model decides nothing, for itself or below.
        assert!(!stage.prim("/World/Set/Loose")?.is_model()?);
        assert_eq!(mode("/World/Set/Loose", None)?, DrawMode::Bounds);
        assert_eq!(mode("/World/Set/Loose/Under", None)?, DrawMode::Bounds);
        assert_eq!(mode("/Plain", None)?, DrawMode::Default);
        assert_eq!(mode("/Plain/Geom", None)?, DrawMode::Default);
        assert_eq!(mode("/", None)?, DrawMode::Default);

        // The parent's mode answers where the prim decides none, and its
        // own mode still comes first.
        assert_eq!(mode("/World/Set/Chair", Some(DrawMode::Origin))?, DrawMode::Origin);
        assert_eq!(mode("/World/Set/Lamp", Some(DrawMode::Inherited))?, DrawMode::Inherited);
        assert_eq!(mode("/World/Set/Table", Some(DrawMode::Origin))?, DrawMode::Cards);
        assert_eq!(mode("/Plain", Some(DrawMode::Cards))?, DrawMode::Cards);
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
