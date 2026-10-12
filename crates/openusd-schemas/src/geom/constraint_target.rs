//! `UsdGeomConstraintTarget` — a named frame a model publishes for other
//! prims to be constrained to.

use openusd::usd;
use openusd::{Result, gf, sdf, tf};

use super::{AttributeMetadata, XformCache, declared_type};
use crate::SchemaError;

/// A constraint target: a matrix-valued attribute of a model, in the
/// `constraintTargets` namespace, that places a frame in the model's own
/// space (C++ `UsdGeomConstraintTarget`).
///
/// A rig publishes the frames something outside it may follow, a hand to
/// hold a prop by say, without exposing the rig behind them. A target is
/// found by its attribute, and its place in the world is the model's.
///
/// [`ModelAPI`](super::ModelAPI) creates and lists the targets of a model.
///
/// # Example
///
/// ```
/// use openusd::usd::{self, SchemaBase};
/// use openusd::gf;
/// use openusd_schemas::geom::{self, XformableExt};
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let xform = geom::Xform::define(&stage, "/Hero")?.set_translate(gf::vec3d(10.0, 0.0, 0.0))?;
/// let hero = xform.prim().clone().set_kind("component")?;
/// let model = geom::ModelAPI::from_prim_unchecked(hero);
///
/// let hand = model.create_constraint_target("leftHand")?;
/// assert_eq!(hand.attribute().name(), "constraintTargets:leftHand");
/// hand.set_at(gf::Mat4d::translation([0.0, 2.0, 0.0]), None)?;
///
/// // The frame is in the model's space, and the model places it.
/// let mut xforms = geom::XformCache::default();
/// let world = hand.in_world_space(&mut xforms)?;
/// assert_eq!(world, Some(gf::Mat4d::translation([10.0, 2.0, 0.0])));
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstraintTarget {
    attribute: usd::Attribute,
}

impl ConstraintTarget {
    /// The namespace a constraint target's attribute is in.
    pub const NAMESPACE: &str = "constraintTargets";

    /// The name of the attribute of the constraint target named
    /// `constraint`: `constraintTargets:<constraint>` (C++
    /// `GetConstraintAttrName`).
    pub fn attr_name(constraint: &str) -> tf::Token {
        tf::Token::from(format!("{}:{constraint}", Self::NAMESPACE))
    }

    /// `true` when `attribute` is a constraint target: its prim is a model,
    /// its name is in the `constraintTargets` namespace, and it is declared
    /// to hold a matrix (C++ `IsValid`). An attribute nothing declares is
    /// none.
    pub fn is_valid(attribute: &usd::Attribute) -> Result<bool> {
        Ok(Self::is_shaped(attribute)? && attribute.prim().is_model()?)
    }

    /// `true` when `attribute` has the name and the type of a constraint
    /// target, whatever its prim is.
    pub(super) fn is_shaped(attribute: &usd::Attribute) -> Result<bool> {
        if !Self::is_name(attribute.name()) {
            return Ok(false);
        }
        Ok(declared_type(attribute)?.is_some_and(|type_name| holds_matrix(&type_name)))
    }

    /// `true` when `name` is an attribute name a constraint target can
    /// have: one whose first namespace is `constraintTargets`, which the
    /// bare name `constraintTargets` is too.
    fn is_name(name: &str) -> bool {
        name.split(':').next() == Some(Self::NAMESPACE)
    }

    /// The constraint target `attribute` is, or `None` where it is
    /// [none](Self::is_valid).
    pub fn from_attribute(attribute: usd::Attribute) -> Result<Option<Self>> {
        Ok(Self::is_valid(&attribute)?.then_some(Self { attribute }))
    }

    /// The constraint target `attribute` is known to be.
    pub(super) fn new(attribute: usd::Attribute) -> Self {
        Self { attribute }
    }

    /// The attribute the target is (C++ `GetAttr`).
    pub fn attribute(&self) -> &usd::Attribute {
        &self.attribute
    }

    /// The attribute the target is, by value.
    pub fn into_attribute(self) -> usd::Attribute {
        self.attribute
    }

    /// The frame at `time`, where `None` is the default time, in the space
    /// of the model (C++ `Get`), or `None` where the attribute reads no
    /// value.
    pub fn get_at(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<Option<gf::Mat4d>> {
        self.attribute.get_at(time)
    }

    /// Author `frame`, in the space of the model, as the target's value at
    /// `time`, where `None` is the default time (C++ `Set`).
    pub fn set_at(
        &self,
        frame: gf::Mat4d,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<(), usd::StageAuthoringError> {
        self.attribute.clone().set_at(frame, time)?;
        Ok(())
    }

    /// The name the target is known by within its model, which need not be
    /// that of its attribute (C++ `GetIdentifier`): the
    /// `constraintTargetIdentifier` of the attribute, or `None` where none
    /// is authored.
    pub fn identifier(&self) -> Result<Option<tf::Token>> {
        self.attribute.constraint_target_identifier()
    }

    /// Author `identifier` as the name the target is known by within its
    /// model (C++ `SetIdentifier`).
    pub fn set_identifier(&self, identifier: impl Into<tf::Token>) -> Result<(), usd::StageAuthoringError> {
        self.attribute
            .clone()
            .set_constraint_target_identifier(identifier.into())?;
        Ok(())
    }

    /// The frame in world space at the time of `xforms`: its value in the
    /// model's space, then the model's local-to-world transform (C++
    /// `ComputeInWorldSpace`). `None` where the attribute reads no value,
    /// where C++ warns and answers the identity.
    ///
    /// The time is the one `xforms` answers at, where C++ takes a time and
    /// moves the cache it is handed to it.
    pub fn in_world_space(&self, xforms: &mut XformCache) -> Result<Option<gf::Mat4d>, SchemaError> {
        let Some(frame) = self.get_at(xforms.time())? else {
            return Ok(None);
        };
        Ok(Some(frame * xforms.local_to_world_transform(&self.attribute.prim())?))
    }
}

/// `true` when `type_name` is that of one matrix of four rows, under
/// whichever of the names that spell one.
pub(super) fn holds_matrix(type_name: &sdf::ValueTypeName) -> bool {
    type_name.kind() == Some(sdf::ValueKind::Matrix4d)
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, sdf, tf};

    use super::ConstraintTarget;
    use crate::SchemaError;
    use crate::geom::xformable::tests::assert_close;
    use crate::geom::{ModelAPI, Xform, XformCache, XformableExt};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// The model `/Hero` of a new stage, ten along X, with a prim beneath
    /// it that is no model.
    fn hero() -> Result<(usd::Stage, ModelAPI)> {
        let stage = crate::tests::stage("anon.usda")?;
        let xform = Xform::define(&stage, "/Hero")?.set_translate(gf::vec3d(10.0, 0.0, 0.0))?;
        let hero = xform.prim().clone().set_kind("component")?;
        Xform::define(&stage, "/Hero/Rig")?;
        Ok((stage, ModelAPI::from_prim_unchecked(hero)))
    }

    /// A target is created as a `matrix4d` attribute that is not custom, in
    /// the namespace, and reads back what is authored on it.
    #[test]
    fn create_and_read() -> Result {
        let (_stage, model) = hero()?;
        assert_eq!(model.constraint_target("hand")?, None);
        assert!(model.constraint_targets()?.is_empty());

        let hand = model.create_constraint_target("hand")?;
        let attr = hand.attribute();
        assert_eq!(attr.name(), "constraintTargets:hand");
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::MATRIX4D));
        assert!(!attr.is_custom()?);
        assert_eq!(hand.get_at(None)?, None);
        assert_eq!(hand.identifier()?, None);

        let frame = gf::Mat4d::translation([0.0, 2.0, 0.0]);
        hand.set_at(frame, None)?;
        hand.set_at(gf::Mat4d::translation([0.0, 4.0, 0.0]), usd::TimeCode::new(5.0))?;
        assert_eq!(hand.get_at(None)?, Some(frame));
        assert_eq!(
            hand.get_at(usd::TimeCode::new(5.0))?,
            Some(gf::Mat4d::translation([0.0, 4.0, 0.0]))
        );
        hand.set_identifier("left")?;
        assert_eq!(hand.identifier()?, Some(tf::Token::new("left")));

        // Asked for again, the target is the same attribute.
        assert_eq!(model.constraint_target("hand")?, Some(hand.clone()));
        assert_eq!(model.create_constraint_target("hand")?, hand);
        assert_eq!(hand.get_at(None)?, Some(frame));
        Ok(())
    }

    /// The targets of a model are listed in the order of its attributes,
    /// and only the matrix-valued ones in the namespace are among them.
    #[test]
    fn targets_listed() -> Result {
        let (_stage, model) = hero()?;
        let prim = model.prim();
        model.create_constraint_target("b")?;
        model.create_constraint_target("a:deep")?;
        prim.attribute_builder("constraintTargets:scalar", sdf::ValueTypeName::DOUBLE)
            .build()?;
        prim.attribute_builder("other:frame", sdf::ValueTypeName::MATRIX4D)
            .build()?;
        prim.attribute_builder("constraintTargets:framed", sdf::ValueTypeName::FRAME4D)
            .build()?;

        let names: Vec<_> = (model.constraint_targets()?.iter())
            .map(|target| target.attribute().name().to_string())
            .collect();
        assert_eq!(
            names,
            [
                "constraintTargets:a:deep",
                "constraintTargets:b",
                "constraintTargets:framed"
            ]
        );
        assert_eq!(model.constraint_target("scalar")?, None);
        assert!(!ConstraintTarget::is_valid(&prim.attribute("other:frame"))?);
        assert!(!ConstraintTarget::is_valid(
            &prim.attribute("constraintTargets:absent")
        )?);
        Ok(())
    }

    /// The targets follow the order a layer authors for the prim's
    /// properties, the attribute named for the namespace alone among them.
    #[test]
    fn targets_follow_property_order() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Hero" (kind = "component")
{
    reorder properties = ["constraintTargets:hand", "constraintTargets", "constraintTargets:foot"]
    matrix4d constraintTargets
    matrix4d constraintTargets:foot
    matrix4d constraintTargets:hand
}
"#,
        )?;
        let model = ModelAPI::from_prim_unchecked(stage.prim("/Hero")?);
        let names: Vec<_> = (model.constraint_targets()?.iter())
            .map(|target| target.attribute().name().to_string())
            .collect();
        assert_eq!(
            names,
            ["constraintTargets:hand", "constraintTargets", "constraintTargets:foot"]
        );
        let bare = stage.prim("/Hero")?.attribute("constraintTargets");
        assert!(ConstraintTarget::is_valid(&bare)?);
        Ok(())
    }

    /// Only a model has constraint targets: on any other prim none is
    /// created, and an attribute shaped like one is none.
    #[test]
    fn model_required() -> Result {
        let (stage, _model) = hero()?;
        let rig = stage.prim("/Hero/Rig")?;
        assert!(!rig.is_model()?);
        let api = ModelAPI::from_prim_unchecked(rig.clone());
        let refused = api.create_constraint_target("hand");
        assert!(
            matches!(&refused, Err(SchemaError::ConstraintTargetOffModel { prim }) if prim.as_str() == "/Hero/Rig"),
            "{refused:?}"
        );
        assert!(!rig.attribute("constraintTargets:hand").is_defined()?);

        let shaped = rig
            .attribute_builder("constraintTargets:hand", sdf::ValueTypeName::MATRIX4D)
            .build()?;
        assert_eq!(ConstraintTarget::from_attribute(shaped)?, None);
        assert!(api.constraint_targets()?.is_empty());
        assert_eq!(api.constraint_target("hand")?, None);
        Ok(())
    }

    /// A name a relationship already has is refused, and the relationship
    /// is left as it is.
    #[test]
    fn create_over_relationship() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Hero" (kind = "component")
{
    rel constraintTargets:hand = </Hero>
}
"#,
        )?;
        let model = ModelAPI::from_prim_unchecked(stage.prim("/Hero")?);
        let refused = model.create_constraint_target("hand");
        assert!(
            matches!(
                &refused,
                Err(SchemaError::ConstraintTargetType { attribute, type_name })
                    if attribute.as_str() == "/Hero.constraintTargets:hand" && type_name.is_empty()
            ),
            "{refused:?}"
        );
        let hero = stage.prim("/Hero")?;
        assert!(hero.relationship("constraintTargets:hand").is_defined()?);
        assert!(!hero.attribute("constraintTargets:hand").is_defined()?);
        assert!(model.constraint_targets()?.is_empty());
        Ok(())
    }

    /// A name already taken by an attribute that holds no matrix is
    /// refused, and the attribute is left as it is.
    #[test]
    fn create_over_other_type() -> Result {
        let (_stage, model) = hero()?;
        let prim = model.prim();
        prim.attribute_builder("constraintTargets:hand", sdf::ValueTypeName::DOUBLE)
            .build()?;
        let refused = model.create_constraint_target("hand");
        assert!(
            matches!(
                &refused,
                Err(SchemaError::ConstraintTargetType { type_name, .. }) if type_name.as_str() == "double"
            ),
            "{refused:?}"
        );
        let attr = prim.attribute("constraintTargets:hand");
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::DOUBLE));
        Ok(())
    }

    /// In world space a target is its frame under the model's transform at
    /// the cache's time, and none where it has no frame there.
    #[test]
    fn world_space() -> Result {
        let (stage, model) = hero()?;
        let hand = model.create_constraint_target("hand")?;
        let mut xforms = XformCache::default();
        assert_eq!(hand.in_world_space(&mut xforms)?, None);

        hand.set_at(gf::Mat4d::translation([0.0, 2.0, 0.0]), None)?;
        hand.set_at(gf::Mat4d::translation([0.0, 4.0, 0.0]), usd::TimeCode::new(5.0))?;
        assert_eq!(
            hand.in_world_space(&mut xforms)?,
            Some(gf::Mat4d::translation([10.0, 2.0, 0.0]))
        );

        stage
            .attribute("/Hero.xformOp:translate")?
            .set_at(gf::vec3d(20.0, 0.0, 0.0), usd::TimeCode::new(5.0))?;
        let mut xforms = XformCache::new(usd::TimeCode::new(5.0));
        assert_eq!(
            hand.in_world_space(&mut xforms)?,
            Some(gf::Mat4d::translation([20.0, 4.0, 0.0]))
        );

        // The frame comes first and the model's transform after it: a
        // frame one along X of a model turned a quarter about Z is one
        // along Y in the world.
        let turned = Xform::define(&stage, "/Turned")?.set_rotate_z(90.0)?;
        let turned = ModelAPI::from_prim_unchecked(turned.prim().clone().set_kind("component")?);
        let grip = turned.create_constraint_target("grip")?;
        let frame = gf::Mat4d::translation([1.0, 0.0, 0.0]);
        grip.set_at(frame, None)?;
        let world = grip.in_world_space(&mut XformCache::default())?.expect("a frame");
        assert_close(world, frame * gf::Mat4d::rotation_z(90f64.to_radians()));
        let origin = world.transform(gf::vec3d(0.0, 0.0, 0.0));
        assert!((origin - gf::vec3d(0.0, 1.0, 0.0)).length() < 1e-9, "{origin:?}");
        Ok(())
    }
}
