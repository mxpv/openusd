//! The metrics a stage states for all the geometry on it: which axis is up
//! and how long one unit is (C++ `usdGeom/metrics.h`).
//!
//! Both are stage metadata, which [`StageMetadata`](super::StageMetadata)
//! reads and authors as the tokens and numbers they are: `up_axis` and
//! `set_up_axis`, `meters_per_unit` and `set_meters_per_unit` (C++
//! `UsdGeomSetStageMetersPerUnit`), and [`stage_up_axis`] and
//! [`stage_meters_per_unit`] read them with the fallbacks in hand (C++
//! `UsdGeomGetStageUpAxis` and `UsdGeomGetStageMetersPerUnit`). The
//! registered fallbacks stand behind every read: `Y` up, and `0.01` meters, a
//! centimeter, to the unit. Whether a layer authors the unit (C++
//! `UsdGeomStageHasAuthoredMetersPerUnit`) is
//! [`usd::Stage::has_authored_stage_metadata`] of
//! [`tokens::METERS_PER_UNIT`].

use openusd::Result;
use openusd::{sdf, usd};

use super::{StageMetadata, tokens};

/// The axis a stage calls up. USD has no stage that is X up.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum UpAxis {
    /// `Y`, the fallback the `usdGeom` schema registers.
    #[default]
    Y,
    /// `Z`.
    Z,
}

impl UpAxis {
    /// The token the axis is authored as.
    pub fn as_token(self) -> &'static str {
        match self {
            UpAxis::Y => tokens::Y,
            UpAxis::Z => tokens::Z,
        }
    }

    /// The axis `token` names, or `None` for any other token.
    pub fn from_token(token: impl AsRef<str>) -> Option<Self> {
        Some(match token.as_ref() {
            tokens::Y => UpAxis::Y,
            tokens::Z => UpAxis::Z,
            _ => return None,
        })
    }
}

sdf::impl_token_value!(UpAxis);

/// The axis `stage` is up along (C++ `UsdGeomGetStageUpAxis`): the `upAxis`
/// its session or root layer authors, and the fallback the schema registry
/// holds for the field where neither does, which is what C++
/// `UsdGeomGetFallbackUpAxis` answers. A registry that declares no `upAxis`
/// leaves [`UpAxis::Y`].
///
/// An authored token that names neither `Y` nor `Z` is an error, where C++
/// returns the token.
pub fn stage_up_axis(stage: &usd::Stage) -> Result<UpAxis> {
    match stage.up_axis()? {
        Some(token) => Ok(UpAxis::try_from(sdf::Value::Token(token))?),
        None => Ok(UpAxis::default()),
    }
}

/// Author `axis` as the `upAxis` of `stage` (C++ `UsdGeomSetStageUpAxis`),
/// on the edit target, which must be the root or session layer. An
/// [`UpAxis`] is always an axis a stage can be up along, where
/// [`StageMetadata::set_up_axis`] takes any token.
pub fn set_stage_up_axis(stage: &usd::Stage, axis: UpAxis) -> Result<(), usd::StageAuthoringError> {
    stage.set_stage_metadata(tokens::UP_AXIS, axis)
}

/// The length of one unit of `stage` in meters (C++
/// `UsdGeomGetStageMetersPerUnit`): the `metersPerUnit` its session or root
/// layer authors, and the fallback the schema registry holds for the field
/// where neither does. A registry that declares no `metersPerUnit` leaves
/// [`linear_units::CENTIMETERS`].
pub fn stage_meters_per_unit(stage: &usd::Stage) -> Result<f64> {
    Ok(stage.meters_per_unit()?.unwrap_or(linear_units::CENTIMETERS))
}

/// Common units of length in meters (C++ `UsdGeomLinearUnits`), as
/// `metersPerUnit` states them.
pub mod linear_units {
    use openusd::sdf;

    /// One nanometer.
    pub const NANOMETERS: f64 = 1e-9;
    /// One micrometer.
    pub const MICROMETERS: f64 = 1e-6;
    /// One millimeter.
    pub const MILLIMETERS: f64 = sdf::Unit::Millimeter.scale();
    /// One centimeter, the unit of a stage that authors none.
    pub const CENTIMETERS: f64 = sdf::Unit::Centimeter.scale();
    /// One meter.
    pub const METERS: f64 = sdf::Unit::Meter.scale();
    /// One kilometer.
    pub const KILOMETERS: f64 = sdf::Unit::Kilometer.scale();
    /// One light year, for a year of 365.25 days.
    pub const LIGHT_YEARS: f64 = 9.460_730_472_580_8e15;
    /// One inch.
    pub const INCHES: f64 = sdf::Unit::Inch.scale();
    /// One foot.
    pub const FEET: f64 = sdf::Unit::Foot.scale();
    /// One yard.
    pub const YARDS: f64 = sdf::Unit::Yard.scale();
    /// One mile.
    pub const MILES: f64 = sdf::Unit::Mile.scale();

    /// The relative difference C++ `UsdGeomLinearUnitsAre` allows by
    /// default.
    pub const EPSILON: f64 = 1e-5;

    /// Whether `authored` units are the `standard` ones to within the
    /// relative `epsilon` (C++ `UsdGeomLinearUnitsAre`): their difference is
    /// under `epsilon` of each. Units that are not positive are no unit.
    ///
    /// ```
    /// use openusd_schemas::geom::linear_units;
    ///
    /// let authored = 0.010_000_000_1;
    /// assert!(linear_units::are(authored, linear_units::CENTIMETERS, linear_units::EPSILON));
    /// assert!(!linear_units::are(authored, linear_units::INCHES, linear_units::EPSILON));
    /// ```
    pub fn are(authored: f64, standard: f64, epsilon: f64) -> bool {
        if authored <= 0.0 || standard <= 0.0 {
            return false;
        }
        let difference = (authored - standard).abs();
        difference / authored < epsilon && difference / standard < epsilon
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use openusd::{sdf, usd};

    use super::{StageMetadata, UpAxis, linear_units, set_stage_up_axis, stage_meters_per_unit, stage_up_axis, tokens};
    use crate::SchemaError;

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// A stage that authors neither reads the fallbacks, and says it
    /// authors no unit.
    #[test]
    fn unauthored_fallbacks() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        assert_eq!(stage_up_axis(&stage)?, UpAxis::Y);
        assert_eq!(stage.meters_per_unit()?, Some(linear_units::CENTIMETERS));
        assert_eq!(stage_meters_per_unit(&stage)?, linear_units::CENTIMETERS);
        assert!(!stage.has_authored_stage_metadata(tokens::METERS_PER_UNIT)?);

        // A stage whose registry knows neither field still has Y up and a
        // centimeter to the unit.
        let bare = usd::Stage::builder().in_memory("bare.usda")?;
        assert_eq!(bare.up_axis()?, None);
        assert_eq!(stage_up_axis(&bare)?, UpAxis::Y);
        assert_eq!(bare.meters_per_unit()?, None);
        assert_eq!(stage_meters_per_unit(&bare)?, linear_units::CENTIMETERS);
        Ok(())
    }

    /// What is authored reads back, and a unit equal to the fallback still
    /// counts as authored.
    #[test]
    fn authored_metrics() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        set_stage_up_axis(&stage, UpAxis::Z)?;
        stage.set_meters_per_unit(linear_units::CENTIMETERS)?;
        assert_eq!(stage_up_axis(&stage)?, UpAxis::Z);
        assert_eq!(stage.meters_per_unit()?, Some(0.01));
        assert!(stage.has_authored_stage_metadata(tokens::METERS_PER_UNIT)?);

        stage.set_meters_per_unit(linear_units::FEET)?;
        assert_eq!(stage.meters_per_unit()?, Some(0.3048));
        assert_eq!(stage_meters_per_unit(&stage)?, linear_units::FEET);
        Ok(())
    }

    /// The generated setters author on the root or the session layer, whose
    /// opinion wins, and refuse any other edit target.
    #[test]
    fn setters_follow_edit_target() -> Result {
        let dir = tempfile::tempdir().expect("a directory");
        for name in ["root.usda", "session.usda"] {
            fs::write(
                dir.path().join(name),
                "#usda 1.0
",
            )
            .expect("writes");
        }
        let stage = usd::Stage::builder()
            .schema_registry(crate::schema_registry())
            .session_layer(dir.path().join("session.usda").to_string_lossy())
            .open(dir.path().join("root.usda").to_string_lossy().as_ref())?;
        let root = stage.root_layer().identifier().to_string();
        let sub = sdf::Layer::new_anonymous("sub.usda");
        let sub_id = sub.identifier().to_string();
        stage.insert_layer(&root, 0, sub, sdf::LayerOffset::IDENTITY)?;

        stage.set_meters_per_unit(linear_units::METERS)?;
        stage.set_up_axis("Z".into())?;
        assert_eq!(
            stage
                .root_layer()
                .pseudo_root()
                .and_then(|root| root.get::<f64>(tokens::METERS_PER_UNIT)),
            Some(1.0)
        );

        let session = stage.edit_target_session().expect("a session layer");
        stage.set_edit_target(session)?;
        stage.set_meters_per_unit(linear_units::FEET)?;
        assert_eq!(stage.meters_per_unit()?, Some(linear_units::FEET));
        assert_eq!(stage_up_axis(&stage)?, UpAxis::Z);

        stage.set_edit_target(usd::EditTarget::for_layer(sub_id.clone()))?;
        for refused in [
            stage.set_meters_per_unit(linear_units::MILES),
            stage.set_up_axis("Y".into()),
            set_stage_up_axis(&stage, UpAxis::Y),
        ] {
            assert!(matches!(
                refused,
                Err(usd::StageAuthoringError::StageMetadataTarget { layer }) if layer == sub_id
            ));
        }
        assert_eq!(stage.meters_per_unit()?, Some(linear_units::FEET));
        Ok(())
    }

    /// An axis no stage is up along is refused on the way out.
    #[test]
    fn up_axis_x_refused() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        stage.set_up_axis("X".into())?;
        assert!(stage_up_axis(&stage).is_err());
        Ok(())
    }

    /// Units compare by relative difference, either way round, and a unit
    /// that is not positive is no unit.
    #[test]
    fn linear_units_compare() {
        let are = |authored, standard| linear_units::are(authored, standard, linear_units::EPSILON);
        assert!(are(0.01, linear_units::CENTIMETERS));
        assert!(are(0.010_000_05, linear_units::CENTIMETERS));
        assert!(!are(0.010_001, linear_units::CENTIMETERS));
        assert!(!are(linear_units::INCHES, linear_units::CENTIMETERS));
        assert!(!are(0.0, linear_units::CENTIMETERS));
        assert!(!are(linear_units::METERS, -1.0));
        // A loose bound still needs the difference small against both.
        assert!(!linear_units::are(1.0, 2.0, 0.75));
        assert!(linear_units::are(1.0, 2.0, 1.5));
    }
}
