//! Common units of mass in kilograms (C++ `UsdPhysicsMassUnits`), as a
//! stage's `kilogramsPerUnit` states them.
//!
//! The unit is stage metadata, which [`StageMetadata`](super::StageMetadata)
//! reads and authors as the number it is: `kilograms_per_unit` and
//! `set_kilograms_per_unit` (C++ `UsdPhysicsGetStageKilogramsPerUnit` and
//! `UsdPhysicsSetStageKilogramsPerUnit`). The registered fallback stands
//! behind the read: `1.0`, a kilogram, to the unit. Whether a layer authors
//! the unit (C++ `UsdPhysicsStageHasAuthoredKilogramsPerUnit`) is
//! [`openusd::usd::Stage::has_authored_stage_metadata`] of
//! [`tokens::KILOGRAMS_PER_UNIT`](super::tokens::KILOGRAMS_PER_UNIT).

/// One gram.
pub const GRAMS: f64 = 0.001;
/// One kilogram, the unit of a stage that authors none.
pub const KILOGRAMS: f64 = 1.0;
/// One slug.
pub const SLUGS: f64 = 14.5939;

/// The relative difference C++ `UsdPhysicsMassUnitsAre` allows by default.
pub const EPSILON: f64 = 1e-5;

/// Whether `authored` units are the `standard` ones to within the relative
/// `epsilon` (C++ `UsdPhysicsMassUnitsAre`): their difference is under
/// `epsilon` of each. Units that are not positive are no unit.
///
/// ```
/// use openusd_schemas::physics::mass_units;
///
/// let authored = 0.001_000_001;
/// assert!(mass_units::are(authored, mass_units::GRAMS, mass_units::EPSILON));
/// assert!(!mass_units::are(authored, mass_units::KILOGRAMS, mass_units::EPSILON));
/// ```
pub fn are(authored: f64, standard: f64, epsilon: f64) -> bool {
    if authored <= 0.0 || standard <= 0.0 {
        return false;
    }
    let difference = (authored - standard).abs();
    difference / authored < epsilon && difference / standard < epsilon
}

#[cfg(test)]
mod tests {
    use super::{EPSILON, GRAMS, KILOGRAMS, SLUGS, are};
    use crate::SchemaError;
    use crate::physics::{StageMetadata, tokens};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// A stage that authors no unit weighs a kilogram to the unit and says it
    /// authors none; an authored unit reads back and counts as authored (C++
    /// `test_kilogramsPerUnit`).
    #[test]
    fn kilograms_per_unit() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        assert_eq!(stage.kilograms_per_unit()?, Some(KILOGRAMS));
        assert!(!stage.has_authored_stage_metadata(tokens::KILOGRAMS_PER_UNIT)?);

        stage.set_kilograms_per_unit(GRAMS)?;
        assert!(stage.has_authored_stage_metadata(tokens::KILOGRAMS_PER_UNIT)?);
        let authored = stage.kilograms_per_unit()?.expect("an authored unit");
        assert!(are(authored, GRAMS, EPSILON));
        assert!(!are(authored, KILOGRAMS, EPSILON));
        Ok(())
    }

    /// Units compare by relative difference, either way round, and a unit
    /// that is not positive is no unit.
    #[test]
    fn mass_units_compare() {
        let near = |authored, standard| are(authored, standard, EPSILON);
        assert!(near(1.0, KILOGRAMS));
        assert!(near(1.000_005, KILOGRAMS));
        assert!(!near(1.000_1, KILOGRAMS));
        assert!(near(14.5939, SLUGS));
        assert!(!near(GRAMS, KILOGRAMS));
        assert!(!near(SLUGS, KILOGRAMS));
        assert!(!near(0.0, KILOGRAMS));
        assert!(!near(KILOGRAMS, -1.0));
        // A loose bound still needs the difference small against both.
        assert!(!are(1.0, 2.0, 0.75));
        assert!(are(1.0, 2.0, 1.5));
    }
}
