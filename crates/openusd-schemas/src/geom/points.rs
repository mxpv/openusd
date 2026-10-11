//! What `UsdGeomPointBased` and `UsdGeomPoints` answer beyond their own
//! properties: how many points a `Points` prim holds, how `normals` and
//! `widths` lie on the geometry, and where velocities carry the points.

use openusd::usd;
use openusd::{Result, gf};

use super::sampling::{Motion, per_element, positions_after, time_delta};
use super::{Interpolation, PointBased, PointBasedSchema, Points, PointsSchema, array_len, tokens};
use crate::SchemaError;

/// What every `UsdGeomPointBased` answers about its `normals`.
///
/// Every [`PointBasedSchema`] answers it, so a `Mesh` or a `BasisCurves` view
/// has these wherever the generated accessors are.
pub trait PointBasedExt: PointBasedSchema {
    /// How `normals` lie on the geometry (C++ `GetNormalsInterpolation`),
    /// [`Interpolation::Vertex`] where none is authored.
    ///
    /// An authored token that names no interpolation is an error.
    fn normals_interpolation(&self) -> Result<Interpolation> {
        interpolation(&self.normals_attr())
    }

    /// Author the `interpolation` of `normals` (C++
    /// `SetNormalsInterpolation`), declaring the attribute where no layer has
    /// yet.
    fn set_normals_interpolation(&self, interpolation: Interpolation) -> Result<()> {
        set_interpolation(self.normals_attr_builder(), interpolation)
    }

    /// Where the points are at `time`, carried there from `base_time` (C++
    /// `ComputePointsAtTime`); see
    /// [`compute_points_at_times`](Self::compute_points_at_times).
    fn compute_points_at_time(
        &self,
        time: usd::TimeCode,
        base_time: usd::TimeCode,
    ) -> Result<Vec<gf::Vec3f>, SchemaError> {
        let mut samples = self.compute_points_at_times(&[time], base_time)?;
        Ok(samples.pop().unwrap_or_default())
    }

    /// Where the points are at each of `times`, carried there from
    /// `base_time` (C++ `ComputePointsAtTimes`). This is what motion blur
    /// samples: `base_time` is the frame, and `times` are the shutter
    /// samples around it.
    ///
    /// The points are read at the sample at or before `base_time`. Where
    /// `velocities` has a sample at that same time, with the same samples
    /// around `base_time` and one velocity for each point, each point moves
    /// from there by its velocity over the seconds to the time asked for,
    /// and by half its `accelerations` over them where those are sampled
    /// alongside. Otherwise the points are the `points` attribute's own
    /// value at the time asked for, interpolated between its samples. A
    /// time where that value has another number of points than at
    /// `base_time` gets the points of the time before it.
    ///
    /// [`SchemaError::NoValue`] where `points` reads no value at
    /// `base_time`.
    fn compute_points_at_times(
        &self,
        times: &[usd::TimeCode],
        base_time: usd::TimeCode,
    ) -> Result<Vec<Vec<gf::Vec3f>>, SchemaError> {
        let motion = Motion::read(
            &self.points_attr(),
            &self.velocities_attr(),
            &self.accelerations_attr(),
            base_time,
        )?;
        let count = motion.positions.len();
        let time_codes_per_second = self.stage().time_codes_per_second();

        let mut samples = Vec::with_capacity(times.len());
        for &time in times {
            if motion.velocities.is_empty() {
                let points = match self.points_at(time)?.filter(|points| points.len() == count) {
                    Some(points) => points,
                    None => samples.last().unwrap_or(&motion.positions).clone(),
                };
                samples.push(points);
                continue;
            }
            let delta = time_delta(time, motion.velocities_time, time_codes_per_second);
            samples.push(positions_after(
                &motion.positions,
                &motion.velocities,
                &motion.accelerations,
                delta,
            ));
        }
        Ok(samples)
    }
}

impl<T: PointBasedSchema> PointBasedExt for T {}

impl PointBased {
    /// Where `positions` are at `time`, from arrays the caller read (C++
    /// the static `ComputePointsAtTime`): each moved by its velocity over
    /// the seconds from `velocities_sample_time`, in time codes, and by
    /// half its acceleration over them. `time_codes_per_second` is the
    /// stage's, which C++ reads off a stage argument.
    ///
    /// Velocities that are not one for each position move nothing, and
    /// accelerations that are not one for each velocity are left out, where
    /// C++ reads past the arrays.
    pub fn compute_points_from(
        time: usd::TimeCode,
        positions: &[gf::Vec3f],
        velocities: &[gf::Vec3f],
        velocities_sample_time: f64,
        accelerations: &[gf::Vec3f],
        time_codes_per_second: f64,
    ) -> Vec<gf::Vec3f> {
        let velocities = per_element(velocities, positions.len());
        let accelerations = per_element(accelerations, velocities.len());
        let delta = time_delta(time, velocities_sample_time, time_codes_per_second);
        positions_after(positions, velocities, accelerations, delta)
    }
}

impl Points {
    /// How many points the prim holds at `time`, where `None` is the default
    /// time (C++ `GetPointCount`): the length of `points`, and zero where it
    /// reads no value.
    pub fn point_count(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<usize> {
        Ok(array_len(self.points_at(time)?))
    }

    /// How `widths` lie on the points (C++ `GetWidthsInterpolation`),
    /// [`Interpolation::Vertex`] where none is authored.
    ///
    /// An authored token that names no interpolation is an error.
    pub fn widths_interpolation(&self) -> Result<Interpolation> {
        interpolation(&self.widths_attr())
    }

    /// Author the `interpolation` of `widths` (C++ `SetWidthsInterpolation`),
    /// declaring the attribute where no layer has yet.
    pub fn set_widths_interpolation(&self, interpolation: Interpolation) -> Result<()> {
        set_interpolation(self.widths_attr_builder(), interpolation)
    }
}

/// The `interpolation` authored on `attr`, or [`Interpolation::Vertex`], the
/// one `normals` and `widths` have where none is.
pub(super) fn interpolation(attr: &usd::Attribute) -> Result<Interpolation> {
    Ok(attr
        .get_metadata::<Interpolation>(tokens::INTERPOLATION)?
        .unwrap_or(Interpolation::Vertex))
}

/// Author `interpolation` on the attribute `builder` declares, as one edit
/// with the declaration.
pub(super) fn set_interpolation(builder: usd::AttributeBuilder<'_>, interpolation: Interpolation) -> Result<()> {
    builder.metadata(tokens::INTERPOLATION, interpolation).build()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, tf};

    use super::PointBasedExt;
    use crate::SchemaError;
    use crate::geom::{Interpolation, PointBased, PointBasedSchema, Points, PointsSchema, tokens};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// The point-count cases of C++ `testUsdGeomPoints`
    /// `test_ComputePointCount`.
    #[test]
    fn point_count() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let points = |n: usize| vec![gf::vec3f(1.0, 2.0, 3.0); n];
        let unset = Points::define(&stage, "/Unset")?;
        let blocked = Points::define(&stage, "/Blocked")?;
        blocked.create_points_attr()?.block()?;
        let empty = Points::define(&stage, "/Empty")?;
        empty.create_points_attr()?.set(points(0))?;
        let sampled = Points::define(&stage, "/Sampled")?;
        sampled
            .create_points_attr()?
            .set_at(points(3), usd::TimeCode::new(1.0))?;
        let both = Points::define(&stage, "/Both")?;
        both.create_points_attr()?
            .set(points(4))?
            .set_at(points(5), usd::TimeCode::new(1.0))?;

        for (schema, earliest, default) in [
            (&unset, 0, 0),
            (&blocked, 0, 0),
            (&empty, 0, 0),
            (&sampled, 3, 0),
            (&both, 5, 4),
        ] {
            assert_eq!(
                schema.point_count(usd::TimeCode::EARLIEST)?,
                earliest,
                "{}",
                schema.path()
            );
            assert_eq!(schema.point_count(None)?, default, "{}", schema.path());
        }
        Ok(())
    }

    /// Points sampled at times 0 and 10, one unit along x per time code.
    fn moving(stage: &usd::Stage, path: &str) -> Result<Points> {
        let points = Points::define(stage, path)?;
        points
            .create_points_attr()?
            .set_at(vec![gf::vec3f(0.0, 0.0, 0.0)], usd::TimeCode::new(0.0))?
            .set_at(vec![gf::vec3f(10.0, 0.0, 0.0)], usd::TimeCode::new(10.0))?;
        Ok(points)
    }

    fn at(points: &Points, time: f64, base_time: f64) -> Result<gf::Vec3f> {
        let computed = points.compute_points_at_time(usd::TimeCode::new(time), usd::TimeCode::new(base_time))?;
        assert_eq!(computed.len(), 1);
        Ok(computed[0])
    }

    fn assert_close(found: gf::Vec3f, expected: [f32; 3]) {
        let found: [f32; 3] = found.into();
        for (found, expected) in found.iter().zip(expected) {
            assert!((found - expected).abs() < 1e-4, "{found} is not {expected}");
        }
    }

    /// Without velocities the points are interpolated between their samples.
    #[test]
    fn points_interpolated() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let points = moving(&stage, "/Points")?;
        assert_close(at(&points, 5.0, 0.0)?, [5.0, 0.0, 0.0]);

        // Velocities with no sample of their own move nothing.
        points.create_velocities_attr()?.set(vec![gf::vec3f(48.0, 0.0, 0.0)])?;
        assert_close(at(&points, 5.0, 0.0)?, [5.0, 0.0, 0.0]);

        // Nor do velocities sampled at other times than the points.
        points
            .velocities_attr()
            .set_at(vec![gf::vec3f(48.0, 0.0, 0.0)], usd::TimeCode::new(0.0))?
            .set_at(vec![gf::vec3f(48.0, 0.0, 0.0)], usd::TimeCode::new(5.0))?;
        assert_close(at(&points, 5.0, 0.0)?, [5.0, 0.0, 0.0]);
        Ok(())
    }

    /// Velocities sampled with the points carry them from the base time's
    /// sample, at the stage's 24 time codes per second.
    #[test]
    fn points_by_velocity() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let points = moving(&stage, "/Points")?;
        points
            .create_velocities_attr()?
            .set_at(vec![gf::vec3f(48.0, 0.0, 0.0)], usd::TimeCode::new(0.0))?
            .set_at(vec![gf::vec3f(0.0, 24.0, 0.0)], usd::TimeCode::new(10.0))?;

        assert_close(at(&points, 5.0, 0.0)?, [10.0, 0.0, 0.0]);
        assert_close(at(&points, -1.0, 0.0)?, [-2.0, 0.0, 0.0]);
        // A base time between samples holds the sample before it.
        assert_close(at(&points, 5.0, 4.0)?, [10.0, 0.0, 0.0]);
        // The last sample carries on past the end.
        assert_close(at(&points, 12.0, 10.0)?, [10.0, 2.0, 0.0]);

        let times = [usd::TimeCode::new(0.0), usd::TimeCode::new(1.0)];
        let samples = points.compute_points_at_times(&times, usd::TimeCode::new(0.0))?;
        assert_eq!(samples.len(), 2);
        assert_close(samples[0][0], [0.0, 0.0, 0.0]);
        assert_close(samples[1][0], [2.0, 0.0, 0.0]);
        Ok(())
    }

    /// Accelerations sampled with the velocities add half their change over
    /// the time moved, and one array too short is left out.
    #[test]
    fn points_by_acceleration() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let points = moving(&stage, "/Points")?;
        for time in [0.0, 10.0] {
            points
                .velocities_attr_builder()
                .set_at(vec![gf::vec3f(48.0, 0.0, 0.0)], usd::TimeCode::new(time))
                .build()?;
            points
                .accelerations_attr_builder()
                .set_at(vec![gf::vec3f(0.0, 115.2, 0.0)], usd::TimeCode::new(time))
                .build()?;
        }
        // Five time codes are 5/24 s: y = 115.2 * (5/24)^2 / 2.
        assert_close(at(&points, 5.0, 0.0)?, [10.0, 2.5, 0.0]);

        points
            .accelerations_attr()
            .set_at(Vec::<gf::Vec3f>::new(), usd::TimeCode::new(0.0))?;
        assert_close(at(&points, 5.0, 0.0)?, [10.0, 0.0, 0.0]);
        Ok(())
    }

    /// Points with no value at the base time have nowhere to start from,
    /// and an empty array computes to an empty array for each time.
    #[test]
    fn points_missing_or_empty() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let points = Points::define(&stage, "/Points")?;
        let time = usd::TimeCode::new(1.0);
        assert!(matches!(
            points.compute_points_at_time(time, time),
            Err(SchemaError::NoValue { .. })
        ));

        points.create_points_attr()?.set(Vec::<gf::Vec3f>::new())?;
        assert_eq!(points.compute_points_at_times(&[time, time], time)?, [vec![], vec![]]);
        Ok(())
    }

    /// Arrays the caller read move as the attributes do, and velocities
    /// that are not one for each position move nothing.
    #[test]
    fn points_from_arrays() -> Result {
        let positions = [gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(1.0, 0.0, 0.0)];
        let velocities = [gf::vec3f(2.0, 0.0, 0.0); 2];
        let accelerations = [gf::vec3f(4.0, 0.0, 0.0); 2];
        let at = |velocities: &[gf::Vec3f], accelerations: &[gf::Vec3f]| {
            PointBased::compute_points_from(
                usd::TimeCode::new(12.0),
                &positions,
                velocities,
                0.0,
                accelerations,
                24.0,
            )
        };

        // Half a second at 24 time codes per second.
        assert_eq!(
            at(&velocities, &[]),
            [gf::vec3f(1.0, 0.0, 0.0), gf::vec3f(2.0, 0.0, 0.0)]
        );
        assert_eq!(
            at(&velocities, &accelerations),
            [gf::vec3f(1.5, 0.0, 0.0), gf::vec3f(2.5, 0.0, 0.0)]
        );
        assert_eq!(at(&velocities[..1], &accelerations), positions);
        assert_eq!(at(&velocities, &accelerations[..1]), at(&velocities, &[]));
        Ok(())
    }

    /// A `Points` prim's widths carry their own interpolation, and a token
    /// that names none is an error.
    #[test]
    fn points_widths_interpolation() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let points = Points::define(&stage, "/Points")?;
        assert_eq!(points.widths_interpolation()?, Interpolation::Vertex);
        assert_eq!(points.normals_interpolation()?, Interpolation::Vertex);

        points.set_widths_interpolation(Interpolation::Constant)?;
        assert_eq!(points.widths_interpolation()?, Interpolation::Constant);

        points
            .widths_attr()
            .set_metadata(tokens::INTERPOLATION, tf::Token::from("frobosity"))?;
        assert!(points.widths_interpolation().is_err());
        Ok(())
    }
}
