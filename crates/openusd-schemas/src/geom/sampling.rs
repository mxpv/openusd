//! The samples velocity-based motion is computed from: the positions held
//! at a base time, and the velocities and accelerations that move them (C++
//! `usdGeom/samplingUtils`).
//!
//! A value that moves under a velocity is not interpolated between its
//! samples. It is read at the sample at or before the base time and carried
//! forward from there, which only holds while the velocities come from that
//! same sample.

use openusd::usd;
use openusd::{Result, gf, sdf};

use crate::SchemaError;

/// A value read at the sample at or before a base time.
pub(super) struct Held<T> {
    /// The value: the one at [`sample_time`](Self::sample_time), or the
    /// default value of an attribute without samples.
    pub value: T,
    /// The time of the sample read, `None` for an attribute without samples.
    pub sample_time: Option<f64>,
    /// The samples around the base time, `None` for an attribute without
    /// samples. A base time that lies on a sample is bracketed a
    /// [safe step](usd::TimeCode::safe_step_default) later, so the pair is
    /// the span that sample opens.
    bracket: Option<(f64, f64)>,
}

impl<T> Held<T> {
    /// Read `attr` at the sample at or before `base_time`, or its default
    /// value where it has no samples (C++ `_GetAttrForTransforms`). `None`
    /// where that reads no value.
    pub(super) fn read(attr: &usd::Attribute, base_time: usd::TimeCode) -> Result<Option<Self>>
    where
        T: sdf::FromValue,
        T::Error: Into<openusd::Error>,
    {
        // TODO(perf): each bracketing below gathers the attribute's sample
        // times anew, and so does the read. Gathering them once and
        // bracketing that list twice would leave one walk of the sources.
        let bracket = attr.bracketing_time_samples(base_time)?;
        let sample_time = bracket.map(|(lower, _)| lower);
        let Some(value) = attr.get_at::<T>(sample_time.map(usd::TimeCode::new))? else {
            return Ok(None);
        };
        let bracket = match bracket {
            Some((lower, upper)) if same_time(lower, upper) => {
                let later = base_time.value() + usd::TimeCode::safe_step_default();
                attr.bracketing_time_samples(usd::TimeCode::new(later))?
            }
            other => other,
        };
        Ok(Some(Held {
            value,
            sample_time,
            bracket,
        }))
    }

    /// The same sample with its value converted by `f`.
    pub(super) fn map<U>(self, f: impl FnOnce(T) -> U) -> Held<U> {
        Held {
            value: f(self.value),
            sample_time: self.sample_time,
            bracket: self.bracket,
        }
    }
}

impl<T> Held<Vec<T>> {
    /// Read the array `attr` holds for the same sample as `lead`, `len`
    /// elements long (C++ `_CheckSampleAlignment`).
    ///
    /// `None` unless both attributes have samples, the base time has the
    /// same samples around it in both, both were read at the same one, and
    /// the array is `len` long. A rate of change sampled at another time
    /// than the value it moves says nothing about that value.
    pub(super) fn aligned<U>(
        attr: &usd::Attribute,
        base_time: usd::TimeCode,
        lead: &Held<U>,
        len: usize,
    ) -> Result<Option<Self>>
    where
        Vec<T>: sdf::FromValue,
        <Vec<T> as TryFrom<sdf::Value>>::Error: Into<openusd::Error>,
    {
        let (Some(lead_time), Some(lead_bracket)) = (lead.sample_time, lead.bracket) else {
            return Ok(None);
        };
        let Some(held) = Self::read(attr, base_time)? else {
            return Ok(None);
        };
        let aligned = held.value.len() == len
            && held.sample_time.is_some_and(|time| same_time(time, lead_time))
            && held
                .bracket
                .is_some_and(|(lower, upper)| same_time(lower, lead_bracket.0) && same_time(upper, lead_bracket.1));
        Ok(aligned.then_some(held))
    }
}

/// Positions and what moves them from the time they were sampled at.
pub(super) struct Motion {
    /// The positions at the sample at or before the base time.
    pub positions: Vec<gf::Vec3f>,
    /// One velocity for each position, or none where the positions do not
    /// move by velocity.
    pub velocities: Vec<gf::Vec3f>,
    /// The time the velocities were sampled at, which the positions move
    /// from. Zero without velocities.
    pub velocities_time: f64,
    /// One acceleration for each velocity, or none.
    pub accelerations: Vec<gf::Vec3f>,
}

impl Motion {
    /// Read positions and the velocities and accelerations aligned with
    /// them at `base_time` (C++
    /// `UsdGeom_GetPositionsVelocitiesAndAccelerations`).
    /// [`SchemaError::NoValue`] where the positions read no value.
    ///
    /// Velocities are kept only when they are [aligned](Held::aligned) with
    /// the positions, and accelerations only when aligned with velocities
    /// that were kept.
    pub(super) fn read(
        positions: &usd::Attribute,
        velocities: &usd::Attribute,
        accelerations: &usd::Attribute,
        base_time: usd::TimeCode,
    ) -> Result<Self, SchemaError> {
        let Some(positions) = Held::<Vec<gf::Vec3f>>::read(positions, base_time)? else {
            return Err(SchemaError::NoValue {
                attribute: positions.path().clone(),
            });
        };
        let len = positions.value.len();
        let velocities = Held::<Vec<gf::Vec3f>>::aligned(velocities, base_time, &positions, len)?;
        let accelerations = match &velocities {
            Some(velocities) => Held::<Vec<gf::Vec3f>>::aligned(accelerations, base_time, velocities, len)?,
            None => None,
        };
        Ok(Motion {
            positions: positions.value,
            velocities_time: velocities
                .as_ref()
                .and_then(|velocities| velocities.sample_time)
                .unwrap_or_default(),
            velocities: velocities.map(|held| held.value).unwrap_or_default(),
            accelerations: accelerations.map(|held| held.value).unwrap_or_default(),
        })
    }
}

/// `values` where they are one for each of `count` elements, and none
/// otherwise: an array of another length says nothing about the elements.
pub(super) fn per_element<T>(values: &[T], count: usize) -> &[T] {
    match values.len() == count {
        true => values,
        false => &[],
    }
}

/// Where each of `positions` is `delta` seconds on, as [`position_after`]
/// moves one. `velocities` hold one element for each position or none, and
/// `accelerations` one for each velocity or none.
pub(super) fn positions_after(
    positions: &[gf::Vec3f],
    velocities: &[gf::Vec3f],
    accelerations: &[gf::Vec3f],
    delta: f64,
) -> Vec<gf::Vec3f> {
    if velocities.is_empty() {
        return positions.to_vec();
    }
    // TODO(rayon): each point is computed from its own position, velocity
    // and acceleration, so the points are independent.
    positions
        .iter()
        .zip(velocities)
        .enumerate()
        .map(|(index, (&position, &velocity))| {
            position_after(position, Some(velocity), accelerations.get(index).copied(), delta)
        })
        .collect()
}

/// Where `position` is `delta` seconds on: moved by its `velocity`, and by
/// half its `acceleration` over that time. A position without a velocity
/// stays.
pub(super) fn position_after(
    position: gf::Vec3f,
    velocity: Option<gf::Vec3f>,
    acceleration: Option<gf::Vec3f>,
    delta: f64,
) -> gf::Vec3f {
    let Some(velocity) = velocity else {
        return position;
    };
    let velocity = match acceleration {
        Some(acceleration) => velocity + scaled(scaled(acceleration, delta), 0.5),
        None => velocity,
    };
    position + scaled(velocity, delta)
}

/// The seconds from `sample_time` to `time`, both in time codes (C++
/// `UsdGeom_CalculateTimeDelta`).
pub(super) fn time_delta(time: usd::TimeCode, sample_time: f64, time_codes_per_second: f64) -> f64 {
    (time.value() - sample_time) / time_codes_per_second
}

/// `v` times `factor`, each product taken in double precision.
fn scaled(v: gf::Vec3f, factor: f64) -> gf::Vec3f {
    gf::vec3f(
        (f64::from(v.x) * factor) as f32,
        (f64::from(v.y) * factor) as f32,
        (f64::from(v.z) * factor) as f32,
    )
}

/// Whether two sample times are the same one, to the precision C++ compares
/// them with.
fn same_time(a: f64, b: f64) -> bool {
    (a - b).abs() < f64::EPSILON
}
