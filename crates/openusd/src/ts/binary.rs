//! The bytes a `usdc` layer stores a [`Spline`] as (C++
//! `Ts_BinaryDataAccess`, `pxr/base/ts/binary.cpp`).
//!
//! Every number is little-endian. Two header bytes hold the format version,
//! the value type, the curve type and the extrapolation modes, and say which
//! of the optional parts follow: the slope of a sloped extrapolation, and the
//! loop parameters. The knots come last, each with its value, pre-value and
//! slopes at the width of the spline's value type. Knot custom data is not
//! part of the encoding; a crate file stores it beside it.

use super::{
    CurveType, Error, Extrapolation, InterpMode, Knot, LoopParams, Spline, Tangent, TangentAlgorithm, ValueType,
};
use crate::gf::f16;

/// The first encoding version.
const VERSION_INITIAL: u8 = 1;
/// The version that added a tangent algorithm to each knot's tangents.
const VERSION_TANGENT_ALGORITHMS: u8 = 2;

impl Spline {
    /// The version of the binary encoding the spline needs: 1, or 2 where a
    /// tangent has an algorithm (C++
    /// `Ts_BinaryDataAccess::GetBinaryFormatVersion`).
    pub fn binary_version(&self) -> u8 {
        match self.has_tangent_algorithms() {
            true => VERSION_TANGENT_ALGORITHMS,
            false => VERSION_INITIAL,
        }
    }

    /// The spline's binary encoding, without its knots' custom data (C++
    /// `Ts_BinaryDataAccess::GetBinaryData`).
    ///
    /// A Hermite spline's tangent widths are not stored: they follow from its
    /// knot times.
    pub fn to_binary(&self) -> Vec<u8> {
        let data = self.data();
        let version = self.binary_version();
        let hermite = data.curve_type == CurveType::Hermite;
        let has_loops = data.loop_params != LoopParams::default();
        let type_descriptor: u8 = match data.value_type {
            ValueType::Double => 1,
            ValueType::Float => 2,
            ValueType::Half => 3,
        };

        // Two header bytes, two slopes, the loop parameters, the knot count,
        // and at most 51 bytes a knot.
        let mut out = Vec::with_capacity(50 + data.knots.len() * 51);
        // Bits 0-3: version. Bits 4-5: value type. Bit 6: whether
        // time-valued. Bit 7: curve type.
        out.push(version | type_descriptor << 4 | u8::from(data.time_valued) << 6 | (data.curve_type as u8) << 7);
        // Bits 0-2: pre-extrapolation mode. Bits 3-5: post-extrapolation
        // mode. Bit 6: whether loop parameters follow.
        out.push(
            extrapolation_mode(data.pre_extrapolation)
                | extrapolation_mode(data.post_extrapolation) << 3
                | u8::from(has_loops) << 6,
        );
        for extrapolation in [data.pre_extrapolation, data.post_extrapolation] {
            if let Extrapolation::Sloped(slope) = extrapolation {
                out.extend(slope.to_le_bytes());
            }
        }
        if has_loops {
            let params = &data.loop_params;
            out.extend(params.proto_start.to_le_bytes());
            out.extend(params.proto_end.to_le_bytes());
            out.extend(params.num_pre_loops.to_le_bytes());
            out.extend(params.num_post_loops.to_le_bytes());
            out.extend(params.value_offset.to_le_bytes());
        }

        // A spline never holds more knots than a layer could have given it.
        #[allow(clippy::cast_possible_truncation)]
        out.extend((data.knots.len() as u32).to_le_bytes());
        for knot in &data.knots {
            // Bit 0: whether dual-valued. Bits 1-2: the next segment's
            // interpolation. Bit 3: a per-knot curve type C++ deprecated,
            // always Bezier.
            out.push(u8::from(knot.is_dual_valued()) | (knot.next_interp as u8) << 1);
            out.extend(knot.time.to_le_bytes());
            write_value(&mut out, data.value_type, knot.value);
            if let Some(pre_value) = knot.pre_value {
                write_value(&mut out, data.value_type, pre_value);
            }
            if !hermite {
                out.extend(knot.pre_tangent.width.to_le_bytes());
                out.extend(knot.post_tangent.width.to_le_bytes());
            }
            write_value(&mut out, data.value_type, knot.pre_tangent.slope);
            write_value(&mut out, data.value_type, knot.post_tangent.slope);
            if version >= VERSION_TANGENT_ALGORITHMS {
                out.push(knot.pre_tangent.algorithm as u8 | (knot.post_tangent.algorithm as u8) << 4);
            }
        }
        out
    }

    /// The spline `bytes` encode (C++
    /// `Ts_BinaryDataAccess::CreateSplineFromBinaryData`). No bytes at all
    /// encode an empty spline of doubles.
    ///
    /// The tangents an algorithm owns are recomputed and regressive Bezier
    /// tangents shortened, as [`set_knots`](Self::set_knots) does and as C++
    /// does on this read (`TsSpline::_UpdateAllTangents`). Knots must come in
    /// time order, one to a time.
    pub fn from_binary(bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut reader = Reader { bytes };
        if bytes.is_empty() {
            return Ok(Self::default());
        }

        let header = reader.u8()?;
        let version = header & 0x0F;
        if !(VERSION_INITIAL..=VERSION_TANGENT_ALGORITHMS).contains(&version) {
            return Err(DecodeError::Version(version));
        }
        let descriptor = (header & 0x30) >> 4;
        let typed = descriptor != 0;
        let value_type = match descriptor {
            2 => ValueType::Float,
            3 => ValueType::Half,
            // A spline with no value type yet is one of doubles.
            _ => ValueType::Double,
        };
        // One bit, each of whose values names a curve type.
        let curve_type = CurveType::from_repr(header >> 7).unwrap_or_default();
        let hermite = curve_type == CurveType::Hermite;

        let modes = reader.u8()?;
        let has_loops = modes & 0x40 != 0;
        let pre_extrapolation = reader.extrapolation(modes & 0x07)?;
        let post_extrapolation = reader.extrapolation((modes & 0x38) >> 3)?;
        let loop_params = match has_loops {
            true => LoopParams {
                proto_start: reader.f64()?,
                proto_end: reader.f64()?,
                num_pre_loops: i32::from_le_bytes(reader.array()?),
                num_post_loops: i32::from_le_bytes(reader.array()?),
                value_offset: reader.f64()?,
            },
            false => LoopParams::default(),
        };

        // A spline with no value type yet has no knots, and C++ writes it
        // with no knot count.
        let count = match typed || !reader.bytes.is_empty() {
            true => u32::from_le_bytes(reader.array()?),
            false => 0,
        };
        let mut knots: Vec<Knot> = Vec::new();
        for _ in 0..count {
            let flags = reader.u8()?;
            let time = reader.f64()?;
            let value = reader.value(value_type)?;
            let pre_value = match flags & 0x01 {
                0 => None,
                _ => Some(reader.value(value_type)?),
            };
            let (pre_width, post_width) = match hermite {
                true => (0.0, 0.0),
                false => (reader.f64()?, reader.f64()?),
            };
            let pre_slope = reader.value(value_type)?;
            let post_slope = reader.value(value_type)?;
            let algorithms = match version >= VERSION_TANGENT_ALGORITHMS {
                true => reader.u8()?,
                false => 0,
            };
            if knots.last().is_some_and(|last| last.time >= time) {
                return Err(DecodeError::KnotOrder(time));
            }
            knots.push(Knot {
                time,
                value,
                pre_value,
                pre_tangent: Tangent {
                    width: pre_width,
                    slope: pre_slope,
                    algorithm: tangent_algorithm(algorithms & 0x0F)?,
                },
                post_tangent: Tangent {
                    width: post_width,
                    slope: post_slope,
                    algorithm: tangent_algorithm(algorithms >> 4)?,
                },
                // Two bits, each of whose values names a mode.
                next_interp: InterpMode::from_repr((flags & 0x06) >> 1).unwrap_or_default(),
                custom_data: Default::default(),
            });
        }
        if !reader.bytes.is_empty() {
            return Err(DecodeError::TrailingBytes(reader.bytes.len()));
        }

        let mut spline = Self::new(value_type);
        spline.set_time_valued(header & 0x40 != 0);
        spline.set_curve_type(curve_type);
        spline.set_pre_extrapolation(pre_extrapolation);
        spline.set_post_extrapolation(post_extrapolation);
        spline.set_loop_params(loop_params);
        // C++ takes a knot as it is stored. What a spline cannot hold of one
        // is reset, as a text layer's is.
        spline.set_knots(knots.into_iter().map(|knot| value_type.sanitize(knot)))?;
        Ok(spline)
    }
}

/// Why bytes do not decode as a [`Spline`].
#[derive(Debug, Clone, Copy, PartialEq, thiserror::Error)]
pub enum DecodeError {
    /// The bytes end inside the encoding.
    #[error("spline data ends early")]
    Truncated,
    /// The encoding is of a version this crate does not read.
    #[error("spline data is of unknown version {0}")]
    Version(u8),
    /// A byte names no extrapolation mode.
    #[error("spline data holds unknown extrapolation mode {0}")]
    ExtrapolationMode(u8),
    /// A byte names no tangent algorithm.
    #[error("spline data holds unknown tangent algorithm {0}")]
    TangentAlgorithm(u8),
    /// A knot is not later than the one before it.
    #[error("spline data holds the knot at time {0} out of time order")]
    KnotOrder(f64),
    /// Bytes follow the last knot.
    #[error("spline data holds {0} bytes past its last knot")]
    TrailingBytes(usize),
    /// A knot is one a spline cannot hold.
    #[error(transparent)]
    Knot(#[from] Error),
}

/// The three bits an extrapolation mode is stored as (C++ `TsExtrapMode`).
fn extrapolation_mode(extrapolation: Extrapolation) -> u8 {
    match extrapolation {
        Extrapolation::ValueBlock => 0,
        Extrapolation::Held => 1,
        Extrapolation::Linear => 2,
        Extrapolation::Sloped(_) => 3,
        Extrapolation::LoopRepeat => 4,
        Extrapolation::LoopReset => 5,
        Extrapolation::LoopOscillate => 6,
    }
}

fn tangent_algorithm(bits: u8) -> Result<TangentAlgorithm, DecodeError> {
    TangentAlgorithm::from_repr(bits).ok_or(DecodeError::TangentAlgorithm(bits))
}

/// Appends `value` at the width of `value_type`.
fn write_value(out: &mut Vec<u8>, value_type: ValueType, value: f64) {
    match value_type {
        ValueType::Double => out.extend(value.to_le_bytes()),
        // A spline's values are already at its precision.
        #[allow(clippy::cast_possible_truncation)]
        ValueType::Float => out.extend((value as f32).to_le_bytes()),
        ValueType::Half => out.extend(f16::from_f64(value).to_le_bytes()),
    }
}

/// The bytes of an encoding not yet read.
struct Reader<'a> {
    bytes: &'a [u8],
}

impl Reader<'_> {
    fn array<const N: usize>(&mut self) -> Result<[u8; N], DecodeError> {
        let (head, rest) = self.bytes.split_first_chunk::<N>().ok_or(DecodeError::Truncated)?;
        self.bytes = rest;
        Ok(*head)
    }

    fn u8(&mut self) -> Result<u8, DecodeError> {
        Ok(self.array::<1>()?[0])
    }

    fn f64(&mut self) -> Result<f64, DecodeError> {
        Ok(f64::from_le_bytes(self.array()?))
    }

    /// A value stored at the width of `value_type`.
    fn value(&mut self, value_type: ValueType) -> Result<f64, DecodeError> {
        Ok(match value_type {
            ValueType::Double => self.f64()?,
            ValueType::Float => f64::from(f32::from_le_bytes(self.array()?)),
            ValueType::Half => f16::from_le_bytes(self.array()?).to_f64(),
        })
    }

    /// The extrapolation `mode` names, reading the slope of a sloped one.
    fn extrapolation(&mut self, mode: u8) -> Result<Extrapolation, DecodeError> {
        Ok(match mode {
            0 => Extrapolation::ValueBlock,
            1 => Extrapolation::Held,
            2 => Extrapolation::Linear,
            3 => Extrapolation::Sloped(self.f64()?),
            4 => Extrapolation::LoopRepeat,
            5 => Extrapolation::LoopReset,
            6 => Extrapolation::LoopOscillate,
            mode => return Err(DecodeError::ExtrapolationMode(mode)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(value_type: ValueType) -> Spline {
        let mut spline = Spline::new(value_type);
        spline.set_pre_extrapolation(Extrapolation::Sloped(0.25));
        spline.set_post_extrapolation(Extrapolation::LoopOscillate);
        spline.set_loop_params(LoopParams {
            proto_start: 1.0,
            proto_end: 4.0,
            num_pre_loops: 1,
            num_post_loops: 2,
            value_offset: 0.5,
        });
        let knots = [
            Knot {
                pre_value: Some(0.5),
                post_tangent: Tangent::new(1.0, 0.25),
                next_interp: InterpMode::Curve,
                ..Knot::new(1.0, 2.0)
            },
            Knot {
                pre_tangent: Tangent::new(0.5, -1.0),
                next_interp: InterpMode::ValueBlock,
                ..Knot::new(4.0, 3.0)
            },
        ];
        spline.set_knots(knots).expect("valid knots");
        spline
    }

    /// Every part of a spline survives its encoding, at each value type.
    #[test]
    fn round_trip() -> Result<(), DecodeError> {
        for value_type in [ValueType::Double, ValueType::Float, ValueType::Half] {
            let spline = sample(value_type);
            assert_eq!(spline.binary_version(), 1);
            assert_eq!(Spline::from_binary(&spline.to_binary())?, spline, "{value_type}");
        }

        let mut timed = sample(ValueType::Double);
        timed.set_time_valued(true);
        timed.set_curve_type(CurveType::Hermite);
        assert_eq!(Spline::from_binary(&timed.to_binary())?, timed);
        assert_eq!(Spline::from_binary(&[])?, Spline::default());
        // A spline with no value type: a header and no knot count.
        let untyped = Spline::from_binary(&[0x01, 0x02 | 0x01 << 3])?;
        assert!(untyped.is_empty());
        assert_eq!(untyped.pre_extrapolation(), Extrapolation::Linear);
        Ok(())
    }

    /// A tangent algorithm needs the second version, which stores one byte
    /// more per knot.
    #[test]
    fn algorithm_version() -> Result<(), DecodeError> {
        let mut spline = Spline::new(ValueType::Float);
        let auto = Tangent {
            algorithm: TangentAlgorithm::AutoEase,
            ..Tangent::default()
        };
        let knot = |time: f64, value: f64| Knot {
            pre_tangent: auto,
            post_tangent: Tangent {
                algorithm: TangentAlgorithm::Custom,
                ..auto
            },
            next_interp: InterpMode::Curve,
            ..Knot::new(time, value)
        };
        spline.set_knots([knot(0.0, 0.0), knot(3.0, 3.0)])?;
        assert_eq!(spline.binary_version(), 2);
        let bytes = spline.to_binary();
        assert_eq!(bytes[0] & 0x0F, 2);
        assert_eq!(Spline::from_binary(&bytes)?, spline);
        Ok(())
    }

    /// The layout of a small spline, byte for byte.
    #[test]
    fn layout() {
        let mut spline = Spline::new(ValueType::Half);
        spline.set_post_extrapolation(Extrapolation::Sloped(2.0));
        spline
            .set_knots([Knot {
                next_interp: InterpMode::Linear,
                ..Knot::new(1.0, 2.0)
            }])
            .expect("a valid knot");

        let mut expected = vec![
            // Version 1, half, Bezier; held before, sloped after.
            0x31,
            0x01 | 0x03 << 3,
        ];
        expected.extend(2.0_f64.to_le_bytes());
        expected.extend(1_u32.to_le_bytes());
        expected.push(0x02 << 1);
        expected.extend(1.0_f64.to_le_bytes());
        expected.extend(f16::from_f64(2.0).to_le_bytes());
        expected.extend([0; 16]);
        expected.extend([0; 4]);
        assert_eq!(spline.to_binary(), expected);
    }

    /// Bytes that are not a spline are refused.
    #[test]
    fn bad_bytes() {
        let bytes = sample(ValueType::Double).to_binary();
        assert_eq!(
            Spline::from_binary(&bytes[..bytes.len() - 1]),
            Err(DecodeError::Truncated)
        );
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_eq!(Spline::from_binary(&trailing), Err(DecodeError::TrailingBytes(1)));
        assert_eq!(
            Spline::from_binary(&[0x11, 0x07]),
            Err(DecodeError::ExtrapolationMode(7))
        );
        assert_eq!(Spline::from_binary(&[0x1F]), Err(DecodeError::Version(15)));

        // Two knots at one time.
        let mut spline = Spline::new(ValueType::Half);
        spline
            .set_knots([Knot::new(1.0, 0.0), Knot::new(2.0, 0.0)])
            .expect("valid knots");
        let mut bytes = spline.to_binary();
        let second_time = bytes.len() - 30;
        bytes[second_time..second_time + 8].copy_from_slice(&1.0_f64.to_le_bytes());
        assert_eq!(Spline::from_binary(&bytes), Err(DecodeError::KnotOrder(1.0)));
    }
}
