//! Integer coding.
//!
//! See <https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/integerCoding.cpp#L40>

use std::{collections::HashMap, io, mem};

use anyhow::{bail, Result};
use num_traits::{AsPrimitive, PrimInt};

use super::reader::ReadExt;

const COMMON: u8 = 0;
const SMALL: u8 = 1;
const MEDIUM: u8 = 2;
const LARGE: u8 = 3;

pub fn encoded_buffer_size<T: PrimInt>(count: usize) -> usize {
    if count == 0 {
        0
    } else {
        let sz = mem::size_of::<T>();
        sz + (count * 2).div_ceil(8) + (sz * count)
    }
}

pub fn decode_ints<T: PrimInt + 'static>(data: &[u8], count: usize) -> Result<Vec<T>>
where
    i64: AsPrimitive<T>,
{
    if count == 0 {
        return Ok(Vec::new());
    }

    let is_64_bit = mem::size_of::<T>() == 8;

    let mut codes_reader = io::Cursor::new(&data[0..]);

    let common_value = if is_64_bit {
        codes_reader.read_pod::<i64>()?
    } else {
        codes_reader.read_pod::<i32>()? as i64
    };

    let num_code_bytes = (count * 2).div_ceil(8);

    let mut ints_reader = {
        let offset = mem::size_of::<T>() + num_code_bytes;
        io::Cursor::new(&data[offset..])
    };

    let mut prev = 0_i64;
    let mut output = Vec::with_capacity(count);

    for _ in 0..num_code_bytes {
        // Code byte stores integer types for the next 4 integers.
        let code_byte = codes_reader.read_pod::<u8>()?;

        for i in 0..4 {
            let ty = (code_byte >> (2 * i)) & 3;
            let delta = match (ty, is_64_bit) {
                (COMMON, _) => common_value,
                (SMALL, true) => ints_reader.read_pod::<i16>()? as i64,
                (SMALL, false) => ints_reader.read_pod::<i8>()? as i64,
                (MEDIUM, true) => ints_reader.read_pod::<i32>()? as i64,
                (MEDIUM, false) => ints_reader.read_pod::<i16>()? as i64,
                (LARGE, true) => ints_reader.read_pod::<i64>()?,
                (LARGE, false) => ints_reader.read_pod::<i32>()? as i64,
                _ => bail!("Unexpected code: {ty}"),
            };

            prev += delta;
            output.push(prev.as_());
        }
    }

    output.truncate(count);
    Ok(output)
}

/// Encode a sequence of integers using the crate file delta/common-value
/// coding scheme. Inverse of [`decode_ints`].
///
/// Format:
/// 1. Common value (i32 for 32-bit T, i64 for 64-bit T)
/// 2. Code bytes: 2 bits per integer, packed 4 per byte, little-endian
/// 3. Payload: variable-width deltas (COMMON omits, SMALL/MEDIUM/LARGE vary by bit-width)
pub fn encode_ints<T>(values: &[T]) -> Vec<u8>
where
    T: PrimInt + 'static + AsPrimitive<i64>,
{
    let count = values.len();
    if count == 0 {
        return Vec::new();
    }

    let is_64_bit = mem::size_of::<T>() == 8;

    // Compute deltas.
    let mut deltas = Vec::with_capacity(count);
    let mut prev = 0_i64;
    for v in values {
        let cur: i64 = (*v).as_();
        deltas.push(cur.wrapping_sub(prev));
        prev = cur;
    }

    // Pick the most frequent delta as the common value.
    let common = most_common(&deltas);

    // Classify each delta.
    let codes: Vec<u8> = deltas
        .iter()
        .map(|&d| {
            if d == common {
                COMMON
            } else if is_64_bit {
                if fits_in_i16(d) {
                    SMALL
                } else if fits_in_i32(d) {
                    MEDIUM
                } else {
                    LARGE
                }
            } else if fits_in_i8(d) {
                SMALL
            } else if fits_in_i16(d) {
                MEDIUM
            } else {
                LARGE
            }
        })
        .collect();

    // Assemble output.
    let mut out = Vec::new();
    if is_64_bit {
        out.extend_from_slice(&common.to_le_bytes());
    } else {
        out.extend_from_slice(&(common as i32).to_le_bytes());
    }

    let num_code_bytes = (count * 2).div_ceil(8);
    let mut code_table = vec![0_u8; num_code_bytes];
    for (i, code) in codes.iter().enumerate() {
        let byte_idx = i / 4;
        let slot = i % 4;
        code_table[byte_idx] |= (code & 0b11) << (2 * slot);
    }
    out.extend_from_slice(&code_table);

    for (code, delta) in codes.iter().zip(deltas.iter()) {
        match (*code, is_64_bit) {
            (COMMON, _) => {}
            (SMALL, true) => out.extend_from_slice(&(*delta as i16).to_le_bytes()),
            (SMALL, false) => out.extend_from_slice(&(*delta as i8).to_le_bytes()),
            (MEDIUM, true) => out.extend_from_slice(&(*delta as i32).to_le_bytes()),
            (MEDIUM, false) => out.extend_from_slice(&(*delta as i16).to_le_bytes()),
            (LARGE, true) => out.extend_from_slice(&(*delta).to_le_bytes()),
            (LARGE, false) => out.extend_from_slice(&(*delta as i32).to_le_bytes()),
            _ => unreachable!(),
        }
    }

    out
}

fn most_common(deltas: &[i64]) -> i64 {
    let mut counts: HashMap<i64, usize> = HashMap::new();
    for &d in deltas {
        *counts.entry(d).or_insert(0) += 1;
    }
    counts.into_iter().max_by_key(|(_, c)| *c).map(|(v, _)| v).unwrap_or(0)
}

fn fits_in_i8(v: i64) -> bool {
    v >= i8::MIN as i64 && v <= i8::MAX as i64
}
fn fits_in_i16(v: i64) -> bool {
    v >= i16::MIN as i64 && v <= i16::MAX as i64
}
fn fits_in_i32(v: i64) -> bool {
    v >= i32::MIN as i64 && v <= i32::MAX as i64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_empty() {
        let out = encode_ints::<i32>(&[]);
        assert!(out.is_empty());
    }

    #[test]
    fn roundtrip_u32() {
        let values: &[u32] = &[123, 124, 125, 100125, 100125, 100126, 100126];
        let encoded = encode_ints(values);
        let decoded = decode_ints::<u32>(&encoded, values.len()).unwrap();
        assert_eq!(decoded, values);
    }

    #[test]
    fn roundtrip_i32_with_negative_deltas() {
        let values: &[i32] = &[10, 5, 3, 100, 99, 200, -50];
        let encoded = encode_ints(values);
        let decoded = decode_ints::<i32>(&encoded, values.len()).unwrap();
        assert_eq!(decoded, values);
    }

    #[test]
    fn roundtrip_u64_large_values() {
        let values: &[u64] = &[0, 1_000_000_000, 5_000_000_000, 9_000_000_000_000];
        let encoded = encode_ints(values);
        let decoded = decode_ints::<u64>(&encoded, values.len()).unwrap();
        assert_eq!(decoded, values);
    }

    #[test]
    fn roundtrip_i64_negative() {
        let values: &[i64] = &[-1_000_000, -999_999, 0, 1_000_000_000_000];
        let encoded = encode_ints(values);
        let decoded = decode_ints::<i64>(&encoded, values.len()).unwrap();
        assert_eq!(decoded, values);
    }

    #[test]
    fn roundtrip_fieldset_sentinel() {
        // Fieldsets store `None` terminators as `u32::MAX`. Verify that value
        // survives encode_ints/decode_ints round-trip unchanged, including
        // when it appears next to small indices that would otherwise push it
        // into a different integer-coding bucket.
        let values: &[u32] = &[0, 1, 2, u32::MAX, 3, 4, u32::MAX, u32::MAX];
        let encoded = encode_ints(values);
        let decoded = decode_ints::<u32>(&encoded, values.len()).unwrap();
        assert_eq!(decoded, values);
    }

    #[test]
    fn roundtrip_u32_common_delta_exceeds_i32_max() {
        // Deltas exceeding i32 range (here, ±3_000_000_000) still round-trip
        // for 32-bit T: the common slot is stored as i32 and LARGE payloads
        // are written with `as i32`, but the final `prev as T` cast reduces
        // mod 2^32, preserving the correct low bits end-to-end.
        let values: &[u32] = &[0, 3_000_000_000, 0, 3_000_000_000, 0, 3_000_000_000];
        let encoded = encode_ints(values);
        let decoded = decode_ints::<u32>(&encoded, values.len()).unwrap();
        assert_eq!(decoded, values);
    }

    #[test]
    fn test_decode() {
        /*
        See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/integerCoding.cpp#L85
        input  = [123, 124, 125, 100125, 100125, 100126, 100126]
        output = [int32(1) 01 00 00 11 01 00 01 XX int8(123) int32(100000) int8(0) int8(0)]
        */

        let mut output = Vec::new();
        output.extend_from_slice(&1_i32.to_le_bytes());
        debug_assert_eq!(output.len(), 4);

        // Little endian, swap bytes.
        let codes: u16 = 0b1100_0001_0001_0001;
        output.extend_from_slice(&codes.to_be_bytes());
        debug_assert_eq!(output.len(), 6);

        output.extend_from_slice(&123_i8.to_le_bytes());
        output.extend_from_slice(&100000_i32.to_le_bytes());
        output.extend_from_slice(&0_i16.to_le_bytes());

        let input = decode_ints::<u32>(&output, 7).expect("Failed to decode integers");

        assert_eq!(input.as_slice(), &[123_u32, 124, 125, 100125, 100125, 100126, 100126])
    }
}
