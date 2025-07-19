//! Integer coding.
//!
//! See <https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/integerCoding.cpp#L40>

use std::{io, mem};

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
    let mut ints_left = count as isize;
    let mut output = Vec::new();

    while ints_left > 0 {
        let n = ints_left.min(4);
        ints_left -= 4;

        // Code byte stores integer types for the next 4 integers.
        let code_byte = codes_reader.read_pod::<u8>()?;

        for i in 0..n {
            let ty = (code_byte >> (2 * i)) & 3;
            let delta = match ty {
                COMMON => common_value,

                // 64 bits targets
                SMALL if is_64_bit => ints_reader.read_pod::<i16>()? as i64,
                MEDIUM if is_64_bit => ints_reader.read_pod::<i32>()? as i64,
                LARGE if is_64_bit => ints_reader.read_pod::<i64>()?,

                // 32 bits
                SMALL => ints_reader.read_pod::<i8>()? as i64,
                MEDIUM => ints_reader.read_pod::<i16>()? as i64,
                LARGE => ints_reader.read_pod::<i32>()? as i64,

                _ => bail!("Unexpected index: {}", ty),
            };

            prev += delta;

            output.push(prev.as_());
        }
    }

    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

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
