//! Various `io::Read` extensions to simplify reading crate files.

use std::{any::type_name, io, mem};

use anyhow::{Context, Result};
use bytemuck::{bytes_of_mut, cast_slice_mut, AnyBitPattern, NoUninit, Pod};
use num_traits::PrimInt;

use super::coding::{self, Int};

pub trait CrateReader {
    /// Read a single "size" or "count" value encoded as `u64`.
    ///
    /// # Format:
    /// - u64 size
    fn read_count(&mut self) -> Result<usize>;

    fn read_pod<T: Default + Pod>(&mut self) -> Result<T>;

    fn read_vec<T: Default + NoUninit + AnyBitPattern>(&mut self, count: usize) -> Result<Vec<T>>;

    /// Reads a lz4 compressed data and returns decompressed raw bytes.
    ///
    /// Format expected:
    /// - u64 uncompressed size
    /// - lz4 compressed block of data.
    ///
    /// # Arguments:
    /// - `estimated_size`: Size enough to hold uncompressed data.
    fn read_compressed<T: Default + NoUninit + AnyBitPattern>(&mut self, estimated_size: usize) -> Result<Vec<T>>;

    /// Reads sequence of compressed integers.
    fn read_encoded_ints<T: PrimInt + Int>(&mut self, count: usize) -> Result<Vec<T>>;
}

impl<R: io::Read> CrateReader for R {
    fn read_count(&mut self) -> Result<usize> {
        let mut count = 0_u64;
        self.read_exact(bytes_of_mut(&mut count))
            .context("Unable to read size from IO stream")?;

        Ok(count as usize)
    }

    fn read_pod<T: Default + Pod>(&mut self) -> Result<T> {
        let mut object = T::default();

        self.read_exact(bytes_of_mut(&mut object))
            .with_context(|| format!("Unable to read pod: {}", type_name::<T>()))?;

        Ok(object)
    }

    fn read_vec<T: Default + NoUninit + AnyBitPattern>(&mut self, count: usize) -> Result<Vec<T>> {
        if count == 0 {
            return Ok(Vec::new());
        }

        let mut vec = vec![T::default(); count];
        self.read_exact(cast_slice_mut(&mut vec))
            .context("Unable to read vec")?;

        Ok(vec)
    }

    fn read_compressed<T: Default + NoUninit + AnyBitPattern>(&mut self, estimated_count: usize) -> Result<Vec<T>> {
        // Read data to memory.
        let compressed_size = self.read_count()?;
        let mut input = vec![0_u8; compressed_size];
        self.read_exact(&mut input)?;

        // Decompress to output buffer.
        let mut output = vec![T::default(); estimated_count];
        let actual_size = decompress_lz4(&input, cast_slice_mut(&mut output))?;

        let actual_count = actual_size / mem::size_of::<T>();

        if actual_count < output.len() {
            output.truncate(actual_count);
        }

        Ok(output)
    }

    fn read_encoded_ints<T: PrimInt + Int>(&mut self, count: usize) -> Result<Vec<T>> {
        let estimated_size = coding::encoded_buffer_size::<u32>(count);

        let buffer = self.read_compressed::<u8>(estimated_size)?;

        let ints = coding::decode32(buffer.as_slice(), count)?;
        debug_assert_eq!(ints.len(), count);

        Ok(ints)
    }
}

fn decompress_lz4(mut input: &[u8], output: &mut [u8]) -> Result<usize> {
    // Check first byte for # chunks.
    // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/base/tf/fastCompression.cpp#L108

    let chunks = input.read_pod::<u8>().context("Unable to read lz4 chunk count")? as usize;

    if chunks == 0 {
        let size = lz4_flex::decompress_into(input, output).context("Failed to decompress data, possibly corrupt?")?;

        Ok(size)
    } else {
        // Decompress chunk by chunk.
        // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/base/tf/fastCompression.cpp#L125

        todo!("Support lz4 chunked decompression")
    }
}
