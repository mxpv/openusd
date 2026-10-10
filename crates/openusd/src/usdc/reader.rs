//! Binary crate file reader.

use std::{any::type_name, collections::HashMap, mem, str};

use crate::gf::f16;
use bytemuck::{AnyBitPattern, NoUninit, Pod, bytes_of, cast_slice_mut, pod_read_unaligned};
use num_traits::{AsPrimitive, Float, PrimInt};

use crate::{
    ar, gf,
    sdf::{self, Value},
    tf,
    usdc::coding,
};

use super::layout::*;
use super::{MAX_NESTING, MIN_COMPRESSED_ARRAY_SIZE, ReadError, ReadResultExt};

/// Returns a [`ReadError::Corrupt`] unless `cond` holds. Without a message the
/// failed condition itself is the reason.
macro_rules! corrupt {
    ($cond:expr) => {
        corrupt!($cond, "{}", stringify!($cond))
    };
    ($cond:expr, $($arg:tt)*) => {
        if !$cond {
            return Err(ReadError::corrupt(format!($($arg)*)));
        }
    };
}

/// Largest single LZ4-decompressed block the reader allocates (4 GiB).
/// (Saturates on 32-bit targets.)
const MAX_DECOMPRESSED_BYTES: usize = if usize::BITS > 32 { 4 << 30 } else { usize::MAX };

/// The shortest crate whose bytes are advised around the structural read.
/// A platform reads ahead by default in windows of about this size, which
/// brings in a shorter crate whole on its first faults; three advice calls
/// per layer would then be cost with nothing to gain, and a scene can hold
/// tens of thousands of short layers.
///
/// TODO(perf): the size is reasoned from the read-ahead window, not
/// measured. A cold open of a scene of many layers, with the threshold
/// moved either way, would say where it belongs.
const MIN_ADVISED_BYTES: usize = 1 << 20;

// Maximum supported USDC crate version.
// See USD Core Specification v1.0.1 §16.3.8.2 for version history:
//   0.10.0 — Path Expression value types
//   0.11.0 — Relocates in layer metadata
//   0.12.0 — Splines
const SW_VERSION: Version = version(0, 12, 0);

/// A crate file: its structural sections, read once by [`open`](Self::open),
/// over the bytes it decodes values from on demand. The bytes live as long
/// as the file, whatever holds them (a buffer or a mapping); decoding never
/// touches a file of its own.
#[derive(Debug)]
pub struct CrateFile {
    /// The whole file.
    pub(super) bytes: ar::AssetBuffer,

    /// File header.
    pub bootstrap: Bootstrap,
    /// Structural sections.
    pub sections: Vec<Section>,
    /// Tokens section.
    pub tokens: Vec<String>,
    /// Strings section.
    pub strings: Vec<usize>,
    /// All unique fields.
    pub fields: Vec<Field>,
    /// A vector of groups of fields, invalid-index terminated.
    pub fieldsets: Vec<Option<usize>>,
    // All unique paths.
    pub paths: Vec<sdf::Path>,
    // All specs.
    pub specs: Vec<Spec>,
}

/// The advice a crate's bytes are under while its structural sections are
/// read: random access from [`begin`](Self::begin) until the value drops,
/// which restores the default on every way out of the read.
///
/// A crate shorter than [`MIN_ADVISED_BYTES`] is read under the default
/// advice it already has.
struct StructuralRead(Option<ar::SharedBuffer>);

impl StructuralRead {
    /// Advises `bytes` for random access when they are a shared view long
    /// enough for advice to matter.
    fn begin(bytes: &ar::AssetBuffer) -> Self {
        let view = match bytes {
            ar::AssetBuffer::Shared(view) if view.len() >= MIN_ADVISED_BYTES => Some(view.clone()),
            _ => None,
        };
        if let Some(view) = &view {
            view.advise(0..view.len(), ar::Advice::Random);
        }
        StructuralRead(view)
    }

    /// Advises the one span from the first of `sections` to the end of the
    /// last as needed soon (C++ `_PrefetchStructuralSections`).
    fn prefetch(&self, sections: &[Section]) {
        let Some(view) = &self.0 else { return };
        let offset = |offset: u64| usize::try_from(offset).unwrap_or(usize::MAX);
        let start = sections.iter().map(|section| offset(section.start)).min();
        let end = sections
            .iter()
            .map(|section| offset(section.start.saturating_add(section.size)))
            .max();
        if let (Some(start), Some(end)) = (start, end) {
            view.advise(start..end, ar::Advice::WillNeed);
        }
    }
}

impl Drop for StructuralRead {
    fn drop(&mut self) {
        if let Some(view) = &self.0 {
            view.advise(0..view.len(), ar::Advice::Normal);
        }
    }
}

/// A cursor over crate bytes: the read primitives every decode is built on.
/// Each is bounded by the slice, which makes a count or offset a file lies
/// about a [`ReadError::Corrupt`] before anything is allocated or read.
pub(super) struct Stream<'a> {
    bytes: &'a [u8],
    pos: usize,
}

/// The structural sections as [`CrateFile::open`] reads them: a cursor into
/// the file's bytes, the header, and the section table every reader seeks
/// by.
struct Loader<'a> {
    stream: Stream<'a>,
    bootstrap: Bootstrap,
    version: Version,
    sections: Vec<Section>,
}

/// One value decode in progress: the file's tables, a cursor over its bytes,
/// and the values nested inside the one being decoded, innermost last.
///
/// A crate file addresses a nested value by offset, so nothing in the format
/// stops one from pointing at itself; C++ keeps the same set for the same
/// reason (`_LocalUnpackRecursionGuard`). A value that nests nothing never
/// touches it.
struct Decoder<'a> {
    file: &'a CrateFile,
    stream: Stream<'a>,
    unpacking: Vec<ValueRep>,
}

impl CrateFile {
    /// Returns file's version extracted from bootstrap header.
    #[inline]
    pub fn version(&self) -> Version {
        Version::from(self.bootstrap)
    }

    /// Read the structural sections of the crate file in `bytes`, which the
    /// file keeps and decodes values from on demand.
    ///
    /// Bytes that are a view of a mapped file are advised around the read as
    /// C++ `CrateFile::_InitMMap` advises its mapping: random access over the
    /// whole crate while the header and section table are read, then the one
    /// span holding every section as needed soon, and the default again once
    /// the sections are read or the read fails. A crate inside a package
    /// advises its own range of the package's mapping.
    pub fn open(bytes: impl Into<ar::AssetBuffer>) -> Result<Self, ReadError> {
        let bytes = bytes.into();
        let advised = StructuralRead::begin(&bytes);
        let mut loader = Loader::new(&bytes)?;
        advised.prefetch(&loader.sections);
        let tokens = loader.read_tokens().ctx("TOKENS section")?;
        let strings = loader.read_strings().ctx("STRINGS section")?;
        let fields = loader.read_fields().ctx("FIELDS section")?;
        let fieldsets = loader.read_fieldsets().ctx("FIELDSETS section")?;
        let paths = loader.read_paths(&tokens).ctx("PATHS section")?;
        let specs = loader.read_specs().ctx("SPECS section")?;
        let Loader {
            bootstrap, sections, ..
        } = loader;

        Ok(CrateFile {
            bytes,
            bootstrap,
            sections,
            tokens,
            strings,
            fields,
            fieldsets,
            paths,
            specs,
        })
    }

    /// The whole file's bytes.
    pub fn bytes(&self) -> &ar::AssetBuffer {
        &self.bytes
    }

    /// Decode the value `rep` describes from the file's bytes.
    pub fn value(&self, rep: ValueRep) -> Result<sdf::Value, ReadError> {
        Decoder::new(self).decode(rep)
    }

    /// Sanity check of structural validity.
    /// Roughly corresponds to `PXR_PREFER_SAFETY_OVER_SPEED` define in USD.
    pub fn validate(&self) -> Result<(), ReadError> {
        // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L3268
        for (index, field) in self.fields.iter().enumerate() {
            corrupt!(
                self.tokens.get(field.token_index).is_some(),
                "Invalid field token index {}: {}",
                index,
                field.token_index
            );
        }

        for (index, fieldset) in self
            .fieldsets
            .iter()
            .enumerate()
            .filter_map(|(i, index)| index.map(|index| (i, index)))
        {
            corrupt!(
                self.fields.get(fieldset).is_some(),
                "Invalid fieldset index {index}: {fieldset}"
            );
        }

        for (index, spec) in self.specs.iter().enumerate() {
            corrupt!(
                self.paths.get(spec.path_index).is_some(),
                "Invalid spec {} path index: {}",
                index,
                spec.path_index
            );

            corrupt!(
                self.fieldsets.get(spec.fieldset_index).is_some(),
                "Invalid spec {} fieldset index: {}",
                index,
                spec.fieldset_index
            );

            // Additionally, a fieldSetIndex must either be 0, or the element at
            // the prior index must be a default-constructed FieldIndex.
            // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L3289

            if spec.fieldset_index > 0 {
                corrupt!(
                    self.fieldsets[spec.fieldset_index - 1].is_none(),
                    "Invalid spec {}, the element at the prior index {} must be a default-constructed field index",
                    index,
                    spec.fieldset_index
                );
            }

            corrupt!(spec.spec_type != sdf::SpecType::Unknown, "Invalid spec {index} type");
        }

        Ok(())
    }
}

impl<'a> Loader<'a> {
    /// Reads and verifies the header of `bytes`, then the section table it
    /// points at.
    fn new(bytes: &'a [u8]) -> Result<Self, ReadError> {
        let mut stream = Stream::new(bytes);
        let bootstrap = stream.read_pod::<Bootstrap>()?;

        corrupt!(bootstrap.ident.eq(super::MAGIC), "Usd crate bootstrap section corrupt");

        corrupt!(bootstrap.toc_offset > 0, "Invalid TOC offset");

        let version = Version::from(bootstrap);

        if !SW_VERSION.can_read(version) {
            return Err(ReadError::unsupported(format!(
                "Usd crate version mismatch, file is {version}, library supports {SW_VERSION}"
            )));
        }

        let sections = read_sections(&mut stream, bootstrap.toc_offset).ctx("sections")?;

        Ok(Loader {
            stream,
            bootstrap,
            version,
            sections,
        })
    }

    /// The TOKENS section: every token's text.
    fn read_tokens(&mut self) -> Result<Vec<String>, ReadError> {
        let Some(section) = section_named(&self.sections, Section::TOKENS) else {
            return Ok(Vec::new());
        };

        self.stream.seek(section.start)?;

        if self.version < version(0, 4, 0) {
            return Err(ReadError::unsupported("Support TOKENS reader for < 0.4.0 files"));
        }

        // Read the number of tokens.
        let count = self.stream.read_count()?;
        let uncompressed_size = self.stream.read_count()?;
        let mut buffer = self.stream.read_compressed(uncompressed_size)?;

        corrupt!(
            buffer.len() == uncompressed_size,
            "Decompressed size mismatch (expected {}, got {})",
            uncompressed_size,
            buffer.len(),
        );

        if buffer.is_empty() {
            corrupt!(
                count == 0,
                "Tokens section claims {count} tokens but the buffer is empty"
            );
            return Ok(Vec::new());
        }

        corrupt!(
            buffer.last() == Some(&b'\0'),
            "Tokens section not null-terminated in crate file"
        );

        // Pop last \0 byte to split strings without empty one at the end.
        buffer.pop();

        let strings = buffer
            .split(|c| *c == b'\0')
            .map(|buf| str::from_utf8(buf).map(|str| str.to_string()))
            .collect::<Result<Vec<_>, str::Utf8Error>>()?;

        corrupt!(
            strings.len() == count,
            "Crate file claims {} tokens, but found {}",
            count,
            strings.len(),
        );

        Ok(strings)
    }

    /// The STRINGS section: each string as an index into the tokens.
    fn read_strings(&mut self) -> Result<Vec<usize>, ReadError> {
        let Some(section) = section_named(&self.sections, Section::STRINGS) else {
            return Ok(Vec::new());
        };

        self.stream.seek(section.start)?;

        let count = self.stream.read_count()?;
        corrupt!(
            count < 128 * 1024 * 1024,
            "Suspiciously large number of strings: {count}"
        );

        let strings = self.stream.read_vec::<u32>(count)?;

        // These are indices, so convert to usize for convenience.
        Ok(strings.into_iter().map(|offset| offset as usize).collect())
    }

    /// The FIELDS section: every unique field.
    fn read_fields(&mut self) -> Result<Vec<Field>, ReadError> {
        let Some(section) = section_named(&self.sections, Section::FIELDS) else {
            return Ok(Vec::new());
        };

        self.stream.seek(section.start)?;

        if self.version < version(0, 4, 0) {
            return Err(ReadError::unsupported("Support FIELDS reader before < 0.4.0"));
        }

        let field_count = self.stream.read_count()?;

        // Compressed fields in 0.4.0.
        let indices = self.stream.read_encoded_ints(field_count)?;

        // Compressed value reps.
        let reps = self.stream.read_compressed(field_count)?;

        let fields: Vec<_> = indices
            .iter()
            .zip(reps.iter())
            .map(|(index, value)| Field::new(*index, *value))
            .collect();

        corrupt!(fields.len() == field_count);

        Ok(fields)
    }

    /// The FIELDSETS section: runs of field indices, each ended by `None`.
    fn read_fieldsets(&mut self) -> Result<Vec<Option<usize>>, ReadError> {
        let Some(section) = section_named(&self.sections, Section::FIELDSETS) else {
            return Ok(Vec::new());
        };

        self.stream.seek(section.start)?;

        if self.version < version(0, 4, 0) {
            return Err(ReadError::unsupported("Support FIELDSETS reader for < 0.4.0 files"));
        }

        let count = self.stream.read_count()?;

        let decoded = self.stream.read_encoded_ints::<u32>(count)?;

        const INVALID_INDEX: u32 = u32::MAX;

        let sets = decoded
            .into_iter()
            .map(|i| if i == INVALID_INDEX { None } else { Some(i as usize) })
            .collect::<Vec<_>>();

        corrupt!(sets.len() == count);

        Ok(sets)
    }

    /// The PATHS section: every unique path, its elements named by `tokens`.
    fn read_paths(&mut self, tokens: &[String]) -> Result<Vec<sdf::Path>, ReadError> {
        let Some(section) = section_named(&self.sections, Section::PATHS) else {
            return Ok(Vec::new());
        };

        self.stream.seek(section.start)?;

        if self.version == version(0, 0, 1) {
            return Err(ReadError::unsupported("Support PATHS reader for == 0.0.1 files"));
        }
        if self.version < version(0, 4, 0) {
            return Err(ReadError::unsupported("Support PATHS reader for < 0.4.0 files"));
        }

        // Read # of paths.
        let path_count = self.stream.read_count()?;
        self.read_compressed_paths(path_count, tokens)
    }

    /// Read compressed paths.
    fn read_compressed_paths(&mut self, path_count: usize, tokens: &[String]) -> Result<Vec<sdf::Path>, ReadError> {
        // Read number of encoded paths.
        let count: usize = self.stream.read_count()?;
        // The table interns unique paths; only the empty path has no encoding.
        corrupt!(
            path_count.checked_sub(count).is_some_and(|empty| empty <= 1),
            "path table has {path_count} slots for {count} encoded paths"
        );

        // Read compressed data.

        let path_indexes = self.stream.read_encoded_ints::<u32>(count)?;
        corrupt!(path_indexes.len() == count);

        let element_token_indexes = self.stream.read_encoded_ints::<i32>(count)?;
        corrupt!(element_token_indexes.len() == count);

        let jumps = self.stream.read_encoded_ints::<i32>(count)?;
        corrupt!(jumps.len() == count);

        for &index in &path_indexes {
            corrupt!(
                (index as usize) < path_count,
                "path index {index} exceeds {path_count} slots"
            );
        }
        // Allocate slots after all three encoded tables have been decoded.
        let mut paths = Vec::new();
        paths
            .try_reserve_exact(path_count)
            .map_err(|error| ReadError::corrupt(format!("cannot allocate {path_count} path slots: {error}")))?;
        paths.resize(path_count, sdf::Path::default());

        build_compressed_paths(&mut paths, tokens, &path_indexes, &element_token_indexes, &jumps)?;

        Ok(paths)
    }

    /// The SPECS section: every spec, by path and fieldset index.
    fn read_specs(&mut self) -> Result<Vec<Spec>, ReadError> {
        let Some(section) = section_named(&self.sections, Section::SPECS) else {
            return Ok(Vec::new());
        };

        self.stream.seek(section.start)?;

        if self.version == version(0, 0, 1) {
            return Err(ReadError::unsupported("Support SPECS reader for == 0.0.1 files"));
        }
        if self.version < version(0, 4, 0) {
            return Err(ReadError::unsupported("Support SPECS reader for < 0.4.0 files"));
        }

        // Version 0.4.0 specs are compressed
        let spec_count = self.stream.read_count()?;

        let path_indexes = self.stream.read_encoded_ints::<u32>(spec_count)?;
        let fieldset_indexes = self.stream.read_encoded_ints::<u32>(spec_count)?;
        let spec_types = self.stream.read_encoded_ints::<u32>(spec_count)?;

        path_indexes
            .into_iter()
            .zip(fieldset_indexes)
            .zip(spec_types)
            .map(|((path, fieldset), spec_type)| {
                Ok(Spec {
                    path_index: path as usize,
                    fieldset_index: fieldset as usize,
                    spec_type: sdf::SpecType::from_repr(spec_type)
                        .ok_or_else(|| ReadError::corrupt(format!("Unable to parse SDF spec type: {spec_type}")))?,
                })
            })
            .collect()
    }
}

impl<'a> Stream<'a> {
    /// A cursor at the start of `bytes`.
    pub(super) fn new(bytes: &'a [u8]) -> Self {
        Stream { bytes, pos: 0 }
    }

    /// The current offset, for [`rewind`](Self::rewind) to return to.
    fn position(&self) -> usize {
        self.pos
    }

    /// Returns to `position`, one [`position`](Self::position) produced.
    fn rewind(&mut self, position: usize) {
        self.pos = position;
    }

    /// Moves to `position`, an offset the file states, which may be the end
    /// of the stream but not past it.
    pub(super) fn seek(&mut self, position: u64) -> Result<(), ReadError> {
        let pos = usize::try_from(position)
            .ok()
            .filter(|&pos| pos <= self.bytes.len())
            .ok_or_else(|| {
                ReadError::corrupt(format!(
                    "offset {position} is past the {}-byte stream",
                    self.bytes.len()
                ))
            })?;
        self.pos = pos;
        Ok(())
    }

    /// Moves `delta` bytes from the current offset, either way, staying
    /// within the stream.
    fn skip(&mut self, delta: i64) -> Result<(), ReadError> {
        let pos = isize::try_from(delta)
            .ok()
            .and_then(|delta| self.pos.checked_add_signed(delta))
            .filter(|&pos| pos <= self.bytes.len())
            .ok_or_else(|| {
                ReadError::corrupt(format!(
                    "a jump of {delta} bytes from offset {} leaves the {}-byte stream",
                    self.pos,
                    self.bytes.len()
                ))
            })?;
        self.pos = pos;
        Ok(())
    }

    /// The next `len` bytes, which the stream moves past. The one place a
    /// read is bounded: a length that reaches past the stream is corrupt.
    fn take(&mut self, len: usize) -> Result<&'a [u8], ReadError> {
        let end = self
            .pos
            .checked_add(len)
            .filter(|&end| end <= self.bytes.len())
            .ok_or_else(|| {
                ReadError::corrupt(format!(
                    "{len} bytes at offset {} reach past the {}-byte stream",
                    self.pos,
                    self.bytes.len()
                ))
            })?;
        let bytes = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(bytes)
    }

    /// Read a single "size" or "count" value encoded as `u64`.
    fn read_count(&mut self) -> Result<usize, ReadError> {
        let count = self.read_pod::<u64>()?;
        usize::try_from(count).map_err(|_| ReadError::corrupt(format!("count {count} does not fit this platform")))
    }

    /// Read one plain value, whatever its alignment in the stream.
    pub(super) fn read_pod<T: AnyBitPattern>(&mut self) -> Result<T, ReadError> {
        let bytes = self
            .take(mem::size_of::<T>())
            .map_err(|error| error.in_context(format!("pod {}", type_name::<T>())))?;
        Ok(pod_read_unaligned(bytes))
    }

    /// Read `count` plain values into a new vector, copied out of the stream
    /// once. The byte size, the slice and the allocation are each checked in
    /// that order, which fails a lying count before anything is allocated.
    fn read_vec<T: NoUninit + AnyBitPattern>(&mut self, count: usize) -> Result<Vec<T>, ReadError> {
        if count == 0 {
            return Ok(Vec::new());
        }
        let bytes = count
            .checked_mul(mem::size_of::<T>())
            .ok_or_else(|| ReadError::corrupt(format!("vector of {count} elements overflows")))?;
        let raw = self.take(bytes).ctx("vec")?;
        let mut vec = vec![T::zeroed(); count];
        cast_slice_mut(&mut vec).copy_from_slice(raw);
        Ok(vec)
    }

    /// Reads a lz4 compressed data and returns decompressed raw bytes.
    ///
    /// Format expected:
    /// - u64 uncompressed size
    /// - lz4 compressed block of data.
    ///
    /// # Arguments:
    /// - `estimated_size`: Size enough to hold uncompressed data.
    fn read_compressed<T: NoUninit + AnyBitPattern>(&mut self, estimated_count: usize) -> Result<Vec<T>, ReadError> {
        let compressed_size = self.read_count()?;
        let input = self.take(compressed_size)?;

        // Decompress to a buffer no larger than LZ4 can expand this input
        // (`estimated_count` is an upper bound from the file, not a size).
        // A single decoded value over MAX_DECOMPRESSED_BYTES is refused like
        // the other suspiciously large counts: LZ4 alone would allow 255x a
        // compressed block that may be most of the file.
        let most = compressed_size
            .saturating_mul(255)
            .saturating_add(64)
            .min(MAX_DECOMPRESSED_BYTES)
            / mem::size_of::<T>().max(1);
        let mut output = vec![T::zeroed(); estimated_count.min(most)];
        let actual_size = decompress_lz4(input, cast_slice_mut(&mut output))?;

        let actual_count = actual_size / mem::size_of::<T>();

        if actual_count < output.len() {
            output.truncate(actual_count);
        }

        Ok(output)
    }

    /// Reads sequence of compressed integers.
    fn read_encoded_ints<T: PrimInt + 'static>(&mut self, count: usize) -> Result<Vec<T>, ReadError>
    where
        i64: AsPrimitive<T>,
    {
        let estimated_size = coding::encoded_buffer_size::<u32>(count);

        let buffer = self.read_compressed::<u8>(estimated_size)?;

        let ints = coding::decode_ints(buffer.as_slice(), count)?;
        corrupt!(ints.len() == count);

        Ok(ints)
    }
}

impl<'a> Decoder<'a> {
    /// A decoder over `file`'s bytes, at their start.
    fn new(file: &'a CrateFile) -> Self {
        Decoder {
            file,
            stream: Stream::new(&file.bytes),
            unpacking: Vec::new(),
        }
    }

    fn resolve_string(&self, string_index: u32) -> Result<String, ReadError> {
        let token = *indexed(&self.file.strings, string_index as usize, "string")?;
        Ok(indexed(&self.file.tokens, token, "token")?.clone())
    }

    fn unpack_value<T: AnyBitPattern>(&mut self, value: ValueRep) -> Result<T, ReadError> {
        corrupt!(!value.is_array(), "Can't unpack array {value:?} as inline value");

        let ty = value.ty()?;
        corrupt!(ty != Type::Invalid, "Invalid value type");

        // If the value is inlined, just decode it.
        let value = if value.is_inlined() {
            // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1590
            corrupt!(
                mem::size_of::<T>() <= mem::size_of::<u64>(),
                "Can't unpack {} from an inline payload",
                type_name::<T>()
            );
            let tmp = value.payload() & ((1_u64 << (mem::size_of::<u32>() * 8)) - 1);
            pod_read_unaligned(&bytes_of(&tmp)[..mem::size_of::<T>()])
        } else {
            // Otherwise we have to read it from the decoder.
            self.stream.seek(value.payload())?;
            self.stream.read_pod::<T>()?
        };

        Ok(value)
    }

    fn read_token(&mut self, value: ValueRep) -> Result<tf::Token, ReadError> {
        let index: u64 = self.unpack_value(value)?;
        Ok(indexed(&self.file.tokens, index as usize, "token")?.as_str().into())
    }

    /// Read a scalar asset path or path expression.
    ///
    /// Both encode an index that points into the token table when the value is
    /// inlined but into the string table when it is stored on the heap, so the
    /// table is chosen by the inlined flag (mirrors `SdfAssetPath` /
    /// `SdfPathExpression` handling in Pixar's crate reader).
    fn read_asset_path(&mut self, value: ValueRep) -> Result<String, ReadError> {
        let index = self.unpack_value::<u32>(value)?;
        if value.is_inlined() {
            Ok(indexed(&self.file.tokens, index as usize, "token")?.clone())
        } else {
            self.resolve_string(index)
        }
    }

    // Implements various logic and compatibility checks to figure out the array length and whether it's compressed.
    fn unpack_array_len(&mut self, value: ValueRep, kind: ArrayKind) -> Result<(usize, bool), ReadError> {
        corrupt!(!value.is_inlined());

        // Empty array.
        if value.payload() == 0 {
            return Ok((0, false));
        }

        self.stream.seek(value.payload())?;

        if self.file.version() < version(0, 5, 0) {
            // Read and discard shape size.
            let _ = self.stream.read_pod::<u32>()?;
        }

        // Detect compression.
        let mut compressed = true;
        match kind {
            ArrayKind::Ints => {
                // Version 0.5.0 introduced compressed int arrays.
                // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1935
                if self.file.version() < version(0, 5, 0) || !value.is_compressed() {
                    compressed = false;
                }
            }
            ArrayKind::Floats => {
                // Version 0.6.0 introduced compressed floating point arrays.
                // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1961C5-L1961C66
                if self.file.version() < version(0, 6, 0) || !value.is_compressed() {
                    compressed = false;
                }
            }
            ArrayKind::Other => {
                // Fallback to uncompressed.
                // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1868
                corrupt!(!value.is_compressed());
                compressed = false;
            }
        }

        // Read the number of elements.
        let count = if self.file.version() < version(0, 7, 0) {
            self.stream.read_pod::<u32>()? as usize
        } else {
            self.stream.read_pod::<u64>()? as usize
        };

        if count < MIN_COMPRESSED_ARRAY_SIZE {
            compressed = false;
        }

        Ok((count, compressed))
    }

    fn read_ints<T: PrimInt + Pod + Default>(&mut self, value: ValueRep) -> Result<Vec<T>, ReadError>
    where
        i64: AsPrimitive<T>,
    {
        let (count, compressed) = self.unpack_array_len(value, ArrayKind::Ints)?;

        if count == 0 {
            return Ok(Vec::default());
        }

        if compressed {
            self.stream.read_encoded_ints(count)
        } else {
            self.stream.read_vec(count)
        }
    }

    fn read_floats<T: Float + Default + Pod>(&mut self, value: ValueRep) -> Result<Vec<T>, ReadError> {
        use num_traits::cast;
        corrupt!(!value.is_inlined());

        let (count, compressed) = self.unpack_array_len(value, ArrayKind::Floats)?;

        let vec = if compressed {
            let code = self.stream.read_pod::<u8>()?;

            match code {
                // Compressed integers. Pixar's `_ReadCompressedInts` runs the
                // LZ4 block through `Usd_IntegerCompression` decoding after
                // decompression, so the payload must be integer-decoded
                // (`read_encoded_ints`), not reinterpreted as raw `i32`s
                // straight out of LZ4.
                b'i' => {
                    let ints: Vec<i32> = self.stream.read_encoded_ints(count)?;
                    ints.into_iter().map(|i| cast(i).unwrap()).collect()
                }
                // Lookup table and indexes
                b't' => {
                    let lut_size = self.stream.read_pod::<u32>()? as usize;
                    let lut: Vec<T> = self.stream.read_vec(lut_size)?;

                    let indexes: Vec<u32> = self.stream.read_encoded_ints(count)?;
                    corrupt!(
                        indexes.len() == count,
                        "Read invalid number of indexes to decompress doubles array"
                    );

                    let mut output = vec![T::zero(); count];
                    for (i, index) in indexes.into_iter().enumerate() {
                        output[i] = *lut.get(index as usize).ok_or_else(|| {
                            ReadError::corrupt(format!("lookup index {index} is outside a {}-entry table", lut.len()))
                        })?;
                    }

                    output
                }
                _ => {
                    return Err(ReadError::corrupt(format!(
                        "Invalid compressed double array code: {code}"
                    )));
                }
            }
        } else {
            self.stream.read_vec(count)?
        };

        Ok(vec)
    }

    fn read_list_op<T: Default + Clone + PartialEq>(
        &mut self,
        value: ValueRep,
        mut read: impl FnMut(&mut Self) -> Result<Vec<T>, ReadError>,
    ) -> Result<sdf::ListOp<T>, ReadError> {
        self.stream.seek(value.payload())?;

        let mut out = sdf::ListOp::<T>::default();

        let header = self.stream.read_pod::<ListOpHeader>()?;

        if header.is_explicit() {
            out.explicit = true;
        }

        if header.has_explicit() {
            out.explicit_items = read(self)?;
        }

        if header.has_added() {
            out.added_items = read(self)?;
        }

        if header.has_prepend() {
            out.prepended_items = read(self)?;
        }

        if header.has_appended() {
            out.appended_items = read(self)?;
        }

        if header.has_deleted() {
            out.deleted_items = read(self)?;
        }

        if header.has_ordered() {
            out.ordered_items = read(self)?;
        }

        Ok(out)
    }

    /// Reads a count-prefixed vector of `u32` indices and maps each through
    /// `lookup` to produce the element value.
    fn read_indexed_vec<T>(
        &mut self,
        lookup: impl Fn(&Self, usize) -> Result<T, ReadError>,
    ) -> Result<Vec<T>, ReadError> {
        let count = self.stream.read_count()?;
        let indices = self.stream.read_vec::<u32>(count)?;

        indices.into_iter().map(|index| lookup(self, index as usize)).collect()
    }

    fn read_string_vec(&mut self) -> Result<Vec<String>, ReadError> {
        self.read_indexed_vec(|decoder, index| {
            let token = *indexed(&decoder.file.strings, index, "string")?;
            Ok(indexed(&decoder.file.tokens, token, "token")?.clone())
        })
    }

    fn read_token_vec(&mut self) -> Result<Vec<tf::Token>, ReadError> {
        self.read_indexed_vec(|decoder, index| Ok(indexed(&decoder.file.tokens, index, "token")?.as_str().into()))
    }

    fn read_path_vec(&mut self) -> Result<Vec<sdf::Path>, ReadError> {
        self.read_indexed_vec(|decoder, index| Ok(indexed(&decoder.file.paths, index, "path")?.clone()))
    }

    /// Reads a count-prefixed vector of POD values.
    fn read_pod_vec<T: NoUninit + AnyBitPattern>(&mut self) -> Result<Vec<T>, ReadError> {
        let count = self.stream.read_count()?;
        self.stream.read_vec(count)
    }

    fn read_string(&mut self) -> Result<String, ReadError> {
        let index = self.stream.read_pod::<u32>()?;
        self.resolve_string(index)
    }

    fn read_path(&mut self) -> Result<sdf::Path, ReadError> {
        let index = self.stream.read_pod::<u32>()?;
        Ok(indexed(&self.file.paths, index as usize, "path")?.clone())
    }

    fn read_reference(&mut self) -> Result<sdf::Reference, ReadError> {
        let asset_path = self.read_string()?;
        let prim_path = self.read_path()?;
        let layer_offset = self.stream.read_pod::<sdf::LayerOffset>()?;
        let custom_data = self.read_custom_data()?;

        Ok(sdf::Reference {
            asset_path,
            prim_path,
            layer_offset,
            custom_data,
        })
    }

    fn read_payload(&mut self) -> Result<sdf::Payload, ReadError> {
        let asset_path = self.read_string()?;
        let prim_path = self.read_path()?;

        let mut payload = sdf::Payload {
            asset_path,
            prim_path,
            layer_offset: sdf::LayerOffset::IDENTITY,
        };

        // Layer offsets were added to SdfPayload starting in 0.8.0. Files
        // before that cannot have them.
        // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1214C41-L1214C41
        if self.file.version() >= version(0, 8, 0) {
            payload.layer_offset = self.stream.read_pod::<sdf::LayerOffset>()?;
        }

        Ok(payload)
    }

    /// Applies a recursive offset stored inline in the stream.
    ///
    /// USD crate files encode forward jumps as a signed `i64` relative to the
    /// position **before** the offset itself, so we subtract 8 (the size of the
    /// offset we just consumed) to land at the correct location.
    ///
    /// See <https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1100>
    fn apply_recursive_offset(&mut self) -> Result<(), ReadError> {
        let offset = self.stream.read_pod::<i64>()?;
        let delta = offset
            .checked_sub(8)
            .ok_or_else(|| ReadError::corrupt(format!("recursive offset {offset} overflows")))?;
        self.stream.skip(delta)
    }

    /// Reads a crate dictionary value (`customData`, `assetInfo`, and nested
    /// dictionaries).
    fn read_custom_data(&mut self) -> Result<HashMap<String, Value>, ReadError> {
        let mut count = self.stream.read_count()?;
        let mut dict = HashMap::default();

        while count > 0 {
            let key = self.read_string()?;

            dict.insert(key, self.read_nested_value()?);
            count -= 1;
        }

        Ok(dict)
    }

    /// Read a nested, self-describing value: the forward offset to its
    /// `ValueRep`, then the value that rep describes, leaving the stream just
    /// past the rep (C++ `Read<VtValue>`).
    ///
    /// A dictionary entry, an unregistered value and the items of an
    /// unregistered list op all arrive this way, and each can nest another;
    /// [`value`](Self::value) refuses one that names itself or nests too
    /// deep.
    fn read_nested_value(&mut self) -> Result<Value, ReadError> {
        self.apply_recursive_offset()?;

        let rep = self.stream.read_pod::<ValueRep>()?;
        corrupt!(rep.ty()? != Type::Invalid, "Can't parse nested value type");

        let resume = self.stream.position();
        let value = self.nested_value(rep)?;
        self.stream.rewind(resume);

        Ok(value)
    }

    /// Read one operation's items from an unregistered field's list op: a
    /// count, then that many nested values, each holding a recorded body.
    ///
    /// C++ lets an item hold a dictionary or a further list op as well as a
    /// recorded body, which [`sdf::Value::UnregisteredValueListOp`] has no
    /// room for. Such an item is dropped rather than failing the layer around
    /// it, since the rest of the file reads perfectly well without it.
    ///
    /// TODO: widen the list op's item type so those survive.
    fn read_unregistered_items(&mut self) -> Result<Vec<String>, ReadError> {
        let count = self.stream.read_count()?;
        let mut items = Vec::new();
        for _ in 0..count {
            if let sdf::Value::String(text) = self.read_nested_value()? {
                items.push(text);
            }
        }
        Ok(items)
    }

    /// Reads an array of plain values, `U` laid out as the on-disk element:
    /// a scalar, a `[T; N]` group, or a `repr(C)` gf type.
    ///
    /// TODO(perf): the one copy left per array read, which zero-fills the
    /// vector before copying into it. C++ aligns every array payload to 8
    /// bytes, so for a file it wrote `bytemuck::try_cast_slice` over the
    /// taken bytes followed by `to_vec` would copy once with no fill (the
    /// crate writer here does not align, so the fill stays as the fallback).
    /// C++ goes further and hands out arrays of at least 2048 bytes as views
    /// into the mapped file when their address is aligned to the element
    /// (`USDC_ENABLE_ZERO_COPY_ARRAYS`), copying them out only when the file
    /// is replaced; that needs an `sdf::Value` array form over an
    /// `ar::SharedBuffer` view.
    fn read_array<U: NoUninit + AnyBitPattern>(&mut self, value: ValueRep) -> Result<Vec<U>, ReadError> {
        corrupt!(value.is_array() && !value.is_compressed());
        let (count, _) = self.unpack_array_len(value, ArrayKind::Other)?;
        self.stream.read_vec::<U>(count)
    }

    /// Decode the value `rep` describes as one nested in the value being
    /// decoded, refusing one already being decoded above it (a value that
    /// names itself) and one nested deeper than [`MAX_NESTING`].
    fn nested_value(&mut self, rep: ValueRep) -> Result<sdf::Value, ReadError> {
        corrupt!(
            !self.unpacking.contains(&rep),
            "A nested value recursively contains itself"
        );
        corrupt!(
            self.unpacking.len() < MAX_NESTING,
            "Values nested more than {MAX_NESTING} deep"
        );
        self.unpacking.push(rep);
        let value = self.decode(rep);
        self.unpacking.pop();
        value
    }

    fn decode(&mut self, value: ValueRep) -> Result<sdf::Value, ReadError> {
        let ty = value.ty()?;
        corrupt!(ty != Type::Invalid, "Invalid value type");

        let variant = match ty {
            //
            // Bool and chars
            //
            Type::Bool if value.is_array() => {
                sdf::Value::BoolVec(self.read_array::<u8>(value)?.into_iter().map(|v| v != 0).collect())
            }

            Type::Bool => {
                let value: i32 = self.unpack_value(value)?;
                sdf::Value::Bool(value != 0)
            }

            Type::Uchar if value.is_array() => sdf::Value::UcharVec(self.read_array::<u8>(value)?),

            Type::Uchar => {
                let value = self.unpack_value::<u8>(value)?;
                sdf::Value::Uchar(value)
            }

            //
            // Ints (int, uint, int64, uint64)
            //
            Type::Int if value.is_array() => sdf::Value::IntVec(self.read_ints(value)?),
            Type::Int => sdf::Value::Int(self.unpack_value(value)?),

            Type::Uint if value.is_array() => sdf::Value::UintVec(self.read_ints(value)?),
            Type::Uint => sdf::Value::Uint(self.unpack_value(value)?),

            Type::Int64 if value.is_array() => sdf::Value::Int64Vec(self.read_ints(value)?),
            Type::Int64 => sdf::Value::Int64(self.unpack_value(value)?),

            Type::Uint64 if value.is_array() => sdf::Value::Uint64Vec(self.read_ints(value)?),
            Type::Uint64 => sdf::Value::Uint64(self.unpack_value(value)?),

            //
            // Float types (half, float, double)
            //
            Type::Half if value.is_array() => sdf::Value::HalfVec(self.read_floats(value)?),
            Type::Half => sdf::Value::Half(self.unpack_value(value)?),

            Type::Float if value.is_array() => sdf::Value::FloatVec(self.read_floats(value)?),
            Type::Float => sdf::Value::Float(self.unpack_value(value)?),

            Type::Double if value.is_array() => sdf::Value::DoubleVec(self.read_floats(value)?),
            Type::Double if value.is_inlined() => {
                // Stored as f32
                let value = self.unpack_value::<f32>(value)?;
                sdf::Value::Double(value as f64)
            }
            Type::Double => sdf::Value::Double(self.unpack_value(value)?),

            Type::DoubleVector => sdf::Value::DoubleVec(self.read_floats(value)?),

            //
            // Tokens, strings, asset paths
            //
            Type::StringVector => {
                corrupt!(!value.is_inlined());

                self.stream.seek(value.payload())?;
                sdf::Value::StringVec(self.read_string_vec()?)
            }

            Type::String if value.is_array() => {
                self.stream.seek(value.payload())?;
                sdf::Value::StringVec(self.read_string_vec()?)
            }

            Type::String => {
                corrupt!(!value.is_array());

                let string_index = self.unpack_value::<u32>(value)?;
                sdf::Value::String(self.resolve_string(string_index)?)
            }
            Type::AssetPath if value.is_array() => {
                // Asset arrays (`asset[]`, e.g. value-clip `assetPaths`) are
                // stored like string arrays — string-table indices, not direct
                // token indices.
                self.stream.seek(value.payload())?;
                sdf::Value::AssetPathVec(self.read_string_vec()?.into_iter().map(Into::into).collect())
            }
            Type::AssetPath => sdf::Value::AssetPath(self.read_asset_path(value)?.into()),

            Type::Token if value.is_array() => {
                let (count, _) = self.unpack_array_len(value, ArrayKind::Other)?;
                let indices = self.stream.read_vec::<u32>(count)?;
                let tokens = indices
                    .into_iter()
                    .map(|i| Ok(indexed(&self.file.tokens, i as usize, "token")?.as_str().into()))
                    .collect::<Result<Vec<_>, ReadError>>()?;

                sdf::Value::TokenVec(tokens)
            }
            Type::Token => sdf::Value::Token(self.read_token(value)?),

            //
            // Vectors (half, float, double, int + vec{2,3,4})
            //
            Type::Vec2h if value.is_array() => Value::Vec2hVec(self.read_array::<gf::Vec2h>(value)?),
            Type::Vec2f if value.is_array() => Value::Vec2fVec(self.read_array::<gf::Vec2f>(value)?),
            Type::Vec2d if value.is_array() => Value::Vec2dVec(self.read_array::<gf::Vec2d>(value)?),
            Type::Vec2i if value.is_array() => Value::Vec2iVec(self.read_array::<gf::Vec2i>(value)?),

            Type::Vec3h if value.is_array() => Value::Vec3hVec(self.read_array::<gf::Vec3h>(value)?),
            Type::Vec3f if value.is_array() => Value::Vec3fVec(self.read_array::<gf::Vec3f>(value)?),
            Type::Vec3d if value.is_array() => Value::Vec3dVec(self.read_array::<gf::Vec3d>(value)?),
            Type::Vec3i if value.is_array() => Value::Vec3iVec(self.read_array::<gf::Vec3i>(value)?),

            Type::Vec4h if value.is_array() => Value::Vec4hVec(self.read_array::<gf::Vec4h>(value)?),
            Type::Vec4f if value.is_array() => Value::Vec4fVec(self.read_array::<gf::Vec4f>(value)?),
            Type::Vec4d if value.is_array() => Value::Vec4dVec(self.read_array::<gf::Vec4d>(value)?),
            Type::Vec4i if value.is_array() => Value::Vec4iVec(self.read_array::<gf::Vec4i>(value)?),

            // Inlined scalar vecs: the 32-bit inline payload stores [i8; N]
            // sign-extended integers for all types except half-2, which is the
            // only half variant that fits (2 × 2 bytes = 4 bytes).
            Type::Vec2h if value.is_inlined() => sdf::Value::Vec2h(self.unpack_value::<gf::Vec2h>(value)?),
            Type::Vec2f if value.is_inlined() => {
                let [x, y] = to_vec::<f32, 2>(self.unpack_value(value)?);
                sdf::Value::Vec2f(gf::vec2f(x, y))
            }
            Type::Vec2d if value.is_inlined() => {
                let [x, y] = to_vec::<f64, 2>(self.unpack_value(value)?);
                sdf::Value::Vec2d(gf::vec2d(x, y))
            }
            Type::Vec2i if value.is_inlined() => {
                let [x, y] = to_vec::<i32, 2>(self.unpack_value(value)?);
                sdf::Value::Vec2i(gf::vec2i(x, y))
            }

            Type::Vec3h if value.is_inlined() => {
                let [x, y, z] = to_vec::<f16, 3>(self.unpack_value(value)?);
                sdf::Value::Vec3h(gf::vec3h(x, y, z))
            }
            Type::Vec3f if value.is_inlined() => {
                let [x, y, z] = to_vec::<f32, 3>(self.unpack_value(value)?);
                sdf::Value::Vec3f(gf::vec3f(x, y, z))
            }
            Type::Vec3d if value.is_inlined() => {
                let [x, y, z] = to_vec::<f64, 3>(self.unpack_value(value)?);
                sdf::Value::Vec3d(gf::vec3d(x, y, z))
            }
            Type::Vec3i if value.is_inlined() => {
                let [x, y, z] = to_vec::<i32, 3>(self.unpack_value(value)?);
                sdf::Value::Vec3i(gf::vec3i(x, y, z))
            }

            Type::Vec4h if value.is_inlined() => {
                let [x, y, z, w] = to_vec::<f16, 4>(self.unpack_value(value)?);
                sdf::Value::Vec4h(gf::vec4h(x, y, z, w))
            }
            Type::Vec4f if value.is_inlined() => {
                let [x, y, z, w] = to_vec::<f32, 4>(self.unpack_value(value)?);
                sdf::Value::Vec4f(gf::vec4f(x, y, z, w))
            }
            Type::Vec4d if value.is_inlined() => {
                let [x, y, z, w] = to_vec::<f64, 4>(self.unpack_value(value)?);
                sdf::Value::Vec4d(gf::vec4d(x, y, z, w))
            }
            Type::Vec4i if value.is_inlined() => {
                let [x, y, z, w] = to_vec::<i32, 4>(self.unpack_value(value)?);
                sdf::Value::Vec4i(gf::vec4i(x, y, z, w))
            }

            // Non-inlined scalar vecs: repr(C) + Pod layout matches [T; N].
            Type::Vec2h => sdf::Value::Vec2h(self.unpack_value::<gf::Vec2h>(value)?),
            Type::Vec2f => sdf::Value::Vec2f(self.unpack_value::<gf::Vec2f>(value)?),
            Type::Vec2d => sdf::Value::Vec2d(self.unpack_value::<gf::Vec2d>(value)?),
            Type::Vec2i => sdf::Value::Vec2i(self.unpack_value::<gf::Vec2i>(value)?),

            Type::Vec3h => sdf::Value::Vec3h(self.unpack_value::<gf::Vec3h>(value)?),
            Type::Vec3f => sdf::Value::Vec3f(self.unpack_value::<gf::Vec3f>(value)?),
            Type::Vec3d => sdf::Value::Vec3d(self.unpack_value::<gf::Vec3d>(value)?),
            Type::Vec3i => sdf::Value::Vec3i(self.unpack_value::<gf::Vec3i>(value)?),

            Type::Vec4h => sdf::Value::Vec4h(self.unpack_value::<gf::Vec4h>(value)?),
            Type::Vec4f => sdf::Value::Vec4f(self.unpack_value::<gf::Vec4f>(value)?),
            Type::Vec4d => sdf::Value::Vec4d(self.unpack_value::<gf::Vec4d>(value)?),
            Type::Vec4i => sdf::Value::Vec4i(self.unpack_value::<gf::Vec4i>(value)?),

            //
            // Matrices
            //
            Type::Matrix2d if value.is_array() => Value::Matrix2dVec(self.read_array::<gf::Mat2d>(value)?),
            Type::Matrix3d if value.is_array() => Value::Matrix3dVec(self.read_array::<gf::Mat3d>(value)?),
            Type::Matrix4d if value.is_array() => Value::Matrix4dVec(self.read_array::<gf::Matrix4d>(value)?),

            Type::Matrix2d if value.is_inlined() => {
                sdf::Value::Matrix2d(gf::Mat2d(to_mat_diag::<2, 4>(self.unpack_value(value)?)))
            }
            Type::Matrix3d if value.is_inlined() => {
                sdf::Value::Matrix3d(gf::Mat3d(to_mat_diag::<3, 9>(self.unpack_value(value)?)))
            }
            Type::Matrix4d if value.is_inlined() => {
                sdf::Value::Matrix4d(gf::Matrix4d(to_mat_diag::<4, 16>(self.unpack_value(value)?)))
            }

            Type::Matrix2d => sdf::Value::Matrix2d(gf::Mat2d(self.unpack_value::<[f64; 4]>(value)?)),
            Type::Matrix3d => sdf::Value::Matrix3d(gf::Mat3d(self.unpack_value::<[f64; 9]>(value)?)),
            Type::Matrix4d => sdf::Value::Matrix4d(gf::Matrix4d(self.unpack_value::<[f64; 16]>(value)?)),

            //
            // Quats
            //
            // Pixar's GfQuat<T> declares `_imaginary: GfVec3<T>` then
            // `_real: T`, so on-disk bytes are `[imag_x, imag_y, imag_z,
            // real]` = `[x, y, z, w]`. The USDA textual form is
            // `(real, i, j, k)` = `(w, x, y, z)`, which the USDA parser
            // stores verbatim. Reorder USDC bytes here so `Value::Quat*`
            // values are consistently `(w, x, y, z)` regardless of source
            // — without this, binary USDC quats from real production
            // assets (Isaac Sim Agilebot, Omniverse robotics scenes)
            // come out with axes scrambled.
            Type::Quath if value.is_array() => Value::QuathVec(xyzw_to_wxyz_quath(self.read_array::<[f16; 4]>(value)?)),
            Type::Quath => {
                let raw = self.unpack_value::<[f16; 4]>(value)?;
                sdf::Value::quath(raw[3], raw[0], raw[1], raw[2])
            }

            Type::Quatf if value.is_array() => Value::QuatfVec(xyzw_to_wxyz_quatf(self.read_array::<[f32; 4]>(value)?)),
            Type::Quatf => {
                let raw = self.unpack_value::<[f32; 4]>(value)?;
                sdf::Value::quatf(raw[3], raw[0], raw[1], raw[2])
            }

            Type::Quatd if value.is_array() => Value::QuatdVec(xyzw_to_wxyz_quatd(self.read_array::<[f64; 4]>(value)?)),
            Type::Quatd => {
                let raw = self.unpack_value::<[f64; 4]>(value)?;
                sdf::Value::quatd(raw[3], raw[0], raw[1], raw[2])
            }

            //
            // ListOp
            //
            Type::TokenListOp => {
                corrupt!(!value.is_inlined());

                let list = self.read_list_op(value, |decoder: &mut Self| decoder.read_token_vec())?;
                sdf::Value::TokenListOp(list)
            }
            Type::StringListOp => {
                corrupt!(!value.is_inlined());

                let list = self.read_list_op(value, |decoder: &mut Self| decoder.read_string_vec())?;
                sdf::Value::StringListOp(list)
            }
            Type::PathListOp => {
                corrupt!(!value.is_inlined());

                let list = self.read_list_op(value, |decoder: &mut Self| decoder.read_path_vec())?;
                sdf::Value::PathListOp(list)
            }
            Type::ReferenceListOp => {
                corrupt!(!value.is_inlined());

                let list = self.read_list_op(value, |decoder: &mut Self| {
                    let count = decoder.stream.read_count()?;
                    let mut vec = Vec::with_capacity(count.min(1024));

                    for _ in 0..count {
                        let reference = decoder.read_reference()?;
                        vec.push(reference);
                    }

                    Ok(vec)
                })?;

                sdf::Value::ReferenceListOp(list)
            }

            Type::IntListOp => {
                corrupt!(!value.is_inlined());
                sdf::Value::IntListOp(self.read_list_op(value, |f: &mut Self| f.read_pod_vec())?)
            }
            Type::Int64ListOp => {
                corrupt!(!value.is_inlined());
                sdf::Value::Int64ListOp(self.read_list_op(value, |f: &mut Self| f.read_pod_vec())?)
            }
            Type::UIntListOp => {
                corrupt!(!value.is_inlined());
                sdf::Value::UIntListOp(self.read_list_op(value, |f: &mut Self| f.read_pod_vec())?)
            }
            Type::UInt64ListOp => {
                corrupt!(!value.is_inlined());
                sdf::Value::UInt64ListOp(self.read_list_op(value, |f: &mut Self| f.read_pod_vec())?)
            }

            //
            // SDF types
            //
            Type::TokenVector => {
                corrupt!(!value.is_inlined());

                self.stream.seek(value.payload())?;

                sdf::Value::TokenVec(self.read_token_vec()?)
            }

            Type::PathVector => {
                corrupt!(!value.is_inlined());

                self.stream.seek(value.payload())?;

                let paths = self.read_path_vec()?;
                sdf::Value::PathVec(paths)
            }

            Type::Specifier => {
                let tmp: i32 = self.unpack_value(value)?;
                let specifier = sdf::Specifier::from_repr(tmp)
                    .ok_or_else(|| ReadError::corrupt(format!("Unable to parse SDF specifier: {tmp}")))?;

                sdf::Value::Specifier(specifier)
            }

            Type::Permission => {
                let tmp: i32 = self.unpack_value(value)?;
                let permission = sdf::Permission::from_repr(tmp)
                    .ok_or_else(|| ReadError::corrupt(format!("Unable to parse permission: {tmp}")))?;

                sdf::Value::Permission(permission)
            }

            Type::Variability => {
                let tmp: i32 = self.unpack_value(value)?;
                let variability = sdf::Variability::from_repr(tmp)
                    .ok_or_else(|| ReadError::corrupt(format!("Unable to parse variability: {tmp}")))?;

                sdf::Value::Variability(variability)
            }

            Type::LayerOffsetVector => {
                corrupt!(!value.is_inlined());
                corrupt!(!value.is_array());
                corrupt!(!value.is_compressed());

                self.stream.seek(value.payload())?;

                let count = self.stream.read_count()?;
                let vec = self.stream.read_vec(count)?;

                sdf::Value::LayerOffsetVec(vec)
            }

            Type::Payload => {
                corrupt!(!value.is_inlined());
                corrupt!(!value.is_array());
                corrupt!(!value.is_compressed());

                self.stream.seek(value.payload())?;

                let payload = self.read_payload()?;
                sdf::Value::Payload(payload)
            }

            Type::PayloadListOp => {
                let list = self.read_list_op(value, |decoder: &mut Self| {
                    let count = decoder.stream.read_count()?;
                    let mut vec = Vec::with_capacity(count.min(1024));
                    for _ in 0..count {
                        let payload = decoder.read_payload()?;
                        vec.push(payload);
                    }

                    Ok(vec)
                })?;

                sdf::Value::PayloadListOp(list)
            }

            Type::VariantSelectionMap => {
                corrupt!(!value.is_inlined());
                corrupt!(!value.is_array());
                corrupt!(!value.is_compressed());

                self.stream.seek(value.payload())?;

                let count = self.stream.read_count()?;
                let mut map = HashMap::with_capacity(count.min(1024));

                for _ in 0..count {
                    let key = self.read_string()?;
                    let value = self.read_string()?;
                    map.insert(key, value);
                }

                sdf::Value::VariantSelectionMap(map)
            }

            Type::TimeSamples => {
                corrupt!(!value.is_inlined());
                corrupt!(!value.is_compressed());

                self.stream.seek(value.payload())?;

                self.apply_recursive_offset()?;

                let times_rep = self.stream.read_pod::<ValueRep>()?;

                let ty = times_rep.ty()?;
                corrupt!(
                    ty == Type::DoubleVector || (ty == Type::Double && times_rep.is_array()),
                    "Invalid time samples type: expected either double vector or double array"
                );

                // Save current position.
                let saved_position = self.stream.position();

                let times = self
                    .nested_value(times_rep)?
                    .try_as_double_vec()
                    .ok_or_else(|| ReadError::corrupt("Failed to read time samples"))?;

                // Restore position
                self.stream.rewind(saved_position);

                self.apply_recursive_offset()?;

                let count = self.stream.read_count()?;
                corrupt!(count == times.len(), "Invalid time samples count");

                let value_reps = self.stream.read_vec::<ValueRep>(count)?;
                corrupt!(value_reps.len() == count);

                let samples = times
                    .into_iter()
                    .zip(value_reps)
                    .map(|(time, rep)| Ok((time, self.nested_value(rep)?)))
                    .collect::<Result<Vec<_>, ReadError>>()?;

                sdf::Value::TimeSamples(sdf::normalize_time_samples(samples))
            }

            // Empty dictionary.
            Type::Dictionary if value.is_inlined() => sdf::Value::Dictionary(HashMap::default()),
            Type::Dictionary => {
                corrupt!(!value.is_compressed(), "Dictionary {ty} can't be compressed");
                corrupt!(!value.is_array(), "Dictionary {ty} can't be inlined");

                self.stream.seek(value.payload())?;

                sdf::Value::Dictionary(self.read_custom_data()?)
            }

            Type::ValueBlock => sdf::Value::ValueBlock,
            Type::Value => sdf::Value::Value,

            Type::TimeCode if value.is_array() => sdf::Value::TimeCodeVec(
                self.read_floats::<f64>(value)?
                    .into_iter()
                    .map(sdf::TimeCode::from)
                    .collect(),
            ),
            Type::TimeCode => sdf::Value::TimeCode(self.unpack_value::<f64>(value)?.into()),

            Type::PathExpression if value.is_array() => {
                // Path-expression arrays are stored like string arrays
                // (string-table indices), each entry parsed into an expression.
                self.stream.seek(value.payload())?;
                sdf::Value::PathExpressionVec(
                    self.read_string_vec()?
                        .iter()
                        .map(|text| sdf::PathExpression::parse(text))
                        .collect(),
                )
            }
            Type::PathExpression => {
                let expr = self.read_asset_path(value)?;
                sdf::Value::PathExpression(sdf::PathExpression::parse(&expr))
            }

            // An unregistered value wraps a nested, self-describing value,
            // which tells apart the three shapes C++ accepts here.
            Type::UnregisteredValue => {
                corrupt!(!value.is_inlined());
                self.stream.seek(value.payload())?;
                match self.read_nested_value()? {
                    sdf::Value::String(text) => sdf::Value::UnregisteredValue(text),
                    sdf::Value::Dictionary(entries) => sdf::Value::UnregisteredDictionary(entries),
                    list_op @ sdf::Value::UnregisteredValueListOp(_) => list_op,
                    _ => {
                        return Err(ReadError::corrupt(
                            "An unregistered value holds none of a string, a dictionary or a list op",
                        ));
                    }
                }
            }
            Type::UnregisteredValueListOp => {
                corrupt!(!value.is_inlined());
                let list = self.read_list_op(value, Self::read_unregistered_items)?;
                sdf::Value::UnregisteredValueListOp(list)
            }

            Type::Relocates => {
                corrupt!(!value.is_inlined());
                self.stream.seek(value.payload())?;
                let count = self.stream.read_count()?;
                let mut pairs = Vec::with_capacity(count.min(1024));
                for _ in 0..count {
                    let src_idx: u32 = self.stream.read_pod()?;
                    let tgt_idx: u32 = self.stream.read_pod()?;
                    let src = indexed(&self.file.paths, src_idx as usize, "path")?.clone();
                    let tgt = indexed(&self.file.paths, tgt_idx as usize, "path")?.clone();
                    pairs.push((src, tgt));
                }
                sdf::Value::Relocates(pairs)
            }

            Type::Invalid => return Err(ReadError::unsupported(format!("Unsupported value type: {ty}"))),
        };

        Ok(variant)
    }
}

enum ArrayKind {
    Ints,
    Floats,
    Other,
}

/// The section table at `toc_offset`.
fn read_sections(stream: &mut Stream<'_>, toc_offset: u64) -> Result<Vec<Section>, ReadError> {
    stream.seek(toc_offset)?;

    let count = stream.read_count()?;
    corrupt!(count > 0, "Crate file has no sections");
    corrupt!(count < 64, "Suspiciously large number of sections: {count}");

    stream.read_vec::<Section>(count)
}

/// Fills `paths` from the three encoded PATHS tables, each element named by
/// `tokens`.
fn build_compressed_paths(
    paths: &mut [sdf::Path],
    tokens: &[String],
    path_indexes: &[u32],
    element_token_indexes: &[i32],
    jumps: &[i32],
) -> Result<(), ReadError> {
    // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L3760
    //
    // The inner loop walks a child chain; a node that has both a child and a
    // jump-addressed sibling pushes that sibling subtree onto an explicit
    // stack, so stack frames stay bounded by namespace depth (the child
    // chain) while namespace width fans out through the queue. C++
    // `_BuildDecompressedPathsImpl` does the same, dispatching each sibling
    // subtree to a `WorkDispatcher` task.
    //
    // TODO(rayon): this decoder is performance-critical — it runs for every
    // loaded layer and dominates open time on large scenes. The deferred
    // sibling subtrees are independent and should be decoded in parallel, as
    // the C++ WorkDispatcher does.
    //
    // TODO(perf): the append_property / append_variant_segment calls below
    // validate each element token; if the PATHS decode shows in large-scene
    // profiles, add a pub(crate) unchecked single-element append for
    // machine-written crate files.
    //
    // TODO(diagnostics): a single malformed element token fails the whole
    // file load. C++ posts an error and skips the unaddressable subtree;
    // matching that needs a layer-open diagnostics channel to carry the
    // partial-load errors. The same channel would let the traversals that
    // today skip unaddressable authored names silently — the connection
    // graph and collection walks in `usd`, and the layer-registry variant
    // walk — surface each skipped entry as a warning.
    // Nothing to decode when the PATHS section is empty.
    if path_indexes.is_empty() {
        return Ok(());
    }

    let mut pending = vec![(0usize, sdf::Path::default())];

    while let Some((mut current_index, mut parent_path)) = pending.pop() {
        loop {
            let index = current_index;
            current_index += 1;

            if parent_path.is_empty() {
                parent_path = sdf::Path::new("/")?;
                checked_path_slot(paths, index)?;
                paths[index] = parent_path.clone();
            } else {
                let token_index = *indexed(element_token_indexes, index, "path element")?;
                let is_prim_property_path = token_index < 0;
                let token_index = token_index.unsigned_abs() as usize;
                let element_token = indexed(tokens, token_index, "token")?.as_str();

                let slot = *indexed(path_indexes, index, "path")? as usize;
                checked_path_slot(paths, slot)?;
                paths[slot] = if is_prim_property_path {
                    parent_path.append_property(element_token)?
                } else if element_token.starts_with('{') {
                    // Variant segments are appended directly without a separator
                    // to produce canonical paths like /Prim{set=sel}.
                    parent_path.append_variant_segment(element_token)?
                } else {
                    parent_path.append_path(element_token)?
                };
            }

            let jump = *indexed(jumps, index, "path jump")?;
            let has_child = jump > 0 || jump == -1;
            let has_sibling = jump >= 0;

            if has_child {
                if has_sibling {
                    let sibling_index = index + jump as usize;
                    // Siblings share this node's parent; defer the subtree.
                    pending.push((sibling_index, parent_path.clone()));
                }

                // Descend into the child (the next sequential entry) under
                // this node's path.
                let slot = *indexed(path_indexes, index, "path")? as usize;
                parent_path = indexed(paths, slot, "path")?.clone();
            }

            if !has_child && !has_sibling {
                break;
            }
        }
    }

    Ok(())
}

/// The section called `name` among `sections`.
fn section_named<'a>(sections: &'a [Section], name: &str) -> Option<&'a Section> {
    sections.iter().find(|s| s.name() == name)
}

/// Looks up `table[index]`, reporting an out-of-range index — a corrupt
/// crate — as the error the caller propagates instead of panicking.
fn indexed<'a, T>(table: &'a [T], index: usize, what: &'static str) -> Result<&'a T, ReadError> {
    table
        .get(index)
        .ok_or_else(|| ReadError::corrupt(format!("{what} index {index} out of range ({} entries)", table.len())))
}

/// Checks that `slot` addresses an entry of the decoded path table before it
/// is written, so a corrupt jump table cannot write out of bounds.
fn checked_path_slot(paths: &[sdf::Path], slot: usize) -> Result<(), ReadError> {
    indexed(paths, slot, "path")?;
    Ok(())
}

/// Pixar's `GfQuat<T>` stores components on disk as `[x, y, z, w]` (imaginary fields first,
/// Reorder each element from on-disk `[x, y, z, w]` to `(w, x, y, z)` so
/// `Value::Quat*` is always `(real, i, j, k)` regardless of whether the value
/// came from USDC or USDA. Pixar's `GfQuat<T>` declares `_imaginary:
/// GfVec3<T>` before `T _real`, so on-disk bytes are `[x, y, z, w]`.
fn xyzw_to_wxyz_quatf(v: Vec<[f32; 4]>) -> Vec<gf::Quatf> {
    v.into_iter().map(|q| gf::quatf(q[3], q[0], q[1], q[2])).collect()
}

fn xyzw_to_wxyz_quatd(v: Vec<[f64; 4]>) -> Vec<gf::Quatd> {
    v.into_iter().map(|q| gf::quatd(q[3], q[0], q[1], q[2])).collect()
}

fn xyzw_to_wxyz_quath(v: Vec<[f16; 4]>) -> Vec<gf::Quath> {
    v.into_iter().map(|q| gf::quath(q[3], q[0], q[1], q[2])).collect()
}

fn to_vec<T: From<i8>, const N: usize>(data: [i8; N]) -> [T; N] {
    data.map(T::from)
}

fn to_mat_diag<const N: usize, const M: usize>(data: [i8; N]) -> [f64; M] {
    let mut matrix = [0_f64; M];
    for i in 0..N {
        matrix[i * N + i] = data[i] as f64;
    }
    matrix
}

fn decompress_lz4(input: &[u8], output: &mut [u8]) -> Result<usize, ReadError> {
    // Check first byte for # chunks.
    // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/base/tf/fastCompression.cpp#L108

    let (&chunks, input) = input
        .split_first()
        .ok_or_else(|| ReadError::corrupt("lz4 block has no chunk count"))?;

    if chunks == 0 {
        let size = lz4_flex::decompress_into(input, output)?;

        Ok(size)
    } else {
        // Decompress chunk by chunk.
        // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/base/tf/fastCompression.cpp#L125

        Err(ReadError::unsupported("Support lz4 chunked decompression"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Result;
    use crate::usdc;
    use std::fs;
    use std::io;
    use std::ops::Range;

    /// A relationship with a deeply nested target compresses to fewer bytes
    /// than the number of entries in its path table.
    fn compact_paths() -> Result<(Vec<u8>, sdf::Path)> {
        let mut target = sdf::Path::abs_root();
        for _ in 0..1000 {
            target = target.append_path("X")?;
        }
        let mut data = sdf::Data::new();
        data.create_spec(sdf::Path::abs_root(), sdf::SpecType::PseudoRoot)
            .add("primChildren", sdf::Value::token_vec(["P"]));
        let prim = data.create_spec(sdf::Path::new("/P")?, sdf::SpecType::Prim);
        prim.add("specifier", sdf::Value::Specifier(sdf::Specifier::Def));
        prim.add("propertyChildren", sdf::Value::token_vec(["link"]));
        data.create_spec(sdf::Path::new("/P.link")?, sdf::SpecType::Relationship)
            .add(
                "targetPaths",
                sdf::Value::PathListOp(sdf::PathListOp::explicit([target.clone()])),
            );
        let mut output = io::Cursor::new(Vec::new());
        usdc::CrateWriter::write(&data, &mut output)?;
        Ok((output.into_inner(), target))
    }

    #[test]
    fn compact_paths_roundtrip() -> Result<()> {
        let (bytes, target) = compact_paths()?;
        let size = bytes.len();
        let file = CrateFile::open(bytes)?;
        assert!(file.paths.len() > size, "more path entries than file bytes");
        let value = file
            .fields
            .iter()
            .find(|field| file.tokens[field.token_index] == "targetPaths")
            .expect("relationship targets")
            .value_rep;
        let targets = file.value(value)?.try_as_path_list_op().expect("path list");
        assert_eq!(targets.explicit_items, vec![target]);
        Ok(())
    }

    #[test]
    fn empty_path_slot() -> Result<()> {
        let (mut bytes, _) = compact_paths()?;
        let file = CrateFile::open(bytes.clone())?;
        let start = section_named(&file.sections, Section::PATHS)
            .expect("paths section")
            .start as usize;
        let count = file.paths.len();
        bytes[start..start + 8].copy_from_slice(&((count + 1) as u64).to_le_bytes());
        let decoded = CrateFile::open(bytes)?;
        assert_eq!(decoded.paths.len(), count + 1);
        assert!(decoded.paths[count].is_empty());
        Ok(())
    }

    #[test]
    fn invalid_path_counts() -> Result<()> {
        let (bytes, _) = compact_paths()?;
        let file = CrateFile::open(bytes.clone())?;
        let start = section_named(&file.sections, Section::PATHS)
            .expect("paths section")
            .start as usize;
        for count in [0, file.paths.len() as u64 + 2, u64::MAX] {
            let mut damaged = bytes.clone();
            damaged[start..start + 8].copy_from_slice(&count.to_le_bytes());
            let error = CrateFile::open(damaged).expect_err("invalid slot count");
            assert!(format!("{error:?}").contains("path table has"), "{error:?}");
        }
        Ok(())
    }

    #[test]
    fn integer_compressed_float_fixture_uses_i_encoding() -> Result<()> {
        let file = CrateFile::open(fs::read("fixtures/integer_compressed_floats.usdc")?)?;
        let value = file
            .fields
            .iter()
            .find_map(|field| {
                let ty = field.value_rep.ty().ok()?;
                (file.tokens[field.token_index] == "default"
                    && ty == Type::Float
                    && field.value_rep.is_array()
                    && field.value_rep.is_compressed())
                .then_some(field.value_rep)
            })
            .expect("fixture must contain one compressed float default value");

        let mut decoder = Decoder::new(&file);
        decoder.stream.seek(value.payload())?;
        let (count, compressed) = decoder.unpack_array_len(value, ArrayKind::Floats)?;
        assert_eq!(count, 16);
        assert!(compressed);
        assert_eq!(decoder.stream.read_pod::<u8>()?, b'i');
        Ok(())
    }

    /// Every read is bounded by the stream: a take, a seek or a jump past
    /// either end is corrupt, never a panic, and a vector whose byte size
    /// overflows is refused before it is allocated.
    #[test]
    fn stream_bounds() {
        let bytes = [1u8, 2, 3, 4, 5, 6, 7, 8];
        let mut stream = Stream::new(&bytes);
        assert_eq!(stream.read_pod::<u32>().unwrap(), u32::from_le_bytes([1, 2, 3, 4]));
        assert!(stream.take(5).is_err());
        assert_eq!(stream.take(4).unwrap(), &[5, 6, 7, 8]);
        assert!(stream.take(1).is_err());
        assert!(stream.seek(9).is_err());
        stream.seek(8).unwrap();
        assert!(stream.skip(1).is_err());
        assert!(stream.skip(-9).is_err());
        assert!(stream.skip(i64::MIN).is_err());
        stream.skip(-8).unwrap();
        assert_eq!(stream.position(), 0);
        assert!(stream.read_vec::<[f64; 16]>(usize::MAX / 8).is_err());
        assert!(stream.read_vec::<u8>(9).is_err());
        assert_eq!(stream.read_vec::<u8>(8).unwrap(), bytes);
    }

    /// A time-sample block whose sample points back at the block itself is
    /// corrupt, not a stack overflow: the recursion guard covers every nested
    /// decode, time samples included.
    #[test]
    fn time_samples_cycle() -> Result<()> {
        let (bytes, _) = compact_paths()?;
        let file = CrateFile::open(bytes)?;
        let rep = |ty: Type, payload: u64| ValueRep(((ty as u64) << 48) | payload);
        let samples = rep(Type::TimeSamples, 0);
        assert_eq!(samples.ty()?, Type::TimeSamples);
        let times = rep(Type::DoubleVector, 40);
        assert_eq!(times.ty()?, Type::DoubleVector);
        // The block: the jump to the times rep, the times rep, the jump to
        // the sample reps, their count, the one sample rep (the block's own),
        // then the times array the times rep points at.
        let mut block = Vec::new();
        block.extend_from_slice(&8i64.to_le_bytes());
        block.extend_from_slice(&times.0.to_le_bytes());
        block.extend_from_slice(&8i64.to_le_bytes());
        block.extend_from_slice(&1u64.to_le_bytes());
        block.extend_from_slice(&samples.0.to_le_bytes());
        block.extend_from_slice(&1u64.to_le_bytes());
        block.extend_from_slice(&0f64.to_le_bytes());
        let mut decoder = Decoder {
            file: &file,
            stream: Stream::new(&block),
            unpacking: Vec::new(),
        };
        let error = decoder.decode(samples).expect_err("a self-referencing time sample");
        assert!(format!("{error:?}").contains("recursively"), "{error:?}");
        Ok(())
    }

    #[test]
    fn test_read_crate_struct() {
        let path = concat!(
            env!("CARGO_WORKSPACE_DIR"),
            "vendor/usd-wg-assets/full_assets/ElephantWithMonochord/SoC-ElephantWithMonochord.usdc"
        );
        if fs::metadata(path).is_err() {
            eprintln!("Skipping test_read_crate_struct: fixture not available at {path}");
            return;
        }

        let bytes = fs::read(path).expect("Failed to read crate file");
        let file = CrateFile::open(bytes).expect("Failed to read crate file");

        assert_eq!(file.sections.len(), 6);

        file.sections.iter().for_each(|section| {
            assert!(!section.name().is_empty());
            assert_ne!(section.start, 0_u64);
            assert_ne!(section.size, 0_u64);
        });

        assert_eq!(file.tokens.len(), 192);

        assert_eq!(file.fields.len(), 158);

        file.fields.iter().for_each(|field| {
            // Make sure each value rep has a valid type and cab be parsed.
            let _ = field.value_rep.ty().unwrap();
            // Make sure each token index is valid.
            let _ = file.tokens[field.token_index];
        });

        assert_eq!(file.fieldsets.len(), 577);
        assert_eq!(file.paths.len(), 248);
        assert_eq!(file.specs.len(), 248);

        assert!(file.validate().is_ok());
    }

    /// The span from the first section of `file` to the end of its last.
    fn section_span(file: &CrateFile) -> Range<usize> {
        let start = file.sections.iter().map(|section| section.start).min().unwrap();
        let end = file
            .sections
            .iter()
            .map(|section| section.start + section.size)
            .max()
            .unwrap();
        start as usize..end as usize
    }

    /// A crate holding the prim `/P` with one attribute, `name`, of type
    /// `type_name` and default `default`.
    fn attribute_crate(name: &str, type_name: &str, default: sdf::Value) -> Result<Vec<u8>> {
        let mut data = sdf::Data::new();
        data.create_spec(sdf::Path::abs_root(), sdf::SpecType::PseudoRoot)
            .add("primChildren", sdf::Value::token_vec(["P"]));
        let prim = data.create_spec(sdf::Path::new("/P")?, sdf::SpecType::Prim);
        prim.add("specifier", sdf::Value::Specifier(sdf::Specifier::Def));
        prim.add("propertyChildren", sdf::Value::token_vec([name]));
        let attribute = data.create_spec(sdf::Path::new("/P")?.append_property(name)?, sdf::SpecType::Attribute);
        attribute.add("typeName", sdf::Value::Token(type_name.into()));
        attribute.add("default", default);
        let mut output = io::Cursor::new(Vec::new());
        usdc::CrateWriter::write(&data, &mut output)?;
        Ok(output.into_inner())
    }

    /// An integer array is compressed from sixteen elements on, the size
    /// below which a C++ reader takes it as stored uncompressed, and both
    /// forms read back.
    #[test]
    fn int_array_compression_threshold() -> Result<()> {
        for (len, compressed) in [(4, false), (15, false), (16, true), (40, true)] {
            let values: Vec<i32> = (0..len).collect();
            let file = CrateFile::open(attribute_crate("ids", "int[]", sdf::Value::IntVec(values.clone()))?)?;
            let rep = file
                .fields
                .iter()
                .map(|field| field.value_rep)
                .find(|rep| rep.is_array() && rep.ty().is_ok_and(|ty| ty == Type::Int))
                .expect("the integer array");
            assert_eq!(rep.is_compressed(), compressed, "{len} elements");
            assert_eq!(file.value(rep)?, sdf::Value::IntVec(values), "{len} elements");
        }
        Ok(())
    }

    /// A crate long enough for its bytes to be advised when it is opened:
    /// one attribute holding an array past [`MIN_ADVISED_BYTES`].
    fn long_crate() -> Result<Vec<u8>> {
        let weights = sdf::Value::FloatVec(vec![0.5; MIN_ADVISED_BYTES / 4 + 1]);
        attribute_crate("weights", "float[]", weights)
    }

    /// A crate shorter than the threshold is opened without advice.
    #[test]
    fn short_crate_not_advised() -> Result<()> {
        let (bytes, _) = compact_paths()?;
        assert!(bytes.len() < MIN_ADVISED_BYTES);
        let (buffer, log) = ar::tests::recording_source(bytes, true);
        CrateFile::open(buffer)?;
        assert!(log.lock().unwrap().is_empty());
        Ok(())
    }

    /// Opening a crate over shared bytes advises them: random access over
    /// the crate, the span of its sections as needed, then the default.
    #[test]
    fn open_advises_sections() -> Result<()> {
        let bytes = long_crate()?;
        let len = bytes.len();
        let (buffer, log) = ar::tests::recording_source(bytes.clone(), true);
        let file = CrateFile::open(buffer)?;
        let span = section_span(&file);
        assert!(span.start > 0 && span.end <= len);
        assert_eq!(
            *log.lock().unwrap(),
            [
                (0..len, ar::Advice::Random),
                (span, ar::Advice::WillNeed),
                (0..len, ar::Advice::Normal),
            ]
        );
        assert_eq!(file.tokens, CrateFile::open(bytes)?.tokens);
        Ok(())
    }

    /// A crate inside a larger buffer, as a package entry is, advises its
    /// own range of the buffer.
    #[test]
    fn open_advises_own_range() -> Result<()> {
        let bytes = long_crate()?;
        let len = bytes.len();
        let mut package = vec![0u8; 64];
        package.extend_from_slice(&bytes);
        package.extend_from_slice(&[0u8; 32]);
        let (buffer, log) = ar::tests::recording_source(package, true);
        let file = CrateFile::open(buffer.slice(64..64 + len).expect("in range"))?;
        let span = section_span(&file);
        assert_eq!(
            *log.lock().unwrap(),
            [
                (64..64 + len, ar::Advice::Random),
                (64 + span.start..64 + span.end, ar::Advice::WillNeed),
                (64..64 + len, ar::Advice::Normal),
            ]
        );
        Ok(())
    }

    /// A crate that fails to open leaves its bytes under the default advice,
    /// whether the read fails before the sections are located or after.
    #[test]
    fn failed_open_restores_advice() -> Result<()> {
        let bytes = long_crate()?;
        let span = section_span(&CrateFile::open(bytes.clone())?);

        // The section table is past the end: the read fails locating it.
        let truncated = bytes[..bytes.len() - 8].to_vec();
        let len = truncated.len();
        let (buffer, log) = ar::tests::recording_source(truncated, true);
        assert!(CrateFile::open(buffer).is_err());
        assert_eq!(
            *log.lock().unwrap(),
            [(0..len, ar::Advice::Random), (0..len, ar::Advice::Normal)]
        );

        // The first section's bytes are garbage: the read fails inside it.
        let mut garbled = bytes;
        garbled[span.start..span.start + 16].fill(0xFF);
        let len = garbled.len();
        let (buffer, log) = ar::tests::recording_source(garbled, true);
        assert!(CrateFile::open(buffer).is_err());
        assert_eq!(
            *log.lock().unwrap(),
            [
                (0..len, ar::Advice::Random),
                (span, ar::Advice::WillNeed),
                (0..len, ar::Advice::Normal),
            ]
        );
        Ok(())
    }
}
