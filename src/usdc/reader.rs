//! Binary crate file reader.

use std::{
    any::type_name,
    collections::HashMap,
    io::{self, Cursor},
    mem, str, vec,
};

use anyhow::{bail, ensure, Context, Result};
use bytemuck::{bytes_of, bytes_of_mut, cast_slice_mut, AnyBitPattern, NoUninit, Pod};
use half::f16;
use num_traits::{AsPrimitive, Float, PrimInt};

use crate::{
    sdf::{self, Value},
    usdc::coding,
};

use super::layout::*;

// Currently supported USDC version.
// See <https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L340>
const SW_VERSION: Version = version(0, 10, 0);

/// Crate file represents structural data loaded from a USDC file on disk.
#[derive(Debug)]
pub struct CrateFile<R> {
    /// File reader.
    reader: R,

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

impl<R> CrateFile<R> {
    /// Returns file's version extracted from bootstrap header.
    #[inline]
    pub fn version(&self) -> Version {
        Version::from(self.bootstrap)
    }
}

impl<R: io::Read + io::Seek> CrateFile<R> {
    /// Read structural sections of a crate file.
    pub fn open(mut reader: R) -> Result<Self> {
        let bootstrap = Self::read_header(&mut reader)?;

        let mut file = CrateFile {
            reader,
            bootstrap,
            sections: Vec::new(),
            tokens: Vec::new(),
            strings: Vec::new(),
            fields: Vec::new(),
            fieldsets: Vec::new(),
            paths: Vec::new(),
            specs: Vec::new(),
        };

        file.read_sections().context("Unable to read sections")?;
        file.read_tokens().context("Unable to read TOKENS section")?;
        file.read_strings().context("Unable to read STRINGS section")?;
        file.read_fields().context("Unable to read FIELDS section")?;
        file.read_fieldsets().context("Unable to read FIELDSETS section")?;
        file.read_paths().context("Unable to read PATHS section")?;
        file.read_specs().context("Unable to read SPECS section")?;

        Ok(file)
    }

    /// Sanity check of structural validity.
    /// Roughly corresponds to `PXR_PREFER_SAFETY_OVER_SPEED` define in USD.
    pub fn validate(&self) -> Result<()> {
        // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L3268
        self.fields.iter().enumerate().try_for_each(|(index, field)| {
            self.tokens
                .get(field.token_index)
                .with_context(|| format!("Invalid field token index {}: {}", index, field.token_index))?;

            anyhow::Ok(())
        })?;

        self.fieldsets
            .iter()
            .enumerate()
            .filter_map(|(i, index)| index.map(|index| (i, index)))
            .try_for_each(|(index, fieldset)| {
                self.fields
                    .get(fieldset)
                    .with_context(|| format!("Invalid fieldset index {index}: {fieldset}"))?;

                anyhow::Ok(())
            })?;

        self.specs.iter().enumerate().try_for_each(|(index, spec)| {
            self.paths
                .get(spec.path_index)
                .with_context(|| format!("Invalid spec {} path index: {}", index, spec.path_index))?;

            self.fieldsets
                .get(spec.fieldset_index)
                .with_context(|| format!("Invalid spec {} fieldset index: {}", index, spec.fieldset_index))?;

            // Additionally, a fieldSetIndex must either be 0, or the element at
            // the prior index must be a default-constructed FieldIndex.
            // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L3289

            if spec.fieldset_index > 0 {
                ensure!(
                    self.fieldsets[spec.fieldset_index - 1].is_none(),
                    "Invalid spec {}, the element at the prior index {} must be a default-constructed field index",
                    index,
                    spec.fieldset_index
                );
            }

            ensure!(spec.spec_type != sdf::SpecType::Unknown, "Invalid spec {index} type");

            anyhow::Ok(())
        })?;

        Ok(())
    }

    /// Read and verify bootstrap header, retrieve offset to TOC.
    fn read_header(mut reader: impl io::Read + io::Seek) -> Result<Bootstrap> {
        let header = reader.read_pod::<Bootstrap>()?;

        ensure!(header.ident.eq(b"PXR-USDC"), "Usd crate bootstrap section corrupt");

        ensure!(header.toc_offset > 0, "Invalid TOC offset");

        let file_ver = version(header.version[0], header.version[1], header.version[2]);

        ensure!(
            SW_VERSION.can_read(file_ver),
            "Usd crate version mismatch, file is {file_ver}, library supports {SW_VERSION}"
        );

        Ok(header)
    }

    fn read_sections(&mut self) -> Result<()> {
        self.set_position(self.bootstrap.toc_offset)?;

        let count = self.reader.read_count()?;
        ensure!(count > 0, "Crate file has no sections");
        ensure!(count < 64, "Suspiciously large number of sections: {count}");

        self.sections = self.reader.read_vec::<Section>(count)?;

        Ok(())
    }

    fn read_tokens(&mut self) -> Result<()> {
        let Some(section) = self.find_section(Section::TOKENS) else {
            return Ok(());
        };

        self.set_position(section.start)?;

        let file_ver = self.version();

        // Read the number of tokens.
        let count = self.reader.read_count()?;

        self.tokens = if file_ver < version(0, 4, 0) {
            todo!("Support TOKENS reader for < 0.4.0 files");
        } else {
            let uncompressed_size = self.reader.read_count()?;
            let mut buffer = self.read_compressed(uncompressed_size)?;

            ensure!(
                buffer.len() == uncompressed_size,
                "Decompressed size mismatch (expected {}, got {})",
                uncompressed_size,
                buffer.len(),
            );

            ensure!(
                buffer.last() == Some(&b'\0'),
                "Tokens section not null-terminated in crate file"
            );

            // Pop last \0 byte to split strings without empty one at the end.
            buffer.pop();

            let strings = buffer
                .split(|c| *c == b'\0')
                .map(|buf| str::from_utf8(buf).map(|str| str.to_string()))
                .collect::<Result<Vec<_>, str::Utf8Error>>()
                .context("Failed to parse TOKENS section")?;

            ensure!(
                strings.len() == count,
                "Crate file claims {} tokens, but found {}",
                count,
                strings.len(),
            );

            strings
        };

        Ok(())
    }

    fn read_strings(&mut self) -> Result<()> {
        let Some(section) = self.find_section(Section::STRINGS) else {
            return Ok(());
        };

        self.set_position(section.start)?;

        let count = self.reader.read_count()?;
        ensure!(
            count < 128 * 1024 * 1024,
            "Suspiciously large number of strings: {count}"
        );

        let strings = self.reader.read_vec::<u32>(count)?;

        // These are indices, so convert to usize for convenience.
        self.strings = strings.into_iter().map(|offset| offset as usize).collect::<Vec<_>>();

        Ok(())
    }

    fn read_fields(&mut self) -> Result<()> {
        let Some(section) = self.find_section(Section::FIELDS) else {
            return Ok(());
        };

        self.set_position(section.start)?;

        let file_ver = self.version();

        self.fields = if file_ver < version(0, 4, 0) {
            todo!("Support FIELDS reader before < 0.4.0")
        } else {
            let field_count = self.reader.read_count()?;

            // Compressed fields in 0.4.0.
            let indices = self.read_encoded_ints(field_count)?;

            // Compressed value reps.
            let reps = self.read_compressed(field_count)?;

            let fields: Vec<_> = indices
                .iter()
                .zip(reps.iter())
                .map(|(index, value)| Field::new(*index, *value))
                .collect();

            debug_assert_eq!(fields.len(), field_count);

            fields
        };

        Ok(())
    }

    fn read_fieldsets(&mut self) -> Result<()> {
        let Some(section) = self.find_section(Section::FIELDSETS) else {
            return Ok(());
        };

        self.set_position(section.start)?;

        let file_ver = self.version();

        self.fieldsets = if file_ver < version(0, 4, 0) {
            todo!("Support FIELDSETS reader for < 0.4.0 files");
        } else {
            let count = self.reader.read_count()?;

            let decoded = self.read_encoded_ints::<u32>(count)?;

            const INVALID_INDEX: u32 = u32::MAX;

            let sets = decoded
                .into_iter()
                .map(|i| if i == INVALID_INDEX { None } else { Some(i as usize) })
                .collect::<Vec<_>>();

            debug_assert_eq!(sets.len(), count);

            sets
        };

        Ok(())
    }

    fn read_paths(&mut self) -> Result<()> {
        let Some(section) = self.find_section(Section::PATHS) else {
            return Ok(());
        };

        self.set_position(section.start)?;

        let file_ver = self.version();

        if file_ver == version(0, 0, 1) {
            todo!("Support PATHS reader for == 0.0.1 files");
        } else if file_ver < version(0, 4, 0) {
            todo!("Support PATHS reader for < 0.4.0 files");
        } else {
            // Read # of paths.
            let path_count = self.reader.read_count()?;
            self.paths = vec![sdf::Path::default(); path_count];

            self.read_compressed_paths()?;
        };

        Ok(())
    }

    /// Read compressed paths.
    fn read_compressed_paths(&mut self) -> Result<()> {
        // Read number of encoded paths.
        let count: usize = self.reader.read_count()?;

        // Read compressed data.

        let path_indexes = self.read_encoded_ints::<u32>(count)?;
        debug_assert_eq!(path_indexes.len(), count);

        let element_token_indexes = self.read_encoded_ints::<i32>(count)?;
        debug_assert_eq!(element_token_indexes.len(), count);

        let jumps = self.read_encoded_ints::<i32>(count)?;
        debug_assert_eq!(jumps.len(), count);

        self.build_compressed_paths(&path_indexes, &element_token_indexes, &jumps, 0, sdf::Path::default())?;

        Ok(())
    }

    fn build_compressed_paths(
        &mut self,
        path_indexes: &[u32],
        element_token_indexes: &[i32],
        jumps: &[i32],
        mut current_index: usize,
        mut parent_path: sdf::Path,
    ) -> Result<()> {
        // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L3760

        let mut has_child;
        let mut has_sibling;

        loop {
            let this_index = current_index;
            current_index += 1;

            if parent_path.is_empty() {
                parent_path = sdf::Path::new("/")?;
                self.paths[this_index] = parent_path.clone();
            } else {
                let token_index = element_token_indexes[this_index];
                let is_prim_property_path = token_index < 0;
                let token_index = token_index.unsigned_abs() as usize;
                let element_token = self.tokens[token_index].as_str();

                self.paths[path_indexes[this_index] as usize] = if is_prim_property_path {
                    parent_path.append_property(element_token)?
                } else {
                    parent_path.append_path(element_token)?
                };
            }

            has_child = jumps[this_index] > 0 || jumps[this_index] == -1;
            has_sibling = jumps[this_index] >= 0;

            if has_child {
                if has_sibling {
                    let sibling_index = this_index + jumps[this_index] as usize;

                    self.build_compressed_paths(
                        path_indexes,
                        element_token_indexes,
                        jumps,
                        sibling_index,
                        parent_path,
                    )?;
                }

                // Have a child (may have also had a sibling).
                // Reset parent path.
                parent_path = self.paths[path_indexes[this_index] as usize].clone();
            }

            if !has_child && !has_sibling {
                break;
            }
        }

        Ok(())
    }

    fn read_specs(&mut self) -> Result<()> {
        let Some(section) = self.find_section(Section::SPECS) else {
            return Ok(());
        };

        self.set_position(section.start)?;

        let file_ver = self.version();

        self.specs = if file_ver == version(0, 0, 1) {
            todo!("Support SPECS reader for == 0.0.1 files");
        } else if file_ver < version(0, 4, 0) {
            todo!("Support SPECS reader for < 0.4.0 files");
        } else {
            // Version 0.4.0 specs are compressed

            let spec_count = self.reader.read_count()?;

            let mut specs = vec![Spec::default(); spec_count];

            // TODO: Might want to reuse temp buffer space here.

            // pathIndexes.
            let tmp = self.read_encoded_ints::<u32>(spec_count)?;
            for (i, path_index) in tmp.iter().enumerate() {
                specs[i].path_index = *path_index as usize;
            }

            // fieldSetIndexes.
            let tmp = self.read_encoded_ints::<u32>(spec_count)?;
            for (i, field_set_index) in tmp.iter().enumerate() {
                specs[i].fieldset_index = *field_set_index as usize;
            }

            // specTypes.
            let tmp = self.read_encoded_ints::<u32>(spec_count)?;
            for (i, spec_type) in tmp.iter().enumerate() {
                specs[i].spec_type = sdf::SpecType::from_repr(*spec_type)
                    .with_context(|| format!("Unable to parse SDF spec type: {spec_type}"))?;
            }

            specs
        };

        Ok(())
    }

    /// Find section by name.
    pub fn find_section(&self, name: &str) -> Option<&Section> {
        self.sections.iter().find(|s| s.name() == name)
    }

    fn resolve_string(&self, string_index: u32) -> String {
        let token = self.strings[string_index as usize];
        self.tokens[token].clone()
    }

    fn set_position(&mut self, position: u64) -> Result<()> {
        self.reader.seek(io::SeekFrom::Start(position))?;
        Ok(())
    }

    fn unpack_value<T: Default + Pod>(&mut self, value: ValueRep) -> Result<T> {
        ensure!(!value.is_array(), "Can't unpack array {value:?} as inline value");

        let ty = value.ty()?;
        ensure!(ty != Type::Invalid, "Invalid value type");

        // If the value is inlined, just decode it.
        let value = if value.is_inlined() {
            // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1590
            let tmp = value.payload() & ((1_u64 << (mem::size_of::<u32>() * 8)) - 1);
            let mut cursor = Cursor::new(bytes_of(&tmp));
            cursor.read_pod::<T>()?
        } else {
            // Otherwise we have to read it from the file.
            self.set_position(value.payload())?;
            self.reader.read_pod::<T>()?
        };

        Ok(value)
    }

    fn read_token(&mut self, value: ValueRep) -> Result<String> {
        let index: u64 = self.unpack_value(value)?;
        let value = self.tokens[index as usize].clone();

        Ok(value)
    }

    /// Reads a lz4 compressed data and returns decompressed raw bytes.
    ///
    /// Format expected:
    /// - u64 uncompressed size
    /// - lz4 compressed block of data.
    ///
    /// # Arguments:
    /// - `estimated_size`: Size enough to hold uncompressed data.
    fn read_compressed<T: Default + NoUninit + AnyBitPattern>(&mut self, estimated_count: usize) -> Result<Vec<T>> {
        // Read data to memory.
        let compressed_size = self.reader.read_count()?;
        let mut input = vec![0_u8; compressed_size];
        self.reader.read_exact(&mut input)?;

        // Decompress to output buffer.
        let mut output = vec![T::default(); estimated_count];
        let actual_size = decompress_lz4(&input, cast_slice_mut(&mut output))?;

        let actual_count = actual_size / mem::size_of::<T>();

        if actual_count < output.len() {
            output.truncate(actual_count);
        }

        Ok(output)
    }

    /// Reads sequence of compressed integers.
    fn read_encoded_ints<T: PrimInt + 'static>(&mut self, count: usize) -> Result<Vec<T>>
    where
        i64: AsPrimitive<T>,
    {
        let estimated_size = coding::encoded_buffer_size::<u32>(count);

        let buffer = self.read_compressed::<u8>(estimated_size)?;

        let ints = coding::decode_ints(buffer.as_slice(), count)?;
        debug_assert_eq!(ints.len(), count);

        Ok(ints)
    }

    const MIN_COMPRESSED_ARRAY_SIZE: usize = 4;

    // Implements various logic and compatibility checks to figure out the array length and whether it's compressed.
    fn unpack_array_len(&mut self, value: ValueRep, kind: ArrayKind) -> Result<(usize, bool)> {
        debug_assert!(!value.is_inlined());

        // Empty array.
        if value.payload() == 0 {
            return Ok((0, false));
        }

        self.set_position(value.payload())?;

        if self.version() < version(0, 5, 0) {
            // Read and discard shape size.
            let _ = self.reader.read_pod::<u32>()?;
        }

        // Detect compression.
        let mut compressed = true;
        match kind {
            ArrayKind::Ints => {
                // Version 0.5.0 introduced compressed int arrays.
                // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1935
                if self.version() < version(0, 5, 0) || !value.is_compressed() {
                    compressed = false;
                }
            }
            ArrayKind::Floats => {
                // Version 0.6.0 introduced compressed floating point arrays.
                // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1961C5-L1961C66
                if self.version() < version(0, 6, 0) || !value.is_compressed() {
                    compressed = false;
                }
            }
            ArrayKind::Other => {
                // Fallback to uncompressed.
                // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1868
                debug_assert!(!value.is_compressed());
                compressed = false;
            }
        }

        // Read the number of elements.
        let count = if self.version() < version(0, 7, 0) {
            self.reader.read_pod::<u32>()? as usize
        } else {
            self.reader.read_pod::<u64>()? as usize
        };

        if count < Self::MIN_COMPRESSED_ARRAY_SIZE {
            compressed = false;
        }

        Ok((count, compressed))
    }

    fn read_ints<T: PrimInt + Pod + Default>(&mut self, value: ValueRep) -> Result<Vec<T>>
    where
        i64: AsPrimitive<T>,
    {
        let (count, compressed) = self.unpack_array_len(value, ArrayKind::Ints)?;

        if count == 0 {
            return Ok(Vec::default());
        }

        if compressed {
            self.read_encoded_ints(count)
        } else {
            self.reader.read_vec(count)
        }
    }

    fn read_floats<T: Float + Default + Pod>(&mut self, value: ValueRep) -> Result<Vec<T>> {
        use num_traits::cast;
        ensure!(!value.is_inlined());

        let (count, compressed) = self.unpack_array_len(value, ArrayKind::Floats)?;

        let vec = if compressed {
            let code = self.reader.read_pod::<u8>()?;

            match code {
                // Compressed integers
                b'i' => {
                    let ints: Vec<i32> = self.read_compressed(count)?;
                    ints.into_iter().map(|i| cast(i).unwrap()).collect()
                }
                // Lookup table and indexes
                b't' => {
                    let lut_size = self.reader.read_pod::<u32>()? as usize;
                    let lut: Vec<T> = self.reader.read_vec(lut_size)?;

                    let indexes: Vec<u32> = self.read_encoded_ints(count)?;
                    ensure!(
                        indexes.len() == count,
                        "Read invalid number of indexes to decompress doubles array"
                    );

                    let mut output = vec![T::zero(); count];
                    for (i, index) in indexes.into_iter().enumerate() {
                        output[i] = lut[index as usize];
                    }

                    output
                }
                _ => bail!("Invalid compressed double array code: {code}"),
            }
        } else {
            self.reader.read_vec(count)?
        };

        Ok(vec)
    }

    fn read_list_op<T: Default + Clone + PartialEq>(
        &mut self,
        value: ValueRep,
        mut read: impl FnMut(&mut Self) -> Result<Vec<T>>,
    ) -> Result<sdf::ListOp<T>> {
        self.set_position(value.payload())?;

        let mut out = sdf::ListOp::<T>::default();

        let header = self.reader.read_pod::<ListOpHeader>()?;

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

    fn read_string_vec(&mut self) -> Result<Vec<String>> {
        let count = self.reader.read_count()?;
        let indices = self.reader.read_vec::<u32>(count)?;

        let vec = indices
            .into_iter()
            .map(|string_index| {
                let token_index = self.strings[string_index as usize];
                self.tokens[token_index].clone()
            })
            .collect();

        Ok(vec)
    }

    fn read_token_vec(&mut self) -> Result<Vec<String>> {
        let count = self.reader.read_count()?;
        let indices = self.reader.read_vec::<u32>(count)?;

        let vec = indices
            .into_iter()
            .map(|index| self.tokens[index as usize].clone())
            .collect();

        Ok(vec)
    }

    fn read_path_vec(&mut self) -> Result<Vec<sdf::Path>> {
        let count = self.reader.read_count()?;
        let indices = self.reader.read_vec::<u32>(count)?;

        let vec = indices
            .into_iter()
            .map(|index| self.paths[index as usize].clone())
            .collect();

        Ok(vec)
    }

    fn read_string(&mut self) -> Result<String> {
        let index = self.reader.read_pod::<u32>()?;
        let string = self.resolve_string(index);

        Ok(string)
    }

    fn read_path(&mut self) -> Result<sdf::Path> {
        let index = self.reader.read_pod::<u32>()?;
        let path = self.paths[index as usize].clone();

        Ok(path)
    }

    fn read_reference(&mut self) -> Result<sdf::Reference> {
        let asset_path = self.read_string()?;
        let prim_path = self.read_path()?;
        let layer_offset = self.reader.read_pod::<sdf::LayerOffset>()?;
        let custom_data = self.read_custom_data()?;

        Ok(sdf::Reference {
            asset_path,
            prim_path,
            layer_offset,
            custom_data,
        })
    }

    fn read_payload(&mut self) -> Result<sdf::Payload> {
        let asset_path = self.read_string()?;
        let prim_path = self.read_path()?;

        let mut payload = sdf::Payload {
            asset_path,
            prim_path,
            layer_offset: None,
        };

        // Layer offsets were added to SdfPayload starting in 0.8.0. Files
        // before that cannot have them.
        // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1214C41-L1214C41
        if self.version() >= version(0, 8, 0) {
            let layer_offset = self.reader.read_pod::<sdf::LayerOffset>()?;
            payload.layer_offset = Some(layer_offset);
        }

        Ok(payload)
    }

    fn read_custom_data(&mut self) -> Result<HashMap<String, Value>> {
        let mut count = self.reader.read_count()?;
        let mut dict = HashMap::default();

        while count > 0 {
            let key = self.read_string()?;

            let value = {
                // Read recursive offset.
                // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1100
                let offset = self.reader.read_pod::<i64>()?;

                // -8 to compensate sizeof(offset)
                // See https://github.com/syoyo/tinyusdz/blob/b14f625a776042a384743316236ee55685f144bf/src/crate-reader.cc#L1737C5-L1737C39
                self.reader.seek(io::SeekFrom::Current(offset - 8))?;

                let value = self.reader.read_pod::<ValueRep>()?;

                ensure!(value.ty()? != Type::Invalid, "Can't parse dictionary value type");
                ensure!(value.ty()? != Type::Dictionary, "Nested dictionaries are not supported");

                // Save current position.
                let saved_position = self.reader.stream_position()?;

                let value = self.value(value)?;

                // Restore position
                self.set_position(saved_position)?;

                value
            };

            dict.insert(key, value);
            count -= 1;
        }

        Ok(dict)
    }

    // Read an array of vectors.
    fn read_vec_array<T: Default + NoUninit + AnyBitPattern, const N: usize>(
        &mut self,
        value: ValueRep,
    ) -> Result<Vec<T>> {
        debug_assert!(value.is_array());
        debug_assert!(!value.is_compressed());

        let (count, _) = self.unpack_array_len(value, ArrayKind::Other)?;

        // Array allowed to be empty.
        if count == 0 {
            return Ok(Vec::default());
        }

        let value = self.reader.read_vec(count * N)?;

        Ok(value)
    }

    pub fn value(&mut self, value: ValueRep) -> Result<sdf::Value> {
        let ty = value.ty()?;
        ensure!(ty != Type::Invalid, "Invalid value type");

        let variant = match ty {
            //
            // Bool and chars
            //
            Type::Bool if value.is_array() => {
                let vec = self
                    .read_vec_array::<u8, 1>(value)?
                    .into_iter()
                    .map(|value| value != 0)
                    .collect();

                sdf::Value::BoolVec(vec)
            }

            Type::Bool => {
                let value: i32 = self.unpack_value(value)?;
                sdf::Value::Bool(value != 0)
            }

            Type::Uchar if value.is_array() => {
                let vec = self.read_vec_array::<u8, 1>(value)?;
                sdf::Value::UcharVec(vec)
            }

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
                ensure!(!value.is_inlined());

                self.set_position(value.payload())?;
                sdf::Value::StringVec(self.read_string_vec()?)
            }

            Type::String if value.is_array() => sdf::Value::StringVec(self.read_string_vec()?),

            Type::String => {
                ensure!(!value.is_array());

                let string_index = self.unpack_value::<u32>(value)?;
                sdf::Value::String(self.resolve_string(string_index))
            }
            Type::AssetPath => sdf::Value::AssetPath(self.read_token(value)?),

            Type::Token if value.is_array() => {
                let (count, _) = self.unpack_array_len(value, ArrayKind::Other)?;
                let mut tokens = Vec::with_capacity(count);

                if count > 0 {
                    let indices = self.reader.read_vec::<u32>(count)?;

                    for index in indices {
                        tokens.push(self.tokens[index as usize].clone());
                    }
                }

                sdf::Value::TokenVec(tokens)
            }
            Type::Token => sdf::Value::Token(self.read_token(value)?),

            //
            // Vectors (half, float, double, int + vec{2,3,4})
            //
            Type::Vec2h if value.is_array() => Value::Vec2h(self.read_vec_array::<f16, 2>(value)?),
            Type::Vec2f if value.is_array() => Value::Vec2f(self.read_vec_array::<f32, 2>(value)?),
            Type::Vec2d if value.is_array() => Value::Vec2d(self.read_vec_array::<f64, 2>(value)?),
            Type::Vec2i if value.is_array() => Value::Vec2i(self.read_vec_array::<i32, 2>(value)?),

            Type::Vec3h if value.is_array() => Value::Vec3h(self.read_vec_array::<f16, 3>(value)?),
            Type::Vec3f if value.is_array() => Value::Vec3f(self.read_vec_array::<f32, 3>(value)?),
            Type::Vec3d if value.is_array() => Value::Vec3d(self.read_vec_array::<f64, 3>(value)?),
            Type::Vec3i if value.is_array() => Value::Vec3i(self.read_vec_array::<i32, 3>(value)?),

            Type::Vec4h if value.is_array() => Value::Vec4h(self.read_vec_array::<f16, 4>(value)?),
            Type::Vec4f if value.is_array() => Value::Vec4f(self.read_vec_array::<f32, 4>(value)?),
            Type::Vec4d if value.is_array() => Value::Vec4d(self.read_vec_array::<f64, 4>(value)?),
            Type::Vec4i if value.is_array() => Value::Vec4i(self.read_vec_array::<i32, 4>(value)?),

            Type::Vec2h if value.is_inlined() => sdf::Value::Vec2h(to_vec::<f16, 2>(self.unpack_value(value)?)),
            Type::Vec2f if value.is_inlined() => sdf::Value::Vec2f(to_vec::<f32, 2>(self.unpack_value(value)?)),
            Type::Vec2d if value.is_inlined() => sdf::Value::Vec2d(to_vec::<f64, 2>(self.unpack_value(value)?)),
            Type::Vec2i if value.is_inlined() => sdf::Value::Vec2i(to_vec::<i32, 2>(self.unpack_value(value)?)),

            Type::Vec3h if value.is_inlined() => sdf::Value::Vec3h(to_vec::<f16, 3>(self.unpack_value(value)?)),
            Type::Vec3f if value.is_inlined() => sdf::Value::Vec3f(to_vec::<f32, 3>(self.unpack_value(value)?)),
            Type::Vec3d if value.is_inlined() => sdf::Value::Vec3d(to_vec::<f64, 3>(self.unpack_value(value)?)),
            Type::Vec3i if value.is_inlined() => sdf::Value::Vec3i(to_vec::<i32, 3>(self.unpack_value(value)?)),

            Type::Vec4h if value.is_inlined() => sdf::Value::Vec4h(to_vec::<f16, 4>(self.unpack_value(value)?)),
            Type::Vec4f if value.is_inlined() => sdf::Value::Vec4f(to_vec::<f32, 4>(self.unpack_value(value)?)),
            Type::Vec4d if value.is_inlined() => sdf::Value::Vec4d(to_vec::<f64, 4>(self.unpack_value(value)?)),
            Type::Vec4i if value.is_inlined() => sdf::Value::Vec4i(to_vec::<i32, 4>(self.unpack_value(value)?)),

            Type::Vec2h => sdf::Value::Vec2h(self.unpack_value::<[f16; 2]>(value)?.into()),
            Type::Vec2f => sdf::Value::Vec2f(self.unpack_value::<[f32; 2]>(value)?.into()),
            Type::Vec2d => sdf::Value::Vec2d(self.unpack_value::<[f64; 2]>(value)?.into()),
            Type::Vec2i => sdf::Value::Vec2i(self.unpack_value::<[i32; 2]>(value)?.into()),

            Type::Vec3h => sdf::Value::Vec3h(self.unpack_value::<[f16; 3]>(value)?.into()),
            Type::Vec3f => sdf::Value::Vec3f(self.unpack_value::<[f32; 3]>(value)?.into()),
            Type::Vec3d => sdf::Value::Vec3d(self.unpack_value::<[f64; 3]>(value)?.into()),
            Type::Vec3i => sdf::Value::Vec3i(self.unpack_value::<[i32; 3]>(value)?.into()),

            Type::Vec4h => sdf::Value::Vec4h(self.unpack_value::<[f16; 4]>(value)?.into()),
            Type::Vec4f => sdf::Value::Vec4f(self.unpack_value::<[f32; 4]>(value)?.into()),
            Type::Vec4d => sdf::Value::Vec4d(self.unpack_value::<[f64; 4]>(value)?.into()),
            Type::Vec4i => sdf::Value::Vec4i(self.unpack_value::<[i32; 4]>(value)?.into()),

            //
            // Matrices
            //
            Type::Matrix2d if value.is_array() => Value::Matrix2d(self.read_vec_array::<f64, 4>(value)?),
            Type::Matrix3d if value.is_array() => Value::Matrix3d(self.read_vec_array::<f64, 9>(value)?),
            Type::Matrix4d if value.is_array() => Value::Matrix4d(self.read_vec_array::<f64, 16>(value)?),

            Type::Matrix2d if value.is_inlined() => sdf::Value::Matrix2d(to_mat_diag::<2>(self.unpack_value(value)?)),
            Type::Matrix3d if value.is_inlined() => sdf::Value::Matrix2d(to_mat_diag::<3>(self.unpack_value(value)?)),
            Type::Matrix4d if value.is_inlined() => sdf::Value::Matrix2d(to_mat_diag::<4>(self.unpack_value(value)?)),

            Type::Matrix2d => sdf::Value::Matrix2d(self.unpack_value::<[f64; 4]>(value)?.into()),
            Type::Matrix3d => sdf::Value::Matrix3d(self.unpack_value::<[f64; 9]>(value)?.into()),
            Type::Matrix4d => sdf::Value::Matrix4d(self.unpack_value::<[f64; 16]>(value)?.into()),

            //
            // Quats
            //
            Type::Quath if value.is_array() => Value::Quath(self.read_vec_array::<f16, 4>(value)?),
            Type::Quath => sdf::Value::Quath(self.unpack_value::<[f16; 4]>(value)?.into()),

            Type::Quatf if value.is_array() => Value::Quatf(self.read_vec_array::<f32, 4>(value)?),
            Type::Quatf => sdf::Value::Quatf(self.unpack_value::<[f32; 4]>(value)?.into()),

            Type::Quatd if value.is_array() => Value::Quatd(self.read_vec_array::<f64, 4>(value)?),
            Type::Quatd => sdf::Value::Quatd(self.unpack_value::<[f64; 4]>(value)?.into()),

            //
            // ListOp
            //
            Type::TokenListOp => {
                ensure!(!value.is_inlined());

                let list = self.read_list_op(value, |file: &mut Self| file.read_token_vec())?;
                sdf::Value::TokenListOp(list)
            }
            Type::StringListOp => {
                ensure!(!value.is_inlined());

                let list = self.read_list_op(value, |file: &mut Self| file.read_string_vec())?;
                sdf::Value::StringListOp(list)
            }
            Type::PathListOp => {
                ensure!(!value.is_inlined());

                let list = self.read_list_op(value, |file: &mut Self| file.read_path_vec())?;
                sdf::Value::PathListOp(list)
            }
            Type::ReferenceListOp => {
                ensure!(!value.is_inlined());

                let list = self.read_list_op(value, |file: &mut Self| {
                    let count = file.reader.read_count()?;
                    let mut vec = Vec::with_capacity(count);

                    for _ in 0..count {
                        let reference = file.read_reference()?;
                        vec.push(reference);
                    }

                    Ok(vec)
                })?;

                sdf::Value::ReferenceListOp(list)
            }

            //
            // SDF types
            //
            Type::TokenVector => {
                ensure!(!value.is_inlined());

                self.set_position(value.payload())?;

                let tokens = self.read_token_vec()?;
                sdf::Value::TokenVec(tokens)
            }

            Type::Specifier => {
                let tmp: i32 = self.unpack_value(value)?;
                let specifier =
                    sdf::Specifier::from_repr(tmp).with_context(|| format!("Unable to parse SDF specifier: {tmp}"))?;

                sdf::Value::Specifier(specifier)
            }

            Type::Permission => {
                let tmp: i32 = self.unpack_value(value)?;
                let permission =
                    sdf::Permission::from_repr(tmp).with_context(|| format!("Unable to parse permission: {tmp}"))?;

                sdf::Value::Permission(permission)
            }

            Type::Variability => {
                let tmp: i32 = self.unpack_value(value)?;
                let variability =
                    sdf::Variability::from_repr(tmp).with_context(|| format!("Unable to parse variability: {tmp}"))?;

                sdf::Value::Variability(variability)
            }

            Type::LayerOffsetVector => {
                ensure!(!value.is_inlined());
                ensure!(!value.is_array());
                ensure!(!value.is_compressed());

                self.set_position(value.payload())?;

                let count = self.reader.read_count()?;
                let vec = self.reader.read_vec(count)?;

                sdf::Value::LayerOffsetVec(vec)
            }

            Type::Payload => {
                ensure!(!value.is_inlined());
                ensure!(!value.is_array());
                ensure!(!value.is_compressed());

                self.set_position(value.payload())?;

                let payload = self.read_payload()?;
                sdf::Value::Payload(payload)
            }

            Type::PayloadListOp => {
                let list = self.read_list_op(value, |file: &mut Self| {
                    let count = file.reader.read_count()?;
                    let mut vec = Vec::with_capacity(count);
                    for _ in 0..count {
                        let payload = file.read_payload()?;
                        vec.push(payload);
                    }

                    Ok(vec)
                })?;

                sdf::Value::PayloadListOp(list)
            }

            Type::VariantSelectionMap => {
                ensure!(!value.is_inlined());
                ensure!(!value.is_array());
                ensure!(!value.is_compressed());

                self.set_position(value.payload())?;

                let mut count = self.reader.read_count()?;
                let mut map = HashMap::with_capacity(count);

                while count > 0 {
                    let key = self.read_string()?;
                    let value = self.read_string()?;

                    map.insert(key, value);
                    count -= 1;
                }

                sdf::Value::VariantSelectionMap(map)
            }

            Type::TimeSamples => {
                ensure!(!value.is_inlined());
                ensure!(!value.is_compressed());

                self.set_position(value.payload())?;

                {
                    // Read recursive offset.
                    // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1100
                    let offset = self.reader.read_pod::<i64>()?;

                    // -8 to compensate sizeof(offset)
                    // See https://github.com/syoyo/tinyusdz/blob/b14f625a776042a384743316236ee55685f144bf/src/crate-reader.cc#L1737C5-L1737C39
                    self.reader.seek(io::SeekFrom::Current(offset - 8))?;
                }

                let times_rep = self.reader.read_pod::<ValueRep>()?;

                let ty = times_rep.ty()?;
                ensure!(
                    ty == Type::DoubleVector || (ty == Type::Double && times_rep.is_array()),
                    "Invalid time samples type: expected either double vector or double array"
                );

                // Save current position.
                let saved_position = self.reader.stream_position()?;

                let times = self
                    .value(times_rep)?
                    .try_as_double_vec()
                    .context("Failed to read time samples")?;

                // Restore position
                self.set_position(saved_position)?;

                {
                    // Read recursive offset.
                    // See https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L1100
                    let offset = self.reader.read_pod::<i64>()?;

                    // -8 to compensate sizeof(offset)
                    // See https://github.com/syoyo/tinyusdz/blob/b14f625a776042a384743316236ee55685f144bf/src/crate-reader.cc#L1737C5-L1737C39
                    self.reader.seek(io::SeekFrom::Current(offset - 8))?;
                }

                let count = self.reader.read_count()?;
                ensure!(count == times.len(), "Invalid time samples count");

                let value_reps = self.reader.read_vec::<ValueRep>(count)?;
                debug_assert_eq!(value_reps.len(), count);

                let values = value_reps
                    .into_iter()
                    .map(|value| self.value(value))
                    .collect::<Result<Vec<_>>>()?;

                let samples = times.into_iter().zip(values).collect();

                sdf::Value::TimeSamples(samples)
            }

            // Empty dictionary.
            Type::Dictionary if value.is_inlined() => sdf::Value::Dictionary(HashMap::default()),
            Type::Dictionary => {
                ensure!(!value.is_compressed(), "Dictionary {ty} can't be compressed");
                ensure!(!value.is_array(), "Dictionary {ty} can't be inlined");

                self.set_position(value.payload())?;

                sdf::Value::Dictionary(self.read_custom_data()?)
            }

            Type::ValueBlock => sdf::Value::ValueBlock,

            _ => bail!("Unsupported value type: {ty}"),
        };

        Ok(variant)
    }
}

enum ArrayKind {
    Ints,
    #[allow(dead_code)]
    Floats,
    Other,
}

fn to_vec<T: From<i8>, const N: usize>(data: [i8; N]) -> Vec<T> {
    data.map(T::from).into()
}

fn to_mat_diag<const N: usize>(data: [i8; N]) -> Vec<f64> {
    let mut matrix = vec![0_f64; N * N];
    for i in 0..N {
        matrix[i * N + i] = data[i] as f64;
    }
    matrix
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

pub trait ReadExt {
    /// Read a single "size" or "count" value encoded as `u64`.
    ///
    /// # Format:
    /// - u64 size
    fn read_count(&mut self) -> Result<usize>;

    fn read_pod<T: Default + Pod>(&mut self) -> Result<T>;

    fn read_vec<T: Default + NoUninit + AnyBitPattern>(&mut self, count: usize) -> Result<Vec<T>>;
}

impl<R: io::Read> ReadExt for R {
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_read_crate_struct() {
        let path = "./vendor/usd-wg-assets/full_assets/ElephantWithMonochord/SoC-ElephantWithMonochord.usdc";
        if fs::metadata(path).is_err() {
            eprintln!("Skipping test_read_crate_struct: fixture not available at {path}");
            return;
        }

        let mut f = fs::File::open(path).expect("Failed to read crate file");

        let file = CrateFile::open(&mut f).expect("Failed to read crate file");

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
}
