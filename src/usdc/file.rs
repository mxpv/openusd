//! Binary crate file reader.

use std::{
    ffi::CStr,
    io::{self, Cursor},
    mem, str,
};

use anyhow::{ensure, Context, Result};
use bytemuck::{bytes_of, Pod, Zeroable};

use crate::{sdf, usdc};

use usdc::{version, CrateReader, Type, Value, Version};

// Currently supported USDC version.
// See <https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.cpp#L340>
const SW_VERSION: Version = version(0, 10, 0);

/// Appears at start of file, houses version, file identifier string and offset to TOC.
#[repr(C)]
#[derive(Default, Clone, Copy, Pod, Zeroable)]
pub struct Bootstrap {
    /// "PXR-USDC"
    pub ident: [u8; 8],
    /// 0: major, 1: minor, 2: patch, rest unused.
    pub version: [u8; 8],
    /// Offset to TOC.
    pub toc_offset: u64,
    /// Unused.
    reserved: [u8; 8],
}

/// Max section's name length.
const SECTION_NAME_MAX_LENGTH: usize = 15;

#[repr(C)]
#[derive(Default, Clone, Copy, Pod, Zeroable)]
pub struct Section {
    /// Section name bytes (e.g. "TOKENS"), use [Section::name] to retrieve as string.
    name: [u8; SECTION_NAME_MAX_LENGTH + 1],
    /// Section start offset.
    pub start: u64,
    /// Section size.
    pub size: u64,
}

impl Section {
    pub const TOKENS: &'static str = "TOKENS";
    pub const STRINGS: &'static str = "STRINGS";
    pub const FIELDS: &'static str = "FIELDS";
    pub const FIELDSETS: &'static str = "FIELDSETS";
    pub const PATHS: &'static str = "PATHS";
    pub const SPECS: &'static str = "SPECS";

    /// Convert array of bytes to a human-readable string.
    pub fn name(&self) -> &str {
        CStr::from_bytes_until_nul(&self.name)
            .unwrap_or_default()
            .to_str()
            .unwrap_or_default()
    }
}

pub struct Field {
    pub token_index: usize,
    pub value_rep: Value,
}

impl Field {
    pub fn new(index: u32, value: u64) -> Self {
        Self {
            token_index: index as usize,
            value_rep: Value(value),
        }
    }
}

/// Spec data loaded from file.
#[derive(Default, Clone, Copy)]
pub struct Spec {
    pub path_index: usize,
    pub fieldset_index: usize,
    pub spec_type: sdf::SpecType,
}

#[repr(C)]
#[derive(Default, Clone, Copy, Pod, Zeroable)]
pub struct ListOpHeader {
    bits: u8,
}

impl ListOpHeader {
    const IS_EXPLICIT: u8 = 1 << 0;
    const HAS_EXPLICIT_ITEMS: u8 = 1 << 1;
    const HAS_ADDED_ITEMS: u8 = 1 << 2;
    const HAS_DELETED_ITEMS: u8 = 1 << 3;
    const HAS_ORDERED_ITEMS: u8 = 1 << 4;
    const HAS_PREPEND_ITEMS: u8 = 1 << 5;
    const HAS_APPENDED_ITEMS: u8 = 1 << 6;

    #[inline]
    pub fn is_explicit(self) -> bool {
        self.bits & Self::IS_EXPLICIT != 0
    }

    #[inline]
    pub fn has_explicit(self) -> bool {
        self.bits & Self::HAS_EXPLICIT_ITEMS != 0
    }

    #[inline]
    pub fn has_added(self) -> bool {
        self.bits & Self::HAS_ADDED_ITEMS != 0
    }

    #[inline]
    pub fn has_deleted(self) -> bool {
        self.bits & Self::HAS_DELETED_ITEMS != 0
    }

    #[inline]
    pub fn has_ordered(self) -> bool {
        self.bits & Self::HAS_ORDERED_ITEMS != 0
    }

    #[inline]
    pub fn has_prepend(self) -> bool {
        self.bits & Self::HAS_PREPEND_ITEMS != 0
    }

    #[inline]
    pub fn has_appended(self) -> bool {
        self.bits & Self::HAS_APPENDED_ITEMS != 0
    }
}

/// Crate file represents structural data loaded from a USDC file on disk.
pub struct CrateFile<R: io::Read + io::Seek> {
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
                    .with_context(|| format!("Invalid fieldset index {}: {}", index, fieldset))?;

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

            ensure!(spec.spec_type != sdf::SpecType::Unknown, "Invalid spec {} type", index);

            anyhow::Ok(())
        })?;

        Ok(())
    }

    /// Returns file's version extracted from [Bootstrap::version].
    #[inline]
    pub fn version(&self) -> Version {
        Version::from(self.bootstrap)
    }

    /// Read and verify bootstrap header, retrieve offset to TOC.
    fn read_header(mut reader: impl io::Read + io::Seek) -> Result<Bootstrap> {
        let header = reader.read_pod::<Bootstrap>()?;

        ensure!(header.ident.eq(b"PXR-USDC"), "Usd crate bootstrap section corrupt");

        ensure!(header.toc_offset > 0, "Invalid TOC offset");

        let file_ver = version(header.version[0], header.version[1], header.version[2]);

        ensure!(
            SW_VERSION.can_read(file_ver),
            "Usd crate version mismatch, file is {}, library supports {}",
            file_ver,
            SW_VERSION,
        );

        Ok(header)
    }

    fn read_sections(&mut self) -> Result<()> {
        self.set_position(self.bootstrap.toc_offset)?;
        self.sections = self.reader.read_vec::<Section>()?;

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
            let mut buffer = self.reader.read_compressed(uncompressed_size)?;

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

        let strings = self.reader.read_vec::<u32>()?;

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
            let indices = self.reader.read_encoded_ints(field_count)?;

            // Compressed value reps.
            let reps = self.reader.read_compressed(field_count)?;

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

            let decoded = self.reader.read_encoded_ints::<u32>(count)?;

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

        self.paths = if file_ver == version(0, 0, 1) {
            todo!("Support PATHS reader for == 0.0.1 files");
        } else if file_ver < version(0, 4, 0) {
            todo!("Support PATHS reader for < 0.4.0 files");
        } else {
            // Read # of paths.
            let path_count = self.reader.read_count()?;

            // Read compressed paths.
            let paths = self.reader.read_compressed_paths(&self.tokens)?;
            debug_assert_eq!(paths.len(), path_count);

            paths
        };

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
            let tmp = self.reader.read_encoded_ints::<u32>(spec_count)?;
            for (i, path_index) in tmp.iter().enumerate() {
                specs[i].path_index = *path_index as usize;
            }

            // fieldSetIndexes.
            let tmp = self.reader.read_encoded_ints::<u32>(spec_count)?;
            for (i, field_set_index) in tmp.iter().enumerate() {
                specs[i].fieldset_index = *field_set_index as usize;
            }

            // specTypes.
            let tmp = self.reader.read_encoded_ints::<u32>(spec_count)?;
            for (i, spec_type) in tmp.iter().enumerate() {
                specs[i].spec_type = sdf::SpecType::from_repr(*spec_type)
                    .with_context(|| format!("Unable to parse SDF spec type: {}", *spec_type))?;
            }

            specs
        };

        Ok(())
    }

    /// Find section by name.
    pub fn find_section(&self, name: &str) -> Option<&Section> {
        self.sections.iter().find(|s| s.name() == name)
    }

    fn set_position(&mut self, position: u64) -> Result<()> {
        self.reader.seek(io::SeekFrom::Start(position))?;
        Ok(())
    }

    fn unpack_value<T: Default + Pod>(&mut self, value: Value) -> Result<T> {
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

    fn unpack_token(&mut self, value: Value) -> Result<String> {
        let index: u64 = self.unpack_value(value)?;
        let value = self.tokens[index as usize].clone();

        Ok(value)
    }

    fn read_list_op<T: Default>(
        &mut self,
        value: Value,
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

    fn read_token_list_op(&mut self, value: Value) -> Result<sdf::TokenListOp> {
        self.read_list_op(value, |file: &mut Self| file.read_token_vec())
    }

    fn read_token_vec(&mut self) -> Result<Vec<String>> {
        let indices = self.reader.read_vec::<u32>()?;

        let vec = indices
            .into_iter()
            .map(|index| self.tokens[index as usize].clone())
            .collect();

        Ok(vec)
    }

    pub fn value(&mut self, value: Value) -> Result<sdf::Variant> {
        use glam::*;

        let ty = value.ty()?;
        ensure!(ty != Type::Invalid, "Invalid value type");

        let variant = match ty {
            Type::Bool => {
                let value: i32 = self.unpack_value(value)?;
                sdf::Variant::Bool(value != 0)
            }
            Type::UChar => {
                let value = self.unpack_value(value)?;
                sdf::Variant::Uchar(value)
            }
            Type::Int => {
                let value = self.unpack_value(value)?;
                sdf::Variant::Int(value)
            }
            Type::UInt => {
                let value = self.unpack_value(value)?;
                sdf::Variant::Uint(value)
            }
            Type::Int64 => {
                let value = self.unpack_value(value)?;
                sdf::Variant::Int64(value)
            }
            Type::UInt64 => {
                let value = self.unpack_value(value)?;
                sdf::Variant::Uint64(value)
            }
            Type::Float => {
                let value = self.unpack_value(value)?;
                sdf::Variant::Float(value)
            }
            Type::Double => {
                // Stored as float.
                let value: f32 = self.unpack_value(value)?;
                sdf::Variant::Double(value as f64)
            }
            Type::String => {
                let value = self.unpack_token(value)?;
                sdf::Variant::String(value)
            }
            Type::Token => {
                let value = self.unpack_token(value)?;
                sdf::Variant::Token(value)
            }
            Type::AssetPath => {
                let value = self.unpack_token(value)?;
                sdf::Variant::AssetPath(value)
            }
            Type::TokenListOp => {
                let list_op = self.read_token_list_op(value)?;
                sdf::Variant::TokenListOp(list_op)
            }
            Type::TokenVector => {
                ensure!(!value.is_inlined(), "{} can't be inlined", ty);

                self.set_position(value.payload())?;

                let tokens = self.read_token_vec()?;

                sdf::Variant::TokenVector(tokens)
            }
            Type::Specifier => {
                let tmp: i32 = self.unpack_value(value)?;
                let specifier = sdf::Specifier::from_repr(tmp)
                    .with_context(|| format!("Unable to parse SDF specifier: {}", tmp))?;

                sdf::Variant::Specifier(specifier)
            }
            Type::Permission => {
                let tmp: i32 = self.unpack_value(value)?;
                let permission =
                    sdf::Permission::from_repr(tmp).with_context(|| format!("Unable to parse permission: {}", tmp))?;

                sdf::Variant::Permission(permission)
            }
            Type::Variability => {
                let tmp: i32 = self.unpack_value(value)?;
                let variability = sdf::Variability::from_repr(tmp)
                    .with_context(|| format!("Unable to parse variability: {}", tmp))?;

                sdf::Variant::Variability(variability)
            }
            _ => sdf::Variant::Unimplemented,
        };

        Ok(variant)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_read_crate_struct() {
        let mut f =
            fs::File::open("./extern/usd-wg-assets/full_assets/ElephantWithMonochord/SoC-ElephantWithMonochord.usdc")
                .expect("Failed to read crate file");

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
