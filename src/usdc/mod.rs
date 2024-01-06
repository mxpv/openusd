//! Binary crate file (usdc) reader.

use std::{ffi::CStr, io, str};

use anyhow::{ensure, Context, Result};
use bytemuck::{Pod, Zeroable};

mod coding;
mod reader;
mod types;
mod version;

use crate::sdf;
use reader::CrateReader;
pub use types::*;
pub use version::{version, Version};

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

/// Crate file represents structural data loaded from a USDC file on disk.
#[derive(Default)]
pub struct CrateFile {
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

impl CrateFile {
    /// Read structural sections of a crate file.
    pub fn from_reader(mut reader: impl io::Read + io::Seek) -> Result<Self> {
        let bootstrap = Self::read_header(&mut reader)?;

        let mut file = CrateFile {
            bootstrap,
            ..Default::default()
        };

        file.read_sections(&mut reader).context("Unable to read sections")?;

        file.read_tokens(&mut reader).context("Unable to read TOKENS section")?;

        file.read_strings(&mut reader)
            .context("Unable to read STRINGS section")?;

        file.read_fields(&mut reader).context("Unable to read FIELDS section")?;

        file.read_fieldsets(&mut reader)
            .context("Unable to read FIELDSETS section")?;

        file.read_paths(&mut reader).context("Unable to read PATHS section")?;

        file.read_specs(&mut reader).context("Unable to read SPECS section")?;

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

    fn read_sections(&mut self, mut reader: impl io::Read + io::Seek) -> Result<()> {
        reader.seek(io::SeekFrom::Start(self.bootstrap.toc_offset))?;

        self.sections = reader.read_vec::<Section>()?;

        Ok(())
    }

    fn read_tokens(&mut self, mut reader: impl io::Read + io::Seek) -> Result<()> {
        let Some(section) = self.find_section(Section::TOKENS) else {
            return Ok(());
        };

        reader.seek(io::SeekFrom::Start(section.start))?;

        let file_ver = self.version();

        // Read the number of tokens.
        let count = reader.read_count()?;

        self.tokens = if file_ver < version(0, 4, 0) {
            todo!("Support TOKENS reader for < 0.4.0 files");
        } else {
            let uncompressed_size = reader.read_count()?;
            let mut buffer = reader.read_compressed(uncompressed_size)?;

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

    fn read_strings(&mut self, mut reader: impl io::Read + io::Seek) -> Result<()> {
        let Some(section) = self.find_section(Section::STRINGS) else {
            return Ok(());
        };

        reader.seek(io::SeekFrom::Start(section.start))?;

        let strings = reader.read_vec::<u32>()?;

        // These are indices, so convert to usize for convenience.
        self.strings = strings.into_iter().map(|offset| offset as usize).collect::<Vec<_>>();

        Ok(())
    }

    fn read_fields(&mut self, mut reader: impl io::Read + io::Seek) -> Result<()> {
        let Some(section) = self.find_section(Section::FIELDS) else {
            return Ok(());
        };

        reader.seek(io::SeekFrom::Start(section.start))?;

        let file_ver = self.version();

        self.fields = if file_ver < version(0, 4, 0) {
            todo!("Support FIELDS reader before < 0.4.0")
        } else {
            let field_count = reader.read_count()?;

            // Compressed fields in 0.4.0.
            let indices = reader.read_encoded_ints(field_count)?;

            // Compressed value reps.
            let reps = reader.read_compressed(field_count)?;

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

    fn read_fieldsets(&mut self, mut reader: impl io::Read + io::Seek) -> Result<()> {
        let Some(section) = self.find_section(Section::FIELDSETS) else {
            return Ok(());
        };

        reader.seek(io::SeekFrom::Start(section.start))?;

        let file_ver = self.version();

        self.fieldsets = if file_ver < version(0, 4, 0) {
            todo!("Support FIELDSETS reader for < 0.4.0 files");
        } else {
            let count = reader.read_count()?;

            let decoded = reader.read_encoded_ints::<u32>(count)?;

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

    fn read_paths(&mut self, mut reader: impl io::Read + io::Seek) -> Result<()> {
        let Some(section) = self.find_section(Section::PATHS) else {
            return Ok(());
        };

        reader.seek(io::SeekFrom::Start(section.start))?;

        let file_ver = self.version();

        self.paths = if file_ver == version(0, 0, 1) {
            todo!("Support PATHS reader for == 0.0.1 files");
        } else if file_ver < version(0, 4, 0) {
            todo!("Support PATHS reader for < 0.4.0 files");
        } else {
            // Read # of paths.
            let path_count = reader.read_count()?;

            // Read compressed paths.
            let paths = reader.read_compressed_paths(&self.tokens)?;
            debug_assert_eq!(paths.len(), path_count);

            paths
        };

        Ok(())
    }

    fn read_specs(&mut self, mut reader: impl io::Read + io::Seek) -> Result<()> {
        let Some(section) = self.find_section(Section::SPECS) else {
            return Ok(());
        };

        reader.seek(io::SeekFrom::Start(section.start))?;

        let file_ver = self.version();

        self.specs = if file_ver == version(0, 0, 1) {
            todo!("Support SPECS reader for == 0.0.1 files");
        } else if file_ver < version(0, 4, 0) {
            todo!("Support SPECS reader for < 0.4.0 files");
        } else {
            // Version 0.4.0 specs are compressed

            let spec_count = reader.read_count()?;

            let mut specs = vec![Spec::default(); spec_count];

            // TODO: Might want to reuse temp buffer space here.

            // pathIndexes.
            let tmp = reader.read_encoded_ints::<u32>(spec_count)?;
            for (i, path_index) in tmp.iter().enumerate() {
                specs[i].path_index = *path_index as usize;
            }

            // fieldSetIndexes.
            let tmp = reader.read_encoded_ints::<u32>(spec_count)?;
            for (i, field_set_index) in tmp.iter().enumerate() {
                specs[i].fieldset_index = *field_set_index as usize;
            }

            // specTypes.
            let tmp = reader.read_encoded_ints::<u32>(spec_count)?;
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

        let file = CrateFile::from_reader(&mut f).expect("Failed to read crate file");

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
