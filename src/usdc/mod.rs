//! `usdc` file format support.

use std::{collections::HashMap, io, mem};

use anyhow::Result;

mod coding;
mod file;
mod reader;
mod value;
mod version;

pub use file::{Bootstrap, CrateFile};
use reader::CrateReader;
pub use value::*;
pub use version::{version, Version};

use crate::sdf;

#[derive(Default, Debug)]
pub struct Spec {
    /// Specifies the type of an object.
    pub ty: sdf::SpecType,
    /// Spec properties.
    pub fields: HashMap<String, sdf::Variant>,
}

impl Spec {
    #[inline]
    pub fn field(&self, field: &str) -> Option<&sdf::Variant> {
        self.fields.get(field)
    }

    pub fn prim_children(&self) -> &[String] {
        if let Some(sdf::Variant::TokenVector(tokens)) = self.field("primChildren") {
            tokens
        } else {
            &[]
        }
    }
}

#[derive(Default)]
pub struct CrateData {
    data: HashMap<sdf::Path, Spec>,
}

impl CrateData {
    pub fn open(reader: impl io::Read + io::Seek, safe: bool) -> Result<Self> {
        let mut file = CrateFile::open(reader)?;

        if safe {
            file.validate()?;
        }

        // Build crate data

        let mut data = HashMap::default();
        let specs = mem::take(&mut file.specs);

        for filespec in specs {
            let path = file.paths[filespec.path_index].clone();
            let ty = filespec.spec_type;

            let mut fields = HashMap::default();
            let mut index = filespec.fieldset_index;

            while index < file.fieldsets.len() {
                let current = match file.fieldsets[index] {
                    Some(value) => value,
                    None => break,
                };

                index += 1;

                let field = &file.fields[current];

                let name = dbg!(file.tokens[field.token_index].clone());
                let value = dbg!(file.value(field.value_rep)?);

                fields.insert(name, value);
            }

            data.insert(path, Spec { ty, fields });
        }

        Ok(Self { data })
    }

    /// Retrieve a spec by path.
    #[inline]
    pub fn spec(&self, path: &sdf::Path) -> Option<&Spec> {
        self.data.get(path)
    }

    /// Retrieve spec and field.
    #[inline]
    pub fn field(&self, path: &sdf::Path, field: &str) -> Option<&sdf::Variant> {
        self.spec(path).and_then(|spec| spec.field(field))
    }

    #[inline]
    pub fn specs_iter(&self) -> impl Iterator<Item = &Spec> {
        self.data.values()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_crate_hierarchy() {
        let f =
            fs::File::open("./extern/usd-wg-assets/full_assets/ElephantWithMonochord/SoC-ElephantWithMonochord.usdc")
                .expect("Failed to read crate file");

        let data = CrateData::open(f, true).unwrap();

        // There should always be a pseudo root unless there was an error.
        let pseudo_root = data
            .specs_iter()
            .find(|spec| spec.ty == sdf::SpecType::PseudoRoot)
            .expect("Failed to find pseudo root");

        assert_eq!(pseudo_root.prim_children(), &["SoC_ElephantWithMonochord"]);

        let elephant = data
            .spec(&sdf::Path::new("/SoC_ElephantWithMonochord").unwrap())
            .expect("Failed to get SoC_ElephantWithMonochord");

        assert_eq!(
            elephant.prim_children(),
            &["Materials", "Object", "CharacterAudioSource"]
        );

        let materials = data
            .spec(&sdf::Path::new("/SoC_ElephantWithMonochord/Materials").unwrap())
            .expect("Failed to get Materials");

        assert_eq!(materials.prim_children(), &["Elefant_Mat_68050", "Monochord_Mat_68062"]);
    }
}
