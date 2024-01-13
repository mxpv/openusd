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

#[derive(Default, Debug)]
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

                let name = file.tokens[field.token_index].clone();
                let value = file.value(field.value_rep)?;

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

    #[test]
    fn test_read_custom_layer_data() {
        let file = fs::File::open("fixtures/fields.usdc").unwrap();
        let data = dbg!(CrateData::open(file, true).unwrap());

        let pseudo_root = data
            .specs_iter()
            .find(|spec| spec.ty == sdf::SpecType::PseudoRoot)
            .expect("Unable to find pseudo root");

        //  customLayerData = {
        //      string test = "Test string"
        //  }
        let copyright = pseudo_root
            .field("customLayerData")
            .unwrap()
            .as_dict()
            .unwrap()
            .get("test")
            .unwrap()
            .as_str();

        assert_eq!(copyright, "Test string");
    }

    #[test]
    fn test_read_array_fields() {
        let file = fs::File::open("fixtures/fields.usdc").unwrap();
        let data = dbg!(CrateData::open(file, true).unwrap());

        let pseudo_root = data
            .specs_iter()
            .find(|spec| spec.ty == sdf::SpecType::PseudoRoot)
            .expect("Unable to find pseudo root");

        //  defaultPrim = "World"
        let default_prim = pseudo_root.field("defaultPrim").unwrap().as_str();
        assert_eq!(default_prim, "World");

        // float4[] clippingPlanes = []
        let clipping_planes = data
            .field(&sdf::Path::new("/World.clippingPlanes").unwrap(), "default")
            .unwrap();
        assert!(matches!(clipping_planes, sdf::Variant::Vec4f(..)));
        assert_eq!(clipping_planes.as_f32_slice(), Some([].as_slice()));

        // float2 clippingRange = (1, 10000000)
        let clipping_range = data
            .field(&sdf::Path::new("/World.clippingRange").unwrap(), "default")
            .unwrap();
        assert!(matches!(clipping_range, sdf::Variant::Vec2f(..)));
        assert_eq!(clipping_range.as_f32_slice(), Some([1.0, 10000000.0].as_slice()));

        // float3 diffuseColor = (0.18, 0.18, 0.18)
        let diffuse_color = data
            .field(&sdf::Path::new("/World.diffuseColor").unwrap(), "default")
            .unwrap();
        assert!(matches!(diffuse_color, sdf::Variant::Vec3f(..)));
        assert_eq!(diffuse_color.as_f32_slice(), Some([0.18, 0.18, 0.18].as_slice()));

        // int[] faceVertexCounts = [1, 2, 3, 4, 5, 6]
        let face_vertex_counts = data
            .field(&sdf::Path::new("/World.faceVertexCounts").unwrap(), "default")
            .unwrap();
        assert!(matches!(face_vertex_counts, sdf::Variant::Int(..)));
        assert_eq!(face_vertex_counts.as_int_slice(), Some([1, 2, 3, 4, 5, 6].as_slice()));

        // normal3f[] normals = [(0, 1, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 0), (0, 0, 1), (1, 0, 0)]
        let normals = data
            .field(&sdf::Path::new("/World.normals").unwrap(), "default")
            .unwrap();
        assert!(matches!(normals, sdf::Variant::Vec3f(..)));
        assert_eq!(
            normals.as_f32_slice(),
            Some(
                [
                    0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 1.0, 0.0,
                    0.0
                ]
                .as_slice()
            )
        );

        // double3 xformOp:rotateXYZ = (0, 0, 0)
        let xform_op_rotate_xyz = data
            .field(&sdf::Path::new("/World.xformOp:rotateXYZ").unwrap(), "default")
            .unwrap();
        assert!(matches!(xform_op_rotate_xyz, sdf::Variant::Vec3d(..)));
        assert_eq!(xform_op_rotate_xyz.as_f64_slice(), Some([0.0, 0.0, 0.0].as_slice()));

        // double3 xformOp:scale = (1, 1, 1)
        let xform_op_scale = data
            .field(&sdf::Path::new("/World.xformOp:scale").unwrap(), "default")
            .unwrap();
        assert!(matches!(xform_op_scale, sdf::Variant::Vec3d(..)));
        assert_eq!(xform_op_scale.as_f64_slice(), Some([1.0, 1.0, 1.0].as_slice()));

        // double3 xformOp:translate = (0, 1, 0)
        let xform_op_translate = data
            .field(&sdf::Path::new("/World.xformOp:translate").unwrap(), "default")
            .unwrap();
        assert!(matches!(xform_op_translate, sdf::Variant::Vec3d(..)));
        assert_eq!(xform_op_translate.as_f64_slice(), Some([0.0, 1.0, 0.0].as_slice()));
    }
}
