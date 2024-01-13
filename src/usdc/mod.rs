//! `usdc` file format support.

use std::{collections::HashMap, fmt::Debug, io, mem, path::Path};

use anyhow::{bail, Result};

mod coding;
mod file;
mod layout;
mod reader;
mod version;

pub use file::CrateFile;
use layout::ValueRep;
use reader::CrateReader;
pub use version::{version, Version};

use crate::sdf;

#[derive(Default, Debug)]
struct Spec {
    /// Specifies the type of an object.
    ty: sdf::SpecType,
    /// Spec properties.
    fields: HashMap<String, ValueRep>,
}

#[derive(Debug)]
pub struct CrateData<R> {
    file: CrateFile<R>,
    data: HashMap<sdf::Path, Spec>,
}

impl<R> CrateData<R>
where
    R: io::Read + io::Seek,
{
    pub fn open(reader: R, safe: bool) -> Result<Self> {
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

                fields.insert(name, field.value_rep);
            }

            data.insert(path, Spec { ty, fields });
        }

        Ok(Self { file, data })
    }
}

impl<R> sdf::AbstractData for CrateData<R>
where
    R: io::Read + io::Seek,
{
    #[inline]
    fn has_spec(&self, path: &sdf::Path) -> bool {
        self.data.contains_key(path)
    }

    #[inline]
    fn has_field(&self, path: &sdf::Path, field: &str) -> bool {
        self.data
            .get(path)
            .map_or(false, |spec| spec.fields.contains_key(field))
    }

    #[inline]
    fn spec_type(&self, path: &sdf::Path) -> Option<sdf::SpecType> {
        self.data.get(path).map(|spec| spec.ty)
    }

    fn get(&mut self, path: &sdf::Path, field: &str) -> Result<sdf::Value> {
        let Some(spec) = self.data.get(path) else {
            bail!("No spec found for path: {}", path)
        };

        let Some(value_rep) = spec.fields.get(field).cloned() else {
            bail!("No field found for path '{}' and field '{}'", path, field)
        };

        self.file.value(value_rep)
    }

    #[inline]
    fn list(&self, path: &sdf::Path) -> Option<Vec<String>> {
        self.data.get(path).map(|spec| spec.fields.keys().cloned().collect())
    }
}

/// Read `usdc` data from a file on disk.
pub fn read_file(path: impl AsRef<Path>) -> Result<Box<dyn sdf::AbstractData>> {
    let file = std::fs::File::open(path)?;
    let data = CrateData::open(file, true)?;

    Ok(Box::new(data))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_crate_hierarchy() {
        let mut data =
            read_file("./extern/usd-wg-assets/full_assets/ElephantWithMonochord/SoC-ElephantWithMonochord.usdc")
                .unwrap();

        let prim_children = data.get(&sdf::Path::abs_root(), "primChildren").unwrap();
        assert_eq!(
            Vec::<String>::from(prim_children),
            vec!["SoC_ElephantWithMonochord".to_string()]
        );

        let elephant = data
            .get(&sdf::Path::new("/SoC_ElephantWithMonochord").unwrap(), "primChildren")
            .expect("Failed to get SoC_ElephantWithMonochord");

        assert_eq!(
            Vec::<String>::from(elephant),
            vec![
                "Materials".to_string(),
                "Object".to_string(),
                "CharacterAudioSource".to_string()
            ]
        );

        let materials = data
            .get(
                &sdf::Path::new("/SoC_ElephantWithMonochord/Materials").unwrap(),
                "primChildren",
            )
            .expect("Failed to get Materials");

        assert_eq!(
            Vec::<String>::from(materials),
            vec!["Elefant_Mat_68050".to_string(), "Monochord_Mat_68062".to_string()]
        );
    }

    #[test]
    fn test_read_custom_layer_data() {
        let mut data = read_file("fixtures/fields.usdc").unwrap();

        let custom_layer_data = data.get(&sdf::Path::abs_root(), "customLayerData").unwrap();

        // customLayerData = {
        //  string test = "Test string"
        // }
        let copyright = custom_layer_data.as_dict().unwrap().get("test").unwrap().as_str();

        assert_eq!(copyright, "Test string");
    }

    #[test]
    fn test_read_array_fields() {
        let mut data = read_file("fixtures/fields.usdc").unwrap();

        // defaultPrim = "World"
        let default_prim = data.get(&sdf::Path::abs_root(), "defaultPrim").unwrap();
        assert_eq!(default_prim.as_str(), "World");

        // float4[] clippingPlanes = []
        let clipping_planes = data
            .get(&sdf::Path::new("/World.clippingPlanes").unwrap(), "default")
            .unwrap();
        assert!(matches!(clipping_planes, sdf::Value::Vec4f(..)));
        assert_eq!(clipping_planes.as_f32_slice(), Some([].as_slice()));

        // float2 clippingRange = (1, 10000000)
        let clipping_range = data
            .get(&sdf::Path::new("/World.clippingRange").unwrap(), "default")
            .unwrap();
        assert!(matches!(clipping_range, sdf::Value::Vec2f(..)));
        assert_eq!(clipping_range.as_f32_slice(), Some([1.0, 10000000.0].as_slice()));

        // float3 diffuseColor = (0.18, 0.18, 0.18)
        let diffuse_color = data
            .get(&sdf::Path::new("/World.diffuseColor").unwrap(), "default")
            .unwrap();
        assert!(matches!(diffuse_color, sdf::Value::Vec3f(..)));
        assert_eq!(diffuse_color.as_f32_slice(), Some([0.18, 0.18, 0.18].as_slice()));

        // int[] faceVertexCounts = [1, 2, 3, 4, 5, 6]
        let face_vertex_counts = data
            .get(&sdf::Path::new("/World.faceVertexCounts").unwrap(), "default")
            .unwrap();
        assert!(matches!(face_vertex_counts, sdf::Value::Int(..)));
        assert_eq!(face_vertex_counts.as_int_slice(), Some([1, 2, 3, 4, 5, 6].as_slice()));

        // normal3f[] normals = [(0, 1, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 0), (0, 0, 1), (1, 0, 0)]
        let normals = data.get(&sdf::Path::new("/World.normals").unwrap(), "default").unwrap();
        assert!(matches!(normals, sdf::Value::Vec3f(..)));
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
            .get(&sdf::Path::new("/World.xformOp:rotateXYZ").unwrap(), "default")
            .unwrap();
        assert!(matches!(xform_op_rotate_xyz, sdf::Value::Vec3d(..)));
        assert_eq!(xform_op_rotate_xyz.as_f64_slice(), Some([0.0, 0.0, 0.0].as_slice()));

        // double3 xformOp:scale = (1, 1, 1)
        let xform_op_scale = data
            .get(&sdf::Path::new("/World.xformOp:scale").unwrap(), "default")
            .unwrap();
        assert!(matches!(xform_op_scale, sdf::Value::Vec3d(..)));
        assert_eq!(xform_op_scale.as_f64_slice(), Some([1.0, 1.0, 1.0].as_slice()));

        // double3 xformOp:translate = (0, 1, 0)
        let xform_op_translate = data
            .get(&sdf::Path::new("/World.xformOp:translate").unwrap(), "default")
            .unwrap();
        assert!(matches!(xform_op_translate, sdf::Value::Vec3d(..)));
        assert_eq!(xform_op_translate.as_f64_slice(), Some([0.0, 1.0, 0.0].as_slice()));
    }
}
