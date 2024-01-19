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

        Ok(Self { file, data: dbg!(data) })
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
    use half::f16;

    #[test]
    fn test_crate_hierarchy() -> Result<()> {
        let mut data =
            read_file("./extern/usd-wg-assets/full_assets/ElephantWithMonochord/SoC-ElephantWithMonochord.usdc")?;

        let prim_children: Vec<String> = data.get(&sdf::Path::abs_root(), "primChildren")?.try_into()?;
        assert_eq!(prim_children, vec!["SoC_ElephantWithMonochord".to_string()]);

        let elephant: Vec<String> = data
            .get(&sdf::path("/SoC_ElephantWithMonochord")?, "primChildren")?
            .try_into()?;

        assert_eq!(
            elephant,
            vec![
                "Materials".to_string(),
                "Object".to_string(),
                "CharacterAudioSource".to_string()
            ]
        );

        let materials: Vec<String> = data
            .get(&sdf::path("/SoC_ElephantWithMonochord/Materials")?, "primChildren")?
            .try_into()?;

        assert_eq!(
            materials,
            vec!["Elefant_Mat_68050".to_string(), "Monochord_Mat_68062".to_string()]
        );

        Ok(())
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
    fn test_read_sub_layers() -> Result<()> {
        let mut data = read_file("fixtures/expressions.usdc")?;

        let sub_layer_offsets: sdf::LayerOffset = data.get(&sdf::path("/")?, "subLayerOffsets")?.try_into()?;

        assert_eq!(sub_layer_offsets.offset, 0.0);
        assert_eq!(sub_layer_offsets.scale, 1.0);

        let sub_layers: Vec<String> = data.get(&sdf::path("/")?, "subLayers")?.try_into()?;
        assert_eq!(sub_layers, vec!["`\"render_pass_${RENDER_PASS}.usd\"`"]);

        Ok(())
    }

    #[test]
    fn test_read_variant_selection() -> Result<()> {
        let mut data = read_file("fixtures/expressions.usdc")?;

        // prepend variantSets = "displayVariantSet"
        let variant_set_names: sdf::StringListOp = data.get(&sdf::path("/asset1")?, "variantSetNames")?.try_into()?;
        assert_eq!(variant_set_names.prepended_items, vec!["displayVariantSet".to_string()]);

        let variant_selection = {
            let value = data.get(&sdf::path("/asset1")?, "variantSelection")?;
            HashMap::<String, String>::try_from(value)?
        };

        assert_eq!(variant_selection.len(), 1);
        assert_eq!(
            variant_selection.get("displayVariantSet").unwrap(),
            "`${VARIANT_CHOICE}`"
        );

        Ok(())
    }

    #[test]
    fn test_read_connection() -> Result<()> {
        let mut data = read_file("fixtures/connection.usdc")?;

        let conn: sdf::PathListOp = data
            .get(&sdf::path("/boardMat/stReader.inputs:varname")?, "connectionPaths")?
            .try_into()?;

        assert!(conn.explicit);
        assert_eq!(
            conn.explicit_items,
            vec![sdf::path("/TexModel/boardMat.inputs:frame:stPrimvarName")?]
        );

        let conn: sdf::PathListOp = data
            .get(&sdf::path("/boardMat.outputs:surface")?, "connectionPaths")?
            .try_into()?;

        assert!(conn.explicit);
        assert_eq!(
            conn.explicit_items,
            vec![sdf::path("/TexModel/boardMat/PBRShader.outputs:surface")?]
        );

        Ok(())
    }

    #[test]
    fn test_read_reference() -> Result<()> {
        let mut data = read_file("fixtures/reference.usdc")?;

        let references: sdf::ReferenceListOp = data
            .get(&sdf::path("/MarbleCollection/Marble_Red")?, "references")?
            .try_into()?;

        assert!(references.appended_items.is_empty());
        assert!(references.deleted_items.is_empty());
        assert!(references.ordered_items.is_empty());

        assert!(references.explicit);
        assert_eq!(references.explicit_items.len(), 1);

        assert_eq!(references.explicit_items[0].asset_path, "Marble.usd");
        assert_eq!(references.explicit_items[0].prim_path, sdf::path("/Foo/Bar")?);

        Ok(())
    }

    #[test]
    fn test_read_payload() -> Result<()> {
        let mut data = read_file("fixtures/payload.usdc")?;

        let payload = {
            let value = data.get(&sdf::path("/MySphere1")?, "payload")?;
            sdf::Payload::try_from(value)?
        };

        assert_eq!(payload.asset_path, "./payload.usda");
        assert_eq!(payload.prim_path, sdf::path("/MySphere")?);

        assert!(payload.layer_offset.is_some());

        let layer_offset = payload.layer_offset.unwrap();
        assert_eq!(layer_offset.offset, 0.0);
        assert_eq!(layer_offset.scale, 1.0);

        let payload_list_op = {
            let value = data.get(&sdf::path("/MySphere2")?, "payload")?;
            sdf::PayloadListOp::try_from(value)?
        };

        assert!(!payload_list_op.explicit);

        assert!(payload_list_op.explicit_items.is_empty());
        assert!(payload_list_op.added_items.is_empty());
        assert!(payload_list_op.appended_items.is_empty());
        assert!(payload_list_op.deleted_items.is_empty());
        assert!(payload_list_op.ordered_items.is_empty());

        assert_eq!(payload_list_op.prepended_items.len(), 1);
        assert_eq!(payload_list_op.prepended_items[0].asset_path, "./cube_payload.usda");
        assert_eq!(payload_list_op.prepended_items[0].prim_path, sdf::path("/PayloadCube")?);

        Ok(())
    }

    #[test]
    fn test_read_doubles() -> Result<()> {
        let mut data = read_file("fixtures/floats.usdc")?;

        let single: Vec<f64> = data.get(&sdf::path("/PrimD.single")?, "default")?.try_into()?;
        assert_eq!(single, vec![4.3]);

        let array: Vec<f64> = data.get(&sdf::path("/PrimD.simple")?, "default")?.try_into()?;
        assert_eq!(array, vec![0.5, 1.7, 2.4, 3.5, 4.9, 5.3, 6.2, 7.8, 8.6, 9.3]);

        let compressed: Vec<f64> = data.get(&sdf::path("/PrimD.copressed")?, "default")?.try_into()?;
        assert_eq!(
            compressed,
            vec![
                0.5, 1.7, 2.4, 3.5, 4.9, 5.3, 6.2, 7.8, 8.6, 9.3, 5.3, 6.2, 7.8, 8.6, 9.3, 0.5, 1.7, 2.4, 3.5, 4.9,
                0.5, 1.7, 2.4, 3.5, 4.9, 5.3, 6.2, 7.8, 8.6, 9.3, 5.3, 6.2, 7.8, 8.6, 9.3, 0.5, 1.7, 2.4, 3.5, 4.9,
                0.5, 1.7, 2.4, 3.5, 4.9, 5.3, 6.2, 7.8, 8.6, 9.3, 5.3, 6.2, 7.8, 8.6, 9.3, 0.5, 1.7, 2.4, 3.5, 4.9,
                0.5, 1.7, 2.4, 3.5, 4.9, 5.3, 6.2, 7.8, 8.6, 9.3, 5.3, 6.2, 7.8, 8.6, 9.3, 0.5, 1.7, 2.4, 3.5, 4.9,
                0.5, 1.7, 2.4, 3.5, 4.9, 5.3, 6.2, 7.8, 8.6, 9.3, 5.3, 6.2, 7.8, 8.6, 9.3, 0.5, 1.7, 2.4, 3.5, 4.9,
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_floats() -> Result<()> {
        let mut data = read_file("fixtures/floats.usdc")?;

        let single: Vec<f32> = data.get(&sdf::path("/PrimF.single")?, "default")?.try_into()?;
        assert_eq!(single, vec![3.5]);

        let array: Vec<f32> = data.get(&sdf::path("/PrimF.simple")?, "default")?.try_into()?;
        assert_eq!(array, vec![9.1, 2.3, 6.4, 7.4, 3.6, 4.3, 5.3, 5.6, 8.7, 4.7]);

        let compressed: Vec<f32> = data.get(&sdf::path("/PrimF.copressed")?, "default")?.try_into()?;
        assert_eq!(
            compressed,
            vec![
                9.1, 2.3, 6.4, 7.4, 3.6, 4.3, 5.3, 5.6, 8.7, 4.7, 4.7, 9.1, 2.3, 6.4, 7.4, 3.6, 4.3, 5.3, 5.6, 8.7,
                8.7, 4.7, 9.1, 2.3, 6.4, 7.4, 3.6, 4.3, 5.3, 5.6, 5.6, 8.7, 4.7, 9.1, 2.3, 6.4, 7.4, 3.6, 4.3, 5.3,
                5.3, 5.6, 8.7, 4.7, 9.1, 2.3, 6.4, 7.4, 3.6, 4.3,
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_halfs() -> Result<()> {
        let mut data = read_file("fixtures/floats.usdc")?;

        let single: Vec<f16> = data.get(&sdf::path("/PrimH.single")?, "default")?.try_into()?;
        assert_eq!(single, vec![f16::from_f32(2.9)]);

        let array: Vec<f16> = data.get(&sdf::path("/PrimH.simple")?, "default")?.try_into()?;
        assert_eq!(
            array,
            [4.3, 5.3, 5.6, 8.7, 4.7, 9.1, 2.3, 6.4, 7.4, 3.6]
                .into_iter()
                .map(f16::from_f32)
                .collect::<Vec<_>>()
        );

        let compressed: Vec<f16> = data.get(&sdf::path("/PrimH.copressed")?, "default")?.try_into()?;
        assert_eq!(
            compressed,
            [
                4.3, 5.3, 5.6, 8.7, 4.7, 9.1, 2.3, 6.4, 7.4, 3.6, 3.6, 4.3, 5.3, 5.6, 8.7, 4.7, 9.1, 2.3, 6.4, 7.4,
                7.4, 3.6, 4.3, 5.3, 5.6, 8.7, 4.7, 9.1, 2.3, 6.4, 6.4, 7.4, 3.6, 4.3, 5.3, 5.6, 8.7, 4.7, 9.1, 2.3,
                2.3, 6.4, 7.4, 3.6, 4.3, 5.3, 5.6, 8.7, 4.7, 9.1,
            ]
            .into_iter()
            .map(f16::from_f32)
            .collect::<Vec<_>>()
        );

        Ok(())
    }

    #[test]
    fn test_read_time_series() -> Result<()> {
        let mut data = read_file("fixtures/timesamples.usdc")?;

        let samples: sdf::TimeSampleMap = dbg!(data.get(&sdf::path("/Prim.prop")?, "timeSamples")?.try_into()?);
        assert_eq!(samples.len(), 2);

        let keys = samples.iter().map(|(d, _)| d).copied().collect::<Vec<_>>();
        assert_eq!(keys, vec![4.0, 5.0]);

        assert!(matches!(&samples[0].1, sdf::Value::Double(x) if x.len() == 1 && x[0] == 40.0));
        assert!(matches!(samples[1].1, sdf::Value::ValueBlock));

        Ok(())
    }

    #[test]
    fn test_read_array_fields() -> Result<()> {
        let mut data = read_file("fixtures/fields.usdc")?;

        // defaultPrim = "World"
        let default_prim = data.get(&sdf::Path::abs_root(), "defaultPrim")?;
        assert_eq!(default_prim.as_str(), "World");

        // float4[] clippingPlanes = []
        let clipping_planes = data.get(&sdf::path("/World.clippingPlanes")?, "default")?;
        assert!(matches!(clipping_planes, sdf::Value::Vec4f(..)));
        assert_eq!(clipping_planes.as_f32_slice(), Some([].as_slice()));

        // float2 clippingRange = (1, 10000000)
        let clipping_range = data.get(&sdf::path("/World.clippingRange")?, "default")?;
        assert!(matches!(clipping_range, sdf::Value::Vec2f(..)));
        assert_eq!(clipping_range.as_f32_slice(), Some([1.0, 10000000.0].as_slice()));

        // float3 diffuseColor = (0.18, 0.18, 0.18)
        let diffuse_color = data.get(&sdf::path("/World.diffuseColor")?, "default")?;
        assert!(matches!(diffuse_color, sdf::Value::Vec3f(..)));
        assert_eq!(diffuse_color.as_f32_slice(), Some([0.18, 0.18, 0.18].as_slice()));

        // int[] faceVertexCounts = [1, 2, 3, 4, 5, 6]
        let face_vertex_counts = data.get(&sdf::path("/World.faceVertexCounts")?, "default")?;
        assert!(matches!(face_vertex_counts, sdf::Value::Int(..)));
        assert_eq!(face_vertex_counts.as_int_slice(), Some([1, 2, 3, 4, 5, 6].as_slice()));

        // normal3f[] normals = [(0, 1, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 0), (0, 0, 1), (1, 0, 0)]
        let normals = data.get(&sdf::path("/World.normals")?, "default")?;
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
        let xform_op_rotate_xyz = data.get(&sdf::path("/World.xformOp:rotateXYZ")?, "default")?;
        assert!(matches!(xform_op_rotate_xyz, sdf::Value::Vec3d(..)));
        assert_eq!(xform_op_rotate_xyz.as_f64_slice(), Some([0.0, 0.0, 0.0].as_slice()));

        // double3 xformOp:scale = (1, 1, 1)
        let xform_op_scale = data.get(&sdf::path("/World.xformOp:scale")?, "default")?;
        assert!(matches!(xform_op_scale, sdf::Value::Vec3d(..)));
        assert_eq!(xform_op_scale.as_f64_slice(), Some([1.0, 1.0, 1.0].as_slice()));

        // double3 xformOp:translate = (0, 1, 0)
        let xform_op_translate = data.get(&sdf::path("/World.xformOp:translate")?, "default")?;
        assert!(matches!(xform_op_translate, sdf::Value::Vec3d(..)));
        assert_eq!(xform_op_translate.as_f64_slice(), Some([0.0, 1.0, 0.0].as_slice()));

        Ok(())
    }
}
