//! Binary file format (`usdc`) implementation.

use std::{borrow::Cow, collections::HashMap, fmt::Debug, io, mem, path::Path};

use anyhow::{bail, Result};
use layout::ValueRep;

mod coding;
mod layout;
mod reader;

pub use layout::{version, Version};
pub use reader::{CrateFile, ReadExt};

use crate::sdf;

#[derive(Default, Debug)]
struct Spec {
    /// Specifies the type of an object.
    ty: sdf::SpecType,
    /// Spec properties.
    fields: HashMap<String, ValueRep>,
}

/// High level interface to binary data.
#[derive(Debug)]
pub struct CrateData<R> {
    file: CrateFile<R>,
    data: HashMap<sdf::Path, Spec>,
}

impl<R> CrateData<R>
where
    R: io::Read + io::Seek,
{
    /// Read binary data from any reader.
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
        self.data.get(path).is_some_and(|spec| spec.fields.contains_key(field))
    }

    #[inline]
    fn spec_type(&self, path: &sdf::Path) -> Option<sdf::SpecType> {
        self.data.get(path).map(|spec| spec.ty)
    }

    fn get(&mut self, path: &sdf::Path, field: &str) -> Result<Cow<'_, sdf::Value>> {
        let Some(spec) = self.data.get(path) else {
            bail!("No spec found for path: {path}")
        };

        let Some(value_rep) = spec.fields.get(field).cloned() else {
            bail!("No field found for path '{path}' and field '{field}'")
        };

        let value = self.file.value(value_rep)?;

        Ok(Cow::Owned(value))
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
    use std::path::Path;

    #[test]
    fn test_crate_hierarchy() -> Result<()> {
        let path = Path::new("./vendor/usd-wg-assets/full_assets/ElephantWithMonochord/SoC-ElephantWithMonochord.usdc");
        if !path.exists() {
            eprintln!(
                "Skipping test_crate_hierarchy: fixture not available at {}",
                path.display()
            );
            return Ok(());
        }

        let mut data = read_file(path)?;

        let prim_children: Vec<String> = data
            .get(&sdf::Path::abs_root(), "primChildren")?
            .into_owned()
            .try_as_token_vec()
            .unwrap();
        assert_eq!(prim_children, vec!["SoC_ElephantWithMonochord".to_string()]);

        let elephant: Vec<String> = data
            .get(&sdf::path("/SoC_ElephantWithMonochord")?, "primChildren")?
            .into_owned()
            .try_as_token_vec()
            .unwrap();

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
            .into_owned()
            .try_as_token_vec()
            .unwrap();

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
        let copyright = custom_layer_data
            .try_as_dictionary_ref()
            .unwrap()
            .get("test")
            .unwrap()
            .try_as_string_ref()
            .unwrap();

        assert_eq!(copyright, "Test string");
    }

    #[test]
    fn test_read_bool() -> Result<()> {
        let mut data = read_file("fixtures/fields.usdc")?;

        let single = data
            .get(&sdf::path("/World.flipNormals")?, "default")?
            .into_owned()
            .try_as_bool()
            .unwrap();

        assert!(single);

        let bool_array = data
            .get(&sdf::path("/World.boolArray")?, "default")?
            .into_owned()
            .try_as_bool_vec()
            .unwrap();

        assert_eq!(bool_array, vec![true, true, false, false, true, false]);

        Ok(())
    }

    #[test]
    fn test_read_chars() -> Result<()> {
        let mut data = read_file("fixtures/fields.usdc")?;

        let single_char = data
            .get(&sdf::path("/World.singleChar")?, "default")?
            .into_owned()
            .try_as_uchar()
            .unwrap();

        assert_eq!(single_char, 128);

        let char_array = data
            .get(&sdf::path("/World.chars")?, "default")?
            .into_owned()
            .try_as_uchar_vec()
            .unwrap();

        assert_eq!(char_array, vec![128, 129, 130, 131, 132, 133, 134, 135, 136, 137]);

        Ok(())
    }

    #[test]
    fn test_read_quat_floats() -> Result<()> {
        let mut data = read_file("fixtures/fields.usdc")?;

        let quat = data
            .get(&sdf::path("/World.quatfSingle")?, "default")?
            .into_owned()
            .try_as_quatf()
            .unwrap();

        assert_eq!(quat, vec![2.9, 8.5, 4.6, 1.4]);

        let quat = data
            .get(&sdf::path("/World.quatfArr")?, "default")?
            .into_owned()
            .try_as_quatf()
            .unwrap();

        assert_eq!(
            quat,
            vec![
                3.5, 2.6, 3.6, 4.2, // 1
                5.3, 6.3, 5.2, 2.4, // 2
                4.3, 2.4, 6.4, 7.1, // 3
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_quat_doubles() -> Result<()> {
        let mut data = read_file("fixtures/fields.usdc")?;

        let quat = data
            .get(&sdf::path("/World.quatdSingle")?, "default")?
            .into_owned()
            .try_as_quatd()
            .unwrap();

        assert_eq!(quat, vec![5.3, 6.3, 5.2, 2.4]);

        let quat = data
            .get(&sdf::path("/World.quatdArr")?, "default")?
            .into_owned()
            .try_as_quatd()
            .unwrap();

        assert_eq!(
            quat,
            vec![
                3.5, 2.6, 3.6, 4.2, // 1
                4.3, 2.4, 6.4, 7.1, // 2
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_quat_half() -> Result<()> {
        let mut data = read_file("fixtures/fields.usdc")?;

        let quat = data
            .get(&sdf::path("/World.quathSingle")?, "default")?
            .into_owned()
            .try_as_quath()
            .unwrap();

        assert_eq!(
            quat,
            [4.6, 2.5, 7.6, 3.5].into_iter().map(f16::from_f32).collect::<Vec<_>>()
        );

        let quat = data
            .get(&sdf::path("/World.quathArr")?, "default")?
            .into_owned()
            .try_as_quath()
            .unwrap();

        assert_eq!(
            quat,
            [
                2.4, 7.8, 8.5, 4.7, // 1
                6.7, 5.6, 5.3, 4.6, // 2
            ]
            .into_iter()
            .map(f16::from_f32)
            .collect::<Vec<_>>()
        );

        Ok(())
    }

    #[test]
    fn test_read_sub_layers() -> Result<()> {
        let mut data = read_file("fixtures/expressions.usdc")?;

        let sub_layer_offsets = data
            .get(&sdf::path("/")?, "subLayerOffsets")?
            .into_owned()
            .try_as_layer_offset_vec()
            .unwrap()
            .into_iter()
            .next()
            .unwrap();

        assert_eq!(sub_layer_offsets.offset, 0.0);
        assert_eq!(sub_layer_offsets.scale, 1.0);

        let sub_layers = data
            .get(&sdf::path("/")?, "subLayers")?
            .into_owned()
            .try_as_string_vec()
            .unwrap();
        assert_eq!(sub_layers, vec!["`\"render_pass_${RENDER_PASS}.usd\"`"]);

        Ok(())
    }

    #[test]
    fn test_read_variant_selection() -> Result<()> {
        let mut data = read_file("fixtures/expressions.usdc")?;

        // prepend variantSets = "displayVariantSet"
        let variant_set_names = data
            .get(&sdf::path("/asset1")?, "variantSetNames")?
            .into_owned()
            .try_as_string_list_op()
            .unwrap();
        assert_eq!(variant_set_names.prepended_items, vec!["displayVariantSet".to_string()]);

        let variant_selection = data
            .get(&sdf::path("/asset1")?, "variantSelection")?
            .into_owned()
            .try_as_variant_selection_map()
            .unwrap();

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

        let conn = data
            .get(&sdf::path("/boardMat/stReader.inputs:varname")?, "connectionPaths")?
            .into_owned()
            .try_as_path_list_op()
            .unwrap();

        assert!(conn.explicit);
        assert_eq!(
            conn.explicit_items,
            vec![sdf::path("/TexModel/boardMat.inputs:frame:stPrimvarName")?]
        );

        let conn = data
            .get(&sdf::path("/boardMat.outputs:surface")?, "connectionPaths")?
            .into_owned()
            .try_as_path_list_op()
            .unwrap();

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

        let references = data
            .get(&sdf::path("/MarbleCollection/Marble_Red")?, "references")?
            .into_owned()
            .try_as_reference_list_op()
            .unwrap();

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

        let payload = data
            .get(&sdf::path("/MySphere1")?, "payload")?
            .into_owned()
            .try_as_payload()
            .unwrap();

        assert_eq!(payload.asset_path, "./payload.usda");
        assert_eq!(payload.prim_path, sdf::path("/MySphere")?);

        assert!(payload.layer_offset.is_some());

        let layer_offset = payload.layer_offset.unwrap();
        assert_eq!(layer_offset.offset, 0.0);
        assert_eq!(layer_offset.scale, 1.0);

        let payload_list_op = data
            .get(&sdf::path("/MySphere2")?, "payload")?
            .into_owned()
            .try_as_payload_list_op()
            .unwrap();

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

        let single = data
            .get(&sdf::path("/PrimD.single")?, "default")?
            .into_owned()
            .try_as_double()
            .unwrap();
        assert_eq!(single, 4.3_f64);

        let array = data
            .get(&sdf::path("/PrimD.simple")?, "default")?
            .into_owned()
            .try_as_double_vec()
            .unwrap();
        assert_eq!(array, vec![0.5, 1.7, 2.4, 3.5, 4.9, 5.3, 6.2, 7.8, 8.6, 9.3]);

        let compressed = data
            .get(&sdf::path("/PrimD.copressed")?, "default")?
            .into_owned()
            .try_as_double_vec()
            .unwrap();
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

        let single = data
            .get(&sdf::path("/PrimF.single")?, "default")?
            .into_owned()
            .try_as_float()
            .unwrap();
        assert_eq!(single, 3.5);

        let array = data
            .get(&sdf::path("/PrimF.simple")?, "default")?
            .into_owned()
            .try_as_float_vec()
            .unwrap();
        assert_eq!(array, vec![9.1, 2.3, 6.4, 7.4, 3.6, 4.3, 5.3, 5.6, 8.7, 4.7]);

        let compressed = data
            .get(&sdf::path("/PrimF.copressed")?, "default")?
            .into_owned()
            .try_as_float_vec()
            .unwrap();

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

        let single = data
            .get(&sdf::path("/PrimH.single")?, "default")?
            .into_owned()
            .try_as_half()
            .unwrap();

        assert_eq!(single, f16::from_f32(2.9));

        let array = data
            .get(&sdf::path("/PrimH.simple")?, "default")?
            .into_owned()
            .try_as_half_vec()
            .unwrap();

        assert_eq!(
            array,
            [4.3, 5.3, 5.6, 8.7, 4.7, 9.1, 2.3, 6.4, 7.4, 3.6]
                .into_iter()
                .map(f16::from_f32)
                .collect::<Vec<_>>()
        );

        let compressed = data
            .get(&sdf::path("/PrimH.copressed")?, "default")?
            .into_owned()
            .try_as_half_vec()
            .unwrap();

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

        let samples = data
            .get(&sdf::path("/Prim.prop")?, "timeSamples")?
            .into_owned()
            .try_as_time_samples()
            .unwrap();
        assert_eq!(samples.len(), 2);

        let keys = samples.iter().map(|(d, _)| d).copied().collect::<Vec<_>>();
        assert_eq!(keys, vec![4.0, 5.0]);

        assert!(matches!(&samples[0].1, sdf::Value::Double(x) if *x == 40.0_f64));
        assert!(matches!(samples[1].1, sdf::Value::ValueBlock));

        Ok(())
    }

    #[test]
    fn test_read_ints_i32() -> Result<()> {
        let mut data = read_file("fixtures/ints.usdc")?;

        assert_eq!(
            data.get(&sdf::path("/Prim32.single")?, "default")?
                .into_owned()
                .try_as_int()
                .unwrap(),
            12938
        );

        assert_eq!(
            data.get(&sdf::path("/Prim32.compressed")?, "default")?
                .into_owned()
                .try_as_int_vec()
                .unwrap(),
            vec![
                1, 2, 4, 5, -3, 4, 5, -2, 3, -0, 3, 2, 4, -2, 4, 1, 8, -1, 5, -5, 2, 6, -3, 4, 6, 3, -7, 2, -3, 3, 6,
                2, 6, 6, -4, 2, -4, 6, -2, 4
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_ints_i64() -> Result<()> {
        let mut data = read_file("fixtures/ints.usdc")?;

        assert_eq!(
            data.get(&sdf::path("/Prim64.single")?, "default")?
                .into_owned()
                .try_as_int_64()
                .unwrap(),
            1234567890
        );

        assert_eq!(
            data.get(&sdf::path("/Prim64.compressed")?, "default")?
                .into_owned()
                .try_as_int_64_vec()
                .unwrap(),
            vec![
                10, 23, 48, 45, -23, 43, 65, -23, 23, -10, 34, 23, 45, -12, 34, 16, 18, -12, 65, -65, 21, 67, -43, 34,
                36, 34, -67, 25, -23, 63, 65, 23, 65, 63, -54, 23, -44, 65, -62, 54
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_ints_u32() -> Result<()> {
        let mut data = read_file("fixtures/ints.usdc")?;

        assert_eq!(
            data.get(&sdf::path("/PrimU32.single")?, "default")?
                .into_owned()
                .try_as_uint()
                .unwrap(),
            80129
        );

        assert_eq!(
            data.get(&sdf::path("/PrimU32.compressed")?, "default")?
                .into_owned()
                .try_as_uint_vec()
                .unwrap(),
            vec![
                1, 2, 4, 5, 3, 4, 5, 2, 3, 0, 3, 2, 4, 2, 4, 1, 8, 1, 5, 5, 2, 6, 3, 4, 6, 3, 7, 2, 3, 3, 6, 2, 6, 6,
                4, 2, 4, 6, 2, 4
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_ints_u64() -> Result<()> {
        let mut data = read_file("fixtures/ints.usdc")?;

        assert_eq!(
            data.get(&sdf::path("/PrimU64.single")?, "default")?
                .into_owned()
                .try_as_uint_64()
                .unwrap(),
            432423654
        );

        assert_eq!(
            data.get(&sdf::path("/PrimU64.compressed")?, "default")?
                .into_owned()
                .try_as_uint_64_vec()
                .unwrap(),
            vec![
                34, 23, 45, 12, 34, 16, 18, 12, 65, 65, 10, 23, 48, 45, 23, 43, 65, 23, 23, 10, 65, 23, 65, 63, 54, 23,
                44, 65, 62, 54, 21, 67, 43, 34, 36, 34, 67, 25, 23, 63,
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_array_fields() -> Result<()> {
        let mut data = read_file("fixtures/fields.usdc")?;

        // defaultPrim = "World"
        let default_prim = data.get(&sdf::Path::abs_root(), "defaultPrim")?;
        assert_eq!(default_prim.try_as_token_ref().unwrap(), "World");

        // float4[] clippingPlanes = []
        let clipping_planes = data.get(&sdf::path("/World.clippingPlanes")?, "default")?;
        assert!(clipping_planes.into_owned().try_as_vec_4f_ref().unwrap().is_empty());

        // float2 clippingRange = (1, 10000000)
        let clipping_range = data.get(&sdf::path("/World.clippingRange")?, "default")?;
        assert_eq!(
            &clipping_range.into_owned().try_as_vec_2f().unwrap(),
            &[1.0, 10000000.0]
        );

        // float3 diffuseColor = (0.18, 0.18, 0.18)
        let diffuse_color = data.get(&sdf::path("/World.diffuseColor")?, "default")?;
        assert_eq!(
            &diffuse_color.into_owned().try_as_vec_3f().unwrap(),
            &[0.18, 0.18, 0.18]
        );

        // int[] faceVertexCounts = [1, 2, 3, 4, 5, 6]
        let face_vertex_counts = data.get(&sdf::path("/World.faceVertexCounts")?, "default")?;
        assert_eq!(
            &face_vertex_counts.into_owned().try_as_int_vec().unwrap(),
            &[1, 2, 3, 4, 5, 6]
        );

        // normal3f[] normals = [(0, 1, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 0), (0, 0, 1), (1, 0, 0)]
        let normals = data.get(&sdf::path("/World.normals")?, "default")?;
        assert_eq!(
            normals.try_as_vec_3f_ref().unwrap(),
            &[0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 1.0, 0.0, 0.0]
        );

        // double3 xformOp:rotateXYZ = (0, 0, 0)
        let xform_op_rotate_xyz = data.get(&sdf::path("/World.xformOp:rotateXYZ")?, "default")?;
        assert_eq!(xform_op_rotate_xyz.try_as_vec_3d_ref().unwrap(), &[0.0, 0.0, 0.0]);

        // double3 xformOp:scale = (1, 1, 1)
        let xform_op_scale = data.get(&sdf::path("/World.xformOp:scale")?, "default")?;
        assert_eq!(xform_op_scale.try_as_vec_3d_ref().unwrap(), &[1.0, 1.0, 1.0]);

        // double3 xformOp:translate = (0, 1, 0)
        let xform_op_translate = data.get(&sdf::path("/World.xformOp:translate")?, "default")?;
        assert_eq!(xform_op_translate.try_as_vec_3d_ref().unwrap(), &[0.0, 1.0, 0.0]);

        Ok(())
    }
}
