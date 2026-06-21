//! Binary file format (`usdc`) implementation.

use std::{borrow::Cow, cell::RefCell, collections::HashMap, fmt::Debug, io, mem, path::Path};

use anyhow::{Context, Result};
use layout::ValueRep;

mod coding;
mod layout;
mod reader;
mod writer;

pub use layout::{version, Version};
pub use reader::{CrateFile, ReadExt};
pub use writer::CrateWriter;

use crate::{ar, sdf, tf};

/// USDC binary format magic bytes (`PXR-USDC`).
pub const MAGIC: &[u8] = b"PXR-USDC";

/// A spec's type plus where its fields live. The crate stores fields
/// deduplicated and shared across specs, so a spec read from the file keeps only
/// the start of its fieldset; the fields are resolved on demand from the compact
/// [`CrateFile`] arrays rather than expanded into a per-spec list. Fields
/// authored after load are layered in a small overlay, leaving the backend both
/// lazy and writable (C++ `Usd_CrateData` likewise keeps each field as either a
/// `ValueRep` into the crate or an in-memory `VtValue`).
#[derive(Debug)]
struct Spec {
    /// Specifies the type of an object.
    ty: sdf::SpecType,
    /// Start index into the file's `fieldsets` for the fields read from the
    /// crate, or `None` for a spec created in memory.
    fieldset: Option<usize>,
    /// Fields authored after load, layered over the crate fields in authored
    /// order. `Some` sets or overrides a field; `None` tombstones one so it
    /// reads as absent even when the crate holds it.
    authored: Vec<(String, Option<sdf::Value>)>,
}

impl Spec {
    /// Returns the authored override for `field`: `Some(&Some(value))` when set,
    /// `Some(&None)` when tombstoned, `None` when the crate fields alone decide.
    fn authored(&self, field: &str) -> Option<&Option<sdf::Value>> {
        self.authored.iter().find(|(k, _)| k == field).map(|(_, v)| v)
    }

    /// Sets the authored override for `field`, replacing any prior one.
    fn set_authored(&mut self, field: &str, value: Option<sdf::Value>) {
        if let Some(slot) = self.authored.iter_mut().find(|(k, _)| k == field) {
            slot.1 = value;
        } else {
            self.authored.push((field.to_owned(), value));
        }
    }

    /// Drops any authored override for `field`, restoring authored order so a
    /// later set re-appends rather than reusing the old slot.
    fn remove_authored(&mut self, field: &str) {
        self.authored.retain(|(k, _)| k != field);
    }
}

/// High level interface to binary data.
pub struct CrateData<R> {
    file: RefCell<CrateFile<R>>,
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

        // Index each spec by its path, recording only its type and the start of
        // its fieldset. The fields themselves stay in the file's compact,
        // deduplicated arrays and are resolved on demand.
        let specs = mem::take(&mut file.specs);
        let mut data = HashMap::with_capacity(specs.len());

        for spec in &specs {
            let path = file.paths[spec.path_index].clone();
            data.insert(
                path,
                Spec {
                    ty: spec.spec_type,
                    fieldset: Some(spec.fieldset_index),
                    authored: Vec::new(),
                },
            );
        }

        Ok(Self {
            file: RefCell::new(file),
            data,
        })
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

    fn has_field(&self, path: &sdf::Path, field: &str) -> bool {
        let Some(spec) = self.data.get(path) else {
            return false;
        };
        if let Some(authored) = spec.authored(field) {
            return authored.is_some();
        }
        match spec.fieldset {
            Some(start) => crate_fields(&self.file.borrow(), start).any(|(name, _)| name == field),
            None => false,
        }
    }

    #[inline]
    fn spec_type(&self, path: &sdf::Path) -> Option<sdf::SpecType> {
        self.data.get(path).map(|spec| spec.ty)
    }

    fn try_field(&self, path: &sdf::Path, field: &str) -> Result<Option<Cow<'_, sdf::Value>>, sdf::DataError> {
        let Some(spec) = self.data.get(path) else {
            return Ok(None);
        };
        if let Some(authored) = spec.authored(field) {
            return Ok(authored.as_ref().map(Cow::Borrowed));
        }
        let Some(start) = spec.fieldset else {
            return Ok(None);
        };
        let rep = crate_fields(&self.file.borrow(), start)
            .find(|(name, _)| *name == field)
            .map(|(_, rep)| rep);
        let Some(rep) = rep else {
            return Ok(None);
        };
        // The crate value decoder still reports failures as `anyhow`; box it as
        // the typed `DataError`'s source at this trait boundary.
        let value = self.file.borrow_mut().value(rep).map_err(|e| sdf::DataError::Decode {
            path: path.clone(),
            field: field.to_owned(),
            source: e.into(),
        })?;
        Ok(Some(Cow::Owned(value)))
    }

    fn list_fields(&self, path: &sdf::Path) -> Option<Vec<String>> {
        let spec = self.data.get(path)?;
        let mut names = Vec::new();
        if let Some(start) = spec.fieldset {
            for (name, _) in crate_fields(&self.file.borrow(), start) {
                // A tombstoned crate field is skipped; an overridden one keeps
                // its crate position and is not duplicated by the overlay pass.
                if !matches!(spec.authored(name), Some(None)) {
                    names.push(name.to_owned());
                }
            }
        }
        for (field, value) in &spec.authored {
            if value.is_some() && !names.iter().any(|n| n == field) {
                names.push(field.clone());
            }
        }
        Some(names)
    }

    fn spec_paths(&self) -> Vec<sdf::Path> {
        let mut paths: Vec<sdf::Path> = self.data.keys().cloned().collect();
        paths.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        paths
    }

    fn create_spec(&mut self, path: sdf::Path, ty: sdf::SpecType) {
        self.data.insert(
            path,
            Spec {
                ty,
                fieldset: None,
                authored: Vec::new(),
            },
        );
    }

    fn erase_spec(&mut self, path: &sdf::Path) {
        self.data.remove(path);
    }

    fn set_field(&mut self, path: &sdf::Path, field: &str, value: sdf::Value) {
        match self.data.get_mut(path) {
            Some(spec) => spec.set_authored(field, Some(value)),
            None => debug_assert!(false, "set_field on absent spec at {path}"),
        }
    }

    fn erase_field(&mut self, path: &sdf::Path, field: &str) {
        let Some(spec) = self.data.get_mut(path) else {
            return;
        };
        // A tombstone is only needed to mask a field the crate holds; for an
        // authored-only or absent field, dropping the overlay entry keeps erase
        // idempotent and lets a later set re-append in authored order.
        let masks_crate = spec
            .fieldset
            .is_some_and(|start| crate_fields(&self.file.borrow(), start).any(|(name, _)| name == field));
        if masks_crate {
            spec.set_authored(field, None);
        } else {
            spec.remove_authored(field);
        }
    }
}

/// Walks a crate spec's fieldset from `start` to its terminator, yielding each
/// field's resolved name and value representation. Names borrow the shared token
/// table, so iterating makes no per-spec copy.
fn crate_fields<R>(file: &CrateFile<R>, start: usize) -> impl Iterator<Item = (&str, ValueRep)> + '_ {
    file.fieldsets
        .get(start..)
        .unwrap_or(&[])
        .iter()
        .map_while(|slot| *slot)
        .map(move |index| {
            let field = &file.fields[index];
            (field_name(file, field.token_index), field.value_rep)
        })
}

/// Resolves a crate token index to a field name, translating the crate's
/// internal property-children token to the Sdf `propertyChildren` key the rest
/// of the toolkit uses.
fn field_name<R>(file: &CrateFile<R>, token_index: usize) -> &str {
    let raw = file.tokens[token_index].as_str();
    if raw == CRATE_PROPERTY_CHILDREN {
        sdf::ChildrenKey::PropertyChildren.as_str()
    } else {
        raw
    }
}

/// Read `usdc` data from a file on disk.
pub fn read_file(path: impl AsRef<Path>) -> Result<Box<dyn sdf::AbstractData>> {
    let file = std::fs::File::open(path)?;
    let data = CrateData::open(file, true)?;

    Ok(Box::new(data))
}

/// Binary crate format (`.usdc`) as an [`sdf::FileFormat`], wrapping
/// [`CrateData`] and [`CrateWriter`]. Also the default writer for the ambiguous
/// `.usd` extension (C++ `USD_WRITE_NEW_USD_FILES_AS_BINARY`).
pub struct UsdcFileFormat;

impl sdf::FileFormat for UsdcFileFormat {
    fn format_id(&self) -> tf::Token {
        tf::Token::new("usdc")
    }

    fn extensions(&self) -> &[&str] {
        &["usdc", "usd"]
    }

    fn read(&self, resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Result<sdf::LayerData> {
        let bytes = resolver.open_asset(resolved)?.read_all()?;
        let data = CrateData::open(io::Cursor::new(bytes), true).context("failed to parse USDC layer")?;
        Ok(Box::new(data))
    }

    fn write(&self, data: &dyn sdf::AbstractData, mut sink: &mut dyn sdf::WriteSeek) -> Result<()> {
        CrateWriter::write(data, &mut sink)
    }
}

/// The crate (binary) format names the property-children field "properties",
/// while the rest of the toolkit uses the Sdf token "propertyChildren". The
/// crate reader (`CrateData::open`) and writer translate between the two at that
/// boundary, matching the reference crate implementation.
const CRATE_PROPERTY_CHILDREN: &str = "properties";

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf;
    use crate::gf::f16;
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

        let data = read_file(path)?;

        let prim_children: Vec<_> = data
            .get_field(&sdf::Path::abs_root(), "primChildren")?
            .into_owned()
            .try_as_token_vec()
            .unwrap();
        assert_eq!(
            prim_children.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
            ["SoC_ElephantWithMonochord"]
        );

        let elephant: Vec<_> = data
            .get_field(&sdf::path("/SoC_ElephantWithMonochord")?, "primChildren")?
            .into_owned()
            .try_as_token_vec()
            .unwrap();

        assert_eq!(
            elephant.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
            ["Materials", "Object", "CharacterAudioSource"]
        );

        let materials: Vec<_> = data
            .get_field(&sdf::path("/SoC_ElephantWithMonochord/Materials")?, "primChildren")?
            .into_owned()
            .try_as_token_vec()
            .unwrap();

        assert_eq!(
            materials.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
            ["Elefant_Mat_68050", "Monochord_Mat_68062"]
        );

        Ok(())
    }

    #[test]
    fn test_read_custom_layer_data() {
        let data = read_file("fixtures/fields.usdc").unwrap();

        let custom_layer_data = data.get_field(&sdf::Path::abs_root(), "customLayerData").unwrap();

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
    fn erase_then_reauthor_appends() {
        let mut data = read_file("fixtures/fields.usdc").unwrap();
        let path = sdf::path("/erase_order").unwrap();
        data.create_spec(path.clone(), sdf::SpecType::Prim);

        // Erasing an absent field is a no-op, and re-authoring a field appends
        // it in authored order rather than reusing an earlier slot.
        data.erase_field(&path, "alpha");
        data.set_field(&path, "beta", sdf::Value::Token("b".into()));
        data.set_field(&path, "alpha", sdf::Value::Token("a".into()));

        assert_eq!(data.list_fields(&path).unwrap(), ["beta", "alpha"]);
    }

    #[test]
    fn erase_masks_crate_field() {
        let mut data = read_file("fixtures/fields.usdc").unwrap();
        let root = sdf::Path::abs_root();
        assert!(data.has_field(&root, "customLayerData"));

        // A tombstone hides a field the crate holds.
        data.erase_field(&root, "customLayerData");
        assert!(!data.has_field(&root, "customLayerData"));
        assert!(data.try_field(&root, "customLayerData").unwrap().is_none());
    }

    #[test]
    fn test_read_bool() -> Result<()> {
        let data = read_file("fixtures/fields.usdc")?;

        let single = data
            .get_field(&sdf::path("/World.flipNormals")?, "default")?
            .into_owned()
            .try_as_bool()
            .unwrap();

        assert!(single);

        let bool_array = data
            .get_field(&sdf::path("/World.boolArray")?, "default")?
            .into_owned()
            .try_as_bool_vec()
            .unwrap();

        assert_eq!(bool_array, vec![true, true, false, false, true, false]);

        Ok(())
    }

    #[test]
    fn test_read_chars() -> Result<()> {
        let data = read_file("fixtures/fields.usdc")?;

        let single_char = data
            .get_field(&sdf::path("/World.singleChar")?, "default")?
            .into_owned()
            .try_as_uchar()
            .unwrap();

        assert_eq!(single_char, 128);

        let char_array = data
            .get_field(&sdf::path("/World.chars")?, "default")?
            .into_owned()
            .try_as_uchar_vec()
            .unwrap();

        assert_eq!(char_array, vec![128, 129, 130, 131, 132, 133, 134, 135, 136, 137]);

        Ok(())
    }

    #[test]
    fn test_read_quat_floats() -> Result<()> {
        let data = read_file("fixtures/fields.usdc")?;

        let quat = data
            .get_field(&sdf::path("/World.quatfSingle")?, "default")?
            .into_owned()
            .try_as_quatf()
            .unwrap();

        // USDC bytes are `[x, y, z, w]` (Pixar GfQuat layout); the
        // reader reorders to `(w, x, y, z)` to match USDA convention.
        assert_eq!(quat, gf::quatf(1.4, 2.9, 8.5, 4.6));

        let quat = data
            .get_field(&sdf::path("/World.quatfArr")?, "default")?
            .into_owned()
            .try_as_quatf_vec()
            .unwrap();

        assert_eq!(
            quat,
            vec![
                gf::quatf(4.2, 3.5, 2.6, 3.6), // 1
                gf::quatf(2.4, 5.3, 6.3, 5.2), // 2
                gf::quatf(7.1, 4.3, 2.4, 6.4), // 3
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_quat_doubles() -> Result<()> {
        let data = read_file("fixtures/fields.usdc")?;

        let quat = data
            .get_field(&sdf::path("/World.quatdSingle")?, "default")?
            .into_owned()
            .try_as_quatd()
            .unwrap();

        // USDC bytes are `[x, y, z, w]`; reader returns `(w, x, y, z)`.
        assert_eq!(quat, gf::quatd(2.4, 5.3, 6.3, 5.2));

        let quat = data
            .get_field(&sdf::path("/World.quatdArr")?, "default")?
            .into_owned()
            .try_as_quatd_vec()
            .unwrap();

        assert_eq!(
            quat,
            vec![
                gf::quatd(4.2, 3.5, 2.6, 3.6), // 1
                gf::quatd(7.1, 4.3, 2.4, 6.4), // 2
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_quat_half() -> Result<()> {
        let data = read_file("fixtures/fields.usdc")?;

        let quat = data
            .get_field(&sdf::path("/World.quathSingle")?, "default")?
            .into_owned()
            .try_as_quath()
            .unwrap();

        // USDC bytes are `[x, y, z, w]`; reader returns `(w, x, y, z)`.
        assert_eq!(
            quat,
            gf::quath(
                f16::from_f32(3.5),
                f16::from_f32(4.6),
                f16::from_f32(2.5),
                f16::from_f32(7.6)
            )
        );

        let quat = data
            .get_field(&sdf::path("/World.quathArr")?, "default")?
            .into_owned()
            .try_as_quath_vec()
            .unwrap();

        assert_eq!(
            quat,
            vec![
                gf::quath(
                    f16::from_f32(4.7),
                    f16::from_f32(2.4),
                    f16::from_f32(7.8),
                    f16::from_f32(8.5)
                ), // 1
                gf::quath(
                    f16::from_f32(4.6),
                    f16::from_f32(6.7),
                    f16::from_f32(5.6),
                    f16::from_f32(5.3)
                ), // 2
            ]
        );

        Ok(())
    }

    #[test]
    fn test_read_sub_layers() -> Result<()> {
        let data = read_file("fixtures/expressions.usdc")?;

        let sub_layer_offsets = data
            .get_field(&sdf::path("/")?, "subLayerOffsets")?
            .into_owned()
            .try_as_layer_offset_vec()
            .unwrap()
            .into_iter()
            .next()
            .unwrap();

        assert_eq!(sub_layer_offsets.offset, 0.0);
        assert_eq!(sub_layer_offsets.scale, 1.0);

        let sub_layers = data
            .get_field(&sdf::path("/")?, "subLayers")?
            .into_owned()
            .try_as_string_vec()
            .unwrap();
        assert_eq!(sub_layers, vec!["`\"render_pass_${RENDER_PASS}.usd\"`"]);

        Ok(())
    }

    #[test]
    fn test_read_variant_selection() -> Result<()> {
        let data = read_file("fixtures/expressions.usdc")?;

        // prepend variantSets = "displayVariantSet"
        let variant_set_names = data
            .get_field(&sdf::path("/asset1")?, "variantSetNames")?
            .into_owned()
            .try_as_string_list_op()
            .unwrap();
        assert_eq!(variant_set_names.prepended_items, vec!["displayVariantSet".to_string()]);

        let variant_selection = data
            .get_field(&sdf::path("/asset1")?, "variantSelection")?
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
        let data = read_file("fixtures/connection.usdc")?;

        let conn = data
            .get_field(&sdf::path("/boardMat/stReader.inputs:varname")?, "connectionPaths")?
            .into_owned()
            .try_as_path_list_op()
            .unwrap();

        assert!(conn.explicit);
        assert_eq!(
            conn.explicit_items,
            vec![sdf::path("/TexModel/boardMat.inputs:frame:stPrimvarName")?]
        );

        let conn = data
            .get_field(&sdf::path("/boardMat.outputs:surface")?, "connectionPaths")?
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
        let data = read_file("fixtures/reference.usdc")?;

        let references = data
            .get_field(&sdf::path("/MarbleCollection/Marble_Red")?, "references")?
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
        let data = read_file("fixtures/payload.usdc")?;

        let payload = data
            .get_field(&sdf::path("/MySphere1")?, "payload")?
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
            .get_field(&sdf::path("/MySphere2")?, "payload")?
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
        let data = read_file("fixtures/floats.usdc")?;

        let single = data
            .get_field(&sdf::path("/PrimD.single")?, "default")?
            .into_owned()
            .try_as_double()
            .unwrap();
        assert_eq!(single, 4.3_f64);

        let array = data
            .get_field(&sdf::path("/PrimD.simple")?, "default")?
            .into_owned()
            .try_as_double_vec()
            .unwrap();
        assert_eq!(array, vec![0.5, 1.7, 2.4, 3.5, 4.9, 5.3, 6.2, 7.8, 8.6, 9.3]);

        let compressed = data
            .get_field(&sdf::path("/PrimD.copressed")?, "default")?
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
        let data = read_file("fixtures/floats.usdc")?;

        let single = data
            .get_field(&sdf::path("/PrimF.single")?, "default")?
            .into_owned()
            .try_as_float()
            .unwrap();
        assert_eq!(single, 3.5);

        let array = data
            .get_field(&sdf::path("/PrimF.simple")?, "default")?
            .into_owned()
            .try_as_float_vec()
            .unwrap();
        assert_eq!(array, vec![9.1, 2.3, 6.4, 7.4, 3.6, 4.3, 5.3, 5.6, 8.7, 4.7]);

        let compressed = data
            .get_field(&sdf::path("/PrimF.copressed")?, "default")?
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
        let data = read_file("fixtures/floats.usdc")?;

        let single = data
            .get_field(&sdf::path("/PrimH.single")?, "default")?
            .into_owned()
            .try_as_half()
            .unwrap();

        assert_eq!(single, f16::from_f32(2.9));

        let array = data
            .get_field(&sdf::path("/PrimH.simple")?, "default")?
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
            .get_field(&sdf::path("/PrimH.copressed")?, "default")?
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
        let data = read_file("fixtures/timesamples.usdc")?;

        let samples = data
            .get_field(&sdf::path("/Prim.prop")?, "timeSamples")?
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
        let data = read_file("fixtures/ints.usdc")?;

        assert_eq!(
            data.get_field(&sdf::path("/Prim32.single")?, "default")?
                .into_owned()
                .try_as_int()
                .unwrap(),
            12938
        );

        assert_eq!(
            data.get_field(&sdf::path("/Prim32.compressed")?, "default")?
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
        let data = read_file("fixtures/ints.usdc")?;

        assert_eq!(
            data.get_field(&sdf::path("/Prim64.single")?, "default")?
                .into_owned()
                .try_as_int_64()
                .unwrap(),
            1234567890
        );

        assert_eq!(
            data.get_field(&sdf::path("/Prim64.compressed")?, "default")?
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
        let data = read_file("fixtures/ints.usdc")?;

        assert_eq!(
            data.get_field(&sdf::path("/PrimU32.single")?, "default")?
                .into_owned()
                .try_as_uint()
                .unwrap(),
            80129
        );

        assert_eq!(
            data.get_field(&sdf::path("/PrimU32.compressed")?, "default")?
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
        let data = read_file("fixtures/ints.usdc")?;

        assert_eq!(
            data.get_field(&sdf::path("/PrimU64.single")?, "default")?
                .into_owned()
                .try_as_uint_64()
                .unwrap(),
            432423654
        );

        assert_eq!(
            data.get_field(&sdf::path("/PrimU64.compressed")?, "default")?
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
        let data = read_file("fixtures/fields.usdc")?;

        // defaultPrim = "World"
        let default_prim = data.get_field(&sdf::Path::abs_root(), "defaultPrim")?;
        assert_eq!(default_prim.try_as_token_ref().unwrap().as_str(), "World");

        // float4[] clippingPlanes = []
        let clipping_planes = data.get_field(&sdf::path("/World.clippingPlanes")?, "default")?;
        assert!(clipping_planes.into_owned().try_as_vec_4f_vec().unwrap().is_empty());

        // float2 clippingRange = (1, 10000000)
        let clipping_range = data.get_field(&sdf::path("/World.clippingRange")?, "default")?;
        assert_eq!(
            clipping_range.into_owned().try_as_vec_2f().unwrap(),
            gf::vec2f(1.0, 10000000.0)
        );

        // float3 diffuseColor = (0.18, 0.18, 0.18)
        let diffuse_color = data.get_field(&sdf::path("/World.diffuseColor")?, "default")?;
        assert_eq!(
            diffuse_color.into_owned().try_as_vec_3f().unwrap(),
            gf::vec3f(0.18, 0.18, 0.18)
        );

        // int[] faceVertexCounts = [1, 2, 3, 4, 5, 6]
        let face_vertex_counts = data.get_field(&sdf::path("/World.faceVertexCounts")?, "default")?;
        assert_eq!(
            &face_vertex_counts.into_owned().try_as_int_vec().unwrap(),
            &[1, 2, 3, 4, 5, 6]
        );

        // normal3f[] normals = [(0, 1, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 0), (0, 0, 1), (1, 0, 0)]
        let normals = data.get_field(&sdf::path("/World.normals")?, "default")?;
        assert_eq!(
            normals.try_as_vec_3f_vec_ref().unwrap(),
            &[
                gf::vec3f(0.0, 1.0, 0.0),
                gf::vec3f(1.0, 0.0, 0.0),
                gf::vec3f(0.0, 1.0, 0.0),
                gf::vec3f(0.0, 0.0, 1.0),
                gf::vec3f(0.0, 1.0, 0.0),
                gf::vec3f(0.0, 0.0, 1.0),
                gf::vec3f(1.0, 0.0, 0.0),
            ]
        );

        // double3 xformOp:rotateXYZ = (0, 0, 0)
        let xform_op_rotate_xyz = data.get_field(&sdf::path("/World.xformOp:rotateXYZ")?, "default")?;
        assert_eq!(
            *xform_op_rotate_xyz.try_as_vec_3d_ref().unwrap(),
            gf::vec3d(0.0, 0.0, 0.0)
        );

        // double3 xformOp:scale = (1, 1, 1)
        let xform_op_scale = data.get_field(&sdf::path("/World.xformOp:scale")?, "default")?;
        assert_eq!(*xform_op_scale.try_as_vec_3d_ref().unwrap(), gf::vec3d(1.0, 1.0, 1.0));

        // double3 xformOp:translate = (0, 1, 0)
        let xform_op_translate = data.get_field(&sdf::path("/World.xformOp:translate")?, "default")?;
        assert_eq!(
            *xform_op_translate.try_as_vec_3d_ref().unwrap(),
            gf::vec3d(0.0, 1.0, 0.0)
        );

        Ok(())
    }

    #[test]
    fn test_read_time_code() -> Result<()> {
        let data = read_file("fixtures/sdf_types.usdc")?;

        let time_code = data
            .get_field(&sdf::path("/World.timeCodeValue")?, "default")?
            .into_owned()
            .try_as_time_code()
            .unwrap();
        assert_eq!(time_code, sdf::TimeCode(24.0));

        let time_code_array = data
            .get_field(&sdf::path("/World.timeCodeArray")?, "default")?
            .into_owned()
            .try_as_time_code_vec()
            .unwrap();
        assert_eq!(
            time_code_array,
            vec![sdf::TimeCode(1.0), sdf::TimeCode(12.0), sdf::TimeCode(24.0)]
        );

        Ok(())
    }

    #[test]
    fn test_read_target_paths() -> Result<()> {
        let data = read_file("fixtures/sdf_types.usdc")?;

        let targets = data
            .get_field(&sdf::path("/World.targets")?, "targetPaths")?
            .into_owned()
            .try_as_path_list_op()
            .unwrap();

        assert!(targets.explicit);
        assert_eq!(
            targets.explicit_items,
            vec![sdf::path("/World/ChildA")?, sdf::path("/World/ChildB")?]
        );

        Ok(())
    }

    /// String arrays should have a readable default value.
    #[test]
    fn test_read_string_array_default() -> Result<()> {
        let data = read_file(
            "vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/binary/gen_string.usdc",
        )?;

        let array = data
            .get_field(&sdf::path("/root.array")?, "default")?
            .into_owned()
            .try_as_string_vec()
            .unwrap();

        assert_eq!(array, vec!["Hello/World", "Good/Bye"]);

        Ok(())
    }

    /// gf::Vec2h single value should read half-floats, not raw integers.
    #[test]
    fn test_read_vec2h_single() -> Result<()> {
        let data =
            read_file("vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/binary/gen_vec2h.usdc")?;

        let single = data
            .get_field(&sdf::path("/root.single")?, "default")?
            .into_owned()
            .try_as_vec_2h()
            .unwrap();

        #[allow(clippy::approx_constant)]
        let expected_x = f16::from_f32(3.14);
        assert_eq!(single[0], expected_x);
        assert_eq!(single[1], f16::from_f32(4.824));

        // Inlined value should also read correctly.
        let inlined = data
            .get_field(&sdf::path("/root.inlined")?, "default")?
            .into_owned()
            .try_as_vec_2h()
            .unwrap();

        assert_eq!(inlined[0], f16::from_f32(0.0));
        assert_eq!(inlined[1], f16::from_f32(1.0));

        Ok(())
    }
}
