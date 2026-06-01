//! Readers for the [UsdVol](super) schema family.

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::Stage;

use super::tokens::*;
use super::types::*;

/// Read a `Volume` prim, enumerating its `field:<name>` relationships as
/// `(field name, target path)` pairs (sorted by field name). Returns `None`
/// when the prim is not typed `Volume`.
pub fn read_volume(stage: &Stage, prim: &Path) -> Result<Option<ReadVolume>> {
    if stage.type_name(prim)?.as_deref() != Some(T_VOLUME) {
        return Ok(None);
    }
    let mut fields = Vec::new();
    for name in stage.prim_properties(prim.clone())? {
        let Some(field_name) = name.strip_prefix(NS_FIELD) else {
            continue;
        };
        let rel = prim.append_property(&name)?;
        if let Some(target) = stage.relationship_targets(&rel)?.into_iter().next() {
            fields.push((field_name.to_string(), target.as_str().to_string()));
        }
    }
    fields.sort();
    Ok(Some(ReadVolume { fields }))
}

/// Read an `OpenVDBAsset` field prim. Returns `None` when not typed
/// `OpenVDBAsset`.
pub fn read_openvdb_asset(stage: &Stage, prim: &Path) -> Result<Option<ReadOpenVdbAsset>> {
    if stage.type_name(prim)?.as_deref() != Some(T_OPENVDB_ASSET) {
        return Ok(None);
    }
    Ok(Some(ReadOpenVdbAsset {
        base: read_field_asset(stage, prim)?,
        field_class: read_token(stage, prim, A_FIELD_CLASS)?,
    }))
}

/// Read a `Field3DAsset` field prim. Returns `None` when not typed
/// `Field3DAsset`.
pub fn read_field3d_asset(stage: &Stage, prim: &Path) -> Result<Option<ReadField3dAsset>> {
    if stage.type_name(prim)?.as_deref() != Some(T_FIELD3D_ASSET) {
        return Ok(None);
    }
    Ok(Some(ReadField3dAsset {
        base: read_field_asset(stage, prim)?,
        field_purpose: read_token(stage, prim, A_FIELD_PURPOSE)?,
    }))
}

/// Read the shared `FieldAsset` attributes off `prim`.
fn read_field_asset(stage: &Stage, prim: &Path) -> Result<ReadFieldAsset> {
    Ok(ReadFieldAsset {
        file_path: read_asset(stage, prim, A_FILE_PATH)?,
        field_name: read_token(stage, prim, A_FIELD_NAME)?,
        field_index: read_int(stage, prim, A_FIELD_INDEX)?,
        field_data_type: read_token(stage, prim, A_FIELD_DATA_TYPE)?,
        vector_data_role_hint: read_token(stage, prim, A_VECTOR_DATA_ROLE_HINT)?
            .and_then(|t| VectorDataRoleHint::from_token(&t))
            .unwrap_or_default(),
    })
}

fn attr_value(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    stage.field::<Value>(prim.append_property(name)?, FieldKey::Default)
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Token(s) | Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_asset(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::AssetPath(s) | Value::String(s) | Value::Token(s)) => Some(s),
        _ => None,
    })
}

fn read_int(stage: &Stage, prim: &Path, name: &str) -> Result<Option<i32>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Int(i)) => Some(i),
        // Checked narrow so an out-of-range Int64 doesn't silently wrap.
        Some(Value::Int64(i)) => i32::try_from(i).ok(),
        _ => None,
    })
}
