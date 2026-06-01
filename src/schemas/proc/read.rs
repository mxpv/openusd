//! Reader for the [UsdProc](super) schema family.

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::Stage;

use super::tokens::*;
use super::types::*;

/// Read a `GenerativeProcedural` prim. Returns `None` when the prim is not
/// typed `GenerativeProcedural`, so a caller can't fabricate one from an
/// arbitrary prim.
pub fn read_generative_procedural(stage: &Stage, prim: &Path) -> Result<Option<ReadGenerativeProcedural>> {
    if stage.type_name(prim)?.as_deref() != Some(T_GENERATIVE_PROCEDURAL) {
        return Ok(None);
    }
    Ok(Some(ReadGenerativeProcedural {
        procedural_system: read_token(stage, prim, A_PROCEDURAL_SYSTEM)?,
    }))
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(
        match stage.field::<Value>(prim.append_property(name)?, FieldKey::Default)? {
            Some(Value::Token(s) | Value::String(s)) => Some(s),
            _ => None,
        },
    )
}
