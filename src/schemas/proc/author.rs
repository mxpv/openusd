//! `GenerativeProcedural` authoring.
//!
//! Authors the procedural-specific attribute. The prim is also
//! `Boundable` / `Xformable`; its transform / extent / visibility are
//! authored through the UsdGeom layer on the same prim, and its input
//! parameters are authored as `primvars:`.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::common::author_uniform_token;
use crate::schemas::proc::tokens::*;

/// Author a `def GenerativeProcedural` prim at `path`. Returns a chainable
/// [`GenerativeProceduralAuthor`].
pub fn define_generative_procedural<'s>(
    stage: &'s Stage,
    path: impl Into<Path>,
) -> Result<GenerativeProceduralAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_GENERATIVE_PROCEDURAL)?;
    Ok(GenerativeProceduralAuthor { prim })
}

pub struct GenerativeProceduralAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> GenerativeProceduralAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `proceduralSystem` (`uniform token`).
    pub fn set_procedural_system(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_PROCEDURAL_SYSTEM, value)?;
        Ok(self)
    }
}
