//! UsdProc schema reader + authoring.
//!
//! Decodes and authors Pixar's `UsdProc` family. The one concrete schema
//! is [`tokens::T_GENERATIVE_PROCEDURAL`] - a prim whose children are
//! generated at runtime by a named procedural system. It is also
//! `Boundable` / `Xformable` (transform / extent / visibility come from
//! the UsdGeom layer); this module covers the procedural-specific
//! `proceduralSystem` attribute.

pub mod tokens;

mod author;
mod read;
mod types;

pub use author::{define_generative_procedural, GenerativeProceduralAuthor};
pub use read::read_generative_procedural;
pub use types::ReadGenerativeProcedural;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;
    use crate::usd::Stage;
    use anyhow::Result;

    #[test]
    fn generative_procedural_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_generative_procedural(&stage, sdf::path("/World/Proc")?)?.set_procedural_system("Houdini")?;

        let p = read_generative_procedural(&stage, &sdf::path("/World/Proc")?)?.expect("GenerativeProcedural");
        assert_eq!(p.procedural_system.as_deref(), Some("Houdini"));
        Ok(())
    }

    #[test]
    fn defaults_and_type_gate() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_generative_procedural(&stage, sdf::path("/Proc")?)?;

        let p = read_generative_procedural(&stage, &sdf::path("/Proc")?)?.expect("GenerativeProcedural");
        assert_eq!(p, ReadGenerativeProcedural::default());
        assert_eq!(p.procedural_system, None);

        // A non-GenerativeProcedural prim reads back as None.
        stage.define_prim(sdf::path("/NotProc")?)?.set_type_name("Scope")?;
        assert!(read_generative_procedural(&stage, &sdf::path("/NotProc")?)?.is_none());
        Ok(())
    }
}
