//! Imageable / Boundable cross-cutting authoring.
//!
//! Mirrors the cross-cutting readers in [`super::super::read`].
//! `set_visibility` / `set_purpose` author the Imageable attributes
//! on any UsdGeom prim; `set_extent` authors the Boundable attribute
//! on boundable prim types.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::geom::tokens::{A_EXTENT, A_PURPOSE, A_VISIBILITY};
use crate::schemas::geom::types::{Purpose, Visibility};

use super::common::{author_uniform_token, author_vec3f_pair_array};

/// Set `visibility` on a UsdGeomImageable. Per Pixar's spec, an
/// `invisible` opinion on any ancestor prunes the subtree.
pub fn set_visibility(stage: &Stage, prim: &Path, visibility: Visibility) -> Result<()> {
    author_uniform_token(stage, prim, A_VISIBILITY, visibility.as_token())
}

/// Set `purpose` on a UsdGeomImageable. The enum enforces the spec's
/// allowedTokens (`default` / `render` / `proxy` / `guide`).
pub fn set_purpose(stage: &Stage, prim: &Path, purpose: Purpose) -> Result<()> {
    author_uniform_token(stage, prim, A_PURPOSE, purpose.as_token())
}

/// Set `extent` on a UsdGeomBoundable — two `vector3f` corners
/// `[(min_x, min_y, min_z), (max_x, max_y, max_z)]`.
pub fn set_extent(stage: &Stage, prim: &Path, extent: [[f32; 3]; 2]) -> Result<()> {
    author_vec3f_pair_array(stage, prim, A_EXTENT, extent)
}

/// Chainable handle returned by [`apply_imageable_overrides`]; lets
/// callers wrap an existing prim spec and override `visibility` /
/// `purpose` / `extent` opinions without explicitly retyping the
/// path each time.
pub struct ImageableAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> ImageableAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    pub fn set_visibility(self, visibility: Visibility) -> Result<Self> {
        set_visibility(self.prim.stage(), self.prim.path(), visibility)?;
        Ok(self)
    }

    pub fn set_purpose(self, purpose: Purpose) -> Result<Self> {
        set_purpose(self.prim.stage(), self.prim.path(), purpose)?;
        Ok(self)
    }

    pub fn set_extent(self, extent: [[f32; 3]; 2]) -> Result<Self> {
        set_extent(self.prim.stage(), self.prim.path(), extent)?;
        Ok(self)
    }
}

/// Open an existing prim at `path` as `over` for setting Imageable /
/// Boundable opinions. The typed `*Author` returned by the per-shape
/// helpers in sibling modules already expose these setters too —
/// reach for `apply_imageable_overrides` when you need to override
/// these fields on a prim defined elsewhere (under a reference, etc.).
pub fn apply_imageable_overrides<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<ImageableAuthor<'s>> {
    let prim = stage.override_prim(path)?;
    Ok(ImageableAuthor { prim })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn visibility_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        set_visibility(&stage, &sdf::path("/Mesh")?, Visibility::Invisible)?;

        assert_eq!(
            crate::schemas::geom::read_visibility(&stage, &sdf::path("/Mesh")?)?,
            Visibility::Invisible,
        );
        Ok(())
    }

    #[test]
    fn purpose_and_extent_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Cube")?.set_type_name("Cube")?;
        set_purpose(&stage, &sdf::path("/Cube")?, Purpose::Guide)?;
        set_extent(&stage, &sdf::path("/Cube")?, [[-1.0, -1.0, -1.0], [1.0, 1.0, 1.0]])?;

        assert_eq!(
            crate::schemas::geom::read_purpose(&stage, &sdf::path("/Cube")?)?,
            Purpose::Guide,
        );
        let extent = crate::schemas::geom::read_extent(&stage, &sdf::path("/Cube")?)?.expect("extent");
        assert_eq!(extent, [[-1.0, -1.0, -1.0], [1.0, 1.0, 1.0]]);
        Ok(())
    }

    #[test]
    fn imageable_overrides_chain() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        apply_imageable_overrides(&stage, sdf::path("/Mesh")?)?
            .set_visibility(Visibility::Inherited)?
            .set_purpose(Purpose::Render)?;

        assert_eq!(
            crate::schemas::geom::read_purpose(&stage, &sdf::path("/Mesh")?)?,
            Purpose::Render,
        );
        Ok(())
    }
}
