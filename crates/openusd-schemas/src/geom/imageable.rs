//! What `UsdGeomImageable` answers beyond its own properties.

use openusd::Result;
use openusd::sdf;
use openusd::tf;

use super::tokens;
use super::{ImageableSchema, Purpose, Visibility};

/// The questions `visibility` and `purpose` are actually asked, both of which
/// are answered by walking namespace rather than by reading one prim.
///
/// Every [`ImageableSchema`] answers them, so a view has them wherever the
/// generated accessors are.
pub trait ImageableExt: ImageableSchema {
    /// Resolve the effective composed `visibility`, walking ancestors
    /// (C++ `ComputeVisibility`): an `invisible` opinion on this prim or any
    /// ancestor prunes the subtree, so the result is
    /// [`Visibility::Invisible`]; otherwise [`Visibility::Inherited`].
    fn compute_visibility(&self) -> Result<Visibility> {
        let stage = self.stage();
        let mut cur = self.path().clone();
        loop {
            if stage
                .field::<tf::Token>(cur.append_property(tokens::VISIBILITY)?, sdf::FieldKey::Default)?
                .and_then(Visibility::from_token)
                .unwrap_or_default()
                == Visibility::Invisible
            {
                return Ok(Visibility::Invisible);
            }
            match cur.parent() {
                Some(p) if !p.is_abs_root() => cur = p,
                _ => return Ok(Visibility::Inherited),
            }
        }
    }

    /// Resolve the effective composed `purpose` (C++ `ComputePurpose`):
    /// inherited from the closest ancestor with an authored opinion, falling
    /// back to [`Purpose::Default`]. An authored-but-unrecognized token stops
    /// the walk and resolves to [`Purpose::Default`].
    fn compute_purpose(&self) -> Result<Purpose> {
        let stage = self.stage();
        let mut cur = self.path().clone();
        loop {
            if let Some(token) =
                stage.field::<tf::Token>(cur.append_property(tokens::PURPOSE)?, sdf::FieldKey::Default)?
            {
                return Ok(Purpose::from_token(token).unwrap_or_default());
            }
            match cur.parent() {
                Some(p) if !p.is_abs_root() => cur = p,
                _ => return Ok(Purpose::Default),
            }
        }
    }
}

impl<T: ImageableSchema> ImageableExt for T {}
