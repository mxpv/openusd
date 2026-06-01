//! Read struct for the [UsdProc](super) schema family.

/// A `GenerativeProcedural` prim's procedural-specific attributes.
///
/// The prim is also `Boundable` / `Xformable`; its transform, visibility,
/// purpose, and extent are read/authored through the UsdGeom layer, and
/// its input parameters live in the `primvars:` namespace.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ReadGenerativeProcedural {
    /// `proceduralSystem` - the system responsible for evaluating the
    /// procedural (e.g. a Houdini Engine / RenderMan convention). No spec
    /// default; `None` when unauthored.
    pub procedural_system: Option<String>,
}
