//! Prim composition index.
//!
//! A [`PrimIndex`] records, for a single composed prim, the ordered list of
//! layer specs that contribute opinions — from strongest to weakest. The
//! ordering follows USD's LIVERPS strength rules:
//!
//! 1. **L**ocal opinions (root layer stack / sublayers)
//! 2. **I**nherits
//! 3. **V**ariant sets
//! 4. **R**eferences
//! 5. **P**ayloads
//! 6. **S**pecializes
//!
//! See <https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html>

use crate::sdf::Path;

/// The type of composition arc that introduced a [`Node`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArcType {
    /// Direct opinions from the root layer stack (sublayers).
    Root,
    /// Inherited from a class prim.
    Inherit,
    /// Contributed by a selected variant.
    Variant,
    /// Brought in via a reference arc.
    Reference,
    /// Brought in via a payload arc.
    Payload,
    /// Contributed by a specializes arc (weakest).
    Specialize,
}

/// A single contributing spec in the composition index.
///
/// Each node points to a specific layer (by index) and the path within that
/// layer where the prim's opinions live. The path may differ from the
/// composed prim path when namespace remapping is involved (e.g. references).
#[derive(Debug, Clone)]
pub struct Node {
    /// Index into the stage's layer list.
    pub layer_index: usize,
    /// The path within that layer (may differ from composed path due to remapping).
    pub path: Path,
    /// The composition arc that introduced this node.
    pub arc: ArcType,
}

/// Composition index for a single prim.
///
/// Contains an ordered list of [`Node`]s from strongest to weakest.
/// Value resolution walks this list and takes the first opinion found.
#[derive(Debug, Clone)]
pub struct PrimIndex {
    /// Nodes ordered from strongest to weakest.
    pub nodes: Vec<Node>,
}

impl PrimIndex {
    /// Returns `true` if no layers contribute opinions for this prim.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}
