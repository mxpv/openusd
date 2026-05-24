//! Aggregate binding discovery: walk a SkelRoot subtree once and
//! return every `(skeleton, skinned_prim, animation_source)` tuple.
//!
//! Covers the "Discovering Bindings On Skinnable Primitives" entry
//! point from the UsdSkel API intro. The C++ implementation hangs
//! this off a stateful `UsdSkelCache` populated against a SkelRoot;
//! the Rust port keeps it stateless — one walk, one allocation, plain
//! returned data.

use anyhow::Result;

use crate::sdf::Path;
use crate::Stage;

use super::read::{read_inherited_animation_source, read_inherited_skeleton, read_skel_binding};
use super::tokens::{API_SKEL_BINDING, T_SKELETON, T_SKEL_ROOT};
use super::types::ReadSkelBinding;

/// One discovered skinned-prim binding under a SkelRoot.
///
/// All paths are the prim paths as they appear on the composed stage.
/// `binding` carries the per-mesh `SkelBindingAPI` data verbatim;
/// `skeleton` / `animation_source` are the *resolved* paths, walking
/// up the namespace to find the nearest authored binding (per Pixar's
/// inheritance rule).
#[derive(Debug, Clone)]
pub struct SkelBinding {
    /// Path of the skinned prim (typically a Mesh) carrying
    /// `SkelBindingAPI`.
    pub prim: String,
    /// Resolved `skel:skeleton` target. `None` when no ancestor
    /// (including the prim itself) authors one.
    pub skeleton: Option<String>,
    /// Resolved `skel:animationSource` target. `None` when no
    /// ancestor authors one.
    pub animation_source: Option<String>,
    /// The raw `SkelBindingAPI` data authored on `prim`.
    pub binding: ReadSkelBinding,
}

/// Discover every skinnable prim under `skel_root` and resolve each
/// one's inherited skeleton + animation source.
///
/// Mirrors Pixar's `UsdSkelCache::ComputeSkelBindings`, but stateless:
/// the cache pattern doesn't carry its weight in a non-thread-pool
/// single-shot reader. Callers that need to cache results can hold
/// the returned `Vec` for as long as they want.
///
/// `skel_root` is expected to be the path of a `SkelRoot` prim; this
/// function does NOT walk outside its subtree (per the UsdSkel rule
/// that SkelRoot is the enclosing scope for skeletal processing).
pub fn discover_bindings(stage: &Stage, skel_root: &Path) -> Result<Vec<SkelBinding>> {
    let mut out = Vec::new();
    let mut first_err: Result<()> = Ok(());
    stage.traverse(|path| {
        // Restrict to the SkelRoot's subtree. `has_prefix` handles the
        // SkelRoot == "/" case correctly (every absolute path has "/"
        // as a prefix).
        if first_err.is_err() || !path.has_prefix(skel_root) {
            return;
        }
        let mut visit = || -> Result<()> {
            let api = stage.api_schemas(path)?;
            if !api.iter().any(|s| s == API_SKEL_BINDING) {
                return Ok(());
            }
            let Some(binding) = read_skel_binding(stage, path)? else {
                return Ok(());
            };
            let skeleton = read_inherited_skeleton(stage, path)?;
            let animation_source = read_inherited_animation_source(stage, path)?;
            out.push(SkelBinding {
                prim: path.as_str().to_string(),
                skeleton,
                animation_source,
                binding,
            });
            Ok(())
        };
        if let Err(e) = visit() {
            first_err = Err(e);
        }
    })?;
    first_err?;
    Ok(out)
}

/// Discover every `Skeleton` prim under `skel_root`. Useful when a
/// SkelRoot encloses multiple skeletons (the spec permits this; the
/// AnimationSource binding then has to be authored carefully to
/// disambiguate which skeleton each animation drives).
pub fn discover_skeletons(stage: &Stage, skel_root: &Path) -> Result<Vec<String>> {
    let mut out = Vec::new();
    let mut first_err: Result<()> = Ok(());
    stage.traverse(|path| {
        if first_err.is_err() || !path.has_prefix(skel_root) {
            return;
        }
        match stage.type_name(path) {
            Ok(Some(t)) if t == T_SKELETON => out.push(path.as_str().to_string()),
            Ok(_) => {}
            Err(e) => first_err = Err(e),
        }
    })?;
    first_err?;
    Ok(out)
}

/// Find every `SkelRoot` prim on a stage. Convenience entry point
/// for tools that don't know upfront where the SkelRoots live.
pub fn find_skel_roots(stage: &Stage) -> Result<Vec<String>> {
    let mut out = Vec::new();
    let mut first_err: Result<()> = Ok(());
    stage.traverse(|path| {
        if first_err.is_err() {
            return;
        }
        match stage.type_name(path) {
            Ok(Some(t)) if t == T_SKEL_ROOT => out.push(path.as_str().to_string()),
            Ok(_) => {}
            Err(e) => first_err = Err(e),
        }
    })?;
    first_err?;
    Ok(out)
}
