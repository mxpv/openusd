//! Aggregate binding discovery: walk a Root subtree once and return every
//! skinnable prim together with its resolved skeleton + animation source.
//!
//! Covers the "Discovering Bindings On Skinnable Primitives" entry point from
//! the UsdSkel API intro. The C++ implementation hangs this off a stateful
//! `UsdSkelCache` populated against a Root; the Rust port keeps it
//! stateless — one walk, one allocation, plain returned data.

use openusd::Result;

use openusd::sdf::Path;
use openusd::usd::{PrimPredicate, Stage};

use super::BindingAPI;

/// One discovered skinned-prim binding under a Root.
///
/// `binding` is the per-mesh [`BindingAPI`] view; `skeleton` /
/// `animation_source` are the *resolved* targets, walking up the namespace to
/// the nearest authored binding (per Pixar's inheritance rule).
#[derive(Clone)]
pub struct SkelBinding {
    /// Path of the skinned prim (typically a Mesh) carrying `BindingAPI`.
    pub prim: String,
    /// Resolved `skel:skeleton` target. `None` when no ancestor (including the
    /// prim itself) authors one.
    pub skeleton: Option<Path>,
    /// Resolved `skel:animationSource` target. `None` when no ancestor authors
    /// one.
    pub animation_source: Option<Path>,
    /// The `BindingAPI` view authored on `prim`.
    pub binding: BindingAPI,
}

/// Discover every skinnable prim under `skel_root` and resolve each one's
/// inherited skeleton + animation source.
///
/// Mirrors Pixar's `UsdSkelCache::ComputeSkelBindings`, but stateless: the
/// cache pattern doesn't carry its weight in a single-shot reader. Callers that
/// need to cache results can hold the returned `Vec`.
///
/// `skel_root` is expected to be the path of a `Root` prim; this function
/// does NOT walk outside its subtree (per the UsdSkel rule that Root is the
/// enclosing scope for skeletal processing).
pub fn discover_bindings(stage: &Stage, skel_root: &Path) -> Result<Vec<SkelBinding>> {
    let mut out = Vec::new();
    let mut first_err: Result<()> = Ok(());
    stage.traverse(PrimPredicate::DEFAULT_PROXIES, |path| {
        // Restrict to the Root's subtree. `has_prefix` handles the
        // Root == "/" case correctly (every absolute path has "/" as a
        // prefix).
        if first_err.is_err() || !path.has_prefix(skel_root) {
            return;
        }
        let mut visit = || -> Result<()> {
            let Some(binding) = BindingAPI::get(stage, path.clone())? else {
                return Ok(());
            };
            out.push(SkelBinding {
                prim: path.as_str().to_string(),
                skeleton: binding.inherited_skeleton()?,
                animation_source: binding.inherited_animation_source()?,
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
