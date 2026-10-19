//! The extent functions of `Skeleton` and `SkelRoot`, which bound a rig by the
//! pivots of its joints.

use openusd::gf;
use openusd::usd::{Prim, PrimPredicate, SchemaBase, TimeCode};

use super::skinning::joints_extent;
use super::{Cache, Root, Skeleton, SkeletonQuery, SkinningQuery, tokens};
use crate::SchemaError;
use crate::geom::{Boundable, Extent, ExtentContext, ExtentRegistry, XformCache};

/// Add the extent functions of `Skeleton` and `SkelRoot` (C++ registers one
/// from each schema's own file).
pub(crate) fn register_extents(registry: &mut ExtentRegistry) {
    registry
        .register(tokens::SKELETON, skeleton)
        .register(tokens::SKEL_ROOT, root);
}

/// A `Skeleton` from the box around its joints' pivots at `time`, posed by the
/// animation it inherits (C++ `_ComputeExtent` in `skeleton.cpp`). `None` for
/// a skeleton that has no [`SkeletonQuery`], cannot be posed at `time`, or has
/// no joints.
fn skeleton(
    prim: &Prim,
    time: Option<TimeCode>,
    transform: Option<gf::Mat4d>,
    _context: &ExtentContext,
) -> Result<Option<Extent>, SchemaError> {
    let Some(query) = SkeletonQuery::new(&Skeleton::from_prim_unchecked(prim.clone()))? else {
        return Ok(None);
    };
    Ok(query
        .joint_skel_transforms(time)?
        .and_then(|xforms| joints_extent(&xforms, 0.0, transform)))
}

/// A `SkelRoot` from the skeletons bound beneath it, instance proxies
/// included (C++ `_ComputeExtent` in `root.cpp`). Each adds the box around its
/// joints' pivots at `time`, carried into the root's space and padded by the
/// farthest a prim bound to it reaches past its rest pose
/// ([`SkinningQuery::extents_padding`]). Where no skeleton is bound, every
/// `Skeleton` beneath the root adds its box unpadded.
///
/// A skeleton whose transform resets the transform stack keeps its joints out
/// of `transform`. The skeletons are placed in the root's space by their
/// transforms at `time`, where C++ takes the default time. A skeleton that
/// cannot be posed at `time`, or has no joints, adds nothing.
///
/// `None` when one of the skeletons has no [`SkeletonQuery`], as C++ fails,
/// and when no skeleton adds a box, where C++ answers the corners of an empty
/// box.
fn root(
    prim: &Prim,
    time: Option<TimeCode>,
    transform: Option<gf::Mat4d>,
    _context: &ExtentContext,
) -> Result<Option<Extent>, SchemaError> {
    let root = Root::from_prim_unchecked(prim.clone());
    let mut cache = Cache::new();
    cache.populate(&root, PrimPredicate::DEFAULT_PROXIES)?;
    let bindings = cache.skel_bindings(&root, PrimPredicate::DEFAULT_PROXIES)?;
    let skeletons: Vec<(Skeleton, &[SkinningQuery])> = if bindings.is_empty() {
        skeletons_beneath(prim)?
            .into_iter()
            .map(|skeleton| (skeleton, &[][..]))
            .collect()
    } else {
        bindings
            .iter()
            .map(|binding| (binding.skeleton().clone(), binding.skinning_targets()))
            .collect()
    };
    let mut xforms = XformCache::new(time);
    let mut bound: Option<Extent> = None;
    // TODO(rayon): each skeleton's box is independent of the others'.
    for (skeleton, targets) in skeletons {
        let Some(query) = cache.skel_query(&skeleton)? else {
            return Ok(None);
        };
        let Some(skel_xforms) = query.joint_skel_transforms(time)? else {
            continue;
        };
        let mut padding = 0.0_f32;
        if let Some(rest) = query.rest_skel_transforms() {
            for target in targets {
                let boundable = Boundable::from_prim_unchecked(target.prim().clone());
                padding = padding.max(target.extents_padding(rest, &boundable)?);
            }
        }
        let (mut to_root, resets) = xforms.relative_transform(skeleton.prim(), prim)?;
        if !resets && let Some(transform) = transform {
            to_root = to_root * transform;
        }
        let Some([min, max]) = joints_extent(&skel_xforms, padding, Some(to_root)) else {
            continue;
        };
        bound = Some(match bound {
            Some([low, high]) => [low.min(min), high.max(max)],
            None => [min, max],
        });
    }
    Ok(bound)
}

/// Every `Skeleton` at or beneath `prim` among the prims the default
/// predicate lets through, instance proxies included, in depth-first order.
fn skeletons_beneath(prim: &Prim) -> Result<Vec<Skeleton>, SchemaError> {
    let mut skeletons = Vec::new();
    for prim in prim.filtered_subtree(PrimPredicate::DEFAULT_PROXIES)? {
        if let Some(skeleton) = Skeleton::from_prim(prim?)? {
            skeletons.push(skeleton);
        }
    }
    Ok(skeletons)
}
