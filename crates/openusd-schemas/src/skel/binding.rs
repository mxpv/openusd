//! Binding discovery: the skinnable prims beneath a `Root`, each with the
//! skeleton and the binding properties it inherits down namespace (C++
//! `UsdSkelCache::Populate` and `UsdSkelCache::ComputeSkelBindings`).

use std::collections::HashMap;

use openusd::usd::{Attribute, Prim, PrimPredicate, Relationship, SchemaBase};
use openusd::{Result, sdf, tf};

use super::decode::Bound;
use super::{Animation, BindingAPI, Root, Skeleton, tokens};
use crate::geom;

/// A skinnable prim beneath a [`Root`] and the skeleton bound to it.
///
/// Each binding property is the one authored nearest to `prim`, on `prim`
/// itself or on an ancestor at or below the `Root` that carries
/// [`BindingAPI`].
#[derive(Clone)]
pub struct SkelBinding {
    /// The skinnable prim: a boundable prim that is neither a [`Skeleton`] nor
    /// a [`Root`] (C++ `UsdSkelIsSkinnablePrim`).
    pub prim: Prim,
    /// The skeleton bound to `prim`.
    pub skeleton: Skeleton,
    /// The active animation bound to `skeleton` ([`Skeleton::animation_source`];
    /// C++ `UsdSkelSkeletonQuery::GetAnimQuery`).
    pub animation_source: Option<Animation>,
    pub(super) properties: BindingProperties,
}

/// The binding properties in effect at a prim, each the nearest one with an
/// authored value (C++ `UsdSkel_CacheImpl`'s `_SkinningQueryKey`). The
/// blend-shape bindings are read on the skinnable prim alone.
#[derive(Clone, Default)]
pub(super) struct BindingProperties {
    pub(super) joint_indices: Option<Attribute>,
    pub(super) joint_weights: Option<Attribute>,
    pub(super) skinning_method: Option<Attribute>,
    pub(super) geom_bind_transform: Option<Attribute>,
    pub(super) joints: Option<Attribute>,
    pub(super) blend_shapes: Option<Attribute>,
    pub(super) blend_shape_targets: Option<Relationship>,
}

/// The skeleton and binding properties a prim passes down to the prims
/// beneath it.
#[derive(Clone, Default)]
struct Inherited {
    skeleton: Option<Skeleton>,
    properties: BindingProperties,
}

impl Inherited {
    /// The bindings in effect at `prim`: these, with each binding `prim`
    /// authors through [`BindingAPI`] taking precedence. Only a `skinnable`
    /// prim takes its blend-shape bindings.
    fn under(mut self, prim: &Prim, skinnable: bool) -> Result<Self> {
        let Some(binding) = BindingAPI::from_prim(prim.clone())? else {
            return Ok(self);
        };
        if let Bound::Authored(skeleton) = binding.bound_skeleton()? {
            self.skeleton = skeleton;
        }
        let properties = &mut self.properties;
        let attributes = [
            (&mut properties.joint_indices, binding.joint_indices_attr()),
            (&mut properties.joint_weights, binding.joint_weights_attr()),
            (&mut properties.skinning_method, binding.skinning_method_attr()),
            (&mut properties.geom_bind_transform, binding.geom_bind_transform_attr()),
            (&mut properties.joints, binding.joints_attr()),
        ];
        for (slot, attribute) in attributes {
            if attribute.has_authored_value()? {
                *slot = Some(attribute);
            }
        }
        if skinnable {
            let blend_shapes = binding.blend_shapes_attr();
            if blend_shapes.has_authored_value()? {
                properties.blend_shapes = Some(blend_shapes);
            }
            let targets = binding.blend_shape_targets_rel();
            if targets.has_authored_targets()? {
                properties.blend_shape_targets = Some(targets);
            }
        }
        Ok(self)
    }
}

/// Every skinnable prim beneath `root` that has an active skeleton bound to
/// it, in depth-first order (C++ `UsdSkelCache::ComputeSkelBindings`, without
/// the grouping by skeleton).
///
/// The walk skips each prim that is not imageable, along with its subtree, and
/// stops below each skinnable prim. Bindings authored above `root` do not
/// reach the prims beneath it.
pub fn discover_bindings(root: &Root) -> Result<Vec<SkelBinding>> {
    let mut out = Vec::new();
    // Whether each skeleton reached is active, and the animation bound to it.
    let mut skeletons: HashMap<sdf::Path, (bool, Option<Animation>)> = HashMap::new();
    let mut stack = vec![(root.prim().clone(), None, Inherited::default())];
    while let Some((prim, composed, parent)) = stack.pop() {
        let info = prim.prim_type_info()?;
        let registry = prim.stage().schema_registry();
        let is_a = |schema: &'static str| registry.is_a(info.schema_type_name(), &tf::Token::new(schema));
        if !is_a(geom::tokens::IMAGEABLE) {
            continue;
        }
        let skinnable = skinnable_type(is_a);
        let inherited = parent.under(&prim, skinnable)?;
        if skinnable {
            let Some(skeleton) = inherited.skeleton else {
                continue;
            };
            let (active, animation_source) = if let Some(found) = skeletons.get(skeleton.path()) {
                found.clone()
            } else {
                let active = skeleton.is_active()?;
                let animation_source = if active { skeleton.animation_source()? } else { None };
                skeletons.insert(skeleton.path().clone(), (active, animation_source.clone()));
                (active, animation_source)
            };
            if active {
                out.push(SkelBinding {
                    prim,
                    skeleton,
                    animation_source,
                    properties: inherited.properties,
                });
            }
            continue;
        }
        // TODO(rayon): sibling subtrees resolve independently of each other.
        let children = prim.filtered_children_from(PrimPredicate::DEFAULT_PROXIES, composed)?;
        stack.extend(
            children
                .into_iter()
                .rev()
                .map(|(child, composed)| (child, Some(composed), inherited.clone())),
        );
    }
    Ok(out)
}

/// `true` for a boundable prim that is neither a [`Skeleton`] nor a [`Root`]
/// (C++ `UsdSkelIsSkinnablePrim`).
pub fn is_skinnable(prim: &Prim) -> Result<bool> {
    let info = prim.prim_type_info()?;
    let registry = prim.stage().schema_registry();
    Ok(skinnable_type(|schema| {
        registry.is_a(info.schema_type_name(), &tf::Token::new(schema))
    }))
}

/// `true` for a prim type that `is_a` reports boundable and neither a skeleton
/// nor a skel root.
fn skinnable_type(is_a: impl Fn(&'static str) -> bool) -> bool {
    is_a(geom::tokens::BOUNDABLE) && !is_a(tokens::SKELETON) && !is_a(tokens::SKEL_ROOT)
}
