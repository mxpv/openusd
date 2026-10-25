//! Bindings: a skeleton with the skinnable prims bound to it (C++
//! `UsdSkelBinding`), and the walk beneath a `Root` that resolves the skeleton
//! and binding properties each prim inherits down namespace (C++
//! `UsdSkel_CacheImpl`'s populate walk and `_SkinningQueryKey`).

use openusd::usd::{Attribute, Prim, PrimPredicate, Relationship};
use openusd::{Result, tf};

use super::cache::in_prototype;
use super::decode::Bound;
use super::skeleton_query::SkeletonQuery;
use super::skinning_query::SkinningQuery;
use super::{BindingAPI, Skeleton, tokens};
use crate::{SchemaError, geom};

/// A skeleton and the skinnable prims bound to it (C++ `UsdSkelBinding`),
/// as [`Cache::skel_bindings`](super::Cache::skel_bindings) groups them.
#[derive(Debug, Clone)]
pub struct Binding {
    pub(super) skeleton: Skeleton,
    pub(super) skinning_targets: Vec<SkinningQuery>,
}

/// The binding properties a [`SkinningQuery`] is built over: the attribute
/// arguments of C++ `UsdSkelSkinningQuery`'s constructor as one value.
#[derive(Debug, Clone, Default)]
pub struct BindingProperties {
    /// `primvars:skel:jointIndices`.
    pub joint_indices: Option<Attribute>,
    /// `primvars:skel:jointWeights`.
    pub joint_weights: Option<Attribute>,
    /// `primvars:skel:skinningMethod`.
    pub skinning_method: Option<Attribute>,
    /// `primvars:skel:geomBindTransform`.
    pub geom_bind_transform: Option<Attribute>,
    /// `skel:joints`.
    pub joints: Option<Attribute>,
    /// `skel:blendShapes`.
    pub blend_shapes: Option<Attribute>,
    /// `skel:blendShapeTargets`.
    pub blend_shape_targets: Option<Relationship>,
}

/// The skeleton and binding properties a prim passes down to the prims
/// beneath it, each the nearest one with an authored value (C++
/// `UsdSkel_CacheImpl`'s `_SkinningQueryKey`). The blend-shape bindings are
/// read on the skinnable prim alone.
#[derive(Clone, Default)]
pub(super) struct Inherited {
    pub(super) skeleton: Option<Skeleton>,
    pub(super) properties: BindingProperties,
}

/// The schema types the walk tells prims apart by, interned once per walk.
struct SkelTypes {
    imageable: tf::Token,
    boundable: tf::Token,
    skeleton: tf::Token,
    skel_root: tf::Token,
}

impl Binding {
    /// `skeleton` bound to the prims of `skinning_targets` (C++
    /// `UsdSkelBinding`'s constructor).
    ///
    /// Each target must have been built against the skeleton's joint order and
    /// its animation's blend-shape order, both empty where the skeleton is
    /// inactive or its topology invalid, as a [`Cache`](super::Cache) builds
    /// its targets. A target built for another skeleton would deform wrongly
    /// under this one, and is refused with
    /// [`SchemaError::ForeignSkinningTarget`]. C++ trusts the caller.
    pub fn new(skeleton: Skeleton, skinning_targets: Vec<SkinningQuery>) -> Result<Self, SchemaError> {
        // TODO(perf): the check needs only the skeleton's joints and its
        // animation's blend shapes, and builds the whole definition, poses
        // included; a bake of the binding then builds it again.
        let query = SkeletonQuery::new(&skeleton)?;
        if let Some(foreign) = skinning_targets.iter().find(|target| !target.built_for(query.as_ref())) {
            return Err(SchemaError::ForeignSkinningTarget {
                target: foreign.prim().path().clone(),
                skeleton: skeleton.path().clone(),
            });
        }
        Ok(Self {
            skeleton,
            skinning_targets,
        })
    }

    /// The bound skeleton (C++ `GetSkeleton`).
    pub fn skeleton(&self) -> &Skeleton {
        &self.skeleton
    }

    /// The queries of the skinnable prims bound to the skeleton, in walk
    /// order (C++ `GetSkinningTargets`).
    pub fn skinning_targets(&self) -> &[SkinningQuery] {
        &self.skinning_targets
    }
}

impl Inherited {
    /// The bindings in effect at `prim`: these, with each binding `prim`
    /// authors through [`BindingAPI`] taking precedence. Only a `skinnable`
    /// prim takes its blend-shape bindings.
    ///
    /// On an instance proxy, the joint influences, the geom bind transform,
    /// `skel:joints` and the blend-shape bindings are its prim in the
    /// prototype's (C++ `_GetAttrInPrototype` and `_GetRelInPrototype`).
    /// `skel:skeleton` and `skel:skinningMethod` are the proxy's.
    pub(super) fn under(mut self, prim: &Prim, skinnable: bool) -> Result<Self> {
        let Some(binding) = BindingAPI::from_prim(prim.clone())? else {
            return Ok(self);
        };
        self.skeleton = skeleton_under(Some(&binding), self.skeleton.take())?;
        let shared = BindingAPI::from_prim_unchecked(in_prototype(prim)?);
        let properties = &mut self.properties;
        let attributes = [
            (&mut properties.joint_indices, shared.joint_indices_attr()),
            (&mut properties.joint_weights, shared.joint_weights_attr()),
            (&mut properties.skinning_method, binding.skinning_method_attr()),
            (&mut properties.geom_bind_transform, shared.geom_bind_transform_attr()),
            (&mut properties.joints, shared.joints_attr()),
        ];
        for (slot, attribute) in attributes {
            if attribute.has_authored_value()? {
                *slot = Some(attribute);
            }
        }
        if skinnable {
            let blend_shapes = shared.blend_shapes_attr();
            if blend_shapes.has_authored_value()? {
                properties.blend_shapes = Some(blend_shapes);
            }
            let targets = shared.blend_shape_targets_rel();
            if targets.has_authored_targets()? {
                properties.blend_shape_targets = Some(targets);
            }
        }
        Ok(self)
    }
}

impl SkelTypes {
    fn new() -> Self {
        Self {
            imageable: tf::Token::new(geom::tokens::IMAGEABLE),
            boundable: tf::Token::new(geom::tokens::BOUNDABLE),
            skeleton: tf::Token::new(tokens::SKELETON),
            skel_root: tf::Token::new(tokens::SKEL_ROOT),
        }
    }

    /// `None` for a prim that is not imageable, and otherwise whether it is
    /// skinnable.
    fn classify(&self, prim: &Prim) -> Result<Option<bool>> {
        let info = prim.prim_type_info()?;
        let registry = prim.stage().schema_registry();
        let is_a = |schema: &tf::Token| registry.is_a(info.schema_type_name(), schema);
        Ok(is_a(&self.imageable).then(|| self.skinnable(is_a)))
    }

    /// Whether a type `is_a` answers for is skinnable: boundable and neither
    /// a skeleton nor a skel root.
    fn skinnable(&self, is_a: impl Fn(&tf::Token) -> bool) -> bool {
        is_a(&self.boundable) && !is_a(&self.skeleton) && !is_a(&self.skel_root)
    }
}

/// The skeleton in effect at a prim: the one `binding`, the prim's
/// [`BindingAPI`] if it has one, binds or blocks, and `parent`, the one in
/// effect above it, where it authors no binding.
pub(super) fn skeleton_under(binding: Option<&BindingAPI>, parent: Option<Skeleton>) -> Result<Option<Skeleton>> {
    if let Some(binding) = binding
        && let Bound::Authored(skeleton) = binding.bound_skeleton()?
    {
        return Ok(skeleton);
    }
    Ok(parent)
}

/// Visit each prim at or beneath `root` that `predicate` lets through, each
/// before the prims beneath it, skipping a prim that is not imageable along
/// with its subtree (the walk of C++ `UsdSkelCache::Populate` and
/// `ComputeSkelBindings`). A `root` that `predicate` does not let through
/// visits nothing; a `root` that is an instance proxy lets its instance
/// proxies through, as C++ `UsdPrimRange` does. `visit` takes the prim,
/// whether it is skinnable ([`is_skinnable`]), and the state its parent
/// handed down, and answers the state to hand to its children, or `None` to
/// skip them.
pub(super) fn walk<T: Clone>(
    root: &Prim,
    predicate: PrimPredicate,
    state: T,
    mut visit: impl FnMut(&Prim, bool, T) -> Result<Option<T>, SchemaError>,
) -> Result<(), SchemaError> {
    let predicate = if root.is_instance_proxy()? {
        predicate.with_instance_proxies(true)
    } else {
        predicate
    };
    if !root.stage().prim_matches(root.path(), predicate)? {
        return Ok(());
    }
    let types = SkelTypes::new();
    let mut stack = vec![(root.clone(), None, state)];
    while let Some((prim, composed, parent)) = stack.pop() {
        let Some(skinnable) = types.classify(&prim)? else {
            continue;
        };
        let Some(state) = visit(&prim, skinnable, parent)? else {
            continue;
        };
        // TODO(rayon): sibling subtrees resolve independently of each other.
        let children = prim.filtered_children_from(predicate, composed)?;
        stack.extend(
            children
                .into_iter()
                .rev()
                .map(|(child, composed)| (child, Some(composed), state.clone())),
        );
    }
    Ok(())
}

/// `true` for a boundable prim that is neither a [`Skeleton`] nor a
/// [`Root`](super::Root) (C++ `UsdSkelIsSkinnablePrim`).
pub fn is_skinnable(prim: &Prim) -> Result<bool> {
    let info = prim.prim_type_info()?;
    let registry = prim.stage().schema_registry();
    Ok(SkelTypes::new().skinnable(|schema| registry.is_a(info.schema_type_name(), schema)))
}
