//! The skeletons, animations and skinnable prims beneath a `Root`, resolved
//! once and kept (C++ `UsdSkelCache`).

use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use openusd::Result;
use openusd::usd::{Prim, PrimPredicate, SchemaBase};

use super::anim_query::AnimQuery;
use super::binding::{Binding, Inherited, skeleton_under, walk};
use super::skeleton_query::{Definition, SkeletonQuery};
use super::skinning_query::{SkinningQuery, orders};
use super::{Animation, BindingAPI, Root, Skeleton};
use crate::SchemaError;

/// The queries over the skeletons, animations and skinnable prims beneath
/// one or more [`Root`]s (C++ `UsdSkelCache`).
///
/// [`populate`](Self::populate) walks a `Root` and builds a [`SkinningQuery`]
/// for each skinnable prim beneath it, along with the queries over the
/// skeletons bound to them. [`skel_query`](Self::skel_query) and
/// [`anim_query`](Self::anim_query) build their queries on first use. A
/// skeleton's definition, and an animation's query, are kept once for each
/// prim in a prototype and shared by the instance proxies that stand in for
/// it.
///
/// Every entry is keyed by its [`Prim`], which holds the stage beside the
/// path, so one cache can hold the prims of several stages. It keeps each of
/// those stages alive until it is cleared.
///
/// The cache does not observe the stage. Each query is a snapshot of the
/// structure it was built from, as its own documentation lists, and so is
/// the populate walk: which prims are skinnable and the bindings each
/// inherits. After an edit to a skeleton's joints, bind or rest transforms,
/// a binding relationship, whether a binding property is authored, an
/// influence primvar's interpolation or element size, `skel:joints`,
/// `skel:blendShapes`, an animation's `joints` or `blendShapes`, a prim's
/// type, active state or applied schemas, or the namespace beneath a
/// populated `Root`, [`clear`](Self::clear) the cache and populate it again.
#[derive(Debug, Clone, Default)]
pub struct Cache {
    /// The query over each animation, keyed by its prim in the prototype.
    anim_queries: HashMap<Prim, AnimQuery>,
    /// Each skeleton's definition, keyed by its prim in the prototype.
    /// `None` for a skeleton whose joint topology is invalid.
    definitions: HashMap<Prim, Option<Rc<Definition>>>,
    /// The query over each skeleton asked for, keyed by its prim as asked
    /// for.
    skel_queries: HashMap<Prim, Option<SkeletonQuery>>,
    /// The query over each skinnable prim populated, keyed by its prim as
    /// visited.
    skinning_queries: HashMap<Prim, SkinningQuery>,
}

impl Cache {
    /// An empty cache.
    pub fn new() -> Self {
        Self::default()
    }

    /// Drop every query the cache holds (C++ `Clear`).
    pub fn clear(&mut self) {
        *self = Self::default();
    }

    /// Build a [`SkinningQuery`] for each skinnable prim at or beneath `root`
    /// that `predicate` lets through and the cache does not hold yet (C++
    /// `Populate`).
    ///
    /// The walk skips each prim that is not imageable, along with its
    /// subtree, and stops below each skinnable prim. Each prim takes the
    /// skeleton and binding properties authored nearest to it through
    /// [`BindingAPI`], on itself or on an ancestor at or below `root`; the
    /// blend-shape bindings are read on the skinnable prim alone. A skinnable
    /// prim gets a query whether or not a skeleton is bound to it. An instance
    /// proxy's binding properties are its prototype prim's, all but the
    /// skinning method, which stays the proxy's, as in C++.
    pub fn populate(&mut self, root: &Root, predicate: PrimPredicate) -> Result<(), SchemaError> {
        walk(
            root.prim(),
            predicate,
            Inherited::default(),
            |prim, skinnable, parent: Inherited| {
                if skinnable && self.skinning_queries.contains_key(prim) {
                    return Ok(None);
                }
                let inherited = parent.under(prim, skinnable)?;
                if !skinnable {
                    return Ok(Some(inherited));
                }
                let skeleton = match &inherited.skeleton {
                    Some(skeleton) => self.skel_query_entry(skeleton)?,
                    None => None,
                };
                // The queries of one skeleton share its orders.
                let (joint_order, blend_shape_order) = orders(skeleton);
                let query = SkinningQuery::new(prim.clone(), inherited.properties, joint_order, blend_shape_order)?;
                self.skinning_queries.insert(prim.clone(), query);
                Ok(None)
            },
        )
    }

    /// The query a [`populate`](Self::populate) built for `prim`, or `None`
    /// for a prim no populate reached as skinnable (C++ `GetSkinningQuery`).
    pub fn skinning_query(&self, prim: &Prim) -> Option<&SkinningQuery> {
        self.skinning_queries.get(prim)
    }

    /// The query over `skeleton`, bound to the animation it inherits, built
    /// on first use (C++ `GetSkelQuery`). `None` when the skeleton is inactive
    /// or its joint topology is invalid.
    ///
    /// An instance proxy shares the definition of its prim in the prototype:
    /// its joints and its bind and rest poses.
    pub fn skel_query(&mut self, skeleton: &Skeleton) -> Result<Option<SkeletonQuery>> {
        Ok(self.skel_query_entry(skeleton)?.cloned())
    }

    /// The query over `anim`, built on first use (C++ `GetAnimQuery`). `None`
    /// when the animation is inactive. An instance proxy shares the query of
    /// its prim in the prototype.
    pub fn anim_query(&mut self, anim: &Animation) -> Result<Option<AnimQuery>> {
        if !anim.is_active()? {
            return Ok(None);
        }
        let prim = in_prototype(anim.prim())?;
        if let Some(query) = self.anim_queries.get(&prim) {
            return Ok(Some(query.clone()));
        }
        let query = AnimQuery::new(Animation::from_prim_unchecked(prim.clone()))?;
        self.anim_queries.insert(prim, query.clone());
        Ok(Some(query))
    }

    /// The skeletons bound beneath `root`, ordered by path, each with the
    /// queries of the skinnable prims bound to it (C++
    /// `ComputeSkelBindings`).
    ///
    /// The walk is [`populate`](Self::populate)'s, over the prims `predicate`
    /// lets through. A prim joins the binding of the skeleton in effect at it
    /// when that skeleton is active and the cache holds a skinning query for
    /// the prim, and the walk stops below it. Populate `root` first.
    pub fn skel_bindings(&self, root: &Root, predicate: PrimPredicate) -> Result<Vec<Binding>, SchemaError> {
        let mut bindings: BTreeMap<_, Binding> = BTreeMap::new();
        let mut active = HashMap::new();
        self.bound_targets(root, predicate, |skeleton, query| {
            let is_active = if let Some(&known) = active.get(skeleton.prim()) {
                known
            } else {
                let known = skeleton.is_active()?;
                active.insert(skeleton.prim().clone(), known);
                known
            };
            if !is_active {
                return Ok(false);
            }
            // TODO(perf): a binding copies each skinning query it holds;
            // sharing the queries would make the copy cheap, as C++'s is.
            bindings
                .entry(skeleton.path().clone())
                .or_insert_with(|| Binding {
                    skeleton: skeleton.clone(),
                    skinning_targets: Vec::new(),
                })
                .skinning_targets
                .push(query.clone());
            Ok(true)
        })?;
        Ok(bindings.into_values().collect())
    }

    /// The binding of `skeleton` beneath `root`: the queries of the skinnable
    /// prims bound to it, found as [`skel_bindings`](Self::skel_bindings)
    /// finds them, whether or not the skeleton is active (C++
    /// `ComputeSkelBinding`).
    pub fn skel_binding(
        &self,
        root: &Root,
        skeleton: &Skeleton,
        predicate: PrimPredicate,
    ) -> Result<Binding, SchemaError> {
        let mut skinning_targets = Vec::new();
        self.bound_targets(root, predicate, |bound, query| {
            let matches = bound.prim() == skeleton.prim();
            if matches {
                skinning_targets.push(query.clone());
            }
            Ok(matches)
        })?;
        Ok(Binding {
            skeleton: skeleton.clone(),
            skinning_targets,
        })
    }

    /// Walk `root` as [`skel_bindings`](Self::skel_bindings) does, handing
    /// `accept` each prim with a skinning query and a skeleton in effect at
    /// it. `accept` answers whether the prim is bound, which stops the walk
    /// below it.
    fn bound_targets(
        &self,
        root: &Root,
        predicate: PrimPredicate,
        mut accept: impl FnMut(&Skeleton, &SkinningQuery) -> Result<bool>,
    ) -> Result<(), SchemaError> {
        walk(root.prim(), predicate, None, |prim, _, parent: Option<Skeleton>| {
            let skeleton = skeleton_under(BindingAPI::from_prim(prim.clone())?.as_ref(), parent)?;
            if let Some(bound) = &skeleton
                && let Some(query) = self.skinning_queries.get(prim)
                && accept(bound, query)?
            {
                return Ok(None);
            }
            Ok(Some(skeleton))
        })
    }

    /// The query over `skeleton`, kept in the cache, built on first use as
    /// [`skel_query`](Self::skel_query) describes.
    fn skel_query_entry(&mut self, skeleton: &Skeleton) -> Result<Option<&SkeletonQuery>> {
        if !self.skel_queries.contains_key(skeleton.prim()) {
            let query = match self.definition(skeleton)? {
                Some(definition) => {
                    let anim = match skeleton.animation_source()? {
                        Some(anim) => self.anim_query(&anim)?,
                        None => None,
                    };
                    Some(SkeletonQuery::from_definition(skeleton.clone(), definition, anim))
                }
                None => None,
            };
            self.skel_queries.insert(skeleton.prim().clone(), query);
        }
        Ok(self.skel_queries[skeleton.prim()].as_ref())
    }

    /// The definition of `skeleton`'s prim in the prototype, read on first
    /// use. `None` when the skeleton is inactive or its joint topology is
    /// invalid.
    fn definition(&mut self, skeleton: &Skeleton) -> Result<Option<Rc<Definition>>> {
        if !skeleton.is_active()? {
            return Ok(None);
        }
        let prim = in_prototype(skeleton.prim())?;
        if let Some(definition) = self.definitions.get(&prim) {
            return Ok(definition.clone());
        }
        let definition = Definition::new(&Skeleton::from_prim_unchecked(prim.clone()))?.map(Rc::new);
        self.definitions.insert(prim, definition.clone());
        Ok(definition)
    }
}

/// The prim in the prototype that `prim` stands in for, where it is an
/// instance proxy, and `prim` itself otherwise.
pub(super) fn in_prototype(prim: &Prim) -> Result<Prim> {
    Ok(prim.prim_in_prototype()?.unwrap_or_else(|| prim.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two instances of one prototype share its skeleton's definition, and
    /// each query keeps the instance proxy it was asked for.
    #[test]
    fn instances_share_definition() -> Result<()> {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0
def Scope "Model" (instanceable = true) {
    def Skeleton "Skel" {
        uniform token[] joints = ["A", "A/B"]
    }
}
def SkelRoot "R" {
    def Scope "First" (prepend references = </Model>) {}
    def Scope "Second" (prepend references = </Model>) {}
}
"#,
        )?;
        let mut cache = Cache::new();
        for path in ["/R/First/Skel", "/R/Second/Skel"] {
            let skeleton = Skeleton::get(&stage, path)?.expect("Skeleton");
            let query = cache.skel_query(&skeleton)?.expect("valid topology");
            assert_eq!(query.skeleton().path().as_str(), path);
            assert_eq!(query.joint_order().len(), 2);
        }
        assert_eq!(cache.skel_queries.len(), 2);
        assert_eq!(cache.definitions.len(), 1);
        Ok(())
    }
}
