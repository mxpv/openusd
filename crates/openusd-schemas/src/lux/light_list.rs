//! What a light list adds to its generated views: discovering the lights
//! below a prim, and keeping them as a cache on it.

use std::collections::BTreeSet;

use openusd::Result;
use openusd::usd::{self, PrimPredicate, PrimStatus, SchemaBase};
use openusd::{sdf, tf};

use super::{LightListAPI, LightListCacheBehavior, ListAPI, tokens};

/// How [`LightList::compute_light_list`] treats a cache it meets (C++
/// `UsdLuxLightListAPI::ComputeMode`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LightListMode {
    /// Take each `lightList` a prim's `lightList:cacheBehavior` says to
    /// consume, and walk only the model hierarchy below it (C++
    /// `ComputeModeConsultModelHierarchyCache`).
    ConsultCache,
    /// Walk every prim and read no cache (C++ `ComputeModeIgnoreCache`).
    IgnoreCache,
}

/// What a light list adds to its generated view (C++
/// `UsdLuxLightListAPI`), for [`LightListAPI`] and the deprecated
/// [`ListAPI`] alike.
// Both views declare the same `lightList` properties. The default bodies reach
// them through the `LightListAPI` view of the prim.
pub trait LightList: SchemaBase {
    /// The lights and light filters at and below the prim (C++
    /// `UsdLuxLightListAPI::ComputeLightList`).
    ///
    /// A prim is a light when `LightAPI` applies to it, a built-in one
    /// included, and a filter when it is a `LightFilter`. The walk goes
    /// through active, defined, non-abstract prims and into instances, and
    /// in [`LightListMode::ConsultCache`] only through models. The prim
    /// itself is always visited.
    ///
    /// A visited prim other than the pseudo-root whose
    /// `lightList:cacheBehavior` is `consumeAndContinue` adds the
    /// forwarded `lightList` targets in consult mode, and one whose
    /// behavior is `consumeAndHalt` adds them and ends the walk there. The
    /// prim need not carry the API for its cache to count.
    fn compute_light_list(&self, mode: LightListMode) -> Result<BTreeSet<sdf::Path>> {
        let mut lights = BTreeSet::new();
        if visit(self.prim(), mode, &mut lights)? {
            return Ok(lights);
        }
        let mut required = PrimStatus::ACTIVE | PrimStatus::DEFINED;
        if mode == LightListMode::ConsultCache {
            required |= PrimStatus::MODEL;
        }
        let predicate = PrimPredicate::new(required, PrimStatus::ABSTRACT).with_instance_proxies(true);
        // TODO(rayon): sibling subtrees are independent and could be walked
        // in parallel, merging their sets.
        let mut walk = self.prim().filtered_descendants(predicate)?;
        while let Some(prim) = walk.next() {
            if visit(&prim?, mode, &mut lights)? {
                walk.prune_children();
            }
        }
        Ok(lights)
    }

    /// Store `lights` as the prim's cache: the `lightList` targets and a
    /// `lightList:cacheBehavior` of `consumeAndContinue`, as one edit (C++
    /// `UsdLuxLightListAPI::StoreLightList`).
    ///
    /// An absolute path outside the prim's subtree is left out. A relative
    /// one is kept and anchored at the prim, wherever it leads, as C++ keeps
    /// it.
    fn store_light_list(&self, lights: &BTreeSet<sdf::Path>) -> Result<()> {
        let list = LightListAPI::from_prim_unchecked(self.prim().clone());
        let targets = lights
            .iter()
            .filter(|path| !path.is_abs() || path.has_prefix(list.path()));
        list.stage().edit(|edit| {
            list.light_list_rel_builder()
                .set_targets(targets)
                .in_edit(edit)
                .build()?;
            list.light_list_cache_behavior_attr_builder()
                .set(LightListCacheBehavior::ConsumeAndContinue)
                .in_edit(edit)
                .build()?;
            Ok(())
        })
    }

    /// Set `lightList:cacheBehavior` to `ignore`. A walk then reads no cache
    /// here (C++ `UsdLuxLightListAPI::InvalidateLightList`).
    fn invalidate_light_list(&self) -> Result<()> {
        LightListAPI::from_prim_unchecked(self.prim().clone())
            .light_list_cache_behavior_attr_builder()
            .set(LightListCacheBehavior::Ignore)
            .build()?;
        Ok(())
    }
}

impl LightList for LightListAPI {}

impl LightList for ListAPI {}

/// Add `prim` to `lights` if it is a light, and its cache if `mode`
/// consults one, answering whether the cache halts the walk below it (C++
/// `_Traverse` for one prim).
fn visit(prim: &usd::Prim, mode: LightListMode, lights: &mut BTreeSet<sdf::Path>) -> Result<bool> {
    if mode == LightListMode::ConsultCache && !prim.path().is_abs_root() {
        let list = LightListAPI::from_prim_unchecked(prim.clone());
        // The raw token: a value outside the schema's set is no cache.
        // TODO(perf): most model prims author no cache, and each pays a
        // composed value resolution to find that out.
        let behavior = list.light_list_cache_behavior_attr().get::<tf::Token>()?;
        match behavior.as_deref().and_then(LightListCacheBehavior::from_token) {
            Some(LightListCacheBehavior::ConsumeAndHalt) => {
                lights.extend(list.light_list_rel().forwarded_targets()?);
                return Ok(true);
            }
            Some(LightListCacheBehavior::ConsumeAndContinue) => {
                lights.extend(list.light_list_rel().forwarded_targets()?);
            }
            Some(LightListCacheBehavior::Ignore) | None => {}
        }
    }
    if prim.has_api_schema(tf::Token::new(tokens::LIGHT_API))? || prim.is_a(tf::Token::new(tokens::LIGHT_FILTER))? {
        lights.insert(prim.path().clone());
    }
    Ok(false)
}
