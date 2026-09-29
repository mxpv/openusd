//! `UsdGeomXformCache` — world-space transforms, memoized across a hierarchy.
//!
//! An [`XformCache`] answers where a prim sits in world space at one time
//! without re-evaluating every ancestor per query. Each prim it visits keeps
//! an [`XformQuery`] (its ordered ops and reset flag) and, once computed, its
//! local-to-world matrix, which a descendant's query reuses.
//!
//! The cache does not observe the stage. Stage edits do not refresh the op
//! list, reset flag or world matrix an entry holds. Call [`XformCache::clear`]
//! after an edit to `xformOpOrder`, to which op attributes exist, or to an op
//! value already folded into a cached matrix.
//!
//! Each op reads its value through a [`usd::AttributeQuery`], which
//! revalidates its value source against later edits. An edited value may
//! therefore appear in a transform computed afterwards, but not reliably: a
//! prim not yet cached still inherits a stale cached ancestor matrix, and
//! [`XformCache::set_time`] drops matrices only when the time actually
//! changes. Only `clear` guarantees that an edit is seen.

use std::collections::HashMap;

use openusd::gf;
use openusd::usd;

use super::XformQuery;
use crate::SchemaError;

/// A per-time cache of local-to-world transforms (C++ `UsdGeomXformCache`).
///
/// Entries are keyed by [`usd::Prim`]. One cache serves prims of several
/// stages, and each instance proxy of a shared prototype prim is its own
/// entry carrying its own instance's transform. Queries take `&mut self`,
/// since answering one may fill the cache.
///
/// A prim that is not `Xformable` (a `Scope`, an untyped prim, the
/// pseudo-root) contributes identity and passes its parent's transform
/// through. A prim that does not exist on its stage answers identity.
#[derive(Default)]
pub struct XformCache {
    entries: HashMap<usd::Prim, Entry>,
    time: Option<usd::TimeCode>,
}

/// What the cache holds for one prim: its ops, and its local-to-world matrix
/// at the cache's time once computed.
struct Entry {
    query: XformQuery,
    ctm: Option<gf::Matrix4d>,
}

impl XformCache {
    /// A cache answering at `time`, where `None` is the default time. The
    /// [`Default`] cache answers at the default time.
    pub fn new(time: impl Into<Option<usd::TimeCode>>) -> Self {
        Self {
            entries: HashMap::new(),
            time: time.into(),
        }
    }

    /// The time the cache answers at, `None` for the default time (C++
    /// `GetTime`).
    pub fn time(&self) -> Option<usd::TimeCode> {
        self.time
    }

    /// Answer at `time` from now on (C++ `SetTime`). A different time drops
    /// every cached matrix and keeps each prim's ops; the same time changes
    /// nothing.
    pub fn set_time(&mut self, time: impl Into<Option<usd::TimeCode>>) {
        let time = time.into();
        if time == self.time {
            return;
        }
        for entry in self.entries.values_mut() {
            entry.ctm = None;
        }
        self.time = time;
    }

    /// Drop everything cached (C++ `Clear`), as needed after a stage edit.
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// `prim`'s local-to-world transform, its own ops included (C++
    /// `GetLocalToWorldTransform`).
    pub fn local_to_world_transform(&mut self, prim: &usd::Prim) -> Result<gf::Matrix4d, SchemaError> {
        if self.admit(prim)?.is_none() {
            return Ok(gf::Matrix4d::IDENTITY);
        }
        self.ctm(prim)
    }

    /// The local-to-world transform of `prim`'s parent: where `prim`'s own
    /// ops are applied from (C++ `GetParentToWorldTransform`). Identity for
    /// the pseudo-root.
    pub fn parent_to_world_transform(&mut self, prim: &usd::Prim) -> Result<gf::Matrix4d, SchemaError> {
        if self.admit(prim)?.is_none() {
            return Ok(gf::Matrix4d::IDENTITY);
        }
        match prim.parent() {
            Some(parent) => self.ctm(&parent),
            None => Ok(gf::Matrix4d::IDENTITY),
        }
    }

    /// `prim`'s local transform and whether it resets the transform stack
    /// (C++ `GetLocalTransformation`). The ops are cached; the matrix is
    /// evaluated per call.
    pub fn local_transformation(&mut self, prim: &usd::Prim) -> Result<(gf::Matrix4d, bool), SchemaError> {
        let time = self.time;
        match self.admit(prim)? {
            Some(entry) => Ok((
                entry.query.local_transformation(time)?,
                entry.query.resets_xform_stack(),
            )),
            None => Ok((gf::Matrix4d::IDENTITY, false)),
        }
    }

    /// The product of the local transforms from `prim` up to but not
    /// including `ancestor`, and whether one of them resets the transform
    /// stack, which ends the product there (C++ `ComputeRelativeTransform`).
    ///
    /// When `ancestor` is not an ancestor of `prim`, this is `prim`'s
    /// local-to-world transform. The local transforms are cached; the product
    /// is not.
    pub fn compute_relative_transform(
        &mut self,
        prim: &usd::Prim,
        ancestor: &usd::Prim,
    ) -> Result<(gf::Matrix4d, bool), SchemaError> {
        let mut xform = gf::Matrix4d::IDENTITY;
        if self.admit(prim)?.is_none() {
            return Ok((xform, false));
        }
        let time = self.time;
        let mut current = Some(prim.clone());
        while let Some(p) = current.filter(|p| p != ancestor) {
            let query = &self.entry(&p)?.query;
            // Row-vector convention: each ancestor's transform applies after,
            // growing the product on the right.
            xform = xform * query.local_transformation(time)?;
            if query.resets_xform_stack() {
                return Ok((xform, true));
            }
            current = p.parent();
        }
        Ok((xform, false))
    }

    /// `true` when `prim`'s ops reset the transform stack (C++
    /// `GetResetXformStack`).
    pub fn resets_xform_stack(&mut self, prim: &usd::Prim) -> Result<bool, SchemaError> {
        Ok(self.admit(prim)?.is_some_and(|entry| entry.query.resets_xform_stack()))
    }

    /// `true` when `prim`'s local transform might differ between times (C++
    /// `TransformMightBeTimeVarying`). Its ancestors are not consulted.
    pub fn transform_might_be_time_varying(&mut self, prim: &usd::Prim) -> Result<bool, SchemaError> {
        match self.admit(prim)? {
            Some(entry) => Ok(entry.query.transform_might_be_time_varying()?),
            None => Ok(false),
        }
    }

    /// `true` when the attribute named `name` is one of `prim`'s ops (C++
    /// `IsAttributeIncludedInLocalTransform`).
    pub fn is_attribute_included_in_local_transform(
        &mut self,
        prim: &usd::Prim,
        name: &str,
    ) -> Result<bool, SchemaError> {
        Ok(self
            .admit(prim)?
            .is_some_and(|entry| entry.query.is_attribute_included_in_local_transform(name)))
    }

    /// The local-to-world transform of `prim`, a prim that exists (C++
    /// `_GetCtm`).
    ///
    /// Climbs from `prim` until an ancestor with a cached matrix, a prim that
    /// resets the stack, or the pseudo-root, then folds the local transforms
    /// back down, caching each level's matrix on the way.
    fn ctm(&mut self, prim: &usd::Prim) -> Result<gf::Matrix4d, SchemaError> {
        let time = self.time;
        let mut base = gf::Matrix4d::IDENTITY;
        let mut chain = Vec::new();
        let mut current = Some(prim.clone());
        while let Some(p) = current.filter(|p| !p.path().is_abs_root()) {
            let entry = self.entry(&p)?;
            if let Some(ctm) = entry.ctm {
                base = ctm;
                break;
            }
            // A prim that resets the stack ends the climb: its matrix is its
            // local transform alone.
            current = match entry.query.resets_xform_stack() {
                true => None,
                false => p.parent(),
            };
            chain.push((entry.query.local_transformation(time)?, p));
        }

        // TODO(rayon): once a shared ancestor's matrix is cached, sibling
        // subtrees fold independently, the seam C++ `UsdGeomBBoxCache` uses
        // with one cache per thread.
        for (local, p) in chain.into_iter().rev() {
            base = local * base;
            if let Some(entry) = self.entries.get_mut(&p) {
                entry.ctm = Some(base);
            }
        }
        Ok(base)
    }

    /// The entry for `prim`, or `None` when `prim` does not exist on its
    /// stage, which C++ `_GetCtm` answers with identity. Only a prim not yet
    /// cached is checked, since the cache holds only prims that exist.
    fn admit(&mut self, prim: &usd::Prim) -> Result<Option<&mut Entry>, SchemaError> {
        if !self.entries.contains_key(prim) && !prim.is_valid()? {
            return Ok(None);
        }
        self.entry(prim).map(Some)
    }

    /// The entry for `prim`, a prim that exists, built on first use (C++
    /// `_GetCacheEntryForPrim`). Every ancestor of a prim that exists does
    /// too, so the climbs reach their entries through here.
    fn entry(&mut self, prim: &usd::Prim) -> Result<&mut Entry, SchemaError> {
        if !self.entries.contains_key(prim) {
            let query = XformQuery::for_prim(prim)?;
            self.entries.insert(prim.clone(), Entry { query, ctm: None });
        }
        Ok(self.entries.get_mut(prim).expect("inserted above"))
    }
}

#[cfg(test)]
mod tests {
    use super::XformCache;
    use crate::SchemaError;
    use crate::geom::{Xform, XformableExt};
    use openusd::gf;
    use openusd::usd;

    /// Each instance proxy of one prototype prim sits under its own
    /// instance's transform.
    #[test]
    fn instance_proxies_distinct() -> Result<(), SchemaError> {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Proto"
{
    def Xform "Child"
    {
        double3 xformOp:translate = (0, 0, 1)
        uniform token[] xformOpOrder = ["xformOp:translate"]
    }
}

def Xform "A" (
    instanceable = true
    references = </Proto>
)
{
    double3 xformOp:translate = (10, 0, 0)
    uniform token[] xformOpOrder = ["xformOp:translate"]
}

def Xform "B" (
    instanceable = true
    references = </Proto>
)
{
    double3 xformOp:translate = (20, 0, 0)
    uniform token[] xformOpOrder = ["xformOp:translate"]
}
"#,
        )?;
        let (a, b) = (stage.prim("/A/Child")?, stage.prim("/B/Child")?);
        assert!(a.is_instance_proxy()? && b.is_instance_proxy()?);

        let mut cache = XformCache::default();
        assert_eq!(
            cache.local_to_world_transform(&a)?,
            gf::Matrix4d::translation([10.0, 0.0, 1.0])
        );
        assert_eq!(
            cache.local_to_world_transform(&b)?,
            gf::Matrix4d::translation([20.0, 0.0, 1.0])
        );
        assert_eq!(
            cache.parent_to_world_transform(&b)?,
            gf::Matrix4d::translation([20.0, 0.0, 0.0])
        );
        Ok(())
    }

    /// A stage edit is seen once the cache is cleared, not before.
    #[test]
    fn clear_after_edit() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let parent = Xform::define(&stage, "/P")?.set_translate(gf::vec3d(1.0, 0.0, 0.0))?;
        Xform::define(&stage, "/P/C")?.set_translate(gf::vec3d(0.0, 1.0, 0.0))?;
        let child = stage.prim("/P/C")?;

        let mut cache = XformCache::default();
        let before = gf::Matrix4d::translation([1.0, 1.0, 0.0]);
        assert_eq!(cache.local_to_world_transform(&child)?, before);

        let parent = parent.set_translate(gf::vec3d(5.0, 0.0, 0.0))?;
        assert_eq!(
            cache.local_to_world_transform(&child)?,
            before,
            "the cached matrix stands"
        );
        cache.clear();
        assert_eq!(
            cache.local_to_world_transform(&child)?,
            gf::Matrix4d::translation([5.0, 1.0, 0.0])
        );

        // An edited op order is likewise fixed in the cached query.
        parent.set_xform_op_order(Vec::<String>::new())?;
        assert!(cache.is_attribute_included_in_local_transform(&stage.prim("/P")?, "xformOp:translate")?);
        cache.clear();
        assert!(!cache.is_attribute_included_in_local_transform(&stage.prim("/P")?, "xformOp:translate")?);
        assert_eq!(
            cache.local_to_world_transform(&child)?,
            gf::Matrix4d::translation([0.0, 1.0, 0.0])
        );
        Ok(())
    }

    /// A prim that does not exist under a translated parent answers
    /// identity, and leaves the parent's cached answer alone.
    #[test]
    fn missing_prim_identity() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        Xform::define(&stage, "/Parent")?.set_translate(gf::vec3d(1.0, 2.0, 3.0))?;
        let parent = stage.prim("/Parent")?;
        let missing = stage.prim("/Parent/Missing")?;
        let translate = gf::Matrix4d::translation([1.0, 2.0, 3.0]);

        let mut cache = XformCache::default();
        assert_eq!(cache.local_to_world_transform(&parent)?, translate);

        assert_eq!(cache.local_to_world_transform(&missing)?, gf::Matrix4d::IDENTITY);
        assert_eq!(cache.parent_to_world_transform(&missing)?, gf::Matrix4d::IDENTITY);
        assert_eq!(cache.local_transformation(&missing)?, (gf::Matrix4d::IDENTITY, false));
        assert_eq!(
            cache.compute_relative_transform(&missing, &parent)?,
            (gf::Matrix4d::IDENTITY, false)
        );
        assert!(!cache.resets_xform_stack(&missing)?);
        assert!(!cache.transform_might_be_time_varying(&missing)?);
        assert!(!cache.is_attribute_included_in_local_transform(&missing, "xformOp:translate")?);
        assert!(!cache.entries.contains_key(&missing), "a missing prim is not cached");

        assert_eq!(cache.local_to_world_transform(&parent)?, translate);
        Ok(())
    }

    /// A new time recomputes the matrices from the ops already read; the
    /// same time keeps the matrices.
    #[test]
    fn set_time_keeps_queries() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        Xform::define(&stage, "/P")?.set_translate(gf::vec3d(0.0, 0.0, 0.0))?;
        stage
            .attribute("/P.xformOp:translate")?
            .set_at(gf::vec3d(1.0, 0.0, 0.0), usd::TimeCode::new(1.0))?
            .set_at(gf::vec3d(2.0, 0.0, 0.0), usd::TimeCode::new(2.0))?;
        let p = stage.prim("/P")?;

        let mut cache = XformCache::new(usd::TimeCode::new(1.0));
        assert_eq!(
            cache.local_to_world_transform(&p)?,
            gf::Matrix4d::translation([1.0, 0.0, 0.0])
        );
        cache.set_time(usd::TimeCode::new(1.0));
        assert!(cache.entries[&p].ctm.is_some(), "the same time keeps the matrix");

        cache.set_time(usd::TimeCode::new(2.0));
        assert_eq!(cache.time(), Some(usd::TimeCode::new(2.0)));
        assert!(cache.entries[&p].ctm.is_none() && cache.entries.contains_key(&p));
        assert_eq!(
            cache.local_to_world_transform(&p)?,
            gf::Matrix4d::translation([2.0, 0.0, 0.0])
        );
        Ok(())
    }
}
