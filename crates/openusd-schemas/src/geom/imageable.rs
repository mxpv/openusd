//! What `UsdGeomImageable` answers beyond its own properties.

use openusd::Result;
use openusd::gf;
use openusd::sdf;
use openusd::tf;
use openusd::usd;

use super::{BBoxCache, Imageable, ImageableSchema, Purpose, PurposeVisibility, Visibility, VisibilityAPI, XformCache};
use super::{nearest, tokens};
use crate::SchemaError;
use crate::authored_at;

/// The questions `visibility` and `purpose` are actually asked, all of which
/// are answered by walking namespace rather than by reading one prim.
///
/// Every [`ImageableSchema`] answers them, so a view has them wherever the
/// generated accessors are. Each walk starts at the prim itself and climbs to
/// the pseudo-root, reading opinions only on prims that are `Imageable`: an
/// opinion authored on an untyped or non-imageable ancestor is ignored.
///
/// # Example
///
/// ```
/// use openusd::usd;
/// use openusd_schemas::geom::{self, ImageableExt, ImageableSchema};
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let set = geom::Xform::define(&stage, "/Set")?;
/// let prop = geom::Mesh::define(&stage, "/Set/Prop")?;
///
/// // Nothing is authored yet: both answers are the schema's fallbacks.
/// assert_eq!(prop.compute_visibility(None)?, geom::Visibility::Inherited);
/// assert_eq!(prop.compute_purpose()?, geom::Purpose::Default);
///
/// // An opinion on the set reaches every imageable prim beneath it.
/// set.create_visibility_attr()?.set(geom::Visibility::Invisible)?;
/// set.create_purpose_attr()?.set(geom::Purpose::Render)?;
/// assert_eq!(prop.compute_visibility(None)?, geom::Visibility::Invisible);
/// assert_eq!(prop.compute_purpose()?, geom::Purpose::Render);
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
pub trait ImageableExt: ImageableSchema {
    /// Resolve the effective composed `visibility` at `time` (C++
    /// `ComputeVisibility`), where `None` is the default time.
    ///
    /// An `invisible` opinion on this prim or any imageable ancestor prunes
    /// the subtree and gives [`Visibility::Invisible`]. Otherwise the result
    /// is [`Visibility::Inherited`]. Any other authored token, recognized or
    /// not, lets the walk continue.
    fn compute_visibility(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<Visibility> {
        let time = time.into();
        let invisible = nearest(self.stage(), self.path(), Imageable::from_prim, |ip| {
            Ok(is_invisible(ip, time)?.then_some(Visibility::Invisible))
        })?;
        Ok(invisible.unwrap_or(Visibility::Inherited))
    }

    /// The attribute carrying this prim's visibility opinion for `purpose`
    /// (C++ `UsdGeomImageable::GetPurposeVisibilityAttr`).
    ///
    /// [`Purpose::Default`] answers the overall `visibility` attribute. The
    /// other purposes answer the matching [`VisibilityAPI`] attribute, and
    /// `None` where that schema is not applied, even when the attribute is
    /// authored.
    fn purpose_visibility_attr(&self, purpose: Purpose) -> Result<Option<usd::Attribute>> {
        if purpose == Purpose::Default {
            return Ok(Some(self.visibility_attr()));
        }
        Ok(VisibilityAPI::from_prim(self.prim().clone())?.and_then(|api| api.purpose_visibility_attr(purpose)))
    }

    /// Resolve whether this prim is visible for `purpose` at `time` (C++
    /// `ComputeEffectiveVisibility`), where `None` is the default time.
    ///
    /// When [`compute_visibility`](Self::compute_visibility) is
    /// [`Visibility::Invisible`], every purpose is
    /// [`PurposeVisibility::Invisible`]. Otherwise [`Purpose::Default`] is
    /// [`PurposeVisibility::Visible`]. Any other purpose takes the nearest
    /// authored opinion of its
    /// [`purpose_visibility_attr`](Self::purpose_visibility_attr) on this prim
    /// or an imageable ancestor, so a descendant's `visible` overrides an
    /// ancestor's `invisible`. A block is no opinion. With none authored,
    /// `guide` is [`PurposeVisibility::Invisible`] and `proxy` and `render`
    /// are [`PurposeVisibility::Inherited`].
    ///
    /// An authored token outside `inherited`, `invisible` and `visible` still
    /// stops the walk. It fails to decode, and the call returns the
    /// conversion error.
    fn effective_visibility(
        &self,
        purpose: Purpose,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<PurposeVisibility> {
        let time = time.into();
        // TODO(perf): this walks the ancestors twice, once for the overall
        // visibility and once for the purpose opinion. One walk can check
        // both at each level, provided it decodes the first authored purpose
        // opinion only after it finds no `invisible` above it, so that an
        // invisible ancestor still wins over a child's undecodable token.
        if self.compute_visibility(time)? == Visibility::Invisible {
            return Ok(PurposeVisibility::Invisible);
        }
        if purpose == Purpose::Default {
            return Ok(PurposeVisibility::Visible);
        }
        let authored = nearest(self.stage(), self.path(), Imageable::from_prim, |ip| {
            match ip.purpose_visibility_attr(purpose)? {
                Some(attr) => authored_at::<PurposeVisibility>(&attr, time),
                None => Ok(None),
            }
        })?;
        Ok(authored.unwrap_or(match purpose {
            Purpose::Guide => PurposeVisibility::Invisible,
            _ => PurposeVisibility::Inherited,
        }))
    }

    /// Resolve the effective composed `purpose` (C++ `ComputePurpose`).
    ///
    /// The nearest authored opinion on this prim or an imageable ancestor
    /// wins. With none, the result is this prim's own `purpose` fallback, or
    /// [`Purpose::Default`] when this prim is not imageable. An
    /// authored-but-unrecognized token stops the walk and resolves to
    /// [`Purpose::Default`].
    fn compute_purpose(&self) -> Result<Purpose> {
        Ok(self.purpose_info()?.purpose)
    }

    /// Resolve the effective composed `purpose` together with whether this
    /// prim's children inherit it (C++ `ComputePurposeInfo`).
    ///
    /// The purpose is the one [`compute_purpose`](Self::compute_purpose)
    /// answers. It is inheritable when an opinion authored on this prim or an
    /// imageable ancestor decided it, and not when it is a fallback.
    fn purpose_info(&self) -> Result<PurposeInfo> {
        let authored = nearest(self.stage(), self.path(), Imageable::from_prim, authored_purpose)?;
        match authored {
            Some(purpose) => Ok(PurposeInfo::inheritable(purpose)),
            None => fallback_purpose(Imageable::from_prim(self.prim().clone())?.as_ref()),
        }
    }

    /// Resolve the answer of
    /// [`purpose_info`](Self::purpose_info) from the parent
    /// prim's `parent` info, reading this prim alone (C++
    /// `ComputePurposeInfo(parentPurposeInfo)`).
    ///
    /// A traversal that hands each prim's info down to its children resolves
    /// every purpose with one read per prim.
    fn purpose_info_from(&self, parent: PurposeInfo) -> Result<PurposeInfo> {
        let ip = Imageable::from_prim(self.prim().clone())?;
        purpose_below(ip.as_ref(), parent)
    }

    /// Find the prim that stands in for this one under the `proxy` purpose,
    /// and the root of the `render` subtree that names it, in that order (C++
    /// `ComputeProxyPrim`).
    ///
    /// The render root is the highest prim in the unbroken run of prims,
    /// from this one up, whose computed purpose is `render`. Its `proxyPrim`
    /// relationship names the proxy. The answer is `None` when this prim's
    /// purpose is not `render`, when the relationship does not forward to
    /// exactly one target, when the stage holds no prim at the target, and
    /// when the target's computed purpose is not `proxy`.
    fn proxy_prim(&self) -> Result<Option<(usd::Prim, usd::Prim)>> {
        // Each prim's purpose from its parent's, root-most first, so the
        // chain costs one read per prim.
        let mut chain: Vec<_> = self.path().ancestors_below_root().collect();
        chain.reverse();
        let mut info = PurposeInfo::default();
        let mut render_root = None;
        for path in chain {
            let prim = self.stage().prim(path)?;
            info = Imageable::from_prim_unchecked(prim.clone()).purpose_info_from(info)?;
            // The run of `render` prims that reaches this prim starts at
            // the first one after the last prim of another purpose.
            render_root = match info.purpose {
                Purpose::Render => render_root.or(Some(prim)),
                _ => None,
            };
        }
        let Some(render_root) = render_root else {
            return Ok(None);
        };

        let targets = Imageable::from_prim_unchecked(render_root.clone())
            .proxy_prim_rel()
            .forwarded_targets()?;
        let [target] = targets.as_slice() else {
            return Ok(None);
        };
        let proxy = self.stage().prim(target)?;
        if !proxy.is_valid()? || Imageable::from_prim_unchecked(proxy.clone()).compute_purpose()? != Purpose::Proxy {
            return Ok(None);
        }
        Ok(Some((proxy, render_root)))
    }

    /// Author `proxy` as the one target of this prim's `proxyPrim`
    /// relationship (C++ `SetProxyPrim`).
    ///
    /// A `proxy` the stage holds no prim for is
    /// [`usd::StageAuthoringError::PrimNotValid`].
    fn set_proxy_prim(&self, proxy: &usd::Prim) -> Result<usd::Relationship> {
        if !proxy.is_valid()? {
            return Err(usd::StageAuthoringError::PrimNotValid {
                path: proxy.path().clone(),
            }
            .into());
        }
        Ok(self.proxy_prim_rel_builder().set_targets([proxy.path()]).build()?)
    }

    /// Make this prim visible at `time`, where `None` is the default time,
    /// while every prim outside its ancestors and its subtree keeps the
    /// visibility it resolves to now (C++ `MakeVisible`).
    ///
    /// An `invisible` on this prim or an imageable ancestor becomes
    /// `inherited`. From the highest such ancestor down, the siblings of each
    /// prim on the way are made `invisible`, so the subtrees that ancestor
    /// was hiding stay hidden. A sibling that is not imageable has the
    /// imageable prims nearest below it made `invisible` in its place, and
    /// the siblings below an ancestor that is not imageable are hidden like
    /// any others; C++ leaves both visible. An instance that is not imageable
    /// is left as it is: its proxies take no opinion. All of it is one edit.
    fn make_visible(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<()> {
        let time = time.into();
        let stage = self.stage();
        let mut writes = Vec::new();
        if is_invisible(self, time)? {
            writes.push((self.path().clone(), Visibility::Inherited));
        }
        // Root-most first, so an invisible ancestor is found before the
        // siblings below it are visited.
        let mut chain: Vec<_> = self.path().ancestors_below_root().collect();
        chain.reverse();
        let mut has_invisible_ancestor = false;
        for pair in chain.windows(2) {
            let parent = stage.prim(&pair[0])?;
            if let Some(ip) = Imageable::from_prim(parent.clone())?
                && is_invisible(&ip, time)?
            {
                writes.push((parent.path().clone(), Visibility::Inherited));
                has_invisible_ancestor = true;
            }
            if !has_invisible_ancestor {
                continue;
            }
            // Every child, stopping at an instance (C++ `GetAllChildren`): hide
            // each imageable sibling, or the imageable prims nearest below one
            // that is not.
            let every_child = usd::PrimPredicate::new(usd::PrimStatus::empty(), usd::PrimStatus::empty());
            let mut walk = parent.filtered_descendants(every_child)?;
            while let Some(prim) = walk.next() {
                let prim = prim?;
                if prim.path() == &pair[1] {
                    walk.prune_children();
                } else if Imageable::from_prim(prim.clone())?.is_some() {
                    writes.push((prim.path().clone(), Visibility::Invisible));
                    walk.prune_children();
                }
            }
        }

        stage.edit(|edit| {
            for (path, visibility) in writes {
                edit.prim(path)?
                    .attribute_builder(tokens::VISIBILITY, sdf::ValueTypeName::TOKEN)
                    .custom(false)
                    .set_at(visibility, time)
                    .build()?;
            }
            Ok(())
        })
    }

    /// Make this prim invisible at `time`, where `None` is the default time
    /// (C++ `MakeInvisible`).
    ///
    /// Nothing is authored where `visibility` already reads `invisible` at
    /// that time.
    fn make_invisible(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<()> {
        let time = time.into();
        if !is_invisible(self, time)? {
            self.visibility_attr_builder()
                .set_at(Visibility::Invisible, time)
                .build()?;
        }
        Ok(())
    }

    /// This prim's local-to-world transform at `time`, where `None` is the
    /// default time (C++ `ComputeLocalToWorldTransform`).
    ///
    /// Each call evaluates every ancestor afresh; for several prims, or one
    /// prim at several times, query an [`XformCache`] instead.
    fn local_to_world_transform(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<gf::Mat4d, SchemaError> {
        XformCache::new(time).local_to_world_transform(self.prim())
    }

    /// The local-to-world transform of this prim's parent at `time`, where
    /// `None` is the default time (C++ `ComputeParentToWorldTransform`).
    ///
    /// Each call evaluates every ancestor afresh; for several prims, or one
    /// prim at several times, query an [`XformCache`] instead.
    fn parent_to_world_transform(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<gf::Mat4d, SchemaError> {
        XformCache::new(time).parent_to_world_transform(self.prim())
    }

    /// The bound of this prim in world space at `time`, where `None` is the
    /// default time, around the prims at and beneath it whose purpose is one of
    /// `purposes` (C++ `ComputeWorldBound`).
    ///
    /// With no purposes the box is the empty one, as in C++, which also
    /// raises a coding error.
    /// Each call bounds the whole subtree afresh; for several prims, or one
    /// prim at several times, query a [`BBoxCache`] instead.
    ///
    /// # Example
    ///
    /// ```
    /// use openusd::{gf, usd};
    /// use openusd_schemas::geom::{self, ImageableExt, Purpose, XformableExt};
    ///
    /// let stage = usd::Stage::builder()
    ///     .schema_registry(openusd_schemas::schema_registry())
    ///     .in_memory("scene.usda")?;
    /// let set = geom::Xform::define(&stage, "/Set")?.set_translate(gf::vec3d(10.0, 0.0, 0.0))?;
    /// geom::Sphere::define(&stage, "/Set/Ball")?;
    ///
    /// let own = set.untransformed_bound(None, [Purpose::Default])?.aligned_range();
    /// assert_eq!(own.min(), gf::vec3d(-1.0, -1.0, -1.0));
    /// let world = set.world_bound(None, [Purpose::Default])?.aligned_range();
    /// assert_eq!(world.min(), gf::vec3d(9.0, -1.0, -1.0));
    /// # Ok::<(), openusd_schemas::SchemaError>(())
    /// ```
    fn world_bound(
        &self,
        time: impl Into<Option<usd::TimeCode>>,
        purposes: impl IntoIterator<Item = Purpose>,
    ) -> Result<gf::BBox3d, SchemaError> {
        match bound_cache(time, purposes) {
            Some(mut cache) => cache.world_bound(self.prim()),
            None => Ok(gf::BBox3d::default()),
        }
    }

    /// The bound of this prim in its parent's space at `time`, where `None`
    /// is the default time, around the prims at and beneath it whose purpose
    /// is one
    /// of `purposes` (C++ `ComputeLocalBound`).
    ///
    /// With no purposes the box is the empty one, as in C++, which also
    /// raises a coding error.
    /// Each call bounds the whole subtree afresh; for several prims, or one
    /// prim at several times, query a [`BBoxCache`] instead.
    fn local_bound(
        &self,
        time: impl Into<Option<usd::TimeCode>>,
        purposes: impl IntoIterator<Item = Purpose>,
    ) -> Result<gf::BBox3d, SchemaError> {
        match bound_cache(time, purposes) {
            Some(mut cache) => cache.local_bound(self.prim()),
            None => Ok(gf::BBox3d::default()),
        }
    }

    /// The bound of this prim in its own space at `time`, where `None` is
    /// the default time, around the prims at and beneath it whose purpose is
    /// one of
    /// `purposes`, its own transform left out (C++
    /// `ComputeUntransformedBound`).
    ///
    /// With no purposes the box is the empty one, as in C++, which also
    /// raises a coding error.
    /// Each call bounds the whole subtree afresh; for several prims, or one
    /// prim at several times, query a [`BBoxCache`] instead.
    fn untransformed_bound(
        &self,
        time: impl Into<Option<usd::TimeCode>>,
        purposes: impl IntoIterator<Item = Purpose>,
    ) -> Result<gf::BBox3d, SchemaError> {
        match bound_cache(time, purposes) {
            Some(mut cache) => cache.untransformed_bound(self.prim()),
            None => Ok(gf::BBox3d::default()),
        }
    }
}

impl<T: ImageableSchema> ImageableExt for T {}

/// A prim's computed `purpose`, and whether its children inherit it (C++
/// `UsdGeomImageable::PurposeInfo`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PurposeInfo {
    /// The computed purpose.
    pub purpose: Purpose,
    /// Whether a child with no authored `purpose` of its own takes this one.
    pub is_inheritable: bool,
}

impl PurposeInfo {
    /// A purpose an authored opinion decided, which children inherit.
    fn inheritable(purpose: Purpose) -> Self {
        PurposeInfo {
            purpose,
            is_inheritable: true,
        }
    }

    /// The purpose where children inherit it (C++ `GetInheritablePurpose`).
    pub fn inheritable_purpose(&self) -> Option<Purpose> {
        self.is_inheritable.then_some(self.purpose)
    }
}

/// The purpose of a prim whose parent's is `parent`, where `ip` views the
/// prim as imageable and `None` is a prim that is not: what
/// [`ImageableExt::purpose_info_from`] answers, for a caller that already
/// knows which the prim is.
pub(super) fn purpose_below(ip: Option<&Imageable>, parent: PurposeInfo) -> Result<PurposeInfo> {
    let authored = match ip {
        Some(ip) => authored_purpose(ip)?,
        None => None,
    };
    match authored {
        Some(purpose) => Ok(PurposeInfo::inheritable(purpose)),
        None if parent.is_inheritable => Ok(parent),
        None => fallback_purpose(ip),
    }
}

/// A cache for one bound at `time` over `purposes`, or `None` where there
/// is no purpose to bound.
fn bound_cache(
    time: impl Into<Option<usd::TimeCode>>,
    purposes: impl IntoIterator<Item = Purpose>,
) -> Option<BBoxCache> {
    let mut purposes = purposes.into_iter().peekable();
    purposes.peek().is_some().then(|| BBoxCache::new(time, purposes))
}

/// The `purpose` a layer authors on `ip`, where an unrecognized token reads
/// as [`Purpose::Default`].
fn authored_purpose(ip: &Imageable) -> Result<Option<Purpose>> {
    let token = authored_at::<tf::Token>(&ip.purpose_attr(), None)?;
    Ok(token.map(|token| Purpose::from_token(token).unwrap_or_default()))
}

/// The purpose a prim has with no opinion to take: its schema's fallback
/// where `ip` views it as imageable, and [`Purpose::Default`] where it is not.
fn fallback_purpose(ip: Option<&Imageable>) -> Result<PurposeInfo> {
    let fallback = match ip {
        Some(ip) => ip.purpose_attr().get::<tf::Token>()?,
        None => None,
    };
    Ok(PurposeInfo {
        purpose: fallback.and_then(Purpose::from_token).unwrap_or_default(),
        is_inheritable: false,
    })
}

/// `true` when `ip`'s own `visibility` reads `invisible` at `time`.
pub(super) fn is_invisible(ip: &(impl ImageableSchema + ?Sized), time: Option<usd::TimeCode>) -> Result<bool> {
    let token = ip.visibility_attr().get_at::<tf::Token>(time)?;
    Ok(token.as_deref() == Some(tokens::INVISIBLE))
}

#[cfg(test)]
mod tests {
    use openusd::Result;
    use openusd::sdf;
    use openusd::tf;
    use openusd::usd::{self, SchemaBase};

    use super::{ImageableExt, PurposeInfo};
    use crate::SchemaError;
    use crate::geom::{
        BBoxCache, Imageable, ImageableSchema, Purpose, PurposeVisibility, Scope, Visibility, VisibilityAPI,
    };
    use openusd::gf;

    /// A `Scope` at `path` carrying [`VisibilityAPI`].
    fn vis_scope(stage: &usd::Stage, path: &str) -> Result<Scope> {
        let scope = Scope::define(stage, path)?;
        VisibilityAPI::apply(scope.prim())?;
        Ok(scope)
    }

    /// `scope` viewed as [`VisibilityAPI`], whether or not it carries it.
    fn api(scope: &Scope) -> VisibilityAPI {
        VisibilityAPI::from_prim_unchecked(scope.prim().clone())
    }

    /// `/Root/Child` under a `/Root` whose `guideVisibility` is `visible`,
    /// both carrying [`VisibilityAPI`].
    fn under_visible_guide(stage: &usd::Stage) -> Result<Scope> {
        api(&vis_scope(stage, "/Root")?)
            .create_guide_visibility_attr()?
            .set(PurposeVisibility::Visible)?;
        vis_scope(stage, "/Root/Child")
    }

    fn effective(view: &impl ImageableSchema, purpose: Purpose) -> Result<PurposeVisibility> {
        view.effective_visibility(purpose, None)
    }

    /// With nothing authored, `guide` is hidden and `proxy` / `render` are
    /// left to the caller; only the default purpose has an attribute until
    /// the API is applied.
    #[test]
    fn purpose_vis_fallbacks() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let root = Scope::define(&stage, "/Root")?;

        assert_eq!(effective(&root, Purpose::Default)?, PurposeVisibility::Visible);
        assert_eq!(effective(&root, Purpose::Guide)?, PurposeVisibility::Invisible);
        assert_eq!(effective(&root, Purpose::Proxy)?, PurposeVisibility::Inherited);
        assert_eq!(effective(&root, Purpose::Render)?, PurposeVisibility::Inherited);

        assert!(root.purpose_visibility_attr(Purpose::Default)?.is_some());
        for purpose in [Purpose::Guide, Purpose::Proxy, Purpose::Render] {
            assert!(root.purpose_visibility_attr(purpose)?.is_none(), "{purpose:?}");
        }

        // Applying the API brings the attributes and their fallbacks, which
        // agree with the unapplied answers.
        VisibilityAPI::apply(root.prim())?;
        let guide = root.purpose_visibility_attr(Purpose::Guide)?.expect("guideVisibility");
        assert_eq!(guide.get::<PurposeVisibility>()?, Some(PurposeVisibility::Invisible));
        assert_eq!(effective(&root, Purpose::Guide)?, PurposeVisibility::Invisible);
        assert_eq!(effective(&root, Purpose::Render)?, PurposeVisibility::Inherited);
        Ok(())
    }

    /// A parent's opinion reaches the child, and the child's own opinion
    /// overrides it in either direction.
    #[test]
    fn purpose_vis_inherits() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let child = under_visible_guide(&stage)?;
        assert_eq!(effective(&child, Purpose::Guide)?, PurposeVisibility::Visible);

        api(&child)
            .create_guide_visibility_attr()?
            .set(PurposeVisibility::Invisible)?;
        assert_eq!(effective(&child, Purpose::Guide)?, PurposeVisibility::Invisible);

        let root = Scope::get(&stage, "/Root")?.expect("Scope");
        api(&root)
            .create_render_visibility_attr()?
            .set(PurposeVisibility::Invisible)?;
        api(&child)
            .create_render_visibility_attr()?
            .set(PurposeVisibility::Visible)?;
        assert_eq!(effective(&child, Purpose::Render)?, PurposeVisibility::Visible);
        Ok(())
    }

    /// An authored `inherited` is an opinion, so it stops the walk before a
    /// parent's `visible`.
    #[test]
    fn authored_inherited_stops() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let child = under_visible_guide(&stage)?;
        api(&child)
            .create_guide_visibility_attr()?
            .set(PurposeVisibility::Inherited)?;
        assert_eq!(effective(&child, Purpose::Guide)?, PurposeVisibility::Inherited);
        Ok(())
    }

    /// A block is no opinion, so the parent's authored one wins.
    #[test]
    fn blocked_child_inherits() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let child = under_visible_guide(&stage)?;
        api(&child).create_guide_visibility_attr()?.block()?;
        assert_eq!(effective(&child, Purpose::Guide)?, PurposeVisibility::Visible);
        Ok(())
    }

    /// An unrecognized purpose-visibility token is still the nearest
    /// opinion, so the call returns its decode error.
    #[test]
    fn unknown_purpose_vis_errors() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let child = under_visible_guide(&stage)?;
        api(&child)
            .create_guide_visibility_attr()?
            .set(tf::Token::from("bogus"))?;
        assert!(effective(&child, Purpose::Guide).is_err());
        Ok(())
    }

    /// An overall `invisible` hides every purpose, whatever the purpose
    /// visibilities say.
    #[test]
    fn overall_invis_wins() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let child = under_visible_guide(&stage)?;
        let root = Scope::get(&stage, "/Root")?.expect("Scope");
        api(&root)
            .create_render_visibility_attr()?
            .set(PurposeVisibility::Visible)?;
        root.create_visibility_attr()?.set(Visibility::Invisible)?;

        for purpose in [Purpose::Default, Purpose::Guide, Purpose::Proxy, Purpose::Render] {
            assert_eq!(effective(&child, purpose)?, PurposeVisibility::Invisible, "{purpose:?}");
        }
        Ok(())
    }

    /// Without the API, an authored `guideVisibility` is no opinion.
    #[test]
    fn unapplied_api_ignored() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let root = Scope::define(&stage, "/Root")?;
        api(&root)
            .create_guide_visibility_attr()?
            .set(PurposeVisibility::Visible)?;

        assert!(root.purpose_visibility_attr(Purpose::Guide)?.is_none());
        assert_eq!(effective(&root, Purpose::Guide)?, PurposeVisibility::Invisible);
        let child = Scope::define(&stage, "/Root/Child")?;
        assert_eq!(effective(&child, Purpose::Guide)?, PurposeVisibility::Invisible);
        Ok(())
    }

    /// Overall visibility looks only for `invisible`. Another token, whether
    /// `PurposeVisibility` knows it or nothing does, lets the walk reach the
    /// invisible ancestor without a decode error.
    #[test]
    fn unknown_token_walks() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        Scope::define(&stage, "/Root")?
            .create_visibility_attr()?
            .set(Visibility::Invisible)?;
        let child = Scope::define(&stage, "/Root/Child")?;
        for token in ["bogus", "visible"] {
            child.create_visibility_attr()?.set(tf::Token::from(token))?;
            assert_eq!(child.compute_visibility(None)?, Visibility::Invisible, "{token}");
        }
        Ok(())
    }

    /// Animated `visibility` resolves at the time asked for, in both queries.
    #[test]
    fn visibility_animated() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let root = Scope::define(&stage, "/Root")?;
        let child = Scope::define(&stage, "/Root/Child")?;
        root.create_visibility_attr()?
            .set_at(Visibility::Inherited, usd::TimeCode::new(1.0))?
            .set_at(Visibility::Invisible, usd::TimeCode::new(2.0))?;

        for (time, overall, render) in [
            (1.0, Visibility::Inherited, PurposeVisibility::Inherited),
            (2.0, Visibility::Invisible, PurposeVisibility::Invisible),
        ] {
            let time = usd::TimeCode::new(time);
            assert_eq!(child.compute_visibility(time)?, overall, "{time:?}");
            assert_eq!(child.effective_visibility(Purpose::Render, time)?, render, "{time:?}");
        }
        Ok(())
    }

    /// A low-level compatibility case over out-of-schema data: the purpose
    /// visibilities are uniform, so samples on one are not supported
    /// authoring. It pins that the time asked for reaches the purpose
    /// visibility read as well as the overall one.
    #[test]
    fn purpose_vis_animated() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let root = vis_scope(&stage, "/Root")?;
        api(&root)
            .create_guide_visibility_attr()?
            .set_at(PurposeVisibility::Visible, usd::TimeCode::new(1.0))?
            .set_at(PurposeVisibility::Invisible, usd::TimeCode::new(2.0))?;

        for (time, expected) in [(1.0, PurposeVisibility::Visible), (2.0, PurposeVisibility::Invisible)] {
            let time = usd::TimeCode::new(time);
            assert_eq!(root.effective_visibility(Purpose::Guide, time)?, expected, "{time:?}");
        }
        Ok(())
    }

    /// Opinions on a prim that is not imageable are skipped: neither its
    /// `visibility` nor its `purpose` reaches the child, while a typed
    /// grandparent's `purpose` still does.
    #[test]
    fn non_imageable_ignored() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let root = Scope::define(&stage, "/Root")?;
        let untyped = Imageable::from_prim_unchecked(stage.define_prim("/Root/Untyped")?);
        let child = Scope::define(&stage, "/Root/Untyped/Child")?;

        untyped.create_visibility_attr()?.set(Visibility::Invisible)?;
        untyped.create_purpose_attr()?.set(Purpose::Guide)?;
        assert_eq!(child.compute_visibility(None)?, Visibility::Inherited);
        assert_eq!(child.compute_purpose()?, Purpose::Default);

        root.create_purpose_attr()?.set(Purpose::Render)?;
        assert_eq!(child.compute_purpose()?, Purpose::Render);
        Ok(())
    }

    /// An authored purpose is inheritable and a fallback is not, and carrying
    /// the parent's info down gives the answer the full walk does.
    #[test]
    fn purpose_info_inheritable() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let root = Scope::define(&stage, "/Root")?;
        let child = Scope::define(&stage, "/Root/Child")?;

        let fallback = root.purpose_info()?;
        assert_eq!(fallback, PurposeInfo::default());
        assert_eq!(fallback.inheritable_purpose(), None);
        assert_eq!(child.purpose_info_from(fallback)?, fallback);

        root.create_purpose_attr()?.set(Purpose::Render)?;
        let authored = root.purpose_info()?;
        assert_eq!(authored.inheritable_purpose(), Some(Purpose::Render));
        assert_eq!(child.purpose_info()?, authored);
        assert_eq!(child.purpose_info_from(authored)?, authored);

        child.create_purpose_attr()?.set(Purpose::Guide)?;
        let own = child.purpose_info_from(authored)?;
        assert_eq!(own.inheritable_purpose(), Some(Purpose::Guide));
        assert_eq!(own, child.purpose_info()?);
        Ok(())
    }

    /// A prim that is not imageable passes an inheritable purpose through and
    /// otherwise reads `default`.
    #[test]
    fn purpose_info_non_imageable() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let root = Scope::define(&stage, "/Root")?;
        let untyped = Imageable::from_prim_unchecked(stage.define_prim("/Root/Untyped")?);
        untyped.create_purpose_attr()?.set(Purpose::Guide)?;

        assert_eq!(untyped.purpose_info()?, PurposeInfo::default());
        root.create_purpose_attr()?.set(Purpose::Render)?;
        let parent = root.purpose_info()?;
        assert_eq!(untyped.purpose_info_from(parent)?, parent);
        assert_eq!(untyped.purpose_info()?, parent);
        Ok(())
    }

    /// `/Render` with purpose `render` naming `/Proxy`, with purpose `proxy`,
    /// as its proxy, and a `/Render/Geo` beneath it.
    fn render_and_proxy(stage: &usd::Stage) -> Result<(Scope, Scope, Scope)> {
        let render = Scope::define(stage, "/Render")?;
        render.create_purpose_attr()?.set(Purpose::Render)?;
        let geo = Scope::define(stage, "/Render/Geo")?;
        let proxy = Scope::define(stage, "/Proxy")?;
        proxy.create_purpose_attr()?.set(Purpose::Proxy)?;
        render.set_proxy_prim(proxy.prim())?;
        Ok((render, geo, proxy))
    }

    /// Every prim of a render subtree finds the proxy its root names, along
    /// with that root.
    #[test]
    fn proxy_from_render_root() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let (render, geo, proxy) = render_and_proxy(&stage)?;

        for view in [&render, &geo] {
            let (found, root) = view.proxy_prim()?.expect("a proxy");
            assert_eq!(found.path(), proxy.path());
            assert_eq!(root.path(), render.path());
        }
        assert!(proxy.proxy_prim()?.is_none());
        Ok(())
    }

    /// The render root is where the run of `render` prims ends, so a
    /// relationship above a prim of another purpose is out of reach.
    #[test]
    fn proxy_prim_run_breaks() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let (_, geo, _) = render_and_proxy(&stage)?;
        geo.create_purpose_attr()?.set(Purpose::Guide)?;
        let leaf = Scope::define(&stage, "/Render/Geo/Leaf")?;
        leaf.create_purpose_attr()?.set(Purpose::Render)?;

        assert!(geo.proxy_prim()?.is_none());
        assert!(leaf.proxy_prim()?.is_none());
        Ok(())
    }

    /// A target that is not a `proxy` prim, a second target, and a target no
    /// prim is at each leave the prim without a proxy.
    #[test]
    fn proxy_prim_rejects_target() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let (render, geo, proxy) = render_and_proxy(&stage)?;

        proxy.create_purpose_attr()?.set(Purpose::Default)?;
        assert!(geo.proxy_prim()?.is_none());
        proxy.create_purpose_attr()?.set(Purpose::Proxy)?;
        assert!(geo.proxy_prim()?.is_some());

        render
            .proxy_prim_rel_builder()
            .set_targets(["/Proxy", "/Render/Geo"])
            .build()?;
        assert!(geo.proxy_prim()?.is_none());

        render.proxy_prim_rel_builder().set_targets(["/Missing"]).build()?;
        assert!(geo.proxy_prim()?.is_none());
        Ok(())
    }

    /// A prim the stage does not hold cannot be named as a proxy.
    #[test]
    fn set_proxy_prim_invalid() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let render = Scope::define(&stage, "/Render")?;
        assert!(render.set_proxy_prim(&stage.prim("/Missing")?).is_err());
        assert!(!render.proxy_prim_rel().has_authored_targets()?);
        Ok(())
    }

    /// The hierarchy of the C++ `AllInvisible.usda` fixture, every prim
    /// `invisible`.
    fn all_invisible(stage: &usd::Stage) -> Result<()> {
        for path in [
            "/foo",
            "/foo/bar1",
            "/foo/bar1/thing1",
            "/foo/bar1/thing2",
            "/foo/bar2",
            "/foo/bar2/thing",
        ] {
            Scope::define(stage, path)?
                .create_visibility_attr()?
                .set(Visibility::Invisible)?;
        }
        Ok(())
    }

    fn visibility(stage: &usd::Stage, path: &str) -> Result<Visibility> {
        Imageable::get(stage, path)?
            .expect("Imageable")
            .compute_visibility(None)
    }

    /// Making one prim visible under invisible ancestors leaves its siblings,
    /// and its ancestors' siblings, hidden.
    #[test]
    fn make_visible_hides_siblings() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        all_invisible(&stage)?;
        let commits = crate::tests::commits(&stage);
        Imageable::get(&stage, "/foo/bar1/thing1")?
            .expect("Imageable")
            .make_visible(None)?;
        assert_eq!(commits.get(), 1);

        assert_eq!(visibility(&stage, "/foo/bar1/thing1")?, Visibility::Inherited);
        assert_eq!(visibility(&stage, "/foo/bar1/thing2")?, Visibility::Invisible);
        assert_eq!(visibility(&stage, "/foo/bar2")?, Visibility::Invisible);
        assert_eq!(visibility(&stage, "/foo/bar1")?, Visibility::Inherited);
        Ok(())
    }

    /// A sibling that is an instance and not imageable is left as it is:
    /// the prims beneath it are instance proxies, which take no opinion.
    #[test]
    fn make_visible_past_instance() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let foo = Scope::define(&stage, "/foo")?;
        Scope::define(&stage, "/foo/thing")?;
        Scope::define(&stage, "/_prototype/mesh")?;
        stage
            .define_prim("/foo/props")?
            .set_metadata(
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    prim_path: sdf::path("/_prototype")?,
                    ..Default::default()
                }])),
            )?
            .set_instanceable(true)?;
        foo.create_visibility_attr()?.set(Visibility::Invisible)?;

        Imageable::get(&stage, "/foo/thing")?
            .expect("Imageable")
            .make_visible(None)?;
        assert_eq!(visibility(&stage, "/foo/thing")?, Visibility::Inherited);
        let proxy = Imageable::get(&stage, "/foo/props/mesh")?.expect("Imageable");
        assert!(proxy.prim().is_instance_proxy()?);
        assert!(!proxy.visibility_attr().has_authored_value()?);
        assert_eq!(visibility(&stage, "/foo/props/mesh")?, Visibility::Inherited);
        Ok(())
    }

    /// With only the top ancestor invisible, the siblings at every level
    /// below it take an `invisible` of their own.
    #[test]
    fn make_visible_below_ancestor() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let foo = Scope::define(&stage, "/foo")?;
        for path in ["/foo/bar1", "/foo/bar1/thing1", "/foo/bar1/thing2", "/foo/bar2"] {
            Scope::define(&stage, path)?;
        }
        stage.define_prim("/foo/bar1/untyped")?;
        Scope::define(&stage, "/foo/bar1/untyped/deep/thing3")?;
        foo.create_visibility_attr()?.set(Visibility::Invisible)?;

        Imageable::get(&stage, "/foo/bar1/thing1")?
            .expect("Imageable")
            .make_visible(None)?;
        assert_eq!(visibility(&stage, "/foo/bar1/thing1")?, Visibility::Inherited);
        assert_eq!(visibility(&stage, "/foo/bar1/thing2")?, Visibility::Invisible);
        assert_eq!(visibility(&stage, "/foo/bar2")?, Visibility::Invisible);
        // A sibling that is not imageable takes no opinion, and the
        // imageable prim below it takes one in its place.
        let untyped = Imageable::from_prim_unchecked(stage.prim("/foo/bar1/untyped")?);
        assert!(!untyped.visibility_attr().has_authored_value()?);
        assert_eq!(
            visibility(&stage, "/foo/bar1/untyped/deep/thing3")?,
            Visibility::Invisible
        );
        Ok(())
    }

    /// An ancestor that is not imageable passes the hidden state down, so
    /// the siblings below it are hidden as well.
    #[test]
    fn make_visible_untyped_ancestor() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let a = Scope::define(&stage, "/A")?;
        stage.define_prim("/A/U")?;
        Scope::define(&stage, "/A/U/Target")?;
        Scope::define(&stage, "/A/U/Other")?;
        a.create_visibility_attr()?.set(Visibility::Invisible)?;

        Imageable::get(&stage, "/A/U/Target")?
            .expect("Imageable")
            .make_visible(None)?;
        assert_eq!(visibility(&stage, "/A")?, Visibility::Inherited);
        assert_eq!(visibility(&stage, "/A/U/Target")?, Visibility::Inherited);
        assert_eq!(visibility(&stage, "/A/U/Other")?, Visibility::Invisible);
        Ok(())
    }

    /// A prim that is already visible authors nothing, on itself or around
    /// it.
    #[test]
    fn make_visible_noop() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let root = Scope::define(&stage, "/Root")?;
        let child = Scope::define(&stage, "/Root/Child")?;
        let other = Scope::define(&stage, "/Root/Other")?;

        child.make_visible(None)?;
        for view in [&root, &child, &other] {
            assert!(!view.visibility_attr().has_authored_value()?, "{}", view.path());
        }
        Ok(())
    }

    /// Visibility is rewritten at the time asked for, and the default is left
    /// as it was.
    #[test]
    fn make_visible_at_time() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let root = Scope::define(&stage, "/Root")?;
        let time = usd::TimeCode::new(2.0);
        root.create_visibility_attr()?
            .set_at(Visibility::Inherited, usd::TimeCode::new(1.0))?
            .set_at(Visibility::Invisible, time)?;

        root.make_visible(time)?;
        assert_eq!(root.compute_visibility(time)?, Visibility::Inherited);
        root.make_invisible(time)?;
        assert_eq!(root.compute_visibility(time)?, Visibility::Invisible);
        assert_eq!(root.compute_visibility(usd::TimeCode::new(1.0))?, Visibility::Inherited);
        Ok(())
    }

    /// Making a prim invisible authors the opinion once.
    #[test]
    fn make_invisible_once() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let root = Scope::define(&stage, "/Root")?;
        root.make_invisible(None)?;
        assert_eq!(root.visibility()?, Some(Visibility::Invisible));

        let commits = crate::tests::commits(&stage);
        root.make_invisible(None)?;
        assert_eq!(commits.get(), 0);
        Ok(())
    }

    /// A prim's bounds are those a cache of the same time and purposes
    /// answers, in each of the three spaces. With no purposes they are the
    /// empty box.
    #[test]
    fn bounds_as_cache() -> Result<(), SchemaError> {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "World"
{
    double3 xformOp:translate = (0, 0, 7)
    uniform token[] xformOpOrder = ["xformOp:translate"]

    def Xform "Set"
    {
        double3 xformOp:translate.timeSamples = { 1: (10, 0, 0), 2: (20, 0, 0) }
        uniform token[] xformOpOrder = ["xformOp:translate"]

        def Sphere "Ball" {}

        def Cube "Guide"
        {
            uniform token purpose = "guide"
            double3 xformOp:translate = (0, 50, 0)
            uniform token[] xformOpOrder = ["xformOp:translate"]
        }
    }
}
"#,
        )?;
        let set = Imageable::get(&stage, "/World/Set")?.expect("Imageable");
        let range = |min: [f64; 3], max: [f64; 3]| gf::Range3d::new(min.into(), max.into());

        let time = usd::TimeCode::new(2.0);
        let default = [Purpose::Default];
        let own = set.untransformed_bound(time, default)?;
        assert_eq!(own.aligned_range(), range([-1.0; 3], [1.0; 3]));
        let local = set.local_bound(time, default)?;
        assert_eq!(local.aligned_range(), range([19.0, -1.0, -1.0], [21.0, 1.0, 1.0]));
        let world = set.world_bound(time, default)?;
        assert_eq!(world.aligned_range(), range([19.0, -1.0, 6.0], [21.0, 1.0, 8.0]));
        // The default time reads no sample of the translation.
        let world = set.world_bound(None, default)?;
        assert_eq!(world.aligned_range(), range([-1.0, -1.0, 6.0], [1.0, 1.0, 8.0]));

        // The purposes asked for are the ones bounded.
        let cases = [
            (vec![Purpose::Guide], range([-1.0, 49.0, -1.0], [1.0, 51.0, 1.0])),
            (
                vec![Purpose::Default, Purpose::Guide],
                range([-1.0; 3], [1.0, 51.0, 1.0]),
            ),
        ];
        for (purposes, expected) in cases {
            let mut cache = BBoxCache::new(time, purposes.clone());
            assert_eq!(set.world_bound(time, purposes.clone())?, cache.world_bound(set.prim())?);
            assert_eq!(set.local_bound(time, purposes.clone())?, cache.local_bound(set.prim())?);
            let own = set.untransformed_bound(time, purposes)?;
            assert_eq!(own, cache.untransformed_bound(set.prim())?);
            assert_eq!(own.aligned_range(), expected);
        }

        assert_eq!(set.world_bound(time, [])?, gf::BBox3d::default());
        assert_eq!(set.local_bound(time, [])?, gf::BBox3d::default());
        assert_eq!(set.untransformed_bound(time, [])?, gf::BBox3d::default());
        Ok(())
    }

    /// An instance proxy inherits purpose visibility from its instance, while
    /// the prototype's own `child` does not: the prototype root reads no
    /// opinions, so nothing above that child authors one.
    #[test]
    fn purpose_vis_instancing() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        api(&vis_scope(&stage, "/_prototype")?)
            .create_guide_visibility_attr()?
            .set(PurposeVisibility::Visible)?;
        vis_scope(&stage, "/_prototype/child")?;
        Scope::define(&stage, "/instance")?
            .prim()
            .clone()
            .set_metadata(
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    prim_path: sdf::path("/_prototype")?,
                    ..Default::default()
                }])),
            )?
            .set_instanceable(true)?;

        let child = Imageable::get(&stage, "/instance/child")?.expect("Imageable");
        assert!(child.prim().is_instance_proxy()?);
        assert_eq!(effective(&child, Purpose::Guide)?, PurposeVisibility::Visible);

        // Before the instance authors anything, the source's `visible` still
        // reaches the proxy, and only an empty prototype root keeps it from
        // the prototype's own child.
        let instance = Imageable::get(&stage, "/instance")?.expect("Imageable");
        let prototype = instance.prim().prototype()?.expect("a prototype");
        let prototype_child = Imageable::get(&stage, prototype.append_path("child")?)?.expect("Imageable");
        assert_eq!(
            effective(&prototype_child, Purpose::Guide)?,
            PurposeVisibility::Invisible
        );

        instance
            .purpose_visibility_attr(Purpose::Guide)?
            .expect("guideVisibility")
            .set(PurposeVisibility::Invisible)?;
        assert_eq!(effective(&child, Purpose::Guide)?, PurposeVisibility::Invisible);
        Ok(())
    }
}
