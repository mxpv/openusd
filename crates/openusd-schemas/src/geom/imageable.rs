//! What `UsdGeomImageable` answers beyond its own properties.

use openusd::Result;
use openusd::tf;
use openusd::usd;

use super::{Imageable, ImageableSchema, Purpose, PurposeVisibility, Visibility, VisibilityAPI};
use super::{nearest, tokens};
use crate::authored_at;

/// The questions `visibility` and `purpose` are actually asked, all of which
/// are answered by walking namespace rather than by reading one prim.
///
/// Every [`ImageableSchema`] answers them, so a view has them wherever the
/// generated accessors are. Each walk starts at the prim itself and climbs to
/// the pseudo-root, reading opinions only on prims that are `Imageable`: an
/// opinion authored on an untyped or non-imageable ancestor is ignored.
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
            let token = ip.visibility_attr().get_at::<tf::Token>(time)?;
            Ok((token.as_deref() == Some(tokens::INVISIBLE)).then_some(Visibility::Invisible))
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
    fn compute_effective_visibility(
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
        let decode = |token: tf::Token| Purpose::from_token(token).unwrap_or_default();
        let authored = nearest(self.stage(), self.path(), Imageable::from_prim, |ip| {
            authored_at::<tf::Token>(&ip.purpose_attr(), None)
        })?;
        if let Some(token) = authored {
            return Ok(decode(token));
        }
        let fallback = match Imageable::from_prim(self.prim().clone())? {
            Some(ip) => ip.purpose_attr().get::<tf::Token>()?,
            None => None,
        };
        Ok(fallback.map(decode).unwrap_or_default())
    }
}

impl<T: ImageableSchema> ImageableExt for T {}

#[cfg(test)]
mod tests {
    use openusd::Result;
    use openusd::sdf;
    use openusd::tf;
    use openusd::usd::{self, SchemaBase};

    use super::ImageableExt;
    use crate::geom::{Imageable, ImageableSchema, Purpose, PurposeVisibility, Scope, Visibility, VisibilityAPI};

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
        view.compute_effective_visibility(purpose, None)
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
            assert_eq!(
                child.compute_effective_visibility(Purpose::Render, time)?,
                render,
                "{time:?}"
            );
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
            assert_eq!(
                root.compute_effective_visibility(Purpose::Guide, time)?,
                expected,
                "{time:?}"
            );
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
