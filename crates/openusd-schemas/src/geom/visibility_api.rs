//! What `UsdGeomVisibilityAPI` answers beyond its own properties.

use openusd::usd;

use super::{Purpose, VisibilityAPI};

impl VisibilityAPI {
    /// The attribute carrying the visibility opinion for `purpose` (C++
    /// `UsdGeomVisibilityAPI::GetPurposeVisibilityAttr`): `guideVisibility`,
    /// `proxyVisibility` or `renderVisibility`.
    ///
    /// [`Purpose::Default`] has no attribute here and answers `None`; C++
    /// reports it as a coding error. Its visibility is the overall
    /// `visibility`, which
    /// [`ImageableExt::purpose_visibility_attr`](super::ImageableExt::purpose_visibility_attr)
    /// returns for it.
    pub fn purpose_visibility_attr(&self, purpose: Purpose) -> Option<usd::Attribute> {
        match purpose {
            Purpose::Default => None,
            Purpose::Guide => Some(self.guide_visibility_attr()),
            Purpose::Proxy => Some(self.proxy_visibility_attr()),
            Purpose::Render => Some(self.render_visibility_attr()),
        }
    }
}

#[cfg(test)]
mod tests {
    use openusd::Result;

    use openusd::usd::SchemaBase;

    use crate::geom::{Purpose, Scope, VisibilityAPI, tokens};

    /// Each purpose names its attribute, and the default purpose has none.
    #[test]
    fn purpose_attr_names() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let api = VisibilityAPI::apply(Scope::define(&stage, "/S")?.prim())?;
        for (purpose, name) in [
            (Purpose::Guide, tokens::GUIDE_VISIBILITY),
            (Purpose::Proxy, tokens::PROXY_VISIBILITY),
            (Purpose::Render, tokens::RENDER_VISIBILITY),
        ] {
            let attr = api.purpose_visibility_attr(purpose).expect("a purpose attribute");
            assert_eq!(attr.path(), &api.path().append_property(name)?, "{purpose:?}");
        }
        assert!(api.purpose_visibility_attr(Purpose::Default).is_none());
        Ok(())
    }
}
