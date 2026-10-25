//! The `Pass` view's built-in collection (C++ `UsdRenderPass`).

use openusd::usd::{self, SchemaBase};

use super::Pass;
use super::tokens::RENDER_VISIBILITY;

impl Pass {
    /// The `renderVisibility` collection, whose members the pass renders (C++
    /// `UsdRenderPass::GetRenderVisibilityCollectionAPI`).
    ///
    /// Every `RenderPass` carries it, the schema declaring it as a built-in,
    /// so this asks no question of the prim.
    pub fn render_visibility_collection(&self) -> usd::CollectionAPI {
        usd::CollectionAPI::from_prim_unchecked(self.prim().clone(), RENDER_VISIBILITY)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use openusd::Result;
    use openusd::usd::PrimPredicate;

    /// An include authored on the collection reads back as membership.
    #[test]
    fn render_visibility_collection() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let pass = Pass::define(&stage, "/Pass")?;
        stage.define_prim("/World/A")?;
        stage.define_prim("/World/B")?;

        let collection = pass.render_visibility_collection();
        assert_eq!(
            collection.collection_path()?.as_str(),
            "/Pass.collection:renderVisibility"
        );
        collection.set_include_root(false)?;
        collection.include_path("/World/A")?;

        let query = collection.membership_query()?;
        let members = usd::included_paths(&stage, &query, PrimPredicate::DEFAULT)?;
        assert_eq!(
            members.iter().map(|path| path.as_str()).collect::<Vec<_>>(),
            ["/World/A"]
        );
        Ok(())
    }
}
