//! What a light and a light filter add to their generated views: the
//! collections that link them to the geometry they affect.

use openusd::usd::{self, SchemaBase};

use super::{LightAPI, LightFilterSchema, tokens};

impl LightAPI {
    /// The collection of the geometry the light illuminates (C++
    /// `UsdLuxLightAPI::GetLightLinkCollectionAPI`). On a prim `LightAPI`
    /// applies to, the schema includes the root, and a light with nothing
    /// authored links to everything.
    pub fn light_link_collection(&self) -> usd::CollectionAPI {
        usd::CollectionAPI::from_prim_unchecked(self.prim().clone(), tokens::LIGHT_LINK)
    }

    /// The collection of the geometry that casts the light's shadows (C++
    /// `UsdLuxLightAPI::GetShadowLinkCollectionAPI`). On a prim `LightAPI`
    /// applies to, the schema includes the root, and a light with nothing
    /// authored is shadowed by everything.
    pub fn shadow_link_collection(&self) -> usd::CollectionAPI {
        usd::CollectionAPI::from_prim_unchecked(self.prim().clone(), tokens::SHADOW_LINK)
    }
}

/// What every light filter adds to its generated view (C++
/// `UsdLuxLightFilter`), for [`LightFilter`](super::LightFilter) and
/// [`PluginLightFilter`](super::PluginLightFilter) alike.
pub trait LightFilterExt: LightFilterSchema {
    /// The collection of the geometry the filter applies to (C++
    /// `UsdLuxLightFilter::GetFilterLinkCollectionAPI`). The filter's schema
    /// includes the root, and a filter with nothing authored applies to
    /// everything.
    fn filter_link_collection(&self) -> usd::CollectionAPI {
        usd::CollectionAPI::from_prim_unchecked(self.prim().clone(), tokens::FILTER_LINK)
    }
}

impl<T: LightFilterSchema> LightFilterExt for T {}
