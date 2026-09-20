//! The `CollisionGroup` view's collection and filtering rules (C++
//! `UsdPhysicsCollisionGroup`).
//!
//! A group holds its colliders in a built-in `colliders` collection, which
//! the schema declares and this reaches.

use openusd::usd::{CollectionAPI, SchemaBase};

use super::CollisionGroup;
use super::tokens::COLLIDERS;

impl CollisionGroup {
    /// The `colliders` collection, whose members are the colliders this group
    /// holds (C++ `UsdPhysicsCollisionGroup::GetCollidersCollectionAPI`).
    ///
    /// Every `PhysicsCollisionGroup` carries it, the schema declaring it as a
    /// built-in, so this asks no question of the prim. What it holds is read
    /// through the collection itself:
    ///
    /// ```no_run
    /// # use openusd::usd::{self, PrimPredicate};
    /// # use openusd_schemas::physics::CollisionGroup;
    /// # fn main() -> openusd::Result<()> {
    /// # let stage = usd::Stage::open("scene.usda")?;
    /// let group = CollisionGroup::get(&stage, "/World/Group")?.expect("a group");
    /// let query = group.colliders_collection().compute_membership_query()?;
    /// let colliders = usd::compute_included_paths(&stage, &query, PrimPredicate::DEFAULT_PROXIES)?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Instance proxies belong in that predicate: a collection reaches into
    /// instanced content, which is what C++ asks for where it evaluates this
    /// collection.
    pub fn colliders_collection(&self) -> CollectionAPI {
        CollectionAPI::from_prim_unchecked(self.prim().clone(), COLLIDERS)
    }
}
