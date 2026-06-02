//! `PhysicsCollisionGroup` typed prim, plus `PhysicsFilteredPairsAPI`
//! and `PhysicsArticulationRootAPI` applied schemas.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::physics::tokens::{
    API_ARTICULATION_ROOT, API_FILTERED_PAIRS, A_FILTERED_GROUPS, A_FILTERED_PAIRS, A_INVERT_FILTERED_GROUPS,
    A_MERGE_GROUP, T_PHYSICS_COLLISION_GROUP,
};

use super::common::{author_bool, author_rel_targets, author_string};

// ── PhysicsCollisionGroup ──────────────────────────────────────────

/// Author a `def PhysicsCollisionGroup` prim at `path`. Per spec, the
/// prim auto-applies `CollectionAPI:colliders` via the schema
/// registry; members are managed through that collection rather than
/// directly here.
pub fn define_collision_group(stage: &Stage, path: impl Into<Path>) -> Result<CollisionGroupAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_PHYSICS_COLLISION_GROUP)?;
    Ok(CollisionGroupAuthor { prim })
}

pub struct CollisionGroupAuthor {
    prim: Prim,
}

impl CollisionGroupAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:filteredGroups` rel — other CollisionGroup prims
    /// whose pairwise collisions should be filtered.
    pub fn set_filtered_groups<I, P>(self, groups: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        author_rel_targets(self.prim.stage(), self.prim.path(), A_FILTERED_GROUPS, groups)?;
        Ok(self)
    }

    /// Set `physics:mergeGroup` (string) — groups sharing the same
    /// `mergeGroup` token are treated as one logical group.
    pub fn set_merge_group(self, group: impl Into<String>) -> Result<Self> {
        author_string(self.prim.stage(), self.prim.path(), A_MERGE_GROUP, group)?;
        Ok(self)
    }

    /// Set `physics:invertFilteredGroups` — when true, the filter
    /// disables collisions against every group except those in
    /// `filteredGroups`.
    pub fn set_invert_filtered_groups(self, invert: bool) -> Result<Self> {
        author_bool(self.prim.stage(), self.prim.path(), A_INVERT_FILTERED_GROUPS, invert)?;
        Ok(self)
    }
}

// ── PhysicsFilteredPairsAPI ────────────────────────────────────────

/// Apply `PhysicsFilteredPairsAPI` to the prim at `path` and return a
/// chainable [`FilteredPairsAuthor`] for the `filteredPairs` rel.
pub fn apply_filtered_pairs(stage: &Stage, path: impl Into<Path>) -> Result<FilteredPairsAuthor> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_FILTERED_PAIRS)?;
    Ok(FilteredPairsAuthor { prim })
}

pub struct FilteredPairsAuthor {
    prim: Prim,
}

impl FilteredPairsAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:filteredPairs` rel — pairs against which collision
    /// should be disabled.
    pub fn set_filtered_pairs<I, P>(self, pairs: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        author_rel_targets(self.prim.stage(), self.prim.path(), A_FILTERED_PAIRS, pairs)?;
        Ok(self)
    }
}

// ── PhysicsArticulationRootAPI ─────────────────────────────────────

/// Apply `PhysicsArticulationRootAPI` to the prim at `path`. The API
/// has no own attributes — it's a marker for reduced-coordinate
/// articulation roots per the spec.
pub fn apply_articulation_root(stage: &Stage, path: impl Into<Path>) -> Result<Prim> {
    Ok(stage.override_prim(path)?.add_applied_schema(API_ARTICULATION_ROOT)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn collision_group_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_collision_group(&stage, sdf::path("/GroupA")?)?;
        define_collision_group(&stage, sdf::path("/GroupB")?)?
            .set_filtered_groups([sdf::path("/GroupA")?])?
            .set_merge_group("vehicles")?
            .set_invert_filtered_groups(false)?;

        let group =
            crate::schemas::physics::read_collision_group(&stage, &sdf::path("/GroupB")?)?.expect("CollisionGroup");
        assert_eq!(group.filtered_groups, vec!["/GroupA".to_string()]);
        assert_eq!(group.merge_group.as_deref(), Some("vehicles"));
        assert!(!group.invert_filtered_groups);
        Ok(())
    }

    #[test]
    fn filtered_pairs_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Body")?.set_type_name("Xform")?;
        stage.define_prim("/Other")?.set_type_name("Xform")?;
        apply_filtered_pairs(&stage, sdf::path("/Body")?)?.set_filtered_pairs([sdf::path("/Other")?])?;

        let pairs =
            crate::schemas::physics::read_filtered_pairs(&stage, &sdf::path("/Body")?)?.expect("FilteredPairsAPI");
        assert_eq!(pairs.filtered, vec!["/Other".to_string()]);
        Ok(())
    }

    #[test]
    fn articulation_root_is_a_marker() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Robot")?.set_type_name("Xform")?;
        apply_articulation_root(&stage, sdf::path("/Robot")?)?;

        assert!(crate::schemas::physics::read_has_articulation_root(
            &stage,
            &sdf::path("/Robot")?,
        )?);
        Ok(())
    }
}
