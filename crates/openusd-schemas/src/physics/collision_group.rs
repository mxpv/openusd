//! The `CollisionGroup` view's collection and filtering rules (C++
//! `UsdPhysicsCollisionGroup`).
//!
//! A group holds its colliders in a built-in `colliders` collection, and
//! filters which other groups it collides with through `filteredGroups`,
//! `invertFilteredGroups` and `mergeGroupName`. The two are separate
//! questions: [`CollisionGroupTable`] answers which *groups* collide, and the
//! collection answers which colliders are in one. Joining them — deciding
//! whether two colliders collide — is the simulation's own, as it is in C++.

use std::collections::{HashMap, HashSet};

use openusd::Result;
use openusd::sdf::Path;
use openusd::usd::{CollectionAPI, PrimPredicate, SchemaBase, Stage};

use super::tokens::COLLIDERS;
use super::{CollisionGroup, CollisionGroupSchema};

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

/// Which pairs of collision groups collide, once every group's filtering
/// rules on a stage are resolved (C++
/// `UsdPhysicsCollisionGroup::CollisionGroupTable`).
///
/// A snapshot: [`compute_collision_group_table`] reads the stage once and the
/// table answers from what it read. An edit to any group's filters, merge
/// name or inversion flag does not reach a table already computed, so recompute
/// after one.
///
/// The relation is symmetric — a filter authored on one group disables the
/// pair in both directions — and a group collides with itself unless it
/// filters itself out.
#[derive(Debug, Clone, Default)]
pub struct CollisionGroupTable {
    /// Every collision group on the stage, in traversal order. Groups sharing
    /// a merge name each keep their own row.
    groups: Vec<Path>,
    /// One entry per unordered pair, the diagonal included: `false` where a
    /// filtering rule disabled it. Indexed by [`slot`].
    enabled: Vec<bool>,
}

impl CollisionGroupTable {
    /// Every collision group the table covers, in the order it found them.
    pub fn groups(&self) -> &[Path] {
        &self.groups
    }

    /// Whether the groups at `a` and `b` collide.
    ///
    /// A path the table does not cover collides with everything, which is what
    /// a collider outside every group does.
    pub fn is_collision_enabled(&self, a: &Path, b: &Path) -> bool {
        let (Some(a), Some(b)) = (self.index_of(a), self.index_of(b)) else {
            return true;
        };
        self.is_collision_enabled_at(a, b)
    }

    /// Whether the groups at indices `a` and `b` in [`groups`](Self::groups)
    /// collide. An index past the end collides, as an uncovered path does.
    pub fn is_collision_enabled_at(&self, a: usize, b: usize) -> bool {
        match a < self.groups.len() && b < self.groups.len() {
            true => self.enabled[slot(a, b, self.groups.len())],
            false => true,
        }
    }

    /// Where `path` sits in [`groups`](Self::groups).
    fn index_of(&self, path: &Path) -> Option<usize> {
        self.groups.iter().position(|group| group == path)
    }
}

/// Resolve every collision group's filtering rules on `stage` into the table
/// of which pairs collide (C++
/// `UsdPhysicsCollisionGroup::ComputeCollisionGroupTable`).
///
/// Groups sharing a `mergeGroupName` are one group for the purpose of
/// filtering: each contributes its rules, and the result applies to all of
/// them. Filtering only ever disables a pair, so merging can turn collisions
/// off that neither group turned off alone, and never back on.
///
/// The walk is the default predicate's, so a group inside an instance's
/// prototype is not found — matching C++, and deliberately unlike the
/// collection expansion in
/// [`colliders_collection`](CollisionGroup::colliders_collection), which does
/// reach instanced content.
pub fn compute_collision_group_table(stage: &Stage) -> Result<CollisionGroupTable> {
    let groups = collision_groups(stage)?;

    // Every group gets an index, and a merge name is what makes two groups
    // share one. The first group to claim a name decides which index it is.
    let mut merged_of_group: Vec<usize> = Vec::with_capacity(groups.len());
    let mut index_of_merge_name: HashMap<String, usize> = HashMap::new();
    let mut merged_count = 0;
    for group in &groups {
        let index = match merge_group_name(group)? {
            None => {
                merged_count += 1;
                merged_count - 1
            }
            Some(name) => *index_of_merge_name.entry(name).or_insert_with(|| {
                merged_count += 1;
                merged_count - 1
            }),
        };
        merged_of_group.push(index);
    }
    let merged_index: HashMap<&Path, usize> = groups
        .iter()
        .map(|group| group.path())
        .zip(merged_of_group.iter().copied())
        .collect();

    // Resolve the rules over the merged groups. Everything collides until a
    // rule says otherwise, and a rule only ever disables.
    let mut merged = vec![true; pairs(merged_count)];
    for (group, &a) in groups.iter().zip(&merged_of_group) {
        // A target naming no collision group on this stage — a typo, or a
        // path the walk above does not reach — filters nothing. C++ resolves
        // it to the first merged group instead, which filters against a group
        // nobody named.
        let filtered: HashSet<usize> = group
            .filtered_groups_rel()
            .targets()?
            .iter()
            .filter_map(|target| merged_index.get(target).copied())
            .collect();

        match inverts_filtering(group)? {
            // Disable everything the group did not ask for, its own pair
            // included unless it named itself.
            true => {
                for b in (0..merged_count).filter(|b| !filtered.contains(b)) {
                    merged[slot(a, b, merged_count)] = false;
                }
            }
            false => {
                for &b in &filtered {
                    merged[slot(a, b, merged_count)] = false;
                }
            }
        }
    }

    // Spread the merged answers back over the groups that share them.
    let mut enabled = vec![true; pairs(groups.len())];
    for (ia, &a) in merged_of_group.iter().enumerate() {
        for (ib, &b) in merged_of_group.iter().enumerate().skip(ia) {
            enabled[slot(ia, ib, groups.len())] = merged[slot(a, b, merged_count)];
        }
    }

    Ok(CollisionGroupTable {
        groups: groups.iter().map(|group| group.path().clone()).collect(),
        enabled,
    })
}

/// Every collision group on `stage`, in traversal order.
fn collision_groups(stage: &Stage) -> Result<Vec<CollisionGroup>> {
    let mut groups = Vec::new();
    let mut failed = Ok(());
    stage.traverse(PrimPredicate::DEFAULT, |path| {
        if failed.is_err() {
            return;
        }
        match group_at(stage, path) {
            Ok(Some(group)) => groups.push(group),
            Ok(None) => {}
            Err(error) => failed = Err(error),
        }
    })?;
    failed?;
    Ok(groups)
}

/// The collision group at `path`, where the prim there is one.
fn group_at(stage: &Stage, path: &Path) -> Result<Option<CollisionGroup>> {
    CollisionGroup::from_prim(stage.prim(path.clone())?)
}

/// The name `group` merges under, or `None` where it merges with nothing.
///
/// What decides it is whether anything *authors* the property, not whether a
/// value comes back: a spec that only declares `mergeGroup`, and one that
/// blocks it, both merge the group under the empty name, as C++ does. A value
/// of the wrong type is an error rather than a group quietly left unmerged.
fn merge_group_name(group: &CollisionGroup) -> Result<Option<String>> {
    let name = group.merge_group_name_attr();
    if name.property_stack()?.is_empty() {
        return Ok(None);
    }
    Ok(Some(name.get::<String>()?.unwrap_or_default()))
}

/// Whether `group` disables collisions against everything *except* what it
/// filters.
///
/// Unlike the merge name, a value is what decides this: an unauthored flag, a
/// declaration with no value and a blocked one all leave filtering the usual
/// way round. A value of the wrong type is an error.
fn inverts_filtering(group: &CollisionGroup) -> Result<bool> {
    Ok(group.invert_filtered_groups_attr().get::<bool>()?.unwrap_or(false))
}

/// How many unordered pairs `len` groups have, each group's pair with itself
/// included.
fn pairs(len: usize) -> usize {
    len * (len + 1) / 2
}

/// Where the pair `(a, b)` sits in a table of `len` groups.
///
/// One entry per unordered pair, laid out row by row over the upper triangle,
/// so the pair is put in order first and a table cannot disagree with itself
/// about a pair depending on which way round it is asked.
fn slot(a: usize, b: usize, len: usize) -> usize {
    let (low, high) = (a.min(b), a.max(b));
    low * len - pairs(low) + high
}
