//! `UsdCollectionAPI` — named working sets over a stage (spec §15).
//!
//! A collection is a multiple-apply API schema applied to a prim with an
//! *instance name*; its properties live under `collection:<name>:`. A
//! collection names a set of paths via the relationship-linking language —
//! `includes` / `excludes` relationships, an `expansionRule`, and an
//! `includeRoot` flag — which a [`MembershipQuery`] resolves into actual
//! membership.
//!
//! Collections are a *core* USD feature (not tied to any one schema
//! family): UsdShade material binding, UsdRender render passes, UsdPhysics
//! collision groups, and UsdLux light-linking all consume them. This
//! module is therefore always compiled, like
//! [`ConnectionGraph`](super::ConnectionGraph).
//!
//! [`Collection`] is the schema surface — locating collections on a prim
//! and reading their authored opinions. [`MembershipQuery`] is the resolved
//! path-membership predicate built from those opinions.
//!
//! The newer pattern-based `membershipExpression` mode (an
//! `SdfPathExpression` predicate) is read here as a raw string but is not
//! yet *evaluated* — that engine is a separate effort. Relationship-mode
//! collections are fully supported.

use std::collections::{HashMap, HashSet};

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::Stage;

/// Multiple-apply API schema name; instances appear in `apiSchemas` as
/// `CollectionAPI:<name>`.
const API_COLLECTION: &str = "CollectionAPI";
/// Property namespace prefix for every collection property.
const NS_COLLECTION: &str = "collection:";

// Property base names (suffixes after `collection:<name>:`).
const EXPANSION_RULE: &str = "expansionRule";
const INCLUDE_ROOT: &str = "includeRoot";
const INCLUDES: &str = "includes";
const EXCLUDES: &str = "excludes";
const MEMBERSHIP_EXPRESSION: &str = "membershipExpression";

// `expansionRule` token values.
const TOK_EXPLICIT_ONLY: &str = "explicitOnly";
const TOK_EXPAND_PRIMS: &str = "expandPrims";
const TOK_EXPAND_PRIMS_AND_PROPERTIES: &str = "expandPrimsAndProperties";

/// How a collection's `includes`/`excludes` targets expand to members
/// (`collection:<name>:expansionRule`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExpansionRule {
    /// Only the exact included paths are members; no descendant expansion.
    ExplicitOnly,
    /// Every prim descendant of an included path is a member (the default).
    #[default]
    ExpandPrims,
    /// Like [`ExpandPrims`](Self::ExpandPrims), and every included prim's
    /// properties are members too.
    ExpandPrimsAndProperties,
}

impl ExpansionRule {
    pub fn as_token(self) -> &'static str {
        match self {
            ExpansionRule::ExplicitOnly => TOK_EXPLICIT_ONLY,
            ExpansionRule::ExpandPrims => TOK_EXPAND_PRIMS,
            ExpansionRule::ExpandPrimsAndProperties => TOK_EXPAND_PRIMS_AND_PROPERTIES,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            TOK_EXPLICIT_ONLY => ExpansionRule::ExplicitOnly,
            TOK_EXPAND_PRIMS => ExpansionRule::ExpandPrims,
            TOK_EXPAND_PRIMS_AND_PROPERTIES => ExpansionRule::ExpandPrimsAndProperties,
            _ => return None,
        })
    }
}

/// A handle to one `UsdCollectionAPI` instance: the prim it is applied to
/// plus the instance name. Cheap to construct and clone; reads pull from
/// the stage on demand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Collection {
    prim: Path,
    name: String,
}

impl Collection {
    /// A handle to the collection named `name` on `prim`. Does not check
    /// that the collection is actually applied — use [`collections_on`] to
    /// enumerate authored collections.
    pub fn new(prim: impl Into<Path>, name: impl Into<String>) -> Self {
        Collection {
            prim: prim.into(),
            name: name.into(),
        }
    }

    /// The prim the collection is applied to.
    pub fn prim(&self) -> &Path {
        &self.prim
    }

    /// The collection's instance name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The `<prim>.collection:<name>` property path — the collection's
    /// identity, used as a target when one collection includes another.
    pub fn collection_path(&self) -> Result<Path> {
        self.prim.append_property(&format!("{NS_COLLECTION}{}", self.name))
    }

    /// `collection:<name>:<suffix>` property path on the prim.
    fn prop(&self, suffix: &str) -> Result<Path> {
        self.prim
            .append_property(&format!("{NS_COLLECTION}{}:{suffix}", self.name))
    }

    /// `expansionRule` — defaults to [`ExpansionRule::ExpandPrims`].
    pub fn expansion_rule(&self, stage: &Stage) -> Result<ExpansionRule> {
        Ok(
            match stage.field::<Value>(self.prop(EXPANSION_RULE)?, FieldKey::Default)? {
                Some(Value::Token(t) | Value::String(t)) => ExpansionRule::from_token(&t).unwrap_or_default(),
                _ => ExpansionRule::default(),
            },
        )
    }

    /// `includeRoot` — whether the pseudo-root `</>` counts as included.
    /// Defaults to `false`.
    pub fn include_root(&self, stage: &Stage) -> Result<bool> {
        Ok(matches!(
            stage.field::<Value>(self.prop(INCLUDE_ROOT)?, FieldKey::Default)?,
            Some(Value::Bool(true))
        ))
    }

    /// The authored `includes` relationship targets.
    pub fn includes(&self, stage: &Stage) -> Result<Vec<Path>> {
        stage.relationship_targets(&self.prop(INCLUDES)?)
    }

    /// The authored `excludes` relationship targets.
    pub fn excludes(&self, stage: &Stage) -> Result<Vec<Path>> {
        stage.relationship_targets(&self.prop(EXCLUDES)?)
    }

    /// The raw `membershipExpression` string, if authored. Read-only —
    /// expression-mode evaluation is not implemented yet.
    pub fn membership_expression(&self, stage: &Stage) -> Result<Option<String>> {
        Ok(
            match stage.field::<Value>(self.prop(MEMBERSHIP_EXPRESSION)?, FieldKey::Default)? {
                Some(Value::PathExpression(s) | Value::String(s) | Value::Token(s)) => Some(s),
                _ => None,
            },
        )
    }

    /// Whether this collection is authored in expression mode (a
    /// `membershipExpression` with no `includes`/`excludes`/`includeRoot`).
    /// Such collections are not yet evaluated.
    pub fn has_expression(&self, stage: &Stage) -> Result<bool> {
        Ok(self.membership_expression(stage)?.is_some()
            && self.includes(stage)?.is_empty()
            && self.excludes(stage)?.is_empty()
            && !self.include_root(stage)?)
    }

    /// Resolve this collection's authored opinions into a
    /// [`MembershipQuery`] (relationship mode, spec §15.2): `includeRoot`
    /// and each `includes` target take the collection's `expansionRule`,
    /// each `excludes` target is marked excluded, and an `includes` target
    /// that is itself another collection is recursively merged in.
    ///
    /// Cycles among chained collections are broken (each collection visited
    /// once); excludes are applied last so they always win over includes.
    /// Expression-mode collections (`has_expression`) currently resolve to
    /// an empty query.
    pub fn compute_membership_query(&self, stage: &Stage) -> Result<MembershipQuery> {
        let mut map = PathExpansionRuleMap::new();
        let mut visited = HashSet::new();
        visited.insert(self.collection_path()?);
        self.build_into(stage, &mut map, &mut visited)?;
        Ok(MembershipQuery::new(map))
    }

    fn build_into(&self, stage: &Stage, map: &mut PathExpansionRuleMap, visited: &mut HashSet<Path>) -> Result<()> {
        let rule = self.expansion_rule(stage)?;
        let path_rule = PathRule::from_expansion(rule);

        // `includeRoot` injects the pseudo-root as a top-level include
        // (no effect under `explicitOnly`).
        if self.include_root(stage)? && rule != ExpansionRule::ExplicitOnly {
            map.insert(Path::abs_root(), path_rule);
        }

        for included in self.includes(stage)? {
            // A target that is itself a collection is merged recursively.
            if let Some((prim, name)) = is_collection_api_path(&included) {
                let nested = Collection::new(prim, name);
                if visited.insert(nested.collection_path()?) {
                    nested.build_into(stage, map, visited)?;
                }
                // else: cycle / already-merged — skip.
                continue;
            }
            map.insert(included, path_rule);
        }

        // Excludes applied last so they win over any include at the same path.
        for excluded in self.excludes(stage)? {
            map.insert(excluded, PathRule::Exclude);
        }
        Ok(())
    }
}

/// Every `UsdCollectionAPI` instance applied to `prim`, decoded from its
/// `apiSchemas` (`CollectionAPI:<name>`).
pub fn collections_on(stage: &Stage, prim: &Path) -> Result<Vec<Collection>> {
    let mut out = Vec::new();
    for schema in stage.api_schemas(prim)? {
        if let Some(name) = instance_name(&schema) {
            out.push(Collection::new(prim.clone(), name));
        }
    }
    Ok(out)
}

/// Decode the instance name from a `CollectionAPI:<name>` apiSchema entry.
fn instance_name(api_schema: &str) -> Option<String> {
    api_schema
        .strip_prefix(API_COLLECTION)?
        .strip_prefix(':')
        .map(str::to_string)
}

/// If `path` is a collection identity path `<prim>.collection:<name>`,
/// return `(prim, name)`. Used to detect when an `includes` target points
/// at another collection (chained collections). A deeper property path like
/// `collection:<name>:includes` is *not* a collection identity and yields
/// `None`.
pub fn is_collection_api_path(path: &Path) -> Option<(Path, String)> {
    let (prim, property) = path.split_property()?;
    let rest = property.strip_prefix(NS_COLLECTION)?;
    if rest.is_empty() || rest.contains(':') {
        return None;
    }
    Some((prim, rest.to_string()))
}

/// The rule attached to one path in a resolved [`MembershipQuery`] map,
/// including the `Exclude` sentinel that marks an excluded subtree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathRule {
    /// Only this exact path is a member (no descendant expansion).
    ExplicitOnly,
    /// This path and its prim descendants are members.
    ExpandPrims,
    /// This path, its prim descendants, and their properties are members.
    ExpandPrimsAndProperties,
    /// This path and its descendants are excluded.
    Exclude,
}

impl PathRule {
    fn from_expansion(rule: ExpansionRule) -> Self {
        match rule {
            ExpansionRule::ExplicitOnly => PathRule::ExplicitOnly,
            ExpansionRule::ExpandPrims => PathRule::ExpandPrims,
            ExpansionRule::ExpandPrimsAndProperties => PathRule::ExpandPrimsAndProperties,
        }
    }
}

/// Maps each authored/derived path to the rule that governs it (the
/// `Exclude` sentinel marks excluded subtrees). The resolved form of a
/// collection's includes/excludes/expansionRule/includeRoot opinions.
pub type PathExpansionRuleMap = HashMap<Path, PathRule>;

/// A resolved, stage-free membership predicate for a collection (the
/// relationship-linking mode). Build it once (see
/// `compute_membership_query`) and query [`is_path_included`] cheaply; it
/// clones freely so consumers can cache one per collection path.
///
/// [`is_path_included`]: MembershipQuery::is_path_included
#[derive(Debug, Clone, Default, PartialEq)]
pub struct MembershipQuery {
    rule_map: PathExpansionRuleMap,
    has_excludes: bool,
}

impl MembershipQuery {
    /// Build a query from a resolved rule map.
    pub fn new(rule_map: PathExpansionRuleMap) -> Self {
        let has_excludes = rule_map.values().any(|r| *r == PathRule::Exclude);
        MembershipQuery { rule_map, has_excludes }
    }

    /// The resolved per-path rule map.
    pub fn rule_map(&self) -> &PathExpansionRuleMap {
        &self.rule_map
    }

    /// `true` if any path carries the `Exclude` rule — lets a traversal skip
    /// per-prim membership checks when there's nothing to exclude.
    pub fn has_excludes(&self) -> bool {
        self.has_excludes
    }

    /// `true` when the query has no opinions (includes nothing).
    pub fn is_empty(&self) -> bool {
        self.rule_map.is_empty()
    }

    /// Whether `path` is a member, by walking from `path` toward the root and
    /// taking the **closest ancestor with an opinion** (spec §15.2):
    ///
    /// - `Exclude` → not a member;
    /// - `ExplicitOnly` → member only if the opinion is on `path` itself;
    /// - `ExpandPrims` → prim members always; a property only if it is itself
    ///   the explicitly listed path;
    /// - `ExpandPrimsAndProperties` → member.
    ///
    /// Paths with no ancestor opinion are not members.
    pub fn is_path_included(&self, path: &Path) -> bool {
        let is_property = path.is_property_path();
        let mut current = path.clone();
        loop {
            if let Some(rule) = self.rule_map.get(&current) {
                let on_self = &current == path;
                return match rule {
                    PathRule::Exclude => false,
                    PathRule::ExplicitOnly => on_self,
                    PathRule::ExpandPrims => !is_property || on_self,
                    PathRule::ExpandPrimsAndProperties => true,
                };
            }
            match current.parent() {
                Some(parent) if !parent.is_empty() => current = parent,
                _ => return false,
            }
        }
    }

    /// Fast top-down variant for stage traversal: given the rule that applies
    /// to `path`'s parent, decide inclusion and the rule to propagate to
    /// `path`'s own children — without re-walking ancestors. An opinion
    /// authored directly on `path` overrides the inherited `parent_rule`.
    pub fn is_path_included_below(&self, path: &Path, parent_rule: PathRule) -> (bool, PathRule) {
        let rule = self.rule_map.get(path).copied().unwrap_or(parent_rule);
        let on_self = self.rule_map.contains_key(path);
        let is_property = path.is_property_path();
        let included = match rule {
            PathRule::Exclude => false,
            PathRule::ExplicitOnly => on_self,
            PathRule::ExpandPrims => !is_property || on_self,
            PathRule::ExpandPrimsAndProperties => true,
        };
        (included, rule)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;
    use crate::sdf::Variability;

    fn query(entries: &[(&str, PathRule)]) -> MembershipQuery {
        let map = entries.iter().map(|(p, r)| (sdf::path(p).unwrap(), *r)).collect();
        MembershipQuery::new(map)
    }

    fn author_collection(stage: &Stage, prim: &str, name: &str) -> Result<()> {
        stage
            .define_prim(sdf::path(prim)?)?
            .set_type_name("Scope")?
            .add_applied_schema(format!("{API_COLLECTION}:{name}"))?;
        Ok(())
    }

    #[test]
    fn expansion_rule_round_trips() {
        for r in [
            ExpansionRule::ExplicitOnly,
            ExpansionRule::ExpandPrims,
            ExpansionRule::ExpandPrimsAndProperties,
        ] {
            assert_eq!(ExpansionRule::from_token(r.as_token()), Some(r));
        }
        assert_eq!(ExpansionRule::from_token("nope"), None);
        assert_eq!(ExpansionRule::default(), ExpansionRule::ExpandPrims);
    }

    #[test]
    fn decodes_collection_paths() -> Result<()> {
        assert_eq!(
            is_collection_api_path(&sdf::path("/W.collection:render")?),
            Some((sdf::path("/W")?, "render".to_string()))
        );
        // A deeper property (the includes rel) is not a collection identity.
        assert_eq!(
            is_collection_api_path(&sdf::path("/W.collection:render:includes")?),
            None
        );
        // A non-collection property / a prim path.
        assert_eq!(is_collection_api_path(&sdf::path("/W.foo")?), None);
        assert_eq!(is_collection_api_path(&sdf::path("/W")?), None);
        Ok(())
    }

    #[test]
    fn enumerates_collections_on_prim() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage
            .define_prim(sdf::path("/W")?)?
            .set_type_name("Scope")?
            .add_applied_schema("CollectionAPI:render")?
            .add_applied_schema("CollectionAPI:proxy")?
            .add_applied_schema("MaterialBindingAPI")?; // not a collection — ignored

        let names: Vec<String> = collections_on(&stage, &sdf::path("/W")?)?
            .into_iter()
            .map(|c| c.name().to_string())
            .collect();
        assert_eq!(names, vec!["render".to_string(), "proxy".to_string()]);
        Ok(())
    }

    #[test]
    fn reads_authored_opinions() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        author_collection(&stage, "/W", "render")?;
        let w = sdf::path("/W")?;
        let coll = Collection::new(w.clone(), "render");

        // expansionRule (uniform token), includeRoot (uniform bool), includes rel.
        stage
            .create_attribute(coll.prop(EXPANSION_RULE)?, "token")?
            .set_variability(Variability::Uniform)?
            .set(Value::Token(ExpansionRule::ExplicitOnly.as_token().to_string()))?;
        stage
            .create_attribute(coll.prop(INCLUDE_ROOT)?, "bool")?
            .set_variability(Variability::Uniform)?
            .set(Value::Bool(true))?;
        crate::usd::Prim::new(&stage, w.clone())
            .author_relationship_targets(&format!("collection:render:{INCLUDES}"), [sdf::path("/W/A")?])?;

        assert_eq!(coll.expansion_rule(&stage)?, ExpansionRule::ExplicitOnly);
        assert!(coll.include_root(&stage)?);
        assert_eq!(coll.includes(&stage)?, vec![sdf::path("/W/A")?]);
        assert!(coll.excludes(&stage)?.is_empty());

        // Unauthored collection falls back to spec defaults.
        author_collection(&stage, "/X", "c")?;
        let bare = Collection::new(sdf::path("/X")?, "c");
        assert_eq!(bare.expansion_rule(&stage)?, ExpansionRule::ExpandPrims);
        assert!(!bare.include_root(&stage)?);
        Ok(())
    }

    #[test]
    fn expand_prims_includes_descendant_prims_not_properties() -> Result<()> {
        let q = query(&[("/W/A", PathRule::ExpandPrims)]);
        assert!(q.is_path_included(&sdf::path("/W/A")?)); // the include itself
        assert!(q.is_path_included(&sdf::path("/W/A/B")?)); // descendant prim
        assert!(!q.is_path_included(&sdf::path("/W")?)); // ancestor, not a member
        assert!(!q.is_path_included(&sdf::path("/W/A.x")?)); // property: not under expandPrims
        assert!(!q.is_path_included(&sdf::path("/W/Other")?)); // unrelated
        Ok(())
    }

    #[test]
    fn explicit_only_matches_exact_paths() -> Result<()> {
        let q = query(&[("/W/A", PathRule::ExplicitOnly)]);
        assert!(q.is_path_included(&sdf::path("/W/A")?));
        assert!(!q.is_path_included(&sdf::path("/W/A/B")?)); // no descendant expansion
        Ok(())
    }

    #[test]
    fn expand_prims_and_properties_includes_properties() -> Result<()> {
        let q = query(&[("/W/A", PathRule::ExpandPrimsAndProperties)]);
        assert!(q.is_path_included(&sdf::path("/W/A")?));
        assert!(q.is_path_included(&sdf::path("/W/A/B")?));
        assert!(q.is_path_included(&sdf::path("/W/A.x")?)); // property is a member
        Ok(())
    }

    #[test]
    fn closest_ancestor_excludes_win() -> Result<()> {
        // Include /W, exclude the /W/A subtree.
        let q = query(&[("/W", PathRule::ExpandPrims), ("/W/A", PathRule::Exclude)]);
        assert!(q.has_excludes());
        assert!(q.is_path_included(&sdf::path("/W/B")?)); // under the include
        assert!(!q.is_path_included(&sdf::path("/W/A")?)); // excluded
        assert!(!q.is_path_included(&sdf::path("/W/A/C")?)); // closest ancestor is the exclude
        Ok(())
    }

    #[test]
    fn below_propagates_parent_rule() -> Result<()> {
        let q = query(&[("/W", PathRule::ExpandPrims)]);
        // A child with no own opinion inherits the parent rule and is included.
        let (inc, rule) = q.is_path_included_below(&sdf::path("/W/A")?, PathRule::ExpandPrims);
        assert!(inc);
        assert_eq!(rule, PathRule::ExpandPrims);
        // Under an Exclude parent, the child is out.
        let (inc, _) = q.is_path_included_below(&sdf::path("/W/A/B")?, PathRule::Exclude);
        assert!(!inc);
        Ok(())
    }

    /// Author a full collection (apiSchema + expansionRule + includeRoot +
    /// includes/excludes rels) for the compute tests.
    #[allow(clippy::too_many_arguments)]
    fn build_collection(
        stage: &Stage,
        prim: &str,
        name: &str,
        rule: ExpansionRule,
        include_root: bool,
        includes: &[&str],
        excludes: &[&str],
    ) -> Result<()> {
        let prim_path = sdf::path(prim)?;
        stage
            .define_prim(prim_path.clone())?
            .set_type_name("Scope")?
            .add_applied_schema(format!("{API_COLLECTION}:{name}"))?;
        let coll = Collection::new(prim_path.clone(), name);
        stage
            .create_attribute(coll.prop(EXPANSION_RULE)?, "token")?
            .set_variability(Variability::Uniform)?
            .set(Value::Token(rule.as_token().to_string()))?;
        if include_root {
            stage
                .create_attribute(coll.prop(INCLUDE_ROOT)?, "bool")?
                .set_variability(Variability::Uniform)?
                .set(Value::Bool(true))?;
        }
        let prim_handle = crate::usd::Prim::new(stage, prim_path);
        if !includes.is_empty() {
            let targets: Vec<Path> = includes.iter().map(|p| sdf::path(p).unwrap()).collect();
            prim_handle.author_relationship_targets(&format!("collection:{name}:{INCLUDES}"), targets)?;
        }
        if !excludes.is_empty() {
            let targets: Vec<Path> = excludes.iter().map(|p| sdf::path(p).unwrap()).collect();
            prim_handle.author_relationship_targets(&format!("collection:{name}:{EXCLUDES}"), targets)?;
        }
        Ok(())
    }

    #[test]
    fn compute_basic_includes() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        build_collection(&stage, "/W", "c", ExpansionRule::ExpandPrims, false, &["/W/A"], &[])?;
        let q = Collection::new(sdf::path("/W")?, "c").compute_membership_query(&stage)?;
        assert!(q.is_path_included(&sdf::path("/W/A/B")?));
        assert!(!q.is_path_included(&sdf::path("/W/Other")?));
        Ok(())
    }

    #[test]
    fn compute_include_root_with_excludes() -> Result<()> {
        // "Everything but /W/A": includeRoot + an exclude.
        let stage = Stage::builder().in_memory("anon.usda")?;
        build_collection(&stage, "/W", "c", ExpansionRule::ExpandPrims, true, &[], &["/W/A"])?;
        let q = Collection::new(sdf::path("/W")?, "c").compute_membership_query(&stage)?;
        assert!(q.has_excludes());
        assert!(q.is_path_included(&sdf::path("/W/B")?));
        assert!(!q.is_path_included(&sdf::path("/W/A")?));
        assert!(!q.is_path_included(&sdf::path("/W/A/C")?));
        Ok(())
    }

    #[test]
    fn compute_merges_nested_collection() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        // inner includes /W/X; outer includes inner's identity path.
        build_collection(&stage, "/R", "inner", ExpansionRule::ExpandPrims, false, &["/W/X"], &[])?;
        build_collection(
            &stage,
            "/R",
            "outer",
            ExpansionRule::ExpandPrims,
            false,
            &["/R.collection:inner"],
            &[],
        )?;
        let q = Collection::new(sdf::path("/R")?, "outer").compute_membership_query(&stage)?;
        assert!(q.is_path_included(&sdf::path("/W/X/Leaf")?));
        Ok(())
    }

    #[test]
    fn compute_breaks_cycle() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        // a includes b, b includes a — must terminate.
        build_collection(
            &stage,
            "/R",
            "a",
            ExpansionRule::ExpandPrims,
            false,
            &["/R.collection:b"],
            &[],
        )?;
        build_collection(
            &stage,
            "/R",
            "b",
            ExpansionRule::ExpandPrims,
            false,
            &["/R.collection:a"],
            &[],
        )?;
        let q = Collection::new(sdf::path("/R")?, "a").compute_membership_query(&stage)?;
        // No hang; the cyclic includes contribute no concrete paths.
        assert!(q.is_empty());
        Ok(())
    }
}
