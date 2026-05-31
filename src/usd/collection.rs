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

use crate::sdf::{FieldKey, Path, Value, Variability};
use crate::usd::{Prim, PrimPredicate, Stage};

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
        self.prim.append_property(&self.rel_name(suffix))
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

    /// `collection:<name>:<suffix>` relationship/property name (unanchored).
    fn rel_name(&self, suffix: &str) -> String {
        format!("{NS_COLLECTION}{}:{suffix}", self.name)
    }

    /// Set `expansionRule` (`uniform token`).
    pub fn set_expansion_rule(&self, stage: &Stage, rule: ExpansionRule) -> Result<()> {
        stage
            .create_attribute(self.prop(EXPANSION_RULE)?, "token")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::Token(rule.as_token().to_string()))?;
        Ok(())
    }

    /// Set `includeRoot` (`uniform bool`).
    pub fn set_include_root(&self, stage: &Stage, value: bool) -> Result<()> {
        stage
            .create_attribute(self.prop(INCLUDE_ROOT)?, "bool")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::Bool(value))?;
        Ok(())
    }

    /// Make `path` a member, minimizing edits (spec §15, mirroring C++
    /// `UsdCollectionAPI::IncludePath`): if it is already included (e.g. via
    /// an ancestor), do nothing; including `</>` sets `includeRoot`; an
    /// excluded `path` is first un-excluded; and a new `includes` target is
    /// added only if `path` would still not be a member.
    pub fn include_path(&self, stage: &Stage, path: impl Into<Path>) -> Result<()> {
        let path = path.into();
        if self.compute_membership_query(stage)?.is_path_included(&path) {
            return Ok(()); // already included — no edit
        }
        if path.is_abs_root() {
            return self.set_include_root(stage, true);
        }
        let prim = Prim::new(stage, self.prim.clone());
        // Drop a direct exclude of `path`. That can flip membership when an
        // ancestor includes `path`, so re-resolve only when one was removed;
        // otherwise membership is unchanged from the check above.
        if self.excludes(stage)?.contains(&path) {
            prim.create_relationship(&self.rel_name(EXCLUDES))?
                .remove_target(&path)?;
            if self.compute_membership_query(stage)?.is_path_included(&path) {
                return Ok(()); // dropping the exclude was enough
            }
        }
        prim.create_relationship(&self.rel_name(INCLUDES))?.add_target(path)?;
        Ok(())
    }

    /// Remove `path` from membership, minimizing edits (mirroring C++
    /// `UsdCollectionAPI::ExcludePath`): on a non-empty collection where
    /// `path` is already a non-member, do nothing; excluding `</>` clears
    /// `includeRoot`; a directly-included `path` is first un-included; and an
    /// `excludes` target is added when the collection is empty (recording the
    /// intent) or `path` would otherwise still be a member.
    pub fn exclude_path(&self, stage: &Stage, path: impl Into<Path>) -> Result<()> {
        let path = path.into();
        let query = self.compute_membership_query(stage)?;
        if !query.is_empty() && !query.is_path_included(&path) {
            return Ok(()); // already not a member — no edit
        }
        if path.is_abs_root() {
            return self.set_include_root(stage, false);
        }
        let prim = Prim::new(stage, self.prim.clone());
        // Drop a direct include of `path`. That can flip membership when an
        // ancestor still includes `path`, so re-resolve only when one was
        // removed; an explicit exclude is then added when `path` remains a
        // member (via an ancestor / includeRoot) or the collection is now
        // empty (recording the intent).
        if !query.is_empty() && self.includes(stage)?.contains(&path) {
            prim.create_relationship(&self.rel_name(INCLUDES))?
                .remove_target(&path)?;
            let query = self.compute_membership_query(stage)?;
            if !query.is_empty() && !query.is_path_included(&path) {
                return Ok(()); // dropping the include was enough
            }
        }
        prim.create_relationship(&self.rel_name(EXCLUDES))?.add_target(path)?;
        Ok(())
    }

    /// `true` when the collection includes nothing (mirroring C++
    /// `UsdCollectionAPI::HasNoIncludedPaths`): no `includes`, `includeRoot`
    /// off, and either an `excludes` opinion exists or there is no membership
    /// expression. (The expression term matters once expression mode lands.)
    pub fn has_no_included_paths(&self, stage: &Stage) -> Result<bool> {
        Ok(self.includes(stage)?.is_empty()
            && !self.include_root(stage)?
            && (!self.excludes(stage)?.is_empty() || self.membership_expression(stage)?.is_none()))
    }

    fn build_into(&self, stage: &Stage, map: &mut PathExpansionRuleMap, visited: &mut HashSet<Path>) -> Result<()> {
        // TODO(perf): each (possibly nested) invocation re-reads expansionRule,
        // includeRoot, includes and excludes from the stage as separate field
        // lookups; snapshot a collection's authored opinions once per build.
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

        // This collection's own excludes are applied last so they win over
        // every include — including paths brought in by nested collections.
        // (Within the includes pass, later opinions overwrite earlier ones,
        // matching C++ `_ComputeMembershipQueryImpl`'s merge order: a nested
        // collection's opinion can be overridden by a later sibling include,
        // and the owning collection's excludes always take final precedence.)
        for excluded in self.excludes(stage)? {
            map.insert(excluded, PathRule::Exclude);
        }
        Ok(())
    }
}

/// Apply `UsdCollectionAPI` to `prim` with instance name `name` (adds
/// `CollectionAPI:<name>` to `apiSchemas`) and return a handle. Author its
/// membership via the returned [`Collection`]'s setters / `include_path` /
/// `exclude_path`.
pub fn apply_collection(stage: &Stage, prim: impl Into<Path>, name: impl Into<String>) -> Result<Collection> {
    let prim = prim.into();
    let name = name.into();
    // Author an `over` when the prim has no spec on the edit-target layer yet,
    // mirroring C++ `UsdCollectionAPI::Apply` (which authors the spec as
    // needed). `override_prim` is idempotent when a spec already exists.
    stage
        .override_prim(prim.clone())?
        .add_applied_schema(format!("{API_COLLECTION}:{name}"))?;
    Ok(Collection::new(prim, name))
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

/// Enumerate the paths that `query` includes on `stage`, restricted to the
/// prims `predicate` admits (spec §15.2). Returns prim members in traversal
/// order; under `expandPrimsAndProperties` each included prim's member
/// properties follow it, and explicitly listed property targets are
/// included too.
///
/// Walks the stage and tests each prim with
/// [`MembershipQuery::is_path_included`], which honors excludes by the
/// closest-ancestor rule.
pub fn compute_included_paths(stage: &Stage, query: &MembershipQuery, predicate: PrimPredicate) -> Result<Vec<Path>> {
    let mut out = Vec::new();
    if query.is_empty() {
        return Ok(out);
    }
    let mut seen = HashSet::new();
    let mut err: Result<()> = Ok(());
    let collect_props = query.has_property_expansion;

    // Top-down traversal: `traverse` is pre-order, so a prim's parent is
    // resolved just before it. Propagating the parent's effective rule via
    // `is_path_included_below` keeps each prim O(1) instead of re-walking its
    // ancestors. A parent the predicate skipped isn't cached, so its rule is
    // recomputed once with `effective_rule`.
    let mut effective: HashMap<Path, PathRule> = HashMap::new();

    stage.traverse(predicate, |prim| {
        if err.is_err() {
            return;
        }
        let parent_rule = match prim.parent() {
            Some(parent) => effective
                .get(&parent)
                .copied()
                .unwrap_or_else(|| query.effective_rule(&parent)),
            None => PathRule::Exclude,
        };
        let (included, rule) = query.is_path_included_below(prim, parent_rule);
        effective.insert(prim.clone(), rule);
        if !included {
            return;
        }
        if seen.insert(prim.clone()) {
            out.push(prim.clone());
        }
        if collect_props {
            if let Err(e) = push_member_properties(stage, prim, rule, query, &mut seen, &mut out) {
                err = Err(e);
            }
        }
    })?;
    err?;

    // Explicitly listed property targets (e.g. an `includes` of `prim.attr`)
    // aren't reached by the prim walk above.
    for (path, _) in query.rule_map.iter() {
        if path.is_property_path() && query.is_path_included(path) && seen.insert(path.clone()) {
            out.push(path.clone());
        }
    }
    Ok(out)
}

fn push_member_properties(
    stage: &Stage,
    prim: &Path,
    prim_rule: PathRule,
    query: &MembershipQuery,
    seen: &mut HashSet<Path>,
    out: &mut Vec<Path>,
) -> Result<()> {
    for name in stage.prim_properties(prim.clone())? {
        let prop = prim.append_property(&name)?;
        let (included, _) = query.is_path_included_below(&prop, prim_rule);
        if included && seen.insert(prop.clone()) {
            out.push(prop);
        }
    }
    Ok(())
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
    has_property_expansion: bool,
}

impl MembershipQuery {
    /// Build a query from a resolved rule map.
    pub fn new(rule_map: PathExpansionRuleMap) -> Self {
        let has_excludes = rule_map.values().any(|r| *r == PathRule::Exclude);
        let has_property_expansion = rule_map.values().any(|r| *r == PathRule::ExpandPrimsAndProperties);
        MembershipQuery {
            rule_map,
            has_excludes,
            has_property_expansion,
        }
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
        let (rule, on_self) = self.closest_rule(path);
        rule_includes(rule, on_self, path.is_property_path())
    }

    /// Fast top-down variant for stage traversal: given the rule that applies
    /// to `path`'s parent, decide inclusion and the rule to propagate to
    /// `path`'s own children — without re-walking ancestors. An opinion
    /// authored directly on `path` overrides the inherited `parent_rule`.
    pub fn is_path_included_below(&self, path: &Path, parent_rule: PathRule) -> (bool, PathRule) {
        let on_self = self.rule_map.contains_key(path);
        let rule = self.rule_map.get(path).copied().unwrap_or(parent_rule);
        (rule_includes(rule, on_self, path.is_property_path()), rule)
    }

    /// The rule governing `path` by its closest-ancestor opinion, or
    /// [`PathRule::Exclude`] when no ancestor opines. Used to seed the
    /// top-down traversal in [`compute_included_paths`] for a parent the
    /// traversal predicate skipped (so it isn't in the rule cache).
    fn effective_rule(&self, path: &Path) -> PathRule {
        self.closest_rule(path).0
    }

    /// Walk from `path` toward the root and return the closest opinion: its
    /// rule and whether that opinion sits on `path` itself. Returns
    /// [`PathRule::Exclude`] with `on_self = false` when no ancestor opines.
    fn closest_rule(&self, path: &Path) -> (PathRule, bool) {
        let mut current = path.clone();
        loop {
            if let Some(rule) = self.rule_map.get(&current) {
                return (*rule, &current == path);
            }
            match current.parent() {
                Some(parent) if !parent.is_empty() => current = parent,
                _ => return (PathRule::Exclude, false),
            }
        }
    }
}

/// Whether `rule` admits a path, given whether the governing opinion sits on
/// the path itself (`on_self`) and whether the path is a property:
///
/// - [`PathRule::Exclude`] never admits;
/// - [`PathRule::ExplicitOnly`] admits only the exact opinion path;
/// - [`PathRule::ExpandPrims`] admits prims, and a property only when listed
///   explicitly;
/// - [`PathRule::ExpandPrimsAndProperties`] admits everything below it.
fn rule_includes(rule: PathRule, on_self: bool, is_property: bool) -> bool {
    match rule {
        PathRule::Exclude => false,
        PathRule::ExplicitOnly => on_self,
        PathRule::ExpandPrims => !is_property || on_self,
        PathRule::ExpandPrimsAndProperties => true,
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

    /// Evaluate membership the way `compute_included_paths` does: fold
    /// `is_path_included_below` down the ancestor chain from the root,
    /// seeding the top element's parent rule with `effective_rule`. Must
    /// agree with the closest-ancestor point query `is_path_included`.
    fn included_top_down(q: &MembershipQuery, path: &Path) -> bool {
        let mut chain = vec![path.clone()];
        while let Some(parent) = chain.last().unwrap().parent() {
            if parent.is_empty() {
                break;
            }
            chain.push(parent);
        }
        chain.reverse();
        let mut parent_rule = match chain[0].parent() {
            Some(p) if !p.is_empty() => q.effective_rule(&p),
            _ => PathRule::Exclude,
        };
        let mut included = false;
        for elem in &chain {
            let (inc, rule) = q.is_path_included_below(elem, parent_rule);
            included = inc;
            parent_rule = rule;
        }
        included
    }

    #[test]
    fn membership_methods_agree() -> Result<()> {
        // Guards against drift between is_path_included (point query),
        // is_path_included_below (top-down fold) and effective_rule, which
        // share the closest-ancestor walk and rule-match logic.
        let q = query(&[
            ("/W", PathRule::ExpandPrims),
            ("/W/A", PathRule::Exclude),
            ("/W/B", PathRule::ExpandPrimsAndProperties),
            ("/W/C", PathRule::ExplicitOnly),
            ("/W/B.size", PathRule::ExpandPrimsAndProperties),
        ]);
        for p in [
            "/W", "/W/A", "/W/A/C", "/W/B", "/W/B/D", "/W/B.size", "/W/C", "/W/C/D", "/W/D", "/W.x", "/Other",
        ] {
            let path = sdf::path(p)?;
            assert_eq!(
                q.is_path_included(&path),
                included_top_down(&q, &path),
                "point query and top-down fold disagree on {p}"
            );
        }
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

    /// A small scene: /W with children A (and A/C) and B.
    fn scene() -> Result<Stage> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        for p in ["/W", "/W/A", "/W/A/C", "/W/B"] {
            stage.define_prim(sdf::path(p)?)?.set_type_name("Scope")?;
        }
        Ok(stage)
    }

    #[test]
    fn included_paths_expand_prims() -> Result<()> {
        let stage = scene()?;
        build_collection(&stage, "/Col", "c", ExpansionRule::ExpandPrims, false, &["/W/A"], &[])?;
        let q = Collection::new(sdf::path("/Col")?, "c").compute_membership_query(&stage)?;
        let mut paths = compute_included_paths(&stage, &q, PrimPredicate::DEFAULT)?;
        paths.sort();
        assert_eq!(paths, vec![sdf::path("/W/A")?, sdf::path("/W/A/C")?]);
        Ok(())
    }

    #[test]
    fn included_paths_explicit_only() -> Result<()> {
        let stage = scene()?;
        build_collection(&stage, "/Col", "c", ExpansionRule::ExplicitOnly, false, &["/W/A"], &[])?;
        let q = Collection::new(sdf::path("/Col")?, "c").compute_membership_query(&stage)?;
        let paths = compute_included_paths(&stage, &q, PrimPredicate::DEFAULT)?;
        assert_eq!(paths, vec![sdf::path("/W/A")?]); // no descendants
        Ok(())
    }

    #[test]
    fn included_paths_include_root_minus_excludes() -> Result<()> {
        let stage = scene()?;
        // Everything under /W except the /W/A subtree.
        build_collection(
            &stage,
            "/Col",
            "c",
            ExpansionRule::ExpandPrims,
            true,
            &["/W"],
            &["/W/A"],
        )?;
        let q = Collection::new(sdf::path("/Col")?, "c").compute_membership_query(&stage)?;
        let paths = compute_included_paths(&stage, &q, PrimPredicate::DEFAULT)?;
        assert!(paths.contains(&sdf::path("/W/B")?));
        assert!(!paths.contains(&sdf::path("/W/A")?));
        assert!(!paths.contains(&sdf::path("/W/A/C")?));
        Ok(())
    }

    #[test]
    fn authoring_include_exclude_roundtrip() -> Result<()> {
        let stage = scene()?;
        let coll = apply_collection(&stage, sdf::path("/W")?, "c")?;
        coll.set_expansion_rule(&stage, ExpansionRule::ExpandPrims)?;
        coll.include_path(&stage, sdf::path("/W/A")?)?;
        coll.exclude_path(&stage, sdf::path("/W/A/C")?)?;

        // Read back through the membership query.
        let q = coll.compute_membership_query(&stage)?;
        assert!(q.is_path_included(&sdf::path("/W/A")?));
        assert!(!q.is_path_included(&sdf::path("/W/A/C")?));
        // And it's discoverable as an applied collection.
        assert_eq!(collections_on(&stage, &sdf::path("/W")?)?.len(), 1);
        Ok(())
    }

    #[test]
    fn include_path_drops_stale_exclude() -> Result<()> {
        let stage = scene()?;
        let coll = apply_collection(&stage, sdf::path("/W")?, "c")?;
        coll.set_include_root(&stage, true)?;
        coll.exclude_path(&stage, sdf::path("/W/A")?)?;
        assert!(!coll
            .compute_membership_query(&stage)?
            .is_path_included(&sdf::path("/W/A")?));

        // Re-including drops the exclude rather than adding a redundant include.
        coll.include_path(&stage, sdf::path("/W/A")?)?;
        assert!(coll.excludes(&stage)?.is_empty());
        assert!(coll
            .compute_membership_query(&stage)?
            .is_path_included(&sdf::path("/W/A")?));
        Ok(())
    }

    #[test]
    fn apply_authors_missing_prim() -> Result<()> {
        // The prim is never `define`d, so it has no spec on the edit target.
        // apply_collection must author an `over` rather than fail.
        let stage = Stage::builder().in_memory("anon.usda")?;
        let coll = apply_collection(&stage, sdf::path("/W")?, "c")?;
        coll.include_path(&stage, sdf::path("/W/A")?)?;
        assert_eq!(collections_on(&stage, &sdf::path("/W")?)?.len(), 1);
        assert!(coll
            .compute_membership_query(&stage)?
            .is_path_included(&sdf::path("/W/A")?));
        Ok(())
    }

    #[test]
    fn has_no_included_paths_tracks_state() -> Result<()> {
        let stage = scene()?;
        let coll = apply_collection(&stage, sdf::path("/W")?, "c")?;
        assert!(coll.has_no_included_paths(&stage)?);
        coll.include_path(&stage, sdf::path("/W/A")?)?;
        assert!(!coll.has_no_included_paths(&stage)?);
        Ok(())
    }

    #[test]
    fn exclude_path_on_empty_collection_records_target() -> Result<()> {
        // C++ parity: excluding on an empty collection authors the exclude.
        let stage = scene()?;
        let coll = apply_collection(&stage, sdf::path("/W")?, "c")?;
        coll.exclude_path(&stage, sdf::path("/W/A")?)?;
        assert_eq!(coll.excludes(&stage)?, vec![sdf::path("/W/A")?]);
        Ok(())
    }

    #[test]
    fn exclude_root_clears_include_root() -> Result<()> {
        let stage = scene()?;
        let coll = apply_collection(&stage, sdf::path("/W")?, "c")?;
        coll.set_include_root(&stage, true)?;
        coll.exclude_path(&stage, Path::abs_root())?;
        assert!(!coll.include_root(&stage)?);
        Ok(())
    }

    #[test]
    fn include_path_already_included_is_noop() -> Result<()> {
        // Including a descendant of an already-included expandPrims path
        // authors no redundant target.
        let stage = scene()?;
        let coll = apply_collection(&stage, sdf::path("/W")?, "c")?;
        coll.include_path(&stage, sdf::path("/W/A")?)?; // /W/A (+ descendants)
        coll.include_path(&stage, sdf::path("/W/A/C")?)?; // already included
        assert_eq!(coll.includes(&stage)?, vec![sdf::path("/W/A")?]); // no /W/A/C added
        Ok(())
    }

    #[test]
    fn included_paths_expand_properties() -> Result<()> {
        let stage = scene()?;
        stage
            .create_attribute(sdf::path("/W/B.size")?, "float")?
            .set(Value::Float(1.0))?;
        build_collection(
            &stage,
            "/Col",
            "c",
            ExpansionRule::ExpandPrimsAndProperties,
            false,
            &["/W/B"],
            &[],
        )?;
        let q = Collection::new(sdf::path("/Col")?, "c").compute_membership_query(&stage)?;
        let paths = compute_included_paths(&stage, &q, PrimPredicate::DEFAULT)?;
        assert!(paths.contains(&sdf::path("/W/B")?));
        assert!(paths.contains(&sdf::path("/W/B.size")?)); // property is a member
        Ok(())
    }
}
