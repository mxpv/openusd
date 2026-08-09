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
//! path-membership predicate built from those opinions, in either of the
//! two membership languages: the relationship-linking opinions resolve into
//! a rule map, and a pattern-based `membershipExpression`
//! ([`sdf::PathExpression`](crate::sdf::PathExpression)) resolves into a
//! compiled [`CollectionEvaluator`](super::CollectionEvaluator). The `mode`
//! attribute picks between them; under the default `automatic` mode a
//! non-empty rule map wins.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use anyhow::Result;

use crate::sdf::{self, FieldKey, Path, Value, Variability};
use crate::usd::{Prim, PrimPredicate, Relationship, Stage};

use super::collection_expr::{resolve_complete_membership_expression, CollectionEvaluator, CollectionSearcher};

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
const MODE: &str = "mode";

// `expansionRule` token values.
const TOK_EXPLICIT_ONLY: &str = "explicitOnly";
const TOK_EXPAND_PRIMS: &str = "expandPrims";
const TOK_EXPAND_PRIMS_AND_PROPERTIES: &str = "expandPrimsAndProperties";

// `mode` token values.
const TOK_AUTOMATIC: &str = "automatic";
const TOK_RELATIONSHIP: &str = "relationship";
const TOK_EXPRESSION: &str = "expression";

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

/// Which membership language governs a collection
/// (`collection:<name>:mode`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CollectionMode {
    /// Relationship mode when its opinions resolve to any rule, otherwise
    /// the membership expression (the default).
    #[default]
    Automatic,
    /// Only the relationship-linking opinions; the expression is ignored.
    Relationship,
    /// Only the membership expression; relationship opinions are ignored.
    Expression,
}

impl CollectionMode {
    pub fn as_token(self) -> &'static str {
        match self {
            CollectionMode::Automatic => TOK_AUTOMATIC,
            CollectionMode::Relationship => TOK_RELATIONSHIP,
            CollectionMode::Expression => TOK_EXPRESSION,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            TOK_AUTOMATIC => CollectionMode::Automatic,
            TOK_RELATIONSHIP => CollectionMode::Relationship,
            TOK_EXPRESSION => CollectionMode::Expression,
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
        self.prim.append_property(format!("{NS_COLLECTION}{}", self.name))
    }

    /// `collection:<name>:<suffix>` property path on the prim.
    fn prop(&self, suffix: &str) -> Result<Path> {
        self.prim.append_property(self.rel_name(suffix))
    }

    /// `expansionRule` — defaults to [`ExpansionRule::ExpandPrims`].
    pub fn expansion_rule(&self, stage: &Stage) -> Result<ExpansionRule> {
        Ok(
            match stage.field::<Value>(self.prop(EXPANSION_RULE)?, FieldKey::Default)? {
                Some(Value::Token(t)) => ExpansionRule::from_token(t.as_str()).unwrap_or_default(),
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
        stage.relationship(self.prop(INCLUDES)?).targets()
    }

    /// The authored `excludes` relationship targets.
    pub fn excludes(&self, stage: &Stage) -> Result<Vec<Path>> {
        stage.relationship(self.prop(EXCLUDES)?).targets()
    }

    /// The composed `membershipExpression`, if authored. Composition already
    /// substituted `%_` chains and mapped the expression across arcs; a
    /// string- or token-typed opinion parses leniently.
    pub fn membership_expression(&self, stage: &Stage) -> Result<Option<sdf::PathExpression>> {
        Ok(
            match stage.field::<Value>(self.prop(MEMBERSHIP_EXPRESSION)?, FieldKey::Default)? {
                Some(Value::PathExpression(expr)) => Some(expr),
                Some(Value::String(s)) => Some(sdf::PathExpression::parse(&s)),
                Some(Value::Token(s)) => Some(sdf::PathExpression::parse(s.as_str())),
                _ => None,
            },
        )
    }

    /// The membership language governing this collection — defaults to
    /// [`CollectionMode::Automatic`].
    pub fn mode(&self, stage: &Stage) -> Result<CollectionMode> {
        Ok(match stage.field::<Value>(self.prop(MODE)?, FieldKey::Default)? {
            Some(Value::Token(t)) => CollectionMode::from_token(t.as_str()).unwrap_or_default(),
            _ => CollectionMode::default(),
        })
    }

    /// Resolve this collection's authored opinions into a
    /// [`MembershipQuery`] (spec §15.2). Outside [`CollectionMode::Expression`],
    /// the relationship opinions build the rule map: `includeRoot` and each
    /// `includes` target take the collection's `expansionRule`, each
    /// `excludes` target is marked excluded, and an `includes` target that is
    /// itself another collection is recursively merged in (cycles broken,
    /// excludes applied last so they always win). Outside
    /// [`CollectionMode::Relationship`], the resolved membership expression
    /// compiles into the query's evaluator; at query time a non-empty rule
    /// map wins.
    pub fn compute_membership_query(&self, stage: &Stage) -> Result<MembershipQuery> {
        let mode = self.mode(stage)?;
        let mut query = MembershipQuery {
            rule_map: PathExpansionRuleMap::new(),
            top_expansion_rule: self.expansion_rule(stage)?,
            evaluator: None,
        };
        if mode != CollectionMode::Expression {
            let mut visited = HashSet::new();
            visited.insert(self.collection_path()?);
            self.build_into(stage, &mut query.rule_map, &mut visited)?;
        }
        if mode != CollectionMode::Relationship {
            let expression = resolve_complete_membership_expression(stage, self)?;
            if !expression.is_empty() {
                // TODO: report an expression that fails to compile (an
                // unknown predicate, or arguments its binder refuses); the
                // query falls back to matching nothing, as C++ does after
                // its warning.
                if let Ok(evaluator) = CollectionEvaluator::build(stage, expression) {
                    query.evaluator = Some(Rc::new(evaluator));
                }
            }
        }
        Ok(query)
    }

    /// `collection:<name>:<suffix>` relationship/property name (unanchored).
    fn rel_name(&self, suffix: &str) -> String {
        format!("{NS_COLLECTION}{}:{suffix}", self.name)
    }

    /// Create the collection's `<suffix>` relationship on the edit target as a
    /// non-custom schema property — `includes`/`excludes` are built-in schema
    /// relationships, like the `expansionRule`/`includeRoot` attributes above.
    fn schema_rel(&self, prim: &Prim, suffix: &str) -> Result<Relationship> {
        Ok(prim.create_relationship(self.rel_name(suffix))?.set_custom(false)?)
    }

    /// Set `expansionRule` (`uniform token`).
    pub fn set_expansion_rule(&self, stage: &Stage, rule: ExpansionRule) -> Result<()> {
        stage
            .create_attribute(self.prop(EXPANSION_RULE)?, "token")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::token(rule.as_token()))?;
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

    /// Set `membershipExpression` (`uniform pathExpression`).
    pub fn set_membership_expression(&self, stage: &Stage, expression: sdf::PathExpression) -> Result<()> {
        stage
            .create_attribute(self.prop(MEMBERSHIP_EXPRESSION)?, "pathExpression")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::PathExpression(expression))?;
        Ok(())
    }

    /// Set `mode` (`uniform token`).
    pub fn set_mode(&self, stage: &Stage, mode: CollectionMode) -> Result<()> {
        stage
            .create_attribute(self.prop(MODE)?, "token")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::token(mode.as_token()))?;
        Ok(())
    }

    /// Make `path` a member, minimizing edits (spec §15, mirroring C++
    /// `UsdCollectionAPI::IncludePath`): if it is already included (e.g. via
    /// an ancestor), do nothing; including `</>` sets `includeRoot`; an
    /// excluded `path` is first un-excluded; and a new `includes` target is
    /// added only if `path` would still not be a member.
    ///
    /// Un-excluding compares `path` against authored targets by exact path
    /// equality, which holds for the absolute paths authored here; it would
    /// miss a target that composes to `path` through a different authored form
    /// (e.g. remapped across a reference).
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
            self.schema_rel(&prim, EXCLUDES)?.remove_target(&path)?;
            if self.compute_membership_query(stage)?.is_path_included(&path) {
                return Ok(()); // dropping the exclude was enough
            }
        }
        self.schema_rel(&prim, INCLUDES)?.add_target(path)?;
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
            self.schema_rel(&prim, INCLUDES)?.remove_target(&path)?;
            let query = self.compute_membership_query(stage)?;
            if !query.is_empty() && !query.is_path_included(&path) {
                return Ok(()); // dropping the include was enough
            }
        }
        self.schema_rel(&prim, EXCLUDES)?.add_target(path)?;
        Ok(())
    }

    /// `true` when the collection includes nothing (mirroring C++
    /// `UsdCollectionAPI::HasNoIncludedPaths`): no `includes`, `includeRoot`
    /// off, and either an `excludes` opinion exists or there is no membership
    /// expression.
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
    // The instance name is a single token (`:` is the namespace delimiter), so
    // reject anything that isn't a valid identifier before it produces an
    // ambiguous `collection:<name>:...` namespace.
    if !Path::is_valid_identifier(&name) {
        anyhow::bail!("invalid collection name {name:?}: must be a valid identifier");
    }
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
    for schema in stage.prim(prim.clone()).api_schemas()? {
        if let Some(name) = instance_name(&schema) {
            out.push(Collection::new(prim.clone(), name));
        }
    }
    Ok(out)
}

/// Decode the instance name from a `CollectionAPI:<name>` apiSchema entry.
/// Rejects malformed entries (`CollectionAPI:`, `CollectionAPI:a:b`) so a
/// handle is only built for a valid single-token instance name.
fn instance_name(api_schema: &str) -> Option<String> {
    let rest = api_schema.strip_prefix(API_COLLECTION)?.strip_prefix(':')?;
    Path::is_valid_identifier(rest).then(|| rest.to_string())
}

/// If `path` is a collection identity path `<prim>.collection:<name>`,
/// return `(prim, name)`. Used to detect when an `includes` target points
/// at another collection (chained collections). A deeper property path like
/// `collection:<name>:includes` is *not* a collection identity and yields
/// `None`.
pub fn is_collection_api_path(path: &Path) -> Option<(Path, String)> {
    let (prim, property) = path.split_property()?;
    let rest = property.strip_prefix(NS_COLLECTION)?;
    Path::is_valid_identifier(rest).then(|| (prim, rest.to_string()))
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
    if !query.uses_path_expansion_rule_map() {
        return compute_included_by_expression(stage, query, predicate);
    }
    let mut seen = HashSet::new();
    let mut err: Result<()> = Ok(());
    let collect_props = query
        .rule_map
        .values()
        .any(|r| *r == PathRule::ExpandPrimsAndProperties);

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
    // aren't reached by the prim walk above. Like C++ `_ComputeIncludedImpl`,
    // these are emitted when the property exists (C++ checks the same via
    // `GetPropertyAtPath`), regardless of whether their owning prim satisfies
    // `predicate` — only properties reached by prim expansion are gated by it.
    //
    // Sort first: `rule_map` is a `HashMap`, so iterating it directly would
    // yield these tail entries in a non-deterministic order.
    let mut props: Vec<&Path> = query.rule_map.keys().filter(|p| p.is_property_path()).collect();
    props.sort();
    for path in props {
        if query.is_path_included(path) && stage.has_spec(path)? && seen.insert(path.clone()) {
            out.push(path.clone());
        }
    }
    Ok(out)
}

/// Enumerate an expression-mode query by stage traversal, with subtree
/// pruning driven by result constancy (C++
/// `UsdComputeIncludedObjectsFromCollection`'s expression arm).
fn compute_included_by_expression(
    stage: &Stage,
    query: &MembershipQuery,
    predicate: PrimPredicate,
) -> Result<Vec<Path>> {
    let Some(evaluator) = query.expression_evaluator() else {
        return Ok(Vec::new());
    };
    let search_properties = query.top_expansion_rule() == ExpansionRule::ExpandPrimsAndProperties;
    // The searcher's depth-first ordering contract tolerates only
    // whole-subtree skips, so the walk runs under the predicate's inherited
    // projection; when the projection is the predicate itself the walk is
    // unchanged, and otherwise the extra prims feed the searcher without
    // becoming candidates.
    //
    // TODO: Stage::traverse can neither skip a declined prim's subtree (C++
    // UsdPrimRange prunes non-matching prims wholesale) nor let the visitor
    // prune a subtree it has answered (C++ UsdPrimRange::PruneChildren).
    // Generalizing traverse that way would collapse the projected walk and
    // the per-prim `prim_matches` re-test into the C++ loop shape and let
    // constant-answered subtrees go unvisited; today the searcher's memo
    // answers their visits in constant time instead.
    let walk = predicate.inherited_projection();
    let clean = walk == predicate;
    let mut searcher = evaluator.incremental_searcher();
    let mut out = Vec::new();
    let mut err: Result<()> = Ok(());
    stage.traverse(walk, |prim| {
        if err.is_err() {
            return;
        }
        let result = match searcher.next(prim) {
            Ok(result) => result,
            Err(e) => {
                err = Err(e);
                return;
            }
        };
        // A false answer leaves nothing to emit: a constant false covers
        // the properties too, and a varying false leaves only the
        // property-by-property search.
        if !result.value && (!search_properties || result.constant) {
            return;
        }
        let admitted = clean
            || match stage.prim_matches(prim, predicate) {
                Ok(admitted) => admitted,
                Err(e) => {
                    err = Err(e);
                    return;
                }
            };
        if !admitted {
            return;
        }
        if result.value {
            out.push(prim.clone());
        }
        if search_properties {
            // Mirroring C++: a constant-true prim bulk-includes its
            // properties, a varying-true prim's properties are not searched,
            // and a varying-false prim's properties are tested one by one.
            let push = if result.value && result.constant {
                Some(push_all_properties(stage, prim, &mut out))
            } else if !result.value {
                Some(push_matching_properties(stage, &mut searcher, prim, &mut out))
            } else {
                None
            };
            if let Some(Err(e)) = push {
                err = Err(e);
            }
        }
    })?;
    err?;
    Ok(out)
}

fn push_all_properties(stage: &Stage, prim: &Path, out: &mut Vec<Path>) -> Result<()> {
    for name in stage.prim(prim.clone()).property_names()? {
        out.push(prim.append_property(&name)?);
    }
    Ok(())
}

/// Tests each of `prim`'s properties one by one through the searcher —
/// property paths are valid depth-first successors of their prim.
fn push_matching_properties(
    stage: &Stage,
    searcher: &mut CollectionSearcher<'_>,
    prim: &Path,
    out: &mut Vec<Path>,
) -> Result<()> {
    for name in stage.prim(prim.clone()).property_names()? {
        let prop = prim.append_property(&name)?;
        if searcher.next(&prop)?.value {
            out.push(prop);
        }
    }
    Ok(())
}

fn push_member_properties(
    stage: &Stage,
    prim: &Path,
    prim_rule: PathRule,
    query: &MembershipQuery,
    seen: &mut HashSet<Path>,
    out: &mut Vec<Path>,
) -> Result<()> {
    for name in stage.prim(prim.clone()).property_names()? {
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

/// A resolved membership predicate for a collection. Build it once (see
/// `compute_membership_query`) and query [`is_path_included`] cheaply; it
/// clones freely so consumers can cache one per collection path.
///
/// The query carries both membership languages: the relationship opinions'
/// rule map and, for expression-capable modes, the compiled membership
/// expression. A non-empty rule map answers; otherwise the expression does
/// (C++ `UsdCollectionMembershipQuery`). Two queries carrying evaluators
/// never compare equal — evaluators run code — only their absence does.
///
/// The two sides snapshot differently (matching C++): the rule map is fixed
/// at build time, while the evaluator holds a stage handle and answers its
/// predicates (`isa`, `hasAPI`, `variant`, ...) against the stage's state at
/// each query, so later edits shift an expression query's answers.
///
/// [`is_path_included`]: MembershipQuery::is_path_included
#[derive(Debug, Clone, Default)]
pub struct MembershipQuery {
    rule_map: PathExpansionRuleMap,
    top_expansion_rule: ExpansionRule,
    evaluator: Option<Rc<CollectionEvaluator>>,
}

impl PartialEq for MembershipQuery {
    /// Deliberately non-reflexive for expression-carrying queries: an
    /// evaluator runs code, so two are never known equivalent — not even a
    /// query and its clone (C++ `UsdCollectionMembershipQuery` equality).
    fn eq(&self, other: &Self) -> bool {
        self.rule_map == other.rule_map
            && self.top_expansion_rule == other.top_expansion_rule
            && self.evaluator.is_none()
            && other.evaluator.is_none()
    }
}

impl MembershipQuery {
    /// Build a relationship-mode query from a resolved rule map.
    pub fn new(rule_map: PathExpansionRuleMap) -> Self {
        MembershipQuery {
            rule_map,
            top_expansion_rule: ExpansionRule::default(),
            evaluator: None,
        }
    }

    /// The resolved per-path rule map.
    pub fn rule_map(&self) -> &PathExpansionRuleMap {
        &self.rule_map
    }

    /// The collection's own `expansionRule`, which expression-mode
    /// enumeration consults for property expansion.
    pub fn top_expansion_rule(&self) -> ExpansionRule {
        self.top_expansion_rule
    }

    /// The compiled membership expression, when one governs this query.
    pub fn expression_evaluator(&self) -> Option<&CollectionEvaluator> {
        self.evaluator.as_deref()
    }

    /// Whether membership is answered by the rule map rather than the
    /// expression — true whenever the map has any opinion (C++
    /// `UsesPathExpansionRuleMap`).
    pub fn uses_path_expansion_rule_map(&self) -> bool {
        !self.rule_map.is_empty()
    }

    /// `true` when the query has no opinions at all (includes nothing).
    pub fn is_empty(&self) -> bool {
        self.rule_map.is_empty() && self.evaluator.is_none()
    }

    /// Whether `path` is a member. With rule-map opinions, walks from `path`
    /// toward the root and takes the **closest ancestor with an opinion**
    /// (spec §15.2):
    ///
    /// - `Exclude` → not a member;
    /// - `ExplicitOnly` → member only if the opinion is on `path` itself;
    /// - `ExpandPrims` → prim members always; a property only if it is itself
    ///   the explicitly listed path;
    /// - `ExpandPrimsAndProperties` → member.
    ///
    /// Paths with no ancestor opinion are not members. Without rule-map
    /// opinions, the membership expression answers.
    pub fn is_path_included(&self, path: &Path) -> bool {
        if self.uses_path_expansion_rule_map() {
            let (rule, on_self) = self.closest_rule(path);
            return rule_includes(rule, on_self, path.is_property_path());
        }
        match &self.evaluator {
            Some(evaluator) => evaluator.match_path(path).value,
            None => false,
        }
    }

    /// Fast top-down variant for stage traversal: given the rule that applies
    /// to `path`'s parent, decide inclusion and the rule to propagate to
    /// `path`'s own children — without re-walking ancestors. An opinion
    /// authored directly on `path` overrides the inherited `parent_rule`. An
    /// expression-mode query answers through the expression and passes the
    /// parent rule through.
    pub fn is_path_included_below(&self, path: &Path, parent_rule: PathRule) -> (bool, PathRule) {
        if !self.uses_path_expansion_rule_map() {
            return (self.is_path_included(path), parent_rule);
        }
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
            .set(Value::Token(ExpansionRule::ExplicitOnly.as_token().into()))?;
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
            "/W",
            "/W/A",
            "/W/A/C",
            "/W/B",
            "/W/B/D",
            "/W/B.size",
            "/W/C",
            "/W/C/D",
            "/W/D",
            "/W.x",
            "/Other",
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
            .set(Value::token(rule.as_token()))?;
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
    fn apply_rejects_bad_name() -> Result<()> {
        let stage = scene()?;
        assert!(apply_collection(&stage, sdf::path("/W")?, "").is_err()); // empty
        assert!(apply_collection(&stage, sdf::path("/W")?, "a:b").is_err()); // extra ':'
        assert!(apply_collection(&stage, sdf::path("/W")?, "render").is_ok());
        Ok(())
    }

    #[test]
    fn skips_malformed_schemas() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage
            .define_prim(sdf::path("/W")?)?
            .set_type_name("Scope")?
            .add_applied_schema("CollectionAPI:render")?
            .add_applied_schema("CollectionAPI:")? // empty instance name
            .add_applied_schema("CollectionAPI:a:b")?; // extra ':'
        let names: Vec<String> = collections_on(&stage, &sdf::path("/W")?)?
            .into_iter()
            .map(|c| c.name().to_string())
            .collect();
        assert_eq!(names, vec!["render".to_string()]);
        Ok(())
    }

    #[test]
    fn explicit_props_sorted() -> Result<()> {
        // Explicit property targets come from a HashMap; the result must be
        // sorted so it is deterministic across runs.
        let stage = scene()?;
        for p in ["/W/B.a", "/W/B.c", "/W/B.b"] {
            stage.create_attribute(sdf::path(p)?, "float")?.set(Value::Float(0.0))?;
        }
        build_collection(
            &stage,
            "/Col",
            "c",
            ExpansionRule::ExplicitOnly,
            false,
            &["/W/B.c", "/W/B.a", "/W/B.b"],
            &[],
        )?;
        let q = Collection::new(sdf::path("/Col")?, "c").compute_membership_query(&stage)?;
        let paths = compute_included_paths(&stage, &q, PrimPredicate::DEFAULT)?;
        assert_eq!(
            paths,
            vec![sdf::path("/W/B.a")?, sdf::path("/W/B.b")?, sdf::path("/W/B.c")?]
        );
        Ok(())
    }

    #[test]
    fn authored_relationships_not_custom() -> Result<()> {
        // includes/excludes are schema relationships, so authoring them via
        // include_path/exclude_path must mark them non-custom.
        let stage = scene()?;
        let coll = apply_collection(&stage, sdf::path("/W")?, "c")?;
        coll.include_path(&stage, sdf::path("/W")?)?;
        coll.exclude_path(&stage, sdf::path("/W/A")?)?;
        for suffix in [INCLUDES, EXCLUDES] {
            assert_eq!(
                stage.field::<Value>(coll.prop(suffix)?, FieldKey::Custom)?,
                Some(Value::Bool(false)),
                "collection:c:{suffix} should be authored non-custom"
            );
        }
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

    #[test]
    fn included_paths_skip_missing_property() -> Result<()> {
        // An explicit property target is emitted only when the property
        // exists, matching C++ `_ComputeIncludedImpl` / `GetPropertyAtPath`.
        let stage = scene()?;
        stage
            .create_attribute(sdf::path("/W/B.size")?, "float")?
            .set(Value::Float(1.0))?;
        build_collection(
            &stage,
            "/Col",
            "c",
            ExpansionRule::ExpandPrims,
            false,
            &["/W/B.size", "/W/B.ghost"],
            &[],
        )?;
        let q = Collection::new(sdf::path("/Col")?, "c").compute_membership_query(&stage)?;
        let paths = compute_included_paths(&stage, &q, PrimPredicate::DEFAULT)?;
        assert!(paths.contains(&sdf::path("/W/B.size")?)); // exists → emitted
        assert!(!paths.contains(&sdf::path("/W/B.ghost")?)); // unauthored → skipped
        Ok(())
    }

    /// Authors an expression-mode collection named `name` on `/Col`.
    fn build_expression(stage: &Stage, name: &str, expression: &str) -> Result<Collection> {
        author_collection(stage, "/Col", name)?;
        let coll = Collection::new(sdf::path("/Col")?, name);
        coll.set_membership_expression(stage, sdf::PathExpression::parse(expression))?;
        Ok(coll)
    }

    #[test]
    fn mode_round_trips() {
        for mode in [
            CollectionMode::Automatic,
            CollectionMode::Relationship,
            CollectionMode::Expression,
        ] {
            assert_eq!(CollectionMode::from_token(mode.as_token()), Some(mode));
        }
        assert_eq!(CollectionMode::from_token("bogus"), None);
    }

    #[test]
    fn expression_membership() -> Result<()> {
        let stage = scene()?;
        let coll = build_expression(&stage, "e", "/W/A//")?;
        let q = coll.compute_membership_query(&stage)?;
        assert!(!q.uses_path_expansion_rule_map());
        assert!(!q.is_empty());
        assert!(q.is_path_included(&sdf::path("/W/A")?));
        assert!(q.is_path_included(&sdf::path("/W/A/C")?));
        assert!(!q.is_path_included(&sdf::path("/W/B")?));
        // A path with no composed object is a constant non-member.
        assert!(!q.is_path_included(&sdf::path("/W/A/ghost")?));
        Ok(())
    }

    #[test]
    fn automatic_rule_map_wins() -> Result<()> {
        let stage = scene()?;
        build_collection(&stage, "/Col", "c", ExpansionRule::ExpandPrims, false, &["/W/B"], &[])?;
        let coll = Collection::new(sdf::path("/Col")?, "c");
        coll.set_membership_expression(&stage, sdf::PathExpression::parse("/W/A//"))?;

        // Automatic mode: the non-empty rule map answers, not the expression.
        let q = coll.compute_membership_query(&stage)?;
        assert!(q.uses_path_expansion_rule_map());
        assert!(q.is_path_included(&sdf::path("/W/B")?));
        assert!(!q.is_path_included(&sdf::path("/W/A")?));

        // Expression mode ignores the includes outright.
        coll.set_mode(&stage, CollectionMode::Expression)?;
        let q = coll.compute_membership_query(&stage)?;
        assert!(!q.uses_path_expansion_rule_map());
        assert!(q.is_path_included(&sdf::path("/W/A")?));
        assert!(!q.is_path_included(&sdf::path("/W/B")?));
        Ok(())
    }

    #[test]
    fn mode_relationship_ignores_expr() -> Result<()> {
        let stage = scene()?;
        let coll = build_expression(&stage, "e", "/W/A//")?;
        coll.set_mode(&stage, CollectionMode::Relationship)?;
        let q = coll.compute_membership_query(&stage)?;
        assert!(q.is_empty());
        assert!(!q.is_path_included(&sdf::path("/W/A")?));
        Ok(())
    }

    #[test]
    fn expression_included_paths() -> Result<()> {
        let stage = scene()?;
        let coll = build_expression(&stage, "e", "/W/A//")?;
        let q = coll.compute_membership_query(&stage)?;
        let mut paths = compute_included_paths(&stage, &q, PrimPredicate::DEFAULT)?;
        paths.sort();
        assert_eq!(paths, vec![sdf::path("/W/A")?, sdf::path("/W/A/C")?]);
        Ok(())
    }

    #[test]
    fn expression_included_properties() -> Result<()> {
        let stage = scene()?;
        stage
            .create_attribute(sdf::path("/W/A.size")?, "float")?
            .set(Value::Float(1.0))?;
        stage
            .create_attribute(sdf::path("/W/B.size")?, "float")?
            .set(Value::Float(2.0))?;

        // A property pattern matches prims varying-false, so each prim's
        // properties are tested individually under expandPrimsAndProperties.
        let coll = build_expression(&stage, "e", "//A.size")?;
        coll.set_expansion_rule(&stage, ExpansionRule::ExpandPrimsAndProperties)?;
        let q = coll.compute_membership_query(&stage)?;
        let paths = compute_included_paths(&stage, &q, PrimPredicate::DEFAULT)?;
        assert!(paths.contains(&sdf::path("/W/A.size")?));
        assert!(!paths.contains(&sdf::path("/W/B.size")?));

        // A constant-true prim bulk-includes its properties.
        let bulk = build_expression(&stage, "b", "/W/B//")?;
        bulk.set_expansion_rule(&stage, ExpansionRule::ExpandPrimsAndProperties)?;
        let q = bulk.compute_membership_query(&stage)?;
        let paths = compute_included_paths(&stage, &q, PrimPredicate::DEFAULT)?;
        assert!(paths.contains(&sdf::path("/W/B")?));
        assert!(paths.contains(&sdf::path("/W/B.size")?));
        Ok(())
    }

    #[test]
    fn expression_resolves_references() -> Result<()> {
        let stage = scene()?;
        let big = build_expression(&stage, "big", "/W/A// %:small")?;
        build_expression(&stage, "small", "/W/B//")?;

        let resolved = resolve_complete_membership_expression(&stage, &big)?;
        assert_eq!(resolved.to_string(), "/W/A// /W/B//");

        let q = big.compute_membership_query(&stage)?;
        assert!(q.is_path_included(&sdf::path("/W/A")?));
        assert!(q.is_path_included(&sdf::path("/W/B")?));
        Ok(())
    }

    #[test]
    fn expression_reference_cycle() -> Result<()> {
        let stage = scene()?;
        let a = build_expression(&stage, "a", "/W/A// %:b")?;
        build_expression(&stage, "b", "/W/B// %/Col:a")?;

        // The circular hop contributes nothing; both direct patterns stand.
        let resolved = resolve_complete_membership_expression(&stage, &a)?;
        assert_eq!(resolved.to_string(), "/W/A// /W/B//");
        Ok(())
    }

    #[test]
    fn expression_unknown_reference() -> Result<()> {
        let stage = scene()?;
        let coll = build_expression(&stage, "e", "/W/A// %:missing")?;
        let resolved = resolve_complete_membership_expression(&stage, &coll)?;
        assert_eq!(resolved.to_string(), "/W/A//");
        Ok(())
    }

    #[test]
    fn expression_reference_diamond() -> Result<()> {
        let stage = scene()?;
        let top = build_expression(&stage, "top", "%:x %:y")?;
        build_expression(&stage, "x", "%:shared")?;
        build_expression(&stage, "y", "%:shared /W/A//")?;
        build_expression(&stage, "shared", "/W/B//")?;

        // `shared` resolves once and replays from the memo on the second
        // branch.
        let resolved = resolve_complete_membership_expression(&stage, &top)?;
        assert_eq!(resolved.to_string(), "/W/B// (/W/B// /W/A//)");
        Ok(())
    }

    #[test]
    fn expression_cycle_not_memoized() -> Result<()> {
        let stage = scene()?;
        let top = build_expression(&stage, "top", "%:a %:b")?;
        build_expression(&stage, "a", "%:b /W/A//")?;
        build_expression(&stage, "b", "%:a /W/B//")?;

        // Each branch drops only its own back-edge: the chain-dependent
        // placeholder must not replay from the memo, so `b` still expands
        // fully under the second branch.
        let resolved = resolve_complete_membership_expression(&stage, &top)?;
        assert_eq!(resolved.to_string(), "/W/B// /W/A// (/W/A// /W/B//)");
        Ok(())
    }

    #[test]
    fn predicate_unknown_keyword() -> Result<()> {
        let stage = scene()?;
        stage
            .define_prim(sdf::path("/W/M")?)?
            .set_type_name("Scope")?
            .set_kind("component")?;

        // A stray keyword refuses to bind, so the expression fails to
        // compile and the query matches nothing.
        let coll = build_expression(&stage, "k", "/W//{kind(component, bogus=true)}")?;
        let q = coll.compute_membership_query(&stage)?;
        assert!(!q.is_path_included(&sdf::path("/W/M")?));

        let ok = build_expression(&stage, "k2", "/W//{kind(component, strict=true)}")?;
        let q = ok.compute_membership_query(&stage)?;
        assert!(q.is_path_included(&sdf::path("/W/M")?));
        Ok(())
    }

    #[test]
    fn expression_predicates() -> Result<()> {
        let stage = scene()?;
        stage.override_prim(sdf::path("/W/O")?)?;

        // Every scene prim is a def; the over is not defined.
        let defined = build_expression(&stage, "d", "/W//{specifier:def}")?;
        let q = defined.compute_membership_query(&stage)?;
        assert!(q.is_path_included(&sdf::path("/W/A")?));
        assert!(!q.is_path_included(&sdf::path("/W/O")?));

        let overs = build_expression(&stage, "o", "/W//{specifier:over}")?;
        let q = overs.compute_membership_query(&stage)?;
        assert!(q.is_path_included(&sdf::path("/W/O")?));
        assert!(!q.is_path_included(&sdf::path("/W/A")?));
        Ok(())
    }

    #[test]
    fn expression_query_equality() -> Result<()> {
        let stage = scene()?;
        let coll = build_expression(&stage, "e", "/W/A//")?;
        let a = coll.compute_membership_query(&stage)?;
        let b = coll.compute_membership_query(&stage)?;
        // Expression-carrying queries never compare equal — not even a query
        // and its own clone; evaluators run code.
        assert_ne!(a, b);
        assert_ne!(a.clone(), a.clone());
        Ok(())
    }
}
