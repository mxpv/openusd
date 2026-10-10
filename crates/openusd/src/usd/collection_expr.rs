//! Expression-mode collection machinery: the predicate library membership
//! expressions evaluate against (C++ `UsdGetCollectionPredicateLibrary`),
//! the compiled evaluator a [`MembershipQuery`](super::MembershipQuery)
//! carries, and complete-expression resolution
//! (C++ `UsdCollectionAPI::ResolveCompleteMembershipExpression`).

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

use crate::Result;
use crate::sdf::path_expr::{
    FnArg, GlobPattern, IncrementalSearcher, PathExpressionEval, PredResult, PredicateArg, PredicateLibrary,
};
use crate::sdf::{self, Path};
use crate::usd::{Prim, SchemaRegistry, Stage};

use super::{CollectionAPI, SchemaBase};

/// One stage object a membership-expression predicate evaluates against —
/// a prim or a property (C++ `UsdObject`). Predicates that only make sense
/// on prims answer through the *closest prim*: the object itself, or a
/// property's owner.
pub struct CollectionObject {
    stage: Stage,
    path: Path,
}

impl CollectionObject {
    /// Whether the object is a prim (rather than a property).
    fn is_prim(&self) -> bool {
        !self.path.is_property_path()
    }

    /// The object's prim, or the owning prim of a property.
    fn closest_prim(&self) -> Prim {
        Prim::new(&self.stage, self.path.prim_path())
    }
}

/// A membership expression compiled against a stage, answering per-path
/// membership with subtree constancy (C++
/// `UsdObjectCollectionExpressionEvaluator`).
pub struct CollectionEvaluator {
    stage: Stage,
    expression: sdf::PathExpression,
    eval: PathExpressionEval<CollectionObject>,
}

impl fmt::Debug for CollectionEvaluator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The compiled programs are opaque; the expression identifies the
        // evaluator.
        f.debug_struct("CollectionEvaluator")
            .field("expression", &self.expression.to_string())
            .finish()
    }
}

impl CollectionEvaluator {
    /// Compiles `expression` — complete, per
    /// [`resolve_complete_membership_expression`] — against the collection
    /// predicate library.
    pub(super) fn build(stage: &Stage, expression: sdf::PathExpression) -> Result<Self> {
        let eval = PathExpressionEval::build(&expression, &predicate_library(stage.schema_registry()))?;
        Ok(CollectionEvaluator {
            stage: stage.clone(),
            expression,
            eval,
        })
    }

    /// The resolved expression this evaluator answers for.
    pub fn expression(&self) -> &sdf::PathExpression {
        &self.expression
    }

    /// Whether `path` is in the expression's set. A path with no composed
    /// object on the stage is a constant non-member.
    pub fn match_path(&self, path: &Path) -> PredResult {
        if !self.stage.has_spec(path).unwrap_or(false) {
            return PredResult::constant(false);
        }
        self.eval.match_path(path, &self.domain())
    }

    /// A fresh [`CollectionSearcher`] borrowing this evaluator, for
    /// answering a whole depth-first stage traversal incrementally.
    pub fn incremental_searcher(&self) -> CollectionSearcher<'_> {
        CollectionSearcher {
            evaluator: self,
            searcher: self.eval.incremental_searcher(Box::new(self.domain())),
        }
    }

    /// The domain closure mapping a path to the [`CollectionObject`] its
    /// predicates evaluate against.
    fn domain(&self) -> impl Fn(&Path) -> CollectionObject {
        move |p: &Path| CollectionObject {
            stage: self.stage.clone(),
            path: p.clone(),
        }
    }
}

/// A stateful depth-first searcher over a collection expression, created by
/// [`CollectionEvaluator::incremental_searcher`] — the incremental
/// counterpart of [`CollectionEvaluator::match_path`] for stage traversals
/// (C++ `UsdObjectCollectionExpressionEvaluator::IncrementalSearcher`).
pub struct CollectionSearcher<'a> {
    evaluator: &'a CollectionEvaluator,
    searcher: IncrementalSearcher<'a, CollectionObject, CollectionDomain<'a>>,
}

/// The boxed domain closure a [`CollectionSearcher`] carries.
type CollectionDomain<'a> = Box<dyn Fn(&Path) -> CollectionObject + 'a>;

impl CollectionSearcher<'_> {
    /// Advances the search to `path` — the next step of a depth-first
    /// traversal, per [`IncrementalSearcher::next`]'s ordering contract —
    /// and answers whether it is in the expression's set. A path with no
    /// composed object on the stage is a constant non-member; it counts as
    /// skipped rather than visited, so the traversal must not descend
    /// below it.
    pub fn next(&mut self, path: &Path) -> Result<PredResult> {
        if !self.evaluator.stage.has_spec(path)? {
            return Ok(PredResult::constant(false));
        }
        Ok(self.searcher.next(path))
    }
}

/// Resolves a collection's composed `membershipExpression` into a complete
/// expression: every `%path:name` / `%:name` reference is expanded inline
/// into the referenced collection's own resolved expression, recursively
/// (C++ `ResolveCompleteMembershipExpression`).
///
/// A reference that cannot resolve — an unknown collection, an empty name, a
/// surviving weaker reference, or a circular chain — contributes the empty
/// expression. The visited set is scoped to the reference *chain* (entries
/// are dropped on the way back out), so the same collection may appear on
/// sibling branches; only a true cycle dies. A collection referenced from
/// several branches resolves once and replays from a memo.
// TODO: report the dropped references (unknown collection, cycle); C++ warns
// through `TF_WARN` and flags circular dependencies. This crate has no
// diagnostic channel for a query build to carry the report out through.
pub fn resolve_complete_membership_expression(collection: &CollectionAPI) -> Result<sdf::PathExpression> {
    let mut state = ResolveState {
        visited: HashSet::from([(collection.path().clone(), collection.name().to_string())]),
        memo: HashMap::new(),
    };
    Ok(resolve_impl(collection, &mut state)?.expression)
}

/// The bookkeeping one complete-expression resolution carries: the active
/// reference chain for cycle detection, and finished subtree expressions
/// keyed by (prim, collection name) so a diamond of references resolves each
/// collection once.
struct ResolveState {
    visited: HashSet<(Path, String)>,
    memo: HashMap<(Path, String), sdf::PathExpression>,
}

/// One resolved subtree. `cacheable` is `false` when a circular reference was
/// hit anywhere within: the cycle's placeholder stands in for whatever is
/// above it on the active chain, so the result is chain-dependent and must
/// not enter the memo.
struct Resolved {
    expression: sdf::PathExpression,
    cacheable: bool,
}

fn resolve_impl(collection: &CollectionAPI, state: &mut ResolveState) -> Result<Resolved> {
    let Some(expression) = super::collection::membership_expression(collection)? else {
        return Ok(Resolved {
            expression: sdf::PathExpression::nothing(),
            cacheable: true,
        });
    };
    // Composition already anchored and namespace-mapped a typed expression;
    // anchoring again covers the lenient string-typed opinions.
    let expression = expression.make_absolute(collection.path());
    let mut cacheable = true;
    let mut error = None;
    let expression = expression.resolve_references(&mut |reference| {
        if error.is_some() || reference.name.is_empty() || reference.is_weaker() {
            return sdf::PathExpression::nothing();
        }
        let prim = if reference.path.is_empty() {
            collection.path().clone()
        } else {
            reference.path.clone()
        };
        let key = (prim.clone(), reference.name.clone());
        if let Some(memoized) = state.memo.get(&key) {
            return memoized.clone();
        }
        if !state.visited.insert(key.clone()) {
            cacheable = false;
            return sdf::PathExpression::nothing();
        }
        // A referenced collection resolves on the referring one's stage.
        let nested = CollectionAPI::from_prim_unchecked(Prim::new(collection.stage(), prim), reference.name.as_str());
        let resolved = match resolve_impl(&nested, state) {
            Ok(resolved) => resolved,
            Err(e) => {
                error = Some(e);
                return sdf::PathExpression::nothing();
            }
        };
        state.visited.remove(&key);
        if resolved.cacheable {
            state.memo.insert(key, resolved.expression.clone());
        }
        cacheable &= resolved.cacheable;
        resolved.expression
    });
    match error {
        Some(error) => Err(error),
        None => Ok(Resolved { expression, cacheable }),
    }
}

/// The predicate functions membership expressions may call (C++
/// `UsdGetCollectionPredicateLibrary`); each predicate's doc note in the
/// binder body names its semantics and constancy. `registry` supplies the
/// kinds the `kind` predicate knows.
fn predicate_library(registry: &Arc<SchemaRegistry>) -> PredicateLibrary<CollectionObject> {
    let registry = registry.clone();
    PredicateLibrary::new()
        // abstract(isAbstract=true): the closest prim's abstractness. An
        // abstract prim's subtree stays abstract, so a `true` answer is
        // constant; a non-abstract prim may root abstract descendants.
        .define("abstract", |args| {
            let wanted = flag_argument(args, "isAbstract")?;
            Some(predicate(move |obj| {
                let is_abstract = obj.closest_prim().is_abstract().unwrap_or(false);
                PredResult {
                    value: is_abstract == wanted,
                    constant: is_abstract || !obj.is_prim(),
                }
            }))
        })
        // defined(isDefined=true): the closest prim's definedness. An
        // undefined prim's subtree stays undefined (every ancestor must
        // define), so a `false` is constant.
        .define("defined", |args| {
            let wanted = flag_argument(args, "isDefined")?;
            Some(predicate(move |obj| {
                let is_defined = obj.closest_prim().is_defined().unwrap_or(false);
                PredResult {
                    value: is_defined == wanted,
                    constant: !is_defined || !obj.is_prim(),
                }
            }))
        })
        // model(isModel=true): model-hierarchy membership; non-prims are
        // plain false. A prim's answer varies over its subtree either way:
        // an instance below a non-model has proxies its prototype
        // classifies, under a root that is a group.
        .define("model", |args| {
            let wanted = flag_argument(args, "isModel")?;
            Some(predicate(move |obj| {
                if !obj.is_prim() {
                    return PredResult::constant(false);
                }
                let is_model = obj.closest_prim().is_model().unwrap_or(false);
                PredResult::varying(is_model == wanted)
            }))
        })
        // group(isGroup=true): like `model`, for groups.
        .define("group", |args| {
            let wanted = flag_argument(args, "isGroup")?;
            Some(predicate(move |obj| {
                if !obj.is_prim() {
                    return PredResult::constant(false);
                }
                let is_group = obj.closest_prim().is_group().unwrap_or(false);
                PredResult::varying(is_group == wanted)
            }))
        })
        // kind(k1, ..., kN, strict=false): the prim's kind is one of the
        // named kinds — exactly under `strict`, else as the kind registry
        // derives it. A named kind the registry does not know is dropped, and
        // a call naming no known kind refuses to bind. The prim's own kind is
        // what is read, wherever the prim sits in the model hierarchy.
        .define("kind", move |args| {
            if !keywords_within(args, &["strict"]) {
                return None;
            }
            let strict = strict_argument(args)?;
            let kinds = registry.kinds();
            let mut wanted = string_arguments(args)?;
            wanted.retain(|kind| kinds.has_kind(kind));
            if wanted.is_empty() {
                return None;
            }
            // The registry is fixed, so every kind the call accepts is known
            // when it binds.
            let accepted: Vec<String> = if strict {
                wanted
            } else {
                kinds
                    .all_kinds()
                    .into_iter()
                    .filter(|kind| wanted.iter().any(|wanted| kinds.is_a(kind, wanted)))
                    .map(str::to_owned)
                    .collect()
            };
            Some(predicate(move |obj| {
                if !obj.is_prim() {
                    return PredResult::constant(false);
                }
                let Ok(Some(kind)) = obj.closest_prim().kind() else {
                    return PredResult::varying(false);
                };
                PredResult::varying(accepted.iter().any(|accepted| kind == accepted.as_str()))
            }))
        })
        // specifier(s1, ..., sN): the prim's specifier is one of `over`,
        // `class`, `def`; anything else refuses to bind.
        .define("specifier", |args| {
            let names = string_arguments(args)?;
            if args.len() != names.len()
                || names.is_empty()
                || !names.iter().all(|n| matches!(n.as_str(), "over" | "class" | "def"))
            {
                return None;
            }
            Some(predicate(move |obj| {
                if !obj.is_prim() {
                    return PredResult::constant(false);
                }
                let Ok(Some(specifier)) = obj.closest_prim().specifier() else {
                    return PredResult::varying(false);
                };
                let token = match specifier {
                    sdf::Specifier::Def => "def",
                    sdf::Specifier::Over => "over",
                    sdf::Specifier::Class => "class",
                };
                PredResult::varying(names.iter().any(|n| n == token))
            }))
        })
        // isa(schema1, ..., schemaN, strict=false): the prim's typed schema
        // is one of the named schemas — exactly under `strict`, else any
        // subtype (through the stage's schema registry).
        .define("isa", |args| {
            if !keywords_within(args, &["strict"]) {
                return None;
            }
            let strict = strict_argument(args)?;
            let schemas = string_arguments(args)?;
            if schemas.is_empty() {
                return None;
            }
            Some(predicate(move |obj| {
                if !obj.is_prim() {
                    return PredResult::constant(false);
                }
                let prim = obj.closest_prim();
                let value = schemas.iter().any(|schema| {
                    if strict {
                        prim.schema_type().ok().flatten().is_some_and(|t| t.as_str() == schema)
                    } else {
                        prim.is_a(schema.as_str()).unwrap_or(false)
                    }
                });
                PredResult::varying(value)
            }))
        })
        // hasAPI(api1, ..., apiN, instanceName=name): any of the named
        // applied API schemas is present, optionally as the given instance.
        .define("hasAPI", |args| {
            if !keywords_within(args, &["instanceName"]) {
                return None;
            }
            let instance = match args.iter().find(|a| a.name.as_deref() == Some("instanceName")) {
                Some(arg) => Some(arg.value.as_str()?.to_string()),
                None => None,
            };
            let apis = string_arguments(args)?;
            if apis.is_empty() {
                return None;
            }
            Some(predicate(move |obj| {
                if !obj.is_prim() {
                    return PredResult::constant(false);
                }
                let prim = obj.closest_prim();
                let value = apis.iter().any(|api| {
                    let name = SchemaRegistry::make_applied_name(api, instance.as_deref().unwrap_or_default());
                    prim.has_api_schema(name).unwrap_or(false)
                });
                PredResult::varying(value)
            }))
        })
        // variant(set1=sel1, ..., setN=selN): every named variant set's
        // selection matches its value — a literal selection name, or a glob.
        // All arguments must be keyword strings.
        .define("variant", |args| {
            if args.is_empty() {
                return None;
            }
            let mut wanted = Vec::new();
            for arg in args {
                let set = arg.name.clone()?;
                let selection = arg.value.as_str()?;
                let matcher = if Path::is_valid_identifier(selection) {
                    SelectionMatch::Exact(selection.to_string())
                } else {
                    SelectionMatch::Glob(GlobPattern::new(selection))
                };
                wanted.push((set, matcher));
            }
            Some(predicate(move |obj| {
                if !obj.is_prim() {
                    return PredResult::constant(false);
                }
                let selections = obj
                    .closest_prim()
                    .variant_sets()
                    .get_all_variant_selections()
                    .unwrap_or_default();
                let value = wanted.iter().all(|(set, matcher)| {
                    selections
                        .iter()
                        .find(|(s, _)| s == set)
                        .is_some_and(|(_, selection)| matcher.matches(selection))
                });
                PredResult::varying(value)
            }))
        })
}

/// Wraps a plain closure as the reference-counted predicate function the
/// library stores.
fn predicate(f: impl Fn(&CollectionObject) -> PredResult + 'static) -> Rc<dyn Fn(&CollectionObject) -> PredResult> {
    Rc::new(f)
}

/// How a `variant` argument matches a selection.
enum SelectionMatch {
    Exact(String),
    Glob(GlobPattern),
}

impl SelectionMatch {
    fn matches(&self, selection: &str) -> bool {
        match self {
            SelectionMatch::Exact(wanted) => wanted == selection,
            SelectionMatch::Glob(glob) => glob.matches(selection),
        }
    }
}

/// Reads the single optional boolean of `abstract`/`defined`/`model`/`group`
/// — positional or under its keyword name — defaulting to `true`. Any other
/// argument shape refuses to bind.
fn flag_argument(args: &[FnArg], keyword: &str) -> Option<bool> {
    match args {
        [] => Some(true),
        [arg] if arg.name.is_none() || arg.name.as_deref() == Some(keyword) => match arg.value {
            PredicateArg::Bool(value) => Some(value),
            _ => None,
        },
        _ => None,
    }
}

/// Whether every keyword argument's name is one of `allowed`. A predicate
/// refuses to bind a call carrying a keyword it does not define.
fn keywords_within(args: &[FnArg], allowed: &[&str]) -> bool {
    args.iter()
        .filter_map(|arg| arg.name.as_deref())
        .all(|name| allowed.contains(&name))
}

/// Reads the optional `strict` keyword (lenient boolean spelling), `false`
/// when absent.
fn strict_argument(args: &[FnArg]) -> Option<bool> {
    match args.iter().find(|a| a.name.as_deref() == Some("strict")) {
        Some(arg) => arg.value.as_flag(),
        None => Some(false),
    }
}

/// The positional string arguments of a call, ignoring keyword arguments.
/// A positional non-string refuses to bind.
fn string_arguments(args: &[FnArg]) -> Option<Vec<String>> {
    args.iter()
        .filter(|a| a.name.is_none())
        .map(|a| a.value.as_str().map(str::to_string))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::fs;

    use crate::kind;
    use crate::sdf::path_expr::{PredicateExpression, link_predicate_expression};
    use crate::usd::SchemaFamily;

    static SITE: &SchemaFamily<'_> = &SchemaFamily::new("site", &[]).kinds(kind::tests::SITE);

    /// A stage authoring the kinds [`SITE`] declares, with them registered
    /// when `declared`.
    fn show(declared: bool) -> Result<Stage> {
        let mut builder = Stage::builder();
        if declared {
            builder = builder.schema_registry(SchemaRegistry::builder().register(SITE).build()?);
        }
        let stage = builder.in_memory("show.usda")?;
        stage.define_prim("/Show")?.set_kind("chargroup")?;
        stage.define_prim("/Show/Hero")?.set_kind("prop")?;
        stage.define_prim("/Show/Squad")?.set_kind("assembly")?;
        stage.define_prim("/Show/Squad/Unit")?.set_kind("component")?;
        Ok(stage)
    }

    fn evaluator(stage: &Stage, expression: &str) -> Result<CollectionEvaluator> {
        CollectionEvaluator::build(stage, sdf::PathExpression::parse(expression))
    }

    /// The paths of `show`'s prims `expression` holds.
    fn members(stage: &Stage, expression: &str) -> Result<Vec<&'static str>> {
        let evaluator = evaluator(stage, expression)?;
        let mut members = Vec::new();
        for path in ["/Show", "/Show/Hero", "/Show/Squad", "/Show/Squad/Unit"] {
            if evaluator.match_path(&sdf::path(path)?).value {
                members.push(path);
            }
        }
        Ok(members)
    }

    #[test]
    fn kind_derived() -> Result<()> {
        let stage = show(true)?;
        assert_eq!(members(&stage, "//{kind(assembly)}")?, ["/Show", "/Show/Squad"]);
        assert_eq!(members(&stage, "//{kind(assembly, strict=true)}")?, ["/Show/Squad"]);
        assert_eq!(members(&stage, "//{kind(chargroup)}")?, ["/Show"]);
        assert_eq!(
            members(&stage, "//{kind(component)}")?,
            ["/Show/Hero", "/Show/Squad/Unit"]
        );
        assert_eq!(members(&stage, "//{kind(prop, strict=true)}")?, ["/Show/Hero"]);
        assert_eq!(
            members(&stage, "//{kind(model)}")?,
            ["/Show", "/Show/Hero", "/Show/Squad", "/Show/Squad/Unit"]
        );
        Ok(())
    }

    /// A call naming only kinds the registry does not know fails to compile.
    #[test]
    fn kind_unknown_refused() -> Result<()> {
        let unbound = "Invalid arguments to predicate function 'kind'";

        let declared = show(true)?;
        let error = evaluator(&declared, "//{kind(bogus)}").expect_err("no known kind");
        assert!(error.to_string().contains(unbound), "{error}");

        // The same kind is unknown to a stage whose registry does not
        // declare it.
        let plain = show(false)?;
        let error = evaluator(&plain, "//{kind(chargroup)}").expect_err("an undeclared kind");
        assert!(error.to_string().contains(unbound), "{error}");
        Ok(())
    }

    /// An unknown kind beside a known one is dropped and the call binds.
    #[test]
    fn kind_unknown_dropped() -> Result<()> {
        let stage = show(true)?;
        assert_eq!(members(&stage, "//{kind(chargroup, bogus)}")?, ["/Show"]);
        assert_eq!(members(&stage, "//{kind(bogus, prop, strict=true)}")?, ["/Show/Hero"]);
        Ok(())
    }

    #[test]
    fn model_group_derived() -> Result<()> {
        let stage = show(true)?;
        assert_eq!(
            members(&stage, "//{model}")?,
            ["/Show", "/Show/Hero", "/Show/Squad", "/Show/Squad/Unit"]
        );
        assert_eq!(members(&stage, "//{group}")?, ["/Show", "/Show/Squad"]);
        Ok(())
    }

    /// A traversal entering at a prim outside the model hierarchy still finds
    /// the models among the proxies of an instance below it, which the
    /// prototype classifies. `model` and `group` answer a prim as varying.
    #[test]
    fn searcher_crosses_instance() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = dir.path().join("root.usda");
        fs::write(
            &root,
            r#"#usda 1.0
def Scope "Inner"
{
    def Scope "Leaf" (
        kind = "prop"
    )
    {
        def Scope "Part"
        {
        }
    }
}

def Scope "Source"
{
    def Scope "Squad" (
        kind = "chargroup"
    )
    {
    }

    def Scope "Nest" (
        instanceable = true
        references = </Inner>
    )
    {
    }
}

def Scope "Container"
{
    def Scope "Inst" (
        instanceable = true
        references = </Source>
    )
    {
    }
}
"#,
        )?;
        let stage = Stage::builder()
            .schema_registry(SchemaRegistry::builder().register(SITE).build()?)
            .open(root.to_str().expect("utf-8 temp path"))?;

        // Depth-first from the ordinary prim above the instance, through its
        // proxies and the nested instance.
        let walk = [
            "/Container",
            "/Container/Inst",
            "/Container/Inst/Squad",
            "/Container/Inst/Nest",
            "/Container/Inst/Nest/Leaf",
            "/Container/Inst/Nest/Leaf/Part",
        ];
        // The members an incremental search finds, checked at each step
        // against the one-shot answer.
        let search = |expression: &str| -> Result<Vec<&'static str>> {
            let evaluator = evaluator(&stage, expression)?;
            let mut searcher = evaluator.incremental_searcher();
            let mut members = Vec::new();
            for step in walk {
                let path = sdf::path(step)?;
                let found = searcher.next(&path)?.value;
                assert_eq!(found, evaluator.match_path(&path).value, "{expression} at {step}");
                if found {
                    members.push(step);
                }
            }
            Ok(members)
        };
        let models = ["/Container/Inst/Squad", "/Container/Inst/Nest/Leaf"];
        let others = [
            "/Container",
            "/Container/Inst",
            "/Container/Inst/Nest",
            "/Container/Inst/Nest/Leaf/Part",
        ];
        assert_eq!(search("//{model}")?, models);
        assert_eq!(search("//{group}")?, ["/Container/Inst/Squad"]);
        assert_eq!(search("//{model(false)}")?, others);
        assert_eq!(search("//{not model}")?, others);

        let library = predicate_library(stage.schema_registry());
        for predicate in ["model", "group", "not model", "not group"] {
            let program = link_predicate_expression(&PredicateExpression::parse(predicate), &library)?;
            for step in ["/Container", "/Container/Inst", "/Container/Inst/Nest"] {
                let object = CollectionObject {
                    stage: stage.clone(),
                    path: sdf::path(step)?,
                };
                assert!(!program.eval(&object).constant, "{predicate} at {step}");
            }
        }
        Ok(())
    }

    /// An evaluator built before a `kind` edit answers for the edited stage.
    /// An ancestor's kind moves a descendant's `model` answer and leaves its
    /// `kind` answer alone, which reads the descendant's own kind.
    #[test]
    fn evaluator_follows_kind_edit() -> Result<()> {
        let stage = show(true)?;
        let model = evaluator(&stage, "//{model}")?;
        let prop = evaluator(&stage, "//{kind(prop)}")?;
        let hero = sdf::path("/Show/Hero")?;
        assert!(model.match_path(&hero).value && prop.match_path(&hero).value);

        stage.prim("/Show")?.set_kind("site_root")?;
        assert!(!model.match_path(&hero).value);
        assert!(prop.match_path(&hero).value);

        stage.prim("/Show")?.set_kind("chargroup")?;
        assert!(model.match_path(&hero).value);
        assert!(prop.match_path(&hero).value);

        stage.prim("/Show/Hero")?.set_kind("rivet")?;
        assert!(!prop.match_path(&hero).value);
        assert!(!model.match_path(&hero).value);
        Ok(())
    }

    /// One expression over two stages answers by each stage's registry.
    #[test]
    fn evaluator_per_stage_kinds() -> Result<()> {
        let declared = show(true)?;
        let plain = show(false)?;
        assert_eq!(
            members(&declared, "//{model}")?,
            ["/Show", "/Show/Hero", "/Show/Squad", "/Show/Squad/Unit"]
        );
        assert!(members(&plain, "//{model}")?.is_empty());
        assert_eq!(members(&declared, "//{kind(assembly)}")?, ["/Show", "/Show/Squad"]);
        assert_eq!(members(&plain, "//{kind(assembly)}")?, ["/Show/Squad"]);
        Ok(())
    }

    #[test]
    fn flag_argument_shapes() {
        use crate::sdf::path_expr::{FnArg, PredicateArg};
        let arg = |name: Option<&str>, value: PredicateArg| FnArg {
            name: name.map(str::to_string),
            value,
        };
        assert_eq!(flag_argument(&[], "isModel"), Some(true));
        assert_eq!(
            flag_argument(&[arg(None, PredicateArg::Bool(false))], "isModel"),
            Some(false)
        );
        assert_eq!(
            flag_argument(&[arg(Some("isModel"), PredicateArg::Bool(false))], "isModel"),
            Some(false)
        );
        // A stray keyword or a non-bool refuses to bind.
        assert_eq!(
            flag_argument(&[arg(Some("other"), PredicateArg::Bool(true))], "isModel"),
            None
        );
        assert_eq!(flag_argument(&[arg(None, PredicateArg::Int(1))], "isModel"), None);
    }
}
