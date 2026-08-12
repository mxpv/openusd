//! Expression-mode collection machinery: the predicate library membership
//! expressions evaluate against (C++ `UsdGetCollectionPredicateLibrary`),
//! the compiled evaluator a [`MembershipQuery`](super::MembershipQuery)
//! carries, and complete-expression resolution
//! (C++ `UsdCollectionAPI::ResolveCompleteMembershipExpression`).

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use anyhow::Result;

use crate::sdf::path_expr::{
    FnArg, GlobPattern, IncrementalSearcher, PathExpressionEval, PredResult, PredicateArg, PredicateLibrary,
};
use crate::sdf::{self, Path};
use crate::usd::{Prim, Stage};

use super::collection::Collection;

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
        let eval = PathExpressionEval::build(&expression, &predicate_library())?;
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
pub fn resolve_complete_membership_expression(stage: &Stage, collection: &Collection) -> Result<sdf::PathExpression> {
    let mut state = ResolveState {
        visited: HashSet::from([(collection.prim().clone(), collection.name().to_string())]),
        memo: HashMap::new(),
    };
    Ok(resolve_impl(stage, collection, &mut state)?.expression)
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

fn resolve_impl(stage: &Stage, collection: &Collection, state: &mut ResolveState) -> Result<Resolved> {
    let Some(expression) = collection.membership_expression(stage)? else {
        return Ok(Resolved {
            expression: sdf::PathExpression::nothing(),
            cacheable: true,
        });
    };
    // Composition already anchored and namespace-mapped a typed expression;
    // anchoring again covers the lenient string-typed opinions.
    let expression = expression.make_absolute(collection.prim());
    let mut cacheable = true;
    let mut error = None;
    let expression = expression.resolve_references(&mut |reference| {
        if error.is_some() || reference.name.is_empty() || reference.is_weaker() {
            return sdf::PathExpression::nothing();
        }
        let prim = if reference.path.is_empty() {
            collection.prim().clone()
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
        let nested = Collection::from_parts(prim, reference.name.clone());
        let resolved = match resolve_impl(stage, &nested, state) {
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
/// binder body names its semantics and constancy.
fn predicate_library() -> PredicateLibrary<CollectionObject> {
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
        // plain false. The model hierarchy is contiguous from the root, so a
        // non-model's subtree stays non-model.
        .define("model", |args| {
            let wanted = flag_argument(args, "isModel")?;
            Some(predicate(move |obj| {
                if !obj.is_prim() {
                    return PredResult::constant(false);
                }
                let is_model = obj.closest_prim().is_model().unwrap_or(false);
                PredResult {
                    value: is_model == wanted,
                    constant: !is_model,
                }
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
                PredResult {
                    value: is_group == wanted,
                    constant: !is_group,
                }
            }))
        })
        // kind(k1, ..., kN, strict=false): the prim's kind is one of the
        // named kinds — exactly under `strict`, else per the built-in kind
        // hierarchy. Kinds outside the built-in hierarchy still compare by
        // name (this crate has no kind registry for C++'s known-kind filter).
        .define("kind", |args| {
            if !keywords_within(args, &["strict"]) {
                return None;
            }
            let strict = strict_argument(args)?;
            let kinds = string_arguments(args)?;
            if kinds.is_empty() {
                return None;
            }
            Some(predicate(move |obj| {
                if !obj.is_prim() {
                    return PredResult::constant(false);
                }
                let Ok(Some(kind)) = obj.closest_prim().kind() else {
                    return PredResult::varying(false);
                };
                let value = kinds.iter().any(|wanted| {
                    if strict {
                        kind.as_str() == wanted
                    } else {
                        kind_is_a(kind.as_str(), wanted)
                    }
                });
                PredResult::varying(value)
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
                    let name = match &instance {
                        Some(instance) => format!("{api}:{instance}"),
                        None => api.clone(),
                    };
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

/// Whether `kind` is `ancestor` or descends from it in the built-in kind
/// hierarchy (C++ `KindRegistry` defaults): `assembly` and `group` are
/// models, `component` is a model, `subcomponent` stands alone.
fn kind_is_a(kind: &str, ancestor: &str) -> bool {
    if kind == ancestor {
        return true;
    }
    matches!(
        (kind, ancestor),
        ("assembly", "group" | "model") | ("group" | "component", "model")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kind_hierarchy() {
        assert!(kind_is_a("assembly", "model"));
        assert!(kind_is_a("assembly", "group"));
        assert!(kind_is_a("group", "model"));
        assert!(kind_is_a("component", "model"));
        assert!(!kind_is_a("subcomponent", "model"));
        assert!(!kind_is_a("model", "group"));
        assert!(kind_is_a("custom", "custom"));
        assert!(!kind_is_a("custom", "model"));
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
