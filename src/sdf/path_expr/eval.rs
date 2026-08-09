//! Path-expression evaluation (C++ `SdfPathExpressionEval`): a complete
//! expression compiled against a predicate library, answering per-path
//! membership with subtree constancy.
//!
//! Each pattern compiles into its literal prefix plus match segments — runs
//! of name/glob/predicate components separated by `//` stretches. A match
//! walks the queried path's elements below the prefix: the first segment is
//! anchored at the head unless a stretch precedes it, the last at the tail
//! unless a stretch follows it, and interior segments float. The result's
//! [constancy](PredResult) is structural: a path outside the pattern's
//! prefix subtree is constant `false`, a match under a trailing stretch is
//! constant `true`, and everything else may vary over descendants.

use anyhow::{ensure, Result};

use crate::sdf::Path;

use super::glob::GlobPattern;
use super::pattern::PathPattern;
use super::predicate::{link_predicate_expression, PredResult, PredicateLibrary, PredicateProgram};
use super::{ExprNode, PathExpression, SetOp};

/// A compiled path expression over predicate domain `D` (C++
/// `SdfPathExpressionEval`).
///
/// Building requires a [complete](PathExpression::is_complete) expression:
/// references must be resolved and every path anchored first. The empty
/// expression compiles to the empty evaluator, which matches nothing.
pub struct PathExpressionEval<D> {
    ops: Vec<EvalOp>,
    patterns: Vec<PatternImpl<D>>,
}

/// One evaluation instruction; `EvalPattern` consumes the next pattern in
/// order, and each binary operator fences its right operand in
/// `Open`/`Close` so a decided result can skip it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvalOp {
    EvalPattern,
    Not,
    Open,
    Close,
    Or,
    And,
}

/// One compiled pattern (C++ `Sdf_PathExpressionEvalBase::_PatternImplBase`).
struct PatternImpl<D> {
    prefix: Path,
    /// The non-stretch components; stretches survive only as the segment
    /// boundaries and the two flags.
    components: Vec<CompiledComponent>,
    /// Predicate programs the components index into.
    programs: Vec<PredicateProgram<D>>,
    /// Half-open component ranges between stretches.
    segments: Vec<Segment>,
    /// Whether a stretch opens the components, floating the first segment.
    stretch_begin: bool,
    /// Whether a stretch closes the components, extending a match to every
    /// descendant.
    stretch_end: bool,
    matches: ObjectKind,
}

/// One compiled component.
struct CompiledComponent {
    kind: ComponentKind,
    program_index: Option<usize>,
}

enum ComponentKind {
    /// A literal name; empty matches any name (a bare predicate).
    Explicit(String),
    /// A name with wildcards.
    Glob(GlobPattern),
}

impl CompiledComponent {
    /// A bare predicate matches any name — and, uniquely, may bind to the
    /// element the previous segment already matched.
    fn is_bare_predicate(&self) -> bool {
        matches!(&self.kind, ComponentKind::Explicit(name) if name.is_empty()) && self.program_index.is_some()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Segment {
    begin: usize,
    end: usize,
}

/// The candidate end positions of one segment placement; `prior` consumes
/// one element fewer than `full` by binding a leading bare predicate to the
/// previous element.
struct Placements {
    prior: Option<usize>,
    full: Option<usize>,
}

/// Which object kinds a pattern can match.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObjectKind {
    PrimOrProperty,
    PrimOnly,
    PropertyOnly,
}

impl<D> PathExpressionEval<D> {
    /// Compiles `expr` against `library`, binding every embedded predicate.
    pub fn build(expr: &PathExpression, library: &PredicateLibrary<D>) -> Result<Self> {
        ensure!(
            expr.is_complete() || expr.is_empty(),
            "Cannot build an evaluator for an incomplete path expression; resolve references \
             and anchor relative paths first: <{expr}>"
        );
        let mut eval = PathExpressionEval {
            ops: Vec::new(),
            patterns: Vec::new(),
        };
        if let Some(root) = expr.root() {
            eval.compile_node(root, library)?;
        }
        Ok(eval)
    }

    /// Whether the expression was empty; the empty evaluator matches nothing.
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    /// Answers whether `path` is in the expression's set. `domain` supplies
    /// the predicate domain object for a path; it runs only when a predicate
    /// actually needs it.
    pub fn match_path(&self, path: &Path, domain: &impl Fn(&Path) -> D) -> PredResult {
        let mut result = PredResult::constant(false);
        let mut pattern = 0;
        let mut op = 0;
        let mut stack: Vec<(EvalOp, PredResult)> = Vec::new();
        while op < self.ops.len() {
            match self.ops[op] {
                EvalOp::EvalPattern => {
                    result = self.patterns[pattern].match_path(path, domain);
                    pattern += 1;
                }
                EvalOp::Not => result = !result,
                EvalOp::And | EvalOp::Or => {
                    let deciding = self.ops[op] != EvalOp::And;
                    // Constancy is favored over short-circuiting: only a
                    // subtree-wide deciding value may skip its right operand,
                    // since a varying one still needs the operand's constancy.
                    if result.value == deciding && result.constant {
                        let mut depth = 0usize;
                        op += 1;
                        loop {
                            match self.ops[op] {
                                EvalOp::Open => depth += 1,
                                EvalOp::Close => {
                                    depth -= 1;
                                    if depth == 0 {
                                        break;
                                    }
                                }
                                EvalOp::EvalPattern => pattern += 1,
                                _ => {}
                            }
                            op += 1;
                        }
                    } else {
                        stack.push((self.ops[op], result));
                    }
                }
                EvalOp::Open => {}
                EvalOp::Close => {
                    let (pending, saved) = stack.pop().expect("Close pairs with a pushed operator");
                    result = match pending {
                        EvalOp::And => saved.and(result),
                        _ => saved.or(result),
                    };
                }
            }
            op += 1;
        }
        result
    }

    /// Emits `node`'s instructions: patterns in leftmost order, `Not`
    /// postfix, and each binary operator between its operands with the right
    /// operand fenced — a difference becomes `And` with a complemented right
    /// side.
    fn compile_node(&mut self, node: &ExprNode, library: &PredicateLibrary<D>) -> Result<()> {
        match node {
            ExprNode::Pattern(pattern) => {
                self.patterns.push(PatternImpl::compile(pattern, library)?);
                self.ops.push(EvalOp::EvalPattern);
            }
            ExprNode::Reference(_) => {
                unreachable!("a complete expression contains no references")
            }
            ExprNode::Complement(inner) => {
                self.compile_node(inner, library)?;
                self.ops.push(EvalOp::Not);
            }
            ExprNode::Op(op, left, right) => {
                self.compile_node(left, library)?;
                self.ops.push(match op {
                    SetOp::Intersection | SetOp::Difference => EvalOp::And,
                    SetOp::Union | SetOp::ImpliedUnion => EvalOp::Or,
                });
                self.ops.push(EvalOp::Open);
                self.compile_node(right, library)?;
                if *op == SetOp::Difference {
                    self.ops.push(EvalOp::Not);
                }
                self.ops.push(EvalOp::Close);
            }
        }
        Ok(())
    }
}

impl<D> PatternImpl<D> {
    fn compile(pattern: &PathPattern, library: &PredicateLibrary<D>) -> Result<Self> {
        let mut compiled = PatternImpl {
            prefix: pattern.prefix().clone(),
            components: Vec::new(),
            programs: Vec::new(),
            segments: Vec::new(),
            stretch_begin: false,
            stretch_end: false,
            matches: ObjectKind::PrimOrProperty,
        };

        let mut segment_start = 0usize;
        let close_segment = |segments: &mut Vec<Segment>, end: usize, start: &mut usize| {
            if end > *start {
                segments.push(Segment { begin: *start, end });
            }
            *start = end;
        };
        for (i, component) in pattern.components().iter().enumerate() {
            if component.is_stretch() {
                if i == 0 {
                    compiled.stretch_begin = true;
                }
                if i + 1 == pattern.components().len() {
                    compiled.stretch_end = true;
                }
                close_segment(&mut compiled.segments, compiled.components.len(), &mut segment_start);
                continue;
            }
            let program_index = match component.predicate_index {
                Some(index) => {
                    compiled
                        .programs
                        .push(link_predicate_expression(&pattern.pred_exprs()[index], library)?);
                    Some(compiled.programs.len() - 1)
                }
                None => None,
            };
            let kind = if component.is_literal || component.text.is_empty() {
                ComponentKind::Explicit(component.text.clone())
            } else {
                ComponentKind::Glob(GlobPattern::new(&component.text))
            };
            compiled.components.push(CompiledComponent { kind, program_index });
        }
        close_segment(&mut compiled.segments, compiled.components.len(), &mut segment_start);

        // Which object kinds can match: a property pattern only properties; a
        // pattern whose tail is a named component only prims; a stretch or
        // bare-predicate tail either.
        compiled.matches = if pattern.is_property() {
            ObjectKind::PropertyOnly
        } else {
            match pattern.components().last() {
                Some(last) if !last.text.is_empty() => ObjectKind::PrimOnly,
                Some(_) => ObjectKind::PrimOrProperty,
                None => ObjectKind::PrimOnly,
            }
        };
        Ok(compiled)
    }

    fn match_path(&self, path: &Path, domain: &impl Fn(&Path) -> D) -> PredResult {
        // Paths outside the prefix subtree can never match; an ancestor of
        // the prefix still has matching descendants.
        if !path.has_prefix(&self.prefix) {
            return if self.prefix.has_prefix(path) {
                PredResult::varying(false)
            } else {
                PredResult::constant(false)
            };
        }

        // A property pattern cannot match a prim, but the prim's properties
        // still might; a prim pattern can never match a property or anything
        // below it.
        let is_property = path.is_property_path();
        match self.matches {
            ObjectKind::PropertyOnly if !is_property => return PredResult::varying(false),
            ObjectKind::PrimOnly if is_property => return PredResult::constant(false),
            _ => {}
        }

        if self.components.is_empty() {
            // Pure prefix: with a stretch the whole subtree matches; without
            // one only the prefix itself does.
            if self.stretch_begin || self.stretch_end {
                return PredResult::constant(true);
            }
            return if path == &self.prefix {
                PredResult::varying(true)
            } else {
                PredResult::constant(false)
            };
        }

        let Some(elements) = tail_elements(path, &self.prefix) else {
            return PredResult::constant(false);
        };

        if self.match_segments(&elements, domain) {
            if self.stretch_end {
                PredResult::constant(true)
            } else {
                PredResult::varying(true)
            }
        } else {
            PredResult::varying(false)
        }
    }

    /// Places every segment over `elements`: the first anchored at the head
    /// unless a stretch precedes it, the last landing on the tail unless one
    /// follows it, interior segments floating in order. Floating segments
    /// take the placement with the smallest end position — leftmost, and
    /// prior-bound before full-width — which never starves a later segment,
    /// since later segments only need room to the right.
    fn match_segments(&self, elements: &[Element<'_>], domain: &impl Fn(&Path) -> D) -> bool {
        let mut pos = 0usize;
        for (i, segment) in self.segments.iter().enumerate() {
            let first = i == 0;
            let last = i + 1 == self.segments.len();
            let anchored_head = first && !self.stretch_begin;
            let anchored_tail = last && !self.stretch_end;

            let placed = if anchored_head {
                // No stretch precedes the head segment, so the prior-binding
                // shortcut is off: the pattern spells exactly these elements
                // from the front.
                let Placements { full, .. } = self.segment_placements(*segment, elements, 0, false, domain);
                full
            } else if anchored_tail {
                // Either alignment may land the segment exactly on the tail.
                let mut found = None;
                for at in pos..=elements.len() {
                    let Placements { prior, full } = self.segment_placements(*segment, elements, at, true, domain);
                    if prior == Some(elements.len()) || full == Some(elements.len()) {
                        found = Some(elements.len());
                        break;
                    }
                }
                found
            } else {
                let mut found = None;
                for at in pos..=elements.len() {
                    let Placements { prior, full } = self.segment_placements(*segment, elements, at, true, domain);
                    if let Some(consumed) = prior.or(full) {
                        found = Some(consumed);
                        break;
                    }
                }
                found
            };
            match placed {
                Some(consumed) if last && !self.stretch_end && consumed != elements.len() => return false,
                Some(consumed) => pos = consumed,
                None => return false,
            }
        }
        // Leftover tail elements match only under a trailing stretch.
        self.stretch_end || pos == elements.len()
    }

    fn segment_width(&self, segment: Segment) -> usize {
        segment.end - segment.begin
    }

    /// The ways `segment` can match with its body starting at `elements[at]`,
    /// each as the element position after the match. `full` aligns the first
    /// component at `at`. `prior` — offered only when a stretch precedes the
    /// segment (`allow_prior`) and it opens with a bare predicate — binds
    /// that predicate to the element the previous segment already matched
    /// (or, at the very head, to the pattern's own prefix element) and
    /// starts the remainder at `at`, consuming one element fewer.
    fn segment_placements(
        &self,
        segment: Segment,
        elements: &[Element<'_>],
        at: usize,
        allow_prior: bool,
        domain: &impl Fn(&Path) -> D,
    ) -> Placements {
        let full = self
            .try_alignment(segment, segment.begin, elements, at, domain)
            .then(|| at + self.segment_width(segment));

        let mut prior = None;
        if allow_prior && self.components[segment.begin].is_bare_predicate() {
            let prior_matches = if at > 0 {
                self.component_matches(&self.components[segment.begin], &elements[at - 1], domain)
            } else if !self.prefix.is_abs_root() && !self.prefix.is_empty() {
                // C++'s extra-prefix case: the bare predicate may bind the
                // prefix itself (never the pseudo-root).
                let head = &self.components[segment.begin];
                match head.program_index {
                    Some(index) => self.programs[index].eval(&domain(&self.prefix)).value,
                    None => true,
                }
            } else {
                false
            };
            if prior_matches && self.try_alignment(segment, segment.begin + 1, elements, at, domain) {
                prior = Some(at + self.segment_width(segment) - 1);
            }
        }
        Placements { prior, full }
    }

    /// Matches the components from `from` to the segment end against
    /// consecutive elements starting at `at`.
    fn try_alignment(
        &self,
        segment: Segment,
        from: usize,
        elements: &[Element<'_>],
        at: usize,
        domain: &impl Fn(&Path) -> D,
    ) -> bool {
        let count = segment.end - from;
        if at + count > elements.len() {
            return false;
        }
        (from..segment.end).all(|component| {
            self.component_matches(&self.components[component], &elements[at + (component - from)], domain)
        })
    }

    fn component_matches(
        &self,
        component: &CompiledComponent,
        element: &Element<'_>,
        domain: &impl Fn(&Path) -> D,
    ) -> bool {
        let name_matches = match &component.kind {
            ComponentKind::Explicit(name) => name.is_empty() || name == element.name,
            ComponentKind::Glob(glob) => glob.matches(element.name),
        };
        if !name_matches {
            return false;
        }
        match component.program_index {
            Some(index) => self.programs[index].eval(&domain(&element.path)).value,
            None => true,
        }
    }
}

/// One path element below a pattern prefix: its name and the subpath ending
/// at it (the object a predicate evaluates against).
struct Element<'a> {
    name: &'a str,
    path: Path,
}

/// The elements of `path` below `prefix`, root-ward first, the property tail
/// last. `None` for paths the pattern grammar cannot address (variant
/// selections, relationship targets).
fn tail_elements<'a>(path: &'a Path, prefix: &Path) -> Option<Vec<Element<'a>>> {
    if path.contains_prim_variant_selection() || path.as_str().contains('[') {
        return None;
    }

    let mut elements = Vec::new();
    let (prim_path, property) = match path.split_property() {
        Some((prim, name)) => (prim, Some(name)),
        None => (path.clone(), None),
    };

    // Walk prim ancestors down to the prefix. The prefix itself may be a
    // property path only when it equals `path`, which the caller's
    // no-component branch already answered.
    let mut chain: Vec<Path> = Vec::new();
    let mut cursor = prim_path.clone();
    while cursor != *prefix && !cursor.is_empty() {
        if !cursor.has_prefix(prefix) {
            return None;
        }
        chain.push(cursor.clone());
        cursor = cursor.parent()?;
    }
    for ancestor in chain.into_iter().rev() {
        let name_len = ancestor.name().map(str::len)?;
        let start = ancestor.as_str().len() - name_len;
        elements.push(Element {
            // Borrow the name out of `path`, which shares the ancestor text.
            name: &path.as_str()[start..start + name_len],
            path: ancestor,
        });
    }
    if let Some(name) = property {
        let start = path.as_str().len() - name.len();
        elements.push(Element {
            name: &path.as_str()[start..],
            path: path.clone(),
        });
    }
    Some(elements)
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::super::{PathExpression, PredResult, PredicateArg, PredicateLibrary};
    use super::*;
    use crate::sdf::path;

    /// Predicates over the path itself: `name:<leaf>` matches the leaf name,
    /// `always` matches everything.
    fn library() -> PredicateLibrary<Path> {
        PredicateLibrary::new()
            .define("name", |args| {
                let wanted = args.first()?.value.as_str()?.to_string();
                Some(
                    Rc::new(move |p: &Path| PredResult::varying(p.name().is_some_and(|n| n == wanted)))
                        as Rc<dyn Fn(&Path) -> PredResult>,
                )
            })
            .define("always", |_| {
                Some(Rc::new(|_: &Path| PredResult::varying(true)) as Rc<dyn Fn(&Path) -> PredResult>)
            })
            .define("depth", |args| {
                let Some(PredicateArg::Int(wanted)) = args.first().map(|a| &a.value) else {
                    return None;
                };
                let wanted = *wanted as usize;
                Some(
                    Rc::new(move |p: &Path| PredResult::varying(p.prim_element_count() == wanted))
                        as Rc<dyn Fn(&Path) -> PredResult>,
                )
            })
    }

    fn eval(text: &str) -> PathExpressionEval<Path> {
        let expr = PathExpression::parse(text);
        assert!(expr.parse_error().is_none(), "{text}: {:?}", expr.parse_error());
        PathExpressionEval::build(&expr, &library()).expect("builds")
    }

    fn check(evaluator: &PathExpressionEval<Path>, p: &str) -> PredResult {
        evaluator.match_path(&path(p).unwrap(), &|p: &Path| p.clone())
    }

    #[test]
    fn everything_matches() {
        let e = eval("//");
        assert_eq!(check(&e, "/"), PredResult::constant(true));
        assert_eq!(check(&e, "/a"), PredResult::constant(true));
        assert_eq!(check(&e, "/a/b/c"), PredResult::constant(true));
        assert_eq!(check(&e, "/a.attr"), PredResult::constant(true));
    }

    #[test]
    fn empty_matches_nothing() {
        let e = PathExpressionEval::build(&PathExpression::nothing(), &library()).expect("builds");
        assert!(e.is_empty());
        assert_eq!(check(&e, "/a"), PredResult::constant(false));
    }

    #[test]
    fn prefix_constancy() {
        let e = eval("/World/chars//");
        // Inside the subtree: constant true.
        assert_eq!(check(&e, "/World/chars"), PredResult::constant(true));
        assert_eq!(check(&e, "/World/chars/Mike/geo"), PredResult::constant(true));
        // On the way down to the prefix: varying false.
        assert_eq!(check(&e, "/World"), PredResult::varying(false));
        // Elsewhere entirely: constant false.
        assert_eq!(check(&e, "/Else"), PredResult::constant(false));
        assert_eq!(check(&e, "/World2"), PredResult::constant(false));
    }

    #[test]
    fn exact_prim_match() {
        let e = eval("/World/Robot");
        assert_eq!(check(&e, "/World/Robot"), PredResult::varying(true));
        assert_eq!(check(&e, "/World/Robot/arm"), PredResult::constant(false));
        assert_eq!(check(&e, "/World"), PredResult::varying(false));
    }

    #[test]
    fn glob_components() {
        let e = eval("/World//Robot*");
        assert_eq!(check(&e, "/World/Robot1"), PredResult::varying(true));
        assert_eq!(check(&e, "/World/a/b/RobotX"), PredResult::varying(true));
        assert_eq!(check(&e, "/World/Rob"), PredResult::varying(false));
        // Only prims: the tail is a named component.
        assert_eq!(check(&e, "/World/Robot1.attr"), PredResult::constant(false));
    }

    #[test]
    fn multi_segment_anchoring() {
        // First segment anchored at head, interior floats, tail anchored.
        let e = eval("/a/x*//m/n//z");
        assert_eq!(check(&e, "/a/x1/q/m/n/r/z"), PredResult::varying(true));
        assert_eq!(check(&e, "/a/x1/m/n/z"), PredResult::varying(true));
        // Missing interior run.
        assert_eq!(check(&e, "/a/x1/q/m/r/z"), PredResult::varying(false));
        // Tail not at the end.
        assert_eq!(check(&e, "/a/x1/m/n/z/t"), PredResult::varying(false));
        // Head not anchored.
        assert_eq!(check(&e, "/a/q/x1/m/n/z"), PredResult::varying(false));
    }

    #[test]
    fn floating_segment_placement() {
        // A floating segment takes its leftmost placement; later occurrences
        // still satisfy the tail.
        let e = eval("/r//a/b//c");
        assert_eq!(check(&e, "/r/a/b/a/b/c"), PredResult::varying(true));
        assert_eq!(check(&e, "/r/x/a/b/x/c"), PredResult::varying(true));
        assert_eq!(check(&e, "/r/a/x/b/c"), PredResult::varying(false));
    }

    #[test]
    fn bare_predicate_needs_stretch() {
        // Without a preceding stretch the prior-binding shortcut is off: an
        // anchored-head pattern spells exactly its elements.
        let e = eval("/foo/{always}");
        assert_eq!(check(&e, "/foo"), PredResult::varying(false));
        assert_eq!(check(&e, "/foo/child"), PredResult::varying(true));
        let mid = eval("/a/{always}/x");
        assert_eq!(check(&mid, "/a/x"), PredResult::varying(false));
        assert_eq!(check(&mid, "/a/m/x"), PredResult::varying(true));
    }

    #[test]
    fn shorter_placement_feeds_tail() {
        // The prior-bound placement wins over the greedy full-width one, so
        // the anchored tail still finds its elements: {always} binds the
        // prefix /r, `a` takes the first element, and `a/b` lands on the
        // tail.
        let e = eval("/r//{always}/a//a/b");
        assert_eq!(check(&e, "/r/a/a/b"), PredResult::varying(true));
    }

    #[test]
    fn bare_predicate_binds_prefix() {
        // Under a leading stretch, a bare predicate may bind the prefix
        // element itself.
        let e = eval("/foo//{name:foo}");
        assert_eq!(check(&e, "/foo"), PredResult::varying(true));
        let miss = eval("/foo//{name:other}");
        assert_eq!(check(&miss, "/foo"), PredResult::varying(false));
    }

    #[test]
    fn property_patterns() {
        let e = eval("//*.attr");
        assert_eq!(check(&e, "/a.attr"), PredResult::varying(true));
        assert_eq!(check(&e, "/a/b.attr"), PredResult::varying(true));
        assert_eq!(check(&e, "/a.other"), PredResult::varying(false));
        // A prim can never be a property match, but its properties may be.
        assert_eq!(check(&e, "/a"), PredResult::varying(false));

        let exact = eval("/a/b.attr:ns");
        assert_eq!(check(&exact, "/a/b.attr:ns"), PredResult::varying(true));
        assert_eq!(check(&exact, "/a/b"), PredResult::varying(false));
    }

    #[test]
    fn predicate_gating() {
        let e = eval("//{name:tag}");
        assert_eq!(check(&e, "/x/tag"), PredResult::varying(true));
        assert_eq!(check(&e, "/x/other"), PredResult::varying(false));

        // The predicate binds to its own element, not the leaf.
        let mid = eval("//x{depth:2}/y");
        assert_eq!(check(&mid, "/a/x/y"), PredResult::varying(true));
        assert_eq!(check(&mid, "/a/b/x/y"), PredResult::varying(false));
    }

    #[test]
    fn trailing_stretch_after_predicate() {
        // Once the predicate element matched, the whole subtree below it is
        // in: constant true.
        let e = eval("//{name:on}//");
        assert_eq!(check(&e, "/a/on"), PredResult::constant(true));
        assert_eq!(check(&e, "/a/on/deep/below"), PredResult::constant(true));
        assert_eq!(check(&e, "/a/off"), PredResult::varying(false));
    }

    #[test]
    fn bare_predicate_prior_element() {
        // Both bare predicates may bind to the same element: the second
        // segment's leading predicate re-tests the element the first
        // matched.
        let e = eval("//{always}//{name:hit}");
        assert_eq!(check(&e, "/hit"), PredResult::varying(true));
        assert_eq!(check(&e, "/a/hit"), PredResult::varying(true));
        assert_eq!(check(&e, "/miss"), PredResult::varying(false));
    }

    #[test]
    fn set_algebra() {
        let e = eval("/a// - /a/b//");
        // Constant: no descendant of /a/c can sit under /a/b, so the
        // difference holds subtree-wide.
        assert_eq!(check(&e, "/a/c"), PredResult::constant(true));
        // On /a itself the exclusion may bite below: varying.
        assert_eq!(check(&e, "/a"), PredResult::varying(true));
        assert_eq!(check(&e, "/a/b/c"), PredResult::constant(false));

        let union = eval("/a// /b//");
        assert!(check(&union, "/a/x").value);
        assert!(check(&union, "/b/x").value);
        assert!(!check(&union, "/c/x").value);

        let inter = eval("//{name:tag} & /a//");
        assert!(check(&inter, "/a/tag").value);
        assert!(!check(&inter, "/b/tag").value);

        let complement = eval("~/a//");
        assert!(!check(&complement, "/a/x").value);
        assert!(check(&complement, "/b").value);
    }

    #[test]
    fn incomplete_rejected() {
        let library = library();
        for text in ["child//", "/a// %/Sets:b", "/a// %_"] {
            let expr = PathExpression::parse(text);
            assert!(
                PathExpressionEval::build(&expr, &library).is_err(),
                "{text} should be rejected"
            );
        }
    }

    #[test]
    fn variant_paths_never_match() {
        let e = eval("//");
        assert_eq!(
            check(&e, "/a{set=sel}b"),
            PredResult::constant(true),
            "variant selections sit below the everything prefix"
        );
        let named = eval("/a//b");
        assert_eq!(check(&named, "/a{set=sel}b"), PredResult::constant(false));
    }
}
