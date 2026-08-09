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

use anyhow::{Result, ensure};

use crate::sdf::Path;

use super::glob::GlobPattern;
use super::pattern::PathPattern;
use super::predicate::{PredResult, PredicateLibrary, PredicateProgram, link_predicate_expression};
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
    /// The prefix's [`path_depth`].
    prefix_depth: usize,
    /// The non-stretch components; stretches survive only as the segment
    /// boundaries and the two flags.
    components: Vec<CompiledComponent>,
    /// Predicate programs the components index into.
    programs: Vec<PredicateProgram<D>>,
    /// Half-open component ranges between stretches.
    segments: Vec<Segment>,
    /// The widest segment's component count, bounding the element window an
    /// incremental step needs.
    widest_segment: usize,
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
        self.eval_expr(|pattern| self.patterns[pattern].match_path(path, domain))
    }

    /// A fresh [`IncrementalSearcher`] borrowing this evaluator; `domain`
    /// supplies the predicate domain object for a path, as in
    /// [`match_path`](Self::match_path).
    pub fn incremental_searcher<F: Fn(&Path) -> D>(&self, domain: F) -> IncrementalSearcher<'_, D, F> {
        IncrementalSearcher {
            eval: self,
            states: self.patterns.iter().map(|_| PatternSearchState::default()).collect(),
            domain,
            last_path_depth: 0,
        }
    }

    /// Walks the bytecode, sourcing per-pattern answers from `eval_pattern`
    /// (called with each pattern's index, in pattern order) and combining
    /// them through the operators (C++ `_EvalExpr`). A short-circuited
    /// right operand's patterns are passed over without being evaluated.
    fn eval_expr(&self, mut eval_pattern: impl FnMut(usize) -> PredResult) -> PredResult {
        let mut result = PredResult::constant(false);
        let mut pattern = 0;
        let mut op = 0;
        // TODO(perf): expressions nest shallowly, so an inline small-buffer
        // stack would avoid this per-evaluation allocation on the searcher's
        // per-visit path.
        let mut stack: Vec<(EvalOp, PredResult)> = Vec::new();
        while op < self.ops.len() {
            match self.ops[op] {
                EvalOp::EvalPattern => {
                    result = eval_pattern(pattern);
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

/// A stateful depth-first searcher over one expression (C++
/// `SdfPathExpressionEval::IncrementalSearcher`), created by
/// [`PathExpressionEval::incremental_searcher`].
///
/// [`next`](Self::next) must be fed paths in depth-first order: each path a
/// direct child of the previous one, a sibling, or the sibling of one of
/// its ancestors. Never feeding any path under a visited one — skipping
/// that whole subtree — is valid. Each answer's value equals one-shot
/// [`match_path`](PathExpressionEval::match_path) on the same path, at a
/// fraction of the per-visit cost: matched segments and subtree-constant
/// answers are carried between visits, so a visit only tries to extend
/// each pattern's match by the newly added path element. An answer may be
/// subtree-constant where the one-shot answer varies; the values agree
/// everywhere.
// TODO(rayon): C++ supports copying a searcher so a fork can search a
// sibling subtree in parallel; derive `Clone` when a traversal needs it.
pub struct IncrementalSearcher<'a, D, F: Fn(&Path) -> D> {
    eval: &'a PathExpressionEval<D>,
    states: Vec<PatternSearchState>,
    domain: F,
    last_path_depth: usize,
}

impl<D, F: Fn(&Path) -> D> IncrementalSearcher<'_, D, F> {
    /// Advances the search to `path` — the next step of a depth-first
    /// traversal, per the ordering contract above — and answers whether it
    /// is in the expression's set.
    pub fn next(&mut self, path: &Path) -> PredResult {
        let visit = Visit {
            path,
            depth: path_depth(path),
            is_property: path.is_property_path(),
            addressable: addressable(path),
        };
        // Ascending (or stepping to a sibling) invalidates state gathered at
        // or below the new depth — for every pattern, evaluated or not.
        if visit.depth <= self.last_path_depth {
            for state in &mut self.states {
                state.pop(visit.depth);
            }
        }
        self.last_path_depth = visit.depth;
        let (eval, states, domain) = (self.eval, &mut self.states, &self.domain);
        eval.eval_expr(|pattern| eval.patterns[pattern].next(&mut states[pattern], &visit, domain))
    }

    /// Forgets all search state so a new traversal may begin.
    pub fn reset(&mut self) {
        for state in &mut self.states {
            state.segment_match_depths.clear();
            state.constant = None;
        }
        self.last_path_depth = 0;
    }
}

/// Per-pattern incremental search state (C++ `_PatternIncrSearchState`).
#[derive(Debug, Default)]
struct PatternSearchState {
    /// The absolute path depth at which each matched segment's match ended,
    /// one entry per segment matched so far.
    segment_match_depths: Vec<usize>,
    /// The depth at which the answer became subtree-constant, with the
    /// value.
    constant: Option<(usize, bool)>,
}

impl PatternSearchState {
    /// Discards state invalidated by stepping to a path of depth
    /// `new_depth`: segment matches that ended at `new_depth` or deeper
    /// (the element they matched has been replaced), and the constant memo
    /// once the walk climbs back to where it was recorded.
    fn pop(&mut self, new_depth: usize) {
        while self
            .segment_match_depths
            .last()
            .is_some_and(|&depth| depth >= new_depth)
        {
            self.segment_match_depths.pop();
        }
        if self.constant.is_some_and(|(depth, _)| new_depth <= depth) {
            self.constant = None;
        }
    }
}

/// The per-visit facts every pattern's incremental step shares, computed
/// once by [`IncrementalSearcher::next`].
struct Visit<'a> {
    path: &'a Path,
    /// The path's [`path_depth`].
    depth: usize,
    is_property: bool,
    /// Whether the pattern grammar can [address](addressable) the path.
    addressable: bool,
}

impl<D> PatternImpl<D> {
    fn compile(pattern: &PathPattern, library: &PredicateLibrary<D>) -> Result<Self> {
        let mut compiled = PatternImpl {
            prefix: pattern.prefix().clone(),
            prefix_depth: path_depth(pattern.prefix()),
            components: Vec::new(),
            programs: Vec::new(),
            segments: Vec::new(),
            widest_segment: 0,
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
        compiled.widest_segment = compiled.segments.iter().map(|s| s.end - s.begin).max().unwrap_or(0);

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

    /// One incremental search step (C++ `_PatternImplBase::_Next`): the
    /// answer for `visit`'s path, resuming from the segment matches `state`
    /// accumulated over the paths visited above it.
    fn next(&self, state: &mut PatternSearchState, visit: &Visit<'_>, domain: &impl Fn(&Path) -> D) -> PredResult {
        if let Some((_, value)) = state.constant {
            return PredResult::constant(value);
        }

        let Visit { path, depth, .. } = *visit;

        // The prefix needs checking only until the first segment lands;
        // once segments have matched, the walk is inside the prefix subtree.
        if state.segment_match_depths.is_empty() && !path.has_prefix(&self.prefix) {
            return if self.prefix.has_prefix(path) {
                PredResult::varying(false)
            } else {
                state.constant = Some((self.prefix_depth, false));
                PredResult::constant(false)
            };
        }

        // A prim pattern can never match a property or anything below it. A
        // property pattern cannot match a prim, but the prim's elements
        // still feed interior segments and its properties may match below,
        // so the machinery runs and a would-be match is demoted.
        if self.matches == ObjectKind::PrimOnly && visit.is_property {
            return PredResult::constant(false);
        }
        let demote = self.matches == ObjectKind::PropertyOnly && !visit.is_property;

        if self.components.is_empty() {
            // Pure prefix: with a stretch the whole subtree matches; without
            // one only the prefix itself does.
            if self.stretch_begin || self.stretch_end {
                if demote {
                    return PredResult::varying(false);
                }
                state.constant = Some((self.prefix_depth, true));
                return PredResult::constant(true);
            }
            return if depth != self.prefix_depth {
                state.constant = Some((self.prefix_depth, false));
                PredResult::constant(false)
            } else if demote {
                PredResult::varying(false)
            } else {
                PredResult::varying(true)
            };
        }

        if !visit.addressable {
            state.constant = Some((depth, false));
            return PredResult::constant(false);
        }

        // With every segment already matched, the trailing segment gets to
        // re-match deeper: `//Foo//foo/bar` against
        // `/Foo/geom/foo/bar/foo/bar` re-lands `foo/bar` at each deeper
        // occurrence.
        if state.segment_match_depths.len() == self.segments.len() {
            state.segment_match_depths.pop();
        }

        // The candidate elements: alignments only ever read a segment's
        // width plus the prior element a leading bare predicate may bind
        // to, so the widest segment bounds the extraction; each loop
        // iteration works on a suffix of this one window.
        let first_prev = state.segment_match_depths.last().copied().unwrap_or(self.prefix_depth);
        let elements = last_elements(path, (depth - first_prev + 1).min(self.widest_segment + 1));

        // Segments can overlap — a leading bare predicate may bind the
        // element the previous segment ended on, consuming nothing — so one
        // visit may complete several segments.
        loop {
            let index = state.segment_match_depths.len();
            let segment = self.segments[index];
            let has_prev = index > 0;
            let is_final = index + 1 == self.segments.len();
            let prev_end = state.segment_match_depths.last().copied().unwrap_or(self.prefix_depth);
            // The elements grown since the previous segment's match (or the
            // prefix) are all this segment may consume.
            let available = depth - prev_end;
            if available < self.segment_min_match_elts(segment) {
                return PredResult::varying(false);
            }
            let has_stretch = has_prev || self.stretch_begin;
            let width = self.segment_width(segment);
            if !has_stretch && available > width {
                // The head-anchored segment needed to consume every element,
                // and the walk has grown past it.
                state.constant = Some((depth, false));
                return PredResult::constant(false);
            }
            // This segment's window: the deepest `available` elements, plus
            // the prior element a leading bare predicate may bind to, capped
            // to what an alignment can read.
            let bare = self.components[segment.begin].is_bare_predicate();
            let prior = has_stretch && bare && depth != 0;
            let count = (available + usize::from(prior)).min(width + 1).min(elements.len());
            let window = &elements[elements.len() - count..];
            // The segment must land on the path's tail — the newly added
            // element is the only new match opportunity. A non-final segment
            // opening with a bare predicate may instead land one element
            // short, binding that predicate to the prior element (tried
            // first, mirroring `segment_placements`' preference for
            // `prior`).
            let end_depth = window.len().checked_sub(width).and_then(|exact| {
                if !is_final
                    && bare
                    && exact > 0
                    && self.try_alignment(segment, segment.begin, window, exact - 1, domain)
                {
                    Some(depth - 1)
                } else if self.try_alignment(segment, segment.begin, window, exact, domain) {
                    Some(depth)
                } else {
                    None
                }
            });
            match end_depth {
                Some(end) => {
                    state.segment_match_depths.push(end);
                    if is_final {
                        break;
                    }
                }
                None => break,
            }
        }

        if state.segment_match_depths.len() == self.segments.len() {
            let last = *state.segment_match_depths.last().expect("all segments matched");
            if demote {
                // The prim itself cannot be the property match it spells
                // out; its properties answer for themselves.
                return PredResult::varying(false);
            }
            if self.stretch_end {
                state.constant = Some((last, true));
                return PredResult::constant(true);
            }
            // The final segment only ever lands exactly on the path's tail.
            debug_assert_eq!(last, depth);
            return PredResult::varying(true);
        }
        PredResult::varying(false)
    }

    /// The fewest path elements `segment` can consume: its width, less one
    /// when a leading bare predicate may bind the prior element instead
    /// (C++ `_SegmentMinMatchElts`).
    fn segment_min_match_elts(&self, segment: Segment) -> usize {
        self.segment_width(segment) - usize::from(self.components[segment.begin].is_bare_predicate())
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

/// The depth the matchers measure paths by: the number of [`Element`]s the
/// path yields — its prim names plus the property tail.
fn path_depth(path: &Path) -> usize {
    path.prim_element_count() + usize::from(path.is_property_path())
}

/// Whether the pattern grammar can address `path` at all; variant
/// selections and relationship targets are outside it.
fn addressable(path: &Path) -> bool {
    !path.contains_prim_variant_selection() && !path.as_str().contains('[')
}

/// The elements of `path` below `prefix`, root-ward first, the property tail
/// last. `None` for paths the pattern grammar cannot [address](addressable).
/// The prefix itself may be a property path only when it equals `path`,
/// which the callers' no-component branches already answered.
fn tail_elements<'a>(path: &'a Path, prefix: &Path) -> Option<Vec<Element<'a>>> {
    addressable(path).then(|| last_elements(path, path_depth(path) - path_depth(prefix)))
}

/// The deepest `count` elements of `path`, root-ward first, the property
/// tail last; the whole path when it has fewer.
// TODO(perf): an `Element` could be a byte-offset view into the path's
// string, materializing the predicate's domain `Path` only when a component
// actually carries a predicate; that would drop the per-element `Path`
// allocations here for predicate-free patterns.
fn last_elements(path: &Path, count: usize) -> Vec<Element<'_>> {
    let mut elements = Vec::new();
    if count == 0 {
        return elements;
    }
    let (prim_path, property) = match path.split_property() {
        Some((prim, name)) => (prim, Some(name)),
        None => (path.clone(), None),
    };

    let prim_count = count - usize::from(property.is_some());
    let chain: Vec<Path> = prim_path.ancestors_below_root().take(prim_count).collect();
    for ancestor in chain.into_iter().rev() {
        let name_len = ancestor.name().expect("chain holds named ancestors").len();
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
    elements
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

    /// The expressions the searcher is checked against, spanning stretches,
    /// bare predicates (including prefix binding), globs, predicate
    /// arguments, property patterns, and set algebra.
    const CORPUS: &[&str] = &[
        "//",
        "/World/chars//",
        "/World/Robot",
        "/World//Robot*",
        "/a/x*",
        "/a/x*//m/n//z",
        "/r//a/b//c",
        "/foo/{always}",
        "/a/{always}/x",
        "/r//{always}/a//a/b",
        "/foo//{name:foo}",
        "/foo//{name:other}",
        "//*.attr",
        "/a/b.attr:ns",
        "//{name:tag}",
        "//x{depth:2}/y",
        "//{name:on}//",
        "//{always}//{name:hit}",
        "//{always}//{always}",
        "//x//*.attr",
        "/a//b//*.attr",
        "//{always}//*.attr",
        "//Foo//foo/bar",
        "/a// - /a/b//",
        "/a// /b//",
        "//{name:tag} & /a//",
        "~/a//",
    ];

    /// Expands `leaves` into the full tree visit: every ancestor included,
    /// in depth-first pre-order. Lexicographic path order is such an order
    /// here — every fixture name is alphanumeric, so `/` sorts before any
    /// name byte and `.` just before `/`, putting each prim before its
    /// properties and those before its children.
    fn dfs_walk(leaves: &[&str]) -> Vec<Path> {
        let mut all = vec![Path::abs_root()];
        for leaf in leaves {
            let mut cursor = path(leaf).unwrap();
            while !cursor.is_abs_root() {
                all.push(cursor.clone());
                cursor = cursor.parent().expect("fixture paths are absolute");
            }
        }
        all.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        all.dedup();
        all
    }

    /// The synthetic tree the searcher tests walk.
    fn fixture_walk() -> Vec<Path> {
        dfs_walk(&[
            "/Foo/geom/foo/bar/foo/bar/foo/bar",
            "/World/Rob",
            "/World/Robot/arm",
            "/World/Robot1.attr",
            "/World/anim/chars/RobotX",
            "/World/chars/Bob",
            "/World/chars/Mike/geo",
            "/a/b.attr",
            "/a/b.attr:ns",
            "/a/b/c.attr",
            "/a/n/b/c.attr",
            "/a/off",
            "/a/on/deep/below",
            "/a/q/x1/m",
            "/a/tag",
            "/a/w/b.p",
            "/a/w/b/c.attr",
            "/a/x/y",
            "/a/x1/m/n/z",
            "/a/x1/q/m/n/r/z",
            "/b/x",
            "/c/x",
            "/foo/child.attr",
            "/foo/foo",
            "/hit",
            "/q/b/x/y",
            "/r/a/a/b",
            "/r/a/b/a/b/c",
            "/r/x/a/b/x/c",
            "/x/hit",
            "/x/q.attr",
            "/x/tag/y",
        ])
    }

    /// A depth-first subsequence of `full`: some prims prune their whole
    /// subtree (themselves included), decided by a seeded
    /// linear-congruential counter. The absolute root always survives, so
    /// every seed yields a non-empty walk.
    fn pruned_walk(full: &[Path], seed: u64) -> Vec<Path> {
        let mut state = seed;
        let mut skip: Option<Path> = None;
        let mut out = Vec::new();
        for p in full {
            if let Some(prefix) = &skip {
                if p.has_prefix(prefix) {
                    continue;
                }
                skip = None;
            }
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            if state >> 62 == 0 && !p.is_abs_root() {
                skip = Some(p.clone());
            } else {
                out.push(p.clone());
            }
        }
        out
    }

    /// Feeds `walk` — a depth-first path sequence — to a fresh searcher,
    /// checking every step against the one-shot matcher: the values must be
    /// identical, and the searcher may add subtree constancy (C++ `_Next`
    /// prunes harder than `_Match` in places) but never lose it.
    fn check_walk(text: &str, walk: &[Path]) {
        let e = eval(text);
        let mut searcher = e.incremental_searcher(Path::clone);
        for step in walk {
            let one_shot = e.match_path(step, &Path::clone);
            let incr = searcher.next(step);
            assert_eq!(incr.value, one_shot.value, "<{text}> at <{step}>: value diverged");
            assert!(
                incr.constant || !one_shot.constant,
                "<{text}> at <{step}>: constancy lost"
            );
        }
    }

    #[test]
    fn state_pop() {
        let mut state = PatternSearchState {
            segment_match_depths: vec![1, 3, 5],
            constant: Some((4, true)),
        };
        // Matches that ended at the new depth or deeper drop, and climbing
        // to the memo's depth clears it.
        state.pop(4);
        assert_eq!(state.segment_match_depths, [1, 3]);
        assert_eq!(state.constant, None);

        // Descending below both leaves everything in place.
        let mut keep = PatternSearchState {
            segment_match_depths: vec![2],
            constant: Some((2, false)),
        };
        keep.pop(3);
        assert_eq!(keep.segment_match_depths, [2]);
        assert_eq!(keep.constant, Some((2, false)));
    }

    #[test]
    fn searcher_full_walks() {
        let walk = fixture_walk();
        for text in CORPUS {
            check_walk(text, &walk);
        }
    }

    #[test]
    fn searcher_pruned_walks() {
        let full = fixture_walk();
        for seed in 0..8 {
            let walk = pruned_walk(&full, seed);
            for text in CORPUS {
                check_walk(text, &walk);
            }
        }
    }

    #[test]
    fn searcher_zigzag() {
        // Deep chain, back to a shallow sibling, deep again: `pop` must
        // discard exactly the state below each landing depth.
        let walk = dfs_walk(&["/a/x1/q/m/n/r/z", "/b/a/x1/q/m/n/r/z", "/c/z"]);
        for text in CORPUS {
            check_walk(text, &walk);
        }
    }

    #[test]
    fn searcher_rematch_tail() {
        // The trailing `foo/bar` re-lands at every deeper occurrence.
        let walk = dfs_walk(&["/Foo/geom/foo/bar/foo/bar/foo/bar"]);
        let e = eval("//Foo//foo/bar");
        let mut searcher = e.incremental_searcher(Path::clone);
        let values: Vec<bool> = walk.iter().map(|p| searcher.next(p).value).collect();
        assert_eq!(
            values,
            [false, false, false, false, true, false, true, false, true],
            "one hit per /foo/bar tail"
        );
        check_walk("//Foo//foo/bar", &walk);
    }

    #[test]
    fn searcher_binds_prefix() {
        // Under a leading stretch, a bare predicate may bind the prefix
        // element itself — on the searcher's very first step.
        let e = eval("/foo//{name:foo}");
        let mut searcher = e.incremental_searcher(Path::clone);
        assert_eq!(searcher.next(&path("/foo").unwrap()), PredResult::varying(true));

        let miss = eval("/foo//{name:other}");
        let mut searcher = miss.incremental_searcher(Path::clone);
        assert_eq!(searcher.next(&path("/foo").unwrap()), PredResult::varying(false));
    }

    #[test]
    fn searcher_property_segments() {
        // Interior prim segments accumulate at prim visits even though a
        // property pattern can never match the prims themselves.
        let e = eval("//x//*.attr");
        let mut searcher = e.incremental_searcher(Path::clone);
        assert_eq!(searcher.next(&path("/x").unwrap()), PredResult::varying(false));
        assert_eq!(searcher.next(&path("/x/q").unwrap()), PredResult::varying(false));
        assert_eq!(searcher.next(&path("/x/q.attr").unwrap()), PredResult::varying(true));
    }

    #[test]
    fn searcher_overshoot_constant() {
        // Once a head-anchored segment can no longer consume every element,
        // the searcher prunes with a constant answer where the one-shot
        // matcher only reports varying false.
        let e = eval("/a/x*");
        let mut searcher = e.incremental_searcher(Path::clone);
        assert_eq!(searcher.next(&path("/a").unwrap()), PredResult::varying(false));
        assert_eq!(searcher.next(&path("/a/q").unwrap()), PredResult::varying(false));
        assert_eq!(searcher.next(&path("/a/q/r").unwrap()), PredResult::constant(false));
        assert_eq!(check(&e, "/a/q/r"), PredResult::varying(false));
    }

    #[test]
    fn searcher_reset() {
        let e = eval("/r//a/b//c");
        let mut searcher = e.incremental_searcher(Path::clone);
        let walk = dfs_walk(&["/r/a/b/a/b/c"]);
        let first: Vec<PredResult> = walk.iter().map(|p| searcher.next(p)).collect();
        searcher.reset();
        let second: Vec<PredResult> = walk.iter().map(|p| searcher.next(p)).collect();
        assert_eq!(first, second);
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
