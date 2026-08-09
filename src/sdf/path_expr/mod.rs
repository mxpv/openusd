//! Path expressions (C++ `SdfPathExpression`): a set-algebra over path
//! patterns and collection references, the value type behind pattern-based
//! collection membership.
//!
//! An expression combines [`PathPattern`] atoms and [`ExpressionReference`]
//! atoms with `+` (union), `&` (intersection), `-` (difference), `~`
//! (complement), and whitespace (implied union), as in
//! `/World//Robot* + %/Sets:big - //{isa:Camera}`. Expressions compose across
//! opinion strength through the special weaker reference `%_`, which
//! [`PathExpression::compose_over`] substitutes with the next-weaker
//! expression.
//!
//! Parsing never fails a caller: a malformed string becomes the empty
//! expression carrying [`parse_error`](PathExpression::parse_error), which
//! keeps it distinguishable from a genuinely empty one. This module owns the
//! data model and its algebra; matching is [`PathExpressionEval`]'s job,
//! after references are resolved and paths anchored.

mod eval;
mod glob;
mod parser;
mod pattern;
mod predicate;

use std::fmt;
use std::str::FromStr;

use crate::sdf::Path;

pub use eval::{IncrementalSearcher, PathExpressionEval};
pub use glob::GlobPattern;
pub use pattern::{Component, PathPattern};
pub use predicate::{
    link_predicate_expression, FnArg, FnCall, FnCallKind, PredResult, PredicateArg, PredicateBinder,
    PredicateExpression, PredicateFn, PredicateLibrary, PredicateProgram,
};

/// A parsed path expression; see the [module docs](self) for the syntax.
///
/// The empty expression ([`nothing`](Self::nothing)) matches no paths.
/// Equality covers the parse error, so an expression built from a malformed
/// string never equals `nothing()` even though both are
/// [`is_empty`](Self::is_empty); in the expression algebra a failed parse
/// participates as the empty expression, dropping its error. Its *display*
/// keeps the authored text, so a rejected opinion survives serialization
/// round trips.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct PathExpression(Repr);

/// The three states an expression can be in. The tree stays private to the
/// module, so the wrapper is what the crate surface sees.
#[derive(Debug, Clone, PartialEq, Default)]
enum Repr {
    /// The empty expression.
    #[default]
    Nothing,
    /// A parsed, non-empty expression tree.
    Expr(ExprNode),
    /// What a failed parse leaves behind: empty for evaluation, but keeping
    /// the authored text so serializing the value back out preserves the
    /// opinion instead of erasing it.
    Invalid { text: String, message: String },
}

/// One node of the expression tree.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ExprNode {
    Pattern(PathPattern),
    Reference(ExpressionReference),
    Complement(Box<ExprNode>),
    Op(SetOp, Box<ExprNode>, Box<ExprNode>),
}

/// One atom handed to [`PathExpression::map_atoms`]'s mapper.
enum Atom {
    Pattern(PathPattern),
    Reference(ExpressionReference),
}

/// The binary set operators, ordered tightest-binding first. All are
/// left-associative; note `-` binds loosest of all.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SetOp {
    /// Two expressions joined by whitespace.
    ImpliedUnion,
    /// `+`
    Union,
    /// `&`
    Intersection,
    /// `-`
    Difference,
}

/// A reference to another expression (C++
/// `SdfPathExpression::ExpressionReference`).
///
/// `%/World/Sets:big` names the collection `big` on `/World/Sets`; `%:big`
/// names one on the prim the expression itself lives on (empty `path`); and
/// the special weaker reference `%_` (empty `path`, name `_`) stands for the
/// next-weaker opinion's expression during composition.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ExpressionReference {
    /// The referenced prim, empty for `%_` and `%:name`.
    pub path: Path,
    /// The collection name, or `_` for the weaker reference.
    pub name: String,
}

impl ExpressionReference {
    /// The weaker reference `%_`.
    pub fn weaker() -> Self {
        ExpressionReference {
            path: Path::default(),
            name: "_".to_string(),
        }
    }

    /// Whether this is the weaker reference.
    pub fn is_weaker(&self) -> bool {
        self.path.is_empty() && self.name == "_"
    }
}

impl PathExpression {
    /// Parses `text`. An empty string parses to [`nothing`](Self::nothing);
    /// a malformed one to an empty expression carrying
    /// [`parse_error`](Self::parse_error).
    pub fn parse(text: &str) -> Self {
        if text.is_empty() {
            return Self::nothing();
        }
        parser::parse_path_expression(text)
    }

    /// The expression matching every path: `//`.
    pub fn everything() -> Self {
        Self::make_atom_pattern(PathPattern::everything())
    }

    /// The expression matching every path descendant to an anchor: `.//`.
    pub fn every_descendant() -> Self {
        Self::make_atom_pattern(PathPattern::every_descendant())
    }

    /// The empty expression, matching nothing.
    pub fn nothing() -> Self {
        Self::default()
    }

    /// An expression of one pattern.
    pub fn make_atom_pattern(pattern: PathPattern) -> Self {
        PathExpression(Repr::Expr(ExprNode::Pattern(pattern)))
    }

    /// An expression of one reference.
    pub fn make_atom_reference(reference: ExpressionReference) -> Self {
        PathExpression(Repr::Expr(ExprNode::Reference(reference)))
    }

    /// What a failed parse leaves behind: an empty expression carrying the
    /// error and the authored text.
    fn invalid(text: String, message: String) -> Self {
        PathExpression(Repr::Invalid { text, message })
    }

    /// The complement of `expr`, simplifying against the constants:
    /// `~Everything` is `Nothing`, `~Nothing` is `Everything`, and a double
    /// complement cancels.
    pub fn make_complement(expr: PathExpression) -> Self {
        if expr == Self::everything() {
            return Self::nothing();
        }
        match expr.0 {
            Repr::Nothing | Repr::Invalid { .. } => Self::everything(),
            Repr::Expr(ExprNode::Complement(inner)) => PathExpression(Repr::Expr(*inner)),
            Repr::Expr(node) => PathExpression(Repr::Expr(ExprNode::Complement(Box::new(node)))),
        }
    }

    /// Combines two expressions, absorbing the constants: an empty operand
    /// (`Nothing`, or a failed parse) is the identity of the unions and
    /// annihilates intersections, `Everything` the reverse, and a difference
    /// against either constant rewrites to an intersection with a complement
    /// first.
    pub fn make_op(op: SetOp, left: PathExpression, right: PathExpression) -> Self {
        let mut op = op;
        let mut right = right;
        let is_constant = |e: &PathExpression| e.is_empty() || *e == Self::everything();
        if op == SetOp::Difference && (is_constant(&left) || is_constant(&right)) {
            op = SetOp::Intersection;
            right = Self::make_complement(right);
        }

        if left.is_empty() {
            return if op == SetOp::Intersection {
                Self::nothing()
            } else {
                right
            };
        }
        if right.is_empty() {
            return if op == SetOp::Intersection {
                Self::nothing()
            } else {
                left
            };
        }
        if left == Self::everything() {
            return if op == SetOp::Intersection {
                right
            } else {
                Self::everything()
            };
        }
        if right == Self::everything() {
            return if op == SetOp::Intersection {
                left
            } else {
                Self::everything()
            };
        }

        match (left.0, right.0) {
            (Repr::Expr(left), Repr::Expr(right)) => {
                PathExpression(Repr::Expr(ExprNode::Op(op, Box::new(left), Box::new(right))))
            }
            _ => unreachable!("empty operands were absorbed above"),
        }
    }

    /// Whether nothing was parsed — true for both [`nothing`](Self::nothing)
    /// and a failed parse (which still carries its error).
    pub fn is_empty(&self) -> bool {
        !matches!(self.0, Repr::Expr(_))
    }

    /// The parse error, when this expression came from a malformed string.
    pub fn parse_error(&self) -> Option<&str> {
        match &self.0 {
            Repr::Invalid { message, .. } => Some(message),
            _ => None,
        }
    }

    /// Whether any expression reference remains.
    pub fn contains_expression_references(&self) -> bool {
        self.any_reference(|_| true)
    }

    /// Whether the weaker reference `%_` remains, so composition still has
    /// an opinion slot to fill.
    pub fn contains_weaker_reference(&self) -> bool {
        self.any_reference(ExpressionReference::is_weaker)
    }

    /// Whether every pattern prefix and non-empty reference path is absolute.
    pub fn is_absolute(&self) -> bool {
        !self.any_atom(
            |pattern| !pattern.prefix().is_abs(),
            |reference| !reference.path.is_empty() && !reference.path.is_abs(),
        )
    }

    /// Whether the expression can be evaluated as-is: no references remain
    /// and everything is absolute.
    pub fn is_complete(&self) -> bool {
        !self.contains_expression_references() && self.is_absolute()
    }

    /// Anchors every relative pattern prefix and reference path to `anchor`.
    /// The empty reference paths of `%_` and `%:name` stay empty — they are
    /// resolved by name, not by path.
    pub fn make_absolute(self, anchor: &Path) -> Self {
        self.map_atoms(&mut |atom| match atom {
            Atom::Pattern(mut pattern) => {
                pattern.set_prefix(anchor_path(anchor, pattern.prefix()));
                Self::make_atom_pattern(pattern)
            }
            Atom::Reference(mut reference) => {
                if !reference.path.is_empty() && !reference.path.is_abs() {
                    reference.path = anchor.make_absolute(&reference.path);
                }
                Self::make_atom_reference(reference)
            }
        })
    }

    /// Rewrites every pattern prefix and reference path with `f`, replacing
    /// an atom whose path `f` refuses with [`nothing`](Self::nothing) — the
    /// shape namespace mapping across composition arcs needs, where an
    /// unmappable path has no meaning in the target namespace.
    pub fn map_paths(self, mut f: impl FnMut(&Path) -> Option<Path>) -> Self {
        self.map_atoms(&mut |atom| match atom {
            Atom::Pattern(mut pattern) => match f(pattern.prefix()) {
                Some(mapped) => {
                    pattern.set_prefix(mapped);
                    Self::make_atom_pattern(pattern)
                }
                None => Self::nothing(),
            },
            Atom::Reference(mut reference) => {
                if reference.path.is_empty() {
                    return Self::make_atom_reference(reference);
                }
                match f(&reference.path) {
                    Some(mapped) => {
                        reference.path = mapped;
                        Self::make_atom_reference(reference)
                    }
                    None => Self::nothing(),
                }
            }
        })
    }

    /// Replaces the `old` path prefix with `new` in every atom it prefixes;
    /// atoms elsewhere in the namespace are left alone (C++
    /// `SdfPathExpression::ReplacePrefix`).
    pub fn replace_prefix(self, old: &Path, new: &Path) -> Self {
        self.map_atoms(&mut |atom| match atom {
            Atom::Pattern(mut pattern) => {
                if let Some(replaced) = pattern
                    .prefix()
                    .has_prefix(old)
                    .then(|| pattern.prefix().replace_prefix(old, new))
                    .flatten()
                {
                    pattern.set_prefix(replaced);
                }
                Self::make_atom_pattern(pattern)
            }
            Atom::Reference(mut reference) => {
                if let Some(replaced) = reference
                    .path
                    .has_prefix(old)
                    .then(|| reference.path.replace_prefix(old, new))
                    .flatten()
                {
                    reference.path = replaced;
                }
                Self::make_atom_reference(reference)
            }
        })
    }

    /// Substitutes every reference with `resolve`'s expression, rebuilding
    /// through the constructor algebra so a substituted
    /// [`nothing`](Self::nothing) collapses its surroundings.
    pub fn resolve_references(self, resolve: &mut impl FnMut(&ExpressionReference) -> PathExpression) -> Self {
        self.map_atoms(&mut |atom| match atom {
            Atom::Pattern(pattern) => Self::make_atom_pattern(pattern),
            Atom::Reference(reference) => resolve(&reference),
        })
    }

    /// Composes this expression over the next-weaker one: every `%_` becomes
    /// `weaker`. The empty expression stays empty — an absent opinion has no
    /// slot for a weaker one.
    pub fn compose_over(self, weaker: &PathExpression) -> Self {
        if self.is_empty() {
            return self;
        }
        self.resolve_references(&mut |reference| {
            if reference.is_weaker() {
                weaker.clone()
            } else {
                Self::make_atom_reference(reference.clone())
            }
        })
    }

    /// Whether any reference satisfies `wanted`.
    fn any_reference(&self, wanted: impl Fn(&ExpressionReference) -> bool) -> bool {
        self.any_atom(|_| false, wanted)
    }

    /// Whether any atom satisfies its visitor.
    fn any_atom(
        &self,
        pattern: impl Fn(&PathPattern) -> bool,
        reference: impl Fn(&ExpressionReference) -> bool,
    ) -> bool {
        fn walk(
            node: &ExprNode,
            pattern: &impl Fn(&PathPattern) -> bool,
            reference: &impl Fn(&ExpressionReference) -> bool,
        ) -> bool {
            match node {
                ExprNode::Pattern(p) => pattern(p),
                ExprNode::Reference(r) => reference(r),
                ExprNode::Complement(inner) => walk(inner, pattern, reference),
                ExprNode::Op(_, left, right) => walk(left, pattern, reference) || walk(right, pattern, reference),
            }
        }
        match &self.0 {
            Repr::Expr(root) => walk(root, &pattern, &reference),
            _ => false,
        }
    }

    /// Rebuilds the tree with each atom mapped to a replacement expression.
    /// Rebuilding runs through the constructor algebra, so a substituted
    /// constant collapses its surroundings.
    fn map_atoms(self, f: &mut impl FnMut(Atom) -> PathExpression) -> Self {
        fn rebuild(node: ExprNode, f: &mut impl FnMut(Atom) -> PathExpression) -> PathExpression {
            match node {
                ExprNode::Pattern(pattern) => f(Atom::Pattern(pattern)),
                ExprNode::Reference(reference) => f(Atom::Reference(reference)),
                ExprNode::Complement(inner) => PathExpression::make_complement(rebuild(*inner, f)),
                ExprNode::Op(op, left, right) => PathExpression::make_op(op, rebuild(*left, f), rebuild(*right, f)),
            }
        }
        let Repr::Expr(root) = self.0 else {
            return self;
        };
        rebuild(root, f)
    }

    /// The expression tree, for the evaluator's walk.
    pub(super) fn root(&self) -> Option<&ExprNode> {
        match &self.0 {
            Repr::Expr(root) => Some(root),
            _ => None,
        }
    }

    fn fmt_node(node: &ExprNode, parent_rank: u8, right_operand: bool, out: &mut String) {
        // A child that binds looser than its parent parenthesizes, as does
        // the right operand of an equal-rank operator (left associativity).
        let rank = match node {
            ExprNode::Pattern(_) | ExprNode::Reference(_) => 0,
            ExprNode::Complement(_) => 1,
            ExprNode::Op(SetOp::ImpliedUnion, ..) => 2,
            ExprNode::Op(SetOp::Union, ..) => 3,
            ExprNode::Op(SetOp::Intersection, ..) => 4,
            ExprNode::Op(SetOp::Difference, ..) => 5,
        };
        let parenthesize = rank > parent_rank || (rank == parent_rank && right_operand);
        if parenthesize {
            out.push('(');
        }
        match node {
            ExprNode::Pattern(pattern) => out.push_str(&pattern.to_string()),
            ExprNode::Reference(reference) => {
                out.push('%');
                out.push_str(reference.path.as_str());
                // Only the true weaker reference drops the colon; a named
                // collection that happens to be called `_` keeps it, so the
                // text re-parses as the same reference.
                if reference.is_weaker() {
                    out.push('_');
                } else {
                    out.push(':');
                    out.push_str(&reference.name);
                }
            }
            ExprNode::Complement(inner) => {
                out.push('~');
                Self::fmt_node(inner, rank, false, out);
            }
            ExprNode::Op(op, left, right) => {
                Self::fmt_node(left, rank, false, out);
                out.push_str(match op {
                    SetOp::ImpliedUnion => " ",
                    SetOp::Union => " + ",
                    SetOp::Intersection => " & ",
                    SetOp::Difference => " - ",
                });
                Self::fmt_node(right, rank, true, out);
            }
        }
        if parenthesize {
            out.push(')');
        }
    }
}

impl fmt::Display for PathExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Repr::Nothing => Ok(()),
            Repr::Expr(root) => {
                let mut out = String::new();
                Self::fmt_node(root, u8::MAX, false, &mut out);
                f.write_str(&out)
            }
            // Printing the authored text keeps a rejected opinion intact
            // across a load/save round trip rather than erasing it.
            Repr::Invalid { text, .. } => f.write_str(text),
        }
    }
}

impl FromStr for PathExpression {
    type Err = std::convert::Infallible;

    /// Parsing never fails the caller; a malformed string yields an empty
    /// expression carrying [`parse_error`](PathExpression::parse_error).
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(PathExpression::parse(s))
    }
}

/// Anchors one pattern prefix: the reflexive `.` becomes the anchor itself,
/// other relative prefixes resolve against it, absolute ones pass through.
fn anchor_path(anchor: &Path, prefix: &Path) -> Path {
    if prefix.is_abs() {
        return prefix.clone();
    }
    if prefix.as_str() == "." {
        return anchor.clone();
    }
    anchor.make_absolute(prefix)
}
