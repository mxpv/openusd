//! Predicate expressions embedded in path patterns (C++
//! `SdfPredicateExpression`), the library that binds predicate names to
//! functions (C++ `SdfPredicateLibrary`), and the linked program that
//! evaluates an expression against a domain object (C++
//! `SdfPredicateProgram`).

use std::collections::HashMap;
use std::fmt;
use std::ops::Not;
use std::rc::Rc;

use anyhow::{Result, bail};

/// A logical expression of named predicate functions, as written between
/// `{` and `}` in a path pattern (`{isa:Imageable and not abstract}`).
///
/// Calls come in three spellings: bare (`defined`), colon
/// (`isa:mammal,bird` — positional arguments, comma-separated, no spaces),
/// and paren (`isClose(1.23, tolerance=0.01)` — positional then keyword
/// arguments, whitespace allowed). Operator precedence from tightest to
/// loosest: `not`, implied-and (whitespace), `and`, `or`. There are no
/// comparison operators.
///
/// A failed parse leaves the expression empty but carries the error, so it
/// compares unequal to a genuinely empty expression.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct PredicateExpression(pub(super) PredRepr);

/// The three states a predicate expression can be in; the tree stays private
/// to the module.
#[derive(Debug, Clone, PartialEq, Default)]
pub(super) enum PredRepr {
    /// The empty expression.
    #[default]
    Empty,
    /// A parsed, non-empty expression tree.
    Expr(PredNode),
    /// What a failed parse leaves behind: empty for evaluation, keeping the
    /// authored text so it survives serialization.
    Invalid { text: String, message: String },
}

/// One node of a predicate expression tree.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum PredNode {
    Call(FnCall),
    Not(Box<PredNode>),
    Op(PredOp, Box<PredNode>, Box<PredNode>),
}

/// The binary predicate operators, ordered tightest-binding first.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PredOp {
    ImpliedAnd,
    And,
    Or,
}

/// One predicate function invocation.
#[derive(Debug, Clone, PartialEq)]
pub struct FnCall {
    pub kind: FnCallKind,
    pub name: String,
    pub args: Vec<FnArg>,
}

/// How a call was spelled, which [`PredicateExpression`]'s text reproduces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnCallKind {
    /// `active`
    Bare,
    /// `isa:mammal,bird`
    Colon,
    /// `isClose(1.23, tolerance=0.01)`
    Paren,
}

/// One call argument: positional when `name` is `None`, keyword otherwise.
#[derive(Debug, Clone, PartialEq)]
pub struct FnArg {
    pub name: Option<String>,
    pub value: PredicateArg,
}

/// An argument value the predicate grammar can spell.
#[derive(Debug, Clone)]
pub enum PredicateArg {
    Bool(bool),
    Int(i64),
    Float(f64),
    String(String),
}

impl PartialEq for PredicateArg {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PredicateArg::Bool(a), PredicateArg::Bool(b)) => a == b,
            (PredicateArg::Int(a), PredicateArg::Int(b)) => a == b,
            // Bitwise, so an authorable NaN argument keeps expression — and
            // therefore `Value` — equality reflexive.
            (PredicateArg::Float(a), PredicateArg::Float(b)) => a.to_bits() == b.to_bits(),
            (PredicateArg::String(a), PredicateArg::String(b)) => a == b,
            _ => false,
        }
    }
}

/// A predicate function's answer for one domain object, carrying whether the
/// answer is known to hold for every descendant of that object (C++
/// `SdfPredicateFunctionResult`).
///
/// Constancy is what lets an enumeration prune: a constant `false` skips a
/// whole subtree, a constant `true` bulk-includes one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PredResult {
    pub value: bool,
    /// Whether `value` holds for the object and all its descendants.
    pub constant: bool,
}

/// The function a predicate call binds to, evaluated per domain object.
pub type PredicateFn<D> = Rc<dyn Fn(&D) -> PredResult>;

/// Binds one predicate name's calls to functions: given the call's arguments,
/// produce the function, or `None` when the arguments do not bind (C++
/// `SdfPredicateLibrary::DefineBinder`).
pub type PredicateBinder<D> = Rc<dyn Fn(&[FnArg]) -> Option<PredicateFn<D>>>;

/// The predicate functions available to a path expression over domain `D`
/// (C++ `SdfPredicateLibrary`).
pub struct PredicateLibrary<D> {
    binders: HashMap<String, PredicateBinder<D>>,
}

/// A predicate expression linked against a library, ready to evaluate per
/// domain object (C++ `SdfPredicateProgram`).
pub struct PredicateProgram<D> {
    ops: Vec<ProgOp>,
    funcs: Vec<PredicateFn<D>>,
}

impl<D> fmt::Debug for PredicateProgram<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The bound functions are opaque; the instruction list identifies the
        // program's shape.
        f.debug_struct("PredicateProgram").field("ops", &self.ops).finish()
    }
}

/// One linked-program instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProgOp {
    Call,
    Not,
    Open,
    Close,
    And,
    Or,
}

impl PredicateExpression {
    /// Parses `text`; see [`PredicateExpression`] for the grammar. An empty
    /// input parses to the empty expression; a malformed one to an empty
    /// expression carrying [`parse_error`](Self::parse_error).
    pub fn parse(text: &str) -> Self {
        super::parser::parse_predicate_expression(text)
    }

    /// Whether nothing was parsed — true for both the empty expression and a
    /// failed parse (which still carries its error).
    pub fn is_empty(&self) -> bool {
        !matches!(self.0, PredRepr::Expr(_))
    }

    /// The parse error, when this expression came from a malformed string.
    pub fn parse_error(&self) -> Option<&str> {
        match &self.0 {
            PredRepr::Invalid { message, .. } => Some(message),
            _ => None,
        }
    }

    fn fmt_node(node: &PredNode, parent_rank: u8, right_operand: bool, out: &mut String) {
        // A child that binds looser than its parent needs parentheses, as
        // does the right operand of an equal-rank operator (left
        // associativity).
        let rank = match node {
            PredNode::Call(_) => 0,
            PredNode::Not(_) => 1,
            PredNode::Op(PredOp::ImpliedAnd, ..) => 2,
            PredNode::Op(PredOp::And, ..) => 3,
            PredNode::Op(PredOp::Or, ..) => 4,
        };
        let parenthesize = rank > parent_rank || (rank == parent_rank && right_operand);
        if parenthesize {
            out.push('(');
        }
        match node {
            PredNode::Call(call) => out.push_str(&call.to_string()),
            PredNode::Not(inner) => {
                out.push_str("not ");
                Self::fmt_node(inner, rank, false, out);
            }
            PredNode::Op(op, left, right) => {
                Self::fmt_node(left, rank, false, out);
                out.push_str(match op {
                    PredOp::ImpliedAnd => " ",
                    PredOp::And => " and ",
                    PredOp::Or => " or ",
                });
                Self::fmt_node(right, rank, true, out);
            }
        }
        if parenthesize {
            out.push(')');
        }
    }
}

impl fmt::Display for PredicateExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            PredRepr::Empty => Ok(()),
            PredRepr::Expr(root) => {
                let mut out = String::new();
                Self::fmt_node(root, u8::MAX, false, &mut out);
                f.write_str(&out)
            }
            PredRepr::Invalid { text, .. } => f.write_str(text),
        }
    }
}

impl fmt::Display for FnCall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.name)?;
        match self.kind {
            FnCallKind::Bare => Ok(()),
            FnCallKind::Colon => {
                for (i, arg) in self.args.iter().enumerate() {
                    f.write_str(if i == 0 { ":" } else { "," })?;
                    write!(f, "{}", arg.value)?;
                }
                Ok(())
            }
            FnCallKind::Paren => {
                f.write_str("(")?;
                for (i, arg) in self.args.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    if let Some(name) = &arg.name {
                        write!(f, "{name}=")?;
                    }
                    write!(f, "{}", arg.value)?;
                }
                f.write_str(")")
            }
        }
    }
}

impl fmt::Display for PredicateArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PredicateArg::Bool(b) => write!(f, "{b}"),
            PredicateArg::Int(i) => write!(f, "{i}"),
            // An integral float keeps a fractional digit so it re-reads as a
            // float rather than collapsing to an integer.
            PredicateArg::Float(x) if x.is_finite() && x.fract() == 0.0 => write!(f, "{x:.1}"),
            PredicateArg::Float(x) => write!(f, "{x}"),
            // A string that could not be re-read as a bare token is quoted.
            PredicateArg::String(s) => {
                if super::parser::is_bare_argument_token(s) {
                    f.write_str(s)
                } else {
                    write!(f, "\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
                }
            }
        }
    }
}

impl PredicateArg {
    /// The value as a string, accepting only the string spelling.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            PredicateArg::String(s) => Some(s),
            _ => None,
        }
    }

    /// The value read as a boolean: `true`/`false`, a nonzero integer, or a
    /// string starting with `1`, `y`, or `Y` (the lenient C++ `strict`
    /// convention).
    pub fn as_flag(&self) -> Option<bool> {
        match self {
            PredicateArg::Bool(b) => Some(*b),
            PredicateArg::Int(i) => Some(*i != 0),
            PredicateArg::String(s) => Some(matches!(s.chars().next(), Some('1' | 'y' | 'Y'))),
            PredicateArg::Float(_) => None,
        }
    }
}

impl PredResult {
    /// A result that holds for the object and its whole subtree.
    pub fn constant(value: bool) -> Self {
        PredResult { value, constant: true }
    }

    /// A result that may differ on descendants.
    pub fn varying(value: bool) -> Self {
        PredResult { value, constant: false }
    }

    /// Conjunction: constant when both sides are, or when the deciding
    /// (false) side is.
    pub fn and(self, other: PredResult) -> PredResult {
        let left_decides = !self.value && self.constant;
        let right_decides = !other.value && other.constant;
        PredResult {
            value: self.value && other.value,
            constant: (self.constant && other.constant) || left_decides || right_decides,
        }
    }

    /// Disjunction: constant when both sides are, or when the deciding
    /// (true) side is.
    pub fn or(self, other: PredResult) -> PredResult {
        let left_decides = self.value && self.constant;
        let right_decides = other.value && other.constant;
        PredResult {
            value: self.value || other.value,
            constant: (self.constant && other.constant) || left_decides || right_decides,
        }
    }

    /// Takes `other`'s value, downgrading to varying when `other` varies.
    fn set_and_propagate(&mut self, other: PredResult) {
        self.value = other.value;
        self.constant &= other.constant;
    }
}

impl Not for PredResult {
    type Output = PredResult;

    /// Negation preserves constancy: a subtree-wide answer stays subtree-wide.
    fn not(self) -> PredResult {
        PredResult {
            value: !self.value,
            constant: self.constant,
        }
    }
}

impl<D> Default for PredicateLibrary<D> {
    fn default() -> Self {
        PredicateLibrary {
            binders: HashMap::new(),
        }
    }
}

impl<D> PredicateLibrary<D> {
    /// Starts an empty library.
    pub fn new() -> Self {
        Self::default()
    }

    /// Registers the binder for predicate `name`, replacing any prior one.
    pub fn define(
        mut self,
        name: impl Into<String>,
        binder: impl Fn(&[FnArg]) -> Option<PredicateFn<D>> + 'static,
    ) -> Self {
        self.binders.insert(name.into(), Rc::new(binder));
        self
    }

    /// Binds one call to its function. An unknown name or arguments the
    /// binder rejects are errors.
    fn bind(&self, call: &FnCall) -> Result<PredicateFn<D>> {
        let Some(binder) = self.binders.get(&call.name) else {
            bail!("No registered predicate function '{}'", call.name);
        };
        match binder(&call.args) {
            Some(function) => Ok(function),
            None => bail!("Invalid arguments to predicate function '{}'", call.name),
        }
    }
}

/// Links `expr` against `library`, binding every call (C++
/// `SdfLinkPredicateExpression`). An empty expression links to an empty
/// program, which evaluates to a constant `false`.
pub fn link_predicate_expression<D>(
    expr: &PredicateExpression,
    library: &PredicateLibrary<D>,
) -> Result<PredicateProgram<D>> {
    let mut program = PredicateProgram {
        ops: Vec::new(),
        funcs: Vec::new(),
    };
    if let PredRepr::Expr(root) = &expr.0 {
        link_node(root, library, &mut program)?;
    }
    Ok(program)
}

/// Emits `node`'s instructions: calls in leftmost order, `Not` postfix, and
/// each binary operator between its operands with its right operand fenced by
/// `Open`/`Close` so evaluation can skip it.
fn link_node<D>(node: &PredNode, library: &PredicateLibrary<D>, program: &mut PredicateProgram<D>) -> Result<()> {
    match node {
        PredNode::Call(call) => {
            program.funcs.push(library.bind(call)?);
            program.ops.push(ProgOp::Call);
        }
        PredNode::Not(inner) => {
            link_node(inner, library, program)?;
            program.ops.push(ProgOp::Not);
        }
        PredNode::Op(op, left, right) => {
            link_node(left, library, program)?;
            program.ops.push(match op {
                PredOp::ImpliedAnd | PredOp::And => ProgOp::And,
                PredOp::Or => ProgOp::Or,
            });
            program.ops.push(ProgOp::Open);
            link_node(right, library, program)?;
            program.ops.push(ProgOp::Close);
        }
    }
    Ok(())
}

impl<D> PredicateProgram<D> {
    /// Whether the program has no instructions (an empty expression).
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    /// Evaluates the program for one domain object.
    ///
    /// Short-circuits when an operand decides an `and`/`or`, skipping the
    /// fenced right operand entirely; a skipped operand contributes neither
    /// value nor constancy, which is sound because a deciding operand's
    /// constancy alone bounds the combined result.
    pub fn eval(&self, obj: &D) -> PredResult {
        let mut result = PredResult::constant(false);
        let mut func = 0;
        let mut op = 0;
        while op < self.ops.len() {
            match self.ops[op] {
                ProgOp::Call => {
                    result.set_and_propagate(self.funcs[func](obj));
                    func += 1;
                }
                ProgOp::Not => result = !result,
                ProgOp::And | ProgOp::Or => {
                    let deciding = self.ops[op] != ProgOp::And;
                    if result.value == deciding {
                        // Skip the fenced right operand, keeping the function
                        // cursor in step with the skipped calls.
                        let mut depth = 0usize;
                        op += 1;
                        loop {
                            match self.ops[op] {
                                ProgOp::Open => depth += 1,
                                ProgOp::Close => {
                                    depth -= 1;
                                    if depth == 0 {
                                        break;
                                    }
                                }
                                ProgOp::Call => func += 1,
                                _ => {}
                            }
                            op += 1;
                        }
                    }
                }
                ProgOp::Open | ProgOp::Close => {}
            }
            op += 1;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn call(name: &str) -> PredNode {
        PredNode::Call(FnCall {
            kind: FnCallKind::Bare,
            name: name.to_string(),
            args: Vec::new(),
        })
    }

    #[test]
    fn float_arg_nan_eq() {
        // Bitwise comparison keeps argument equality reflexive: a call
        // carrying NaN still equals itself.
        assert_eq!(PredicateArg::Float(f64::NAN), PredicateArg::Float(f64::NAN));
        assert_ne!(PredicateArg::Float(0.0), PredicateArg::Float(f64::NAN));
    }

    fn library() -> PredicateLibrary<bool> {
        // Domain: the object itself is the answer for `yes`; `no` is fixed.
        PredicateLibrary::new()
            .define("yes", |_| Some(Rc::new(|obj: &bool| PredResult::constant(*obj))))
            .define("no", |_| Some(Rc::new(|_: &bool| PredResult::constant(false))))
            .define("varying", |_| Some(Rc::new(|obj: &bool| PredResult::varying(*obj))))
    }

    fn eval(text: &str, obj: bool) -> PredResult {
        let expr = PredicateExpression::parse(text);
        assert!(expr.parse_error().is_none(), "{text}: {:?}", expr.parse_error());
        link_predicate_expression(&expr, &library()).expect("links").eval(&obj)
    }

    #[test]
    fn result_combinators() {
        let ct = PredResult::constant(true);
        let cf = PredResult::constant(false);
        let vt = PredResult::varying(true);
        let vf = PredResult::varying(false);

        // The deciding side's constancy carries the combination.
        assert_eq!(cf.and(vt), PredResult::constant(false));
        assert_eq!(vt.and(cf), PredResult::constant(false));
        assert_eq!(ct.or(vf), PredResult::constant(true));
        assert_eq!(vf.or(ct), PredResult::constant(true));
        // Otherwise both sides must be constant.
        assert_eq!(vt.and(ct), PredResult::varying(true));
        assert_eq!(ct.and(ct), PredResult::constant(true));
        assert_eq!(vf.or(vf), PredResult::varying(false));
        // Negation preserves constancy.
        assert_eq!(!ct, PredResult::constant(false));
        assert_eq!(!vf, PredResult::varying(true));
    }

    #[test]
    fn program_logic() {
        assert!(eval("yes", true).value);
        assert!(!eval("yes", false).value);
        assert!(!eval("not yes", true).value);
        assert!(!eval("yes and no", true).value);
        assert!(eval("yes or no", true).value);
        assert!(eval("no or yes", true).value);
        assert!(eval("yes no or yes", true).value, "implied-and binds tighter than or");
        assert!(!eval("not (yes or no)", true).value);
    }

    #[test]
    fn program_short_circuit_constancy() {
        // A deciding constant false through `and` stays constant even though
        // the skipped side varies.
        assert_eq!(eval("no and varying", true), PredResult::constant(false));
        // A non-deciding constant followed by a varying side downgrades.
        assert_eq!(eval("yes and varying", true), PredResult::varying(true));
    }

    #[test]
    fn empty_program_false() {
        let program = link_predicate_expression(&PredicateExpression::default(), &library()).expect("links");
        assert!(program.is_empty());
        assert_eq!(program.eval(&true), PredResult::constant(false));
    }

    #[test]
    fn unknown_predicate_rejected() {
        let expr = PredicateExpression::parse("bogus");
        let error = link_predicate_expression(&expr, &library()).expect_err("unknown name");
        assert!(error.to_string().contains("bogus"), "{error}");
    }

    #[test]
    fn display_parenthesizes() {
        let a = call("a");
        let b = call("b");
        let c = call("c");
        // (a or b) and c — the looser child of a tighter parent parenthesizes.
        let expr = PredicateExpression(PredRepr::Expr(PredNode::Op(
            PredOp::And,
            Box::new(PredNode::Op(PredOp::Or, Box::new(a), Box::new(b))),
            Box::new(c),
        )));
        assert_eq!(expr.to_string(), "(a or b) and c");
    }
}
