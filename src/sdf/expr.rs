//! Variable expression tokenizer, parser, and evaluator (C++
//! `SdfVariableExpression`).
//!
//! Implements USD variable expressions as described in:
//! <https://openusd.org/dev/user_guides/variable_expressions.html>
//!
//! Expressions are strings enclosed in backticks that are evaluated at runtime
//! to produce a final value. They support variable substitution, function
//! calls, and various literal types. Composing the `expressionVariables` an
//! expression evaluates against across composition arcs is a separate,
//! `pcp`-level concern (C++ `PcpExpressionVariables`).
//!
//! Evaluation ([`Expr::evaluate`]) mirrors the C++ evaluator: a variable whose
//! value is itself a backtick expression is parsed and evaluated recursively
//! in the same context (with a cycle guard), errors aggregate across list
//! elements and function arguments rather than short-circuiting, and every
//! result reports the set of variables the evaluation requested
//! ([`Evaluation::used_variables`]) — including referenced-but-undefined
//! names — so change processing can map a variable edit to the expressions it
//! affects. `matches_regex` patterns use Rust regex syntax (`regex-lite`)
//! where C++ uses POSIX extended regular expressions; see
//! [`Func::MatchesRegex`].
//!
//! # Example
//!
//! ```
//! use openusd::sdf::expr::Expr;
//!
//! let expr: Expr = r#"if(${USE_HIGH_RES}, "high", "low")"#.parse().unwrap();
//! ```

use crate::sdf;
use anyhow::{anyhow, bail, ensure, Result};
use logos::{Logos, SpannedIter};
use regex_lite::Regex;
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::iter::Peekable;
use std::mem;
use std::slice;
use std::str::FromStr;
use strum::{Display, EnumString};

/// Returns `true` if the string is a variable expression: backtick-delimited
/// with a non-empty body (C++ `Sdf_IsVariableExpression`).
pub fn is_expression(s: &str) -> bool {
    s.len() > 2 && s.starts_with('`') && s.ends_with('`')
}

/// Reads a layer's pseudo-root `expressionVariables` dictionary, borrowing it
/// from `data` when the backing store holds it directly (the common in-memory
/// case) and only owning an empty map when the field is absent or not a
/// dictionary. Composing these variables across reference/payload arcs is a
/// `pcp`-level concern (C++ `PcpExpressionVariables`); this is the single
/// per-layer read both layer collection and arc composition share, overlaid
/// with [`compose_over`].
pub fn read_expression_variables(data: &dyn sdf::AbstractData) -> Result<Cow<'_, HashMap<String, sdf::Value>>> {
    let root = sdf::Path::abs_root();
    Ok(
        match data.try_field(&root, sdf::FieldKey::ExpressionVariables.as_str())? {
            Some(Cow::Borrowed(sdf::Value::Dictionary(dict))) => Cow::Borrowed(dict),
            Some(Cow::Owned(sdf::Value::Dictionary(dict))) => Cow::Owned(dict),
            _ => Cow::Owned(HashMap::new()),
        },
    )
}

/// Overlays `overlay`'s expression variables onto `base`, the overlay winning on
/// a key collision — the precedence both layer collection and arc composition
/// need, where the closer-to-root (or stronger) opinion is applied last (C++
/// `PcpExpressionVariables`). Each entry is cloned, since `overlay` is borrowed.
pub fn compose_over(base: &mut HashMap<String, sdf::Value>, overlay: &HashMap<String, sdf::Value>) {
    base.extend(overlay.iter().map(|(k, v)| (k.clone(), v.clone())));
}

/// A layer stack's composed expression variables (C++ `PcpExpressionVariables`):
/// the stack **root** layer's own `expressionVariables` overlaid by `overrides`,
/// the overrides winning on a key collision. `overrides` is the session root
/// layer's own variables for the root stage stack, or a reference/payload arc's
/// inherited overrides for a referenced stack. This is the single set every
/// `${VAR}` sublayer path, reference/payload asset path, and value-time asset
/// attribute in the stack resolves against; sublayers of the root contribute
/// nothing — matching C++, and avoiding the bootstrapping cycle where a sublayer's
/// variable would be needed to resolve the `${VAR}` that pulled it in.
///
/// Parity note: this models the directly-authored `expressionVariables` subset.
/// C++'s `PcpExpressionVariablesSource` / override-source dependency mechanics are
/// not modeled.
///
/// Propagates a backend read error on the root layer's `expressionVariables`
/// field so the loader aborts a corrupt open rather than silently composing
/// against empty variables (which would drop every `${VAR}`-dependent sublayer and
/// reference). Pure-composition callers reading an already-loaded layer discard the
/// error — the loader already validated the read at open time.
pub fn stack_expression_variables(
    root_data: &dyn sdf::AbstractData,
    overrides: &HashMap<String, sdf::Value>,
) -> Result<HashMap<String, sdf::Value>> {
    let mut vars = read_expression_variables(root_data)?.into_owned();
    compose_over(&mut vars, overrides);
    Ok(vars)
}

/// Evaluates a string-valued expression against `vars`, or passes the string
/// through unchanged when it is not a backtick expression. This is the shape
/// every string-carrying composition field shares (C++
/// `Pcp_EvaluateVariableExpression`): reference/payload asset paths, sublayer
/// paths, and variant selections all evaluate their authored value this way.
/// A non-string result is an error; the expression-language `None` yields
/// [`StringEvaluation::value`] `None` with no errors, which callers skip
/// silently.
pub fn evaluate_string(s: &str, vars: &HashMap<String, sdf::Value>) -> StringEvaluation {
    if !is_expression(s) {
        return StringEvaluation {
            value: Some(s.to_string()),
            errors: Vec::new(),
            used_variables: HashSet::new(),
        };
    }
    // TODO(perf): every call re-parses the expression, once per consuming
    // composition arc per prim-index build; a parse memo keyed by the authored
    // string (or a pcp-level `(string, context)` evaluation memo) would
    // evaluate each distinct expression once.
    let expr = match Expr::parse(s) {
        Ok(expr) => expr,
        Err(err) => {
            return StringEvaluation {
                value: None,
                errors: vec![format!("{err:#}")],
                used_variables: HashSet::new(),
            }
        }
    };
    let Evaluation {
        value,
        mut errors,
        used_variables,
    } = expr.evaluate(vars);
    let value = match value {
        Some(EvaluationValue::Value(sdf::Value::String(s))) => Some(s),
        None => None,
        Some(other) => {
            errors.push(format!(
                "Expression evaluated to '{}' but expected 'string'",
                result_type_name(&Some(other))
            ));
            None
        }
    };
    StringEvaluation {
        value,
        errors,
        used_variables,
    }
}

/// The result of evaluating an expression (C++
/// `SdfVariableExpression::Result`), returned by [`Expr::evaluate`].
#[derive(Debug, Clone, PartialEq)]
pub struct Evaluation {
    /// The evaluated value, or `None` when the expression produced the
    /// expression-language `None` or evaluation failed (in which case
    /// [`errors`](Self::errors) is non-empty).
    pub value: Option<EvaluationValue>,
    /// Errors encountered while evaluating the expression.
    pub errors: Vec<String>,
    /// Every variable name the evaluation requested, recorded before lookup,
    /// so the set includes referenced-but-undefined names and names requested
    /// by recursively evaluated sub-expressions. Also includes
    /// `defined()`-checked names (which C++ leaves out): the check is a
    /// dependency, so change processing must see it to know a variable edit
    /// can flip the result. Populated even when evaluation fails.
    pub used_variables: HashSet<String>,
}

/// A successfully evaluated expression value.
#[derive(Debug, Clone, PartialEq)]
pub enum EvaluationValue {
    /// A typed value: `String`, `Int64`, `Bool`, or one of their list types
    /// (`StringVec`, `Int64Vec`, `BoolVec`).
    Value(sdf::Value),
    /// The untyped empty list `[]` (C++ `SdfVariableExpression::EmptyList`):
    /// the expression language has no syntax naming an empty list's element
    /// type, so it is not representable as a typed `sdf::Value` vector —
    /// a caller converting it to one chooses the coercion explicitly.
    EmptyList,
}

/// The result of evaluating a string-valued expression via
/// [`evaluate_string`].
#[derive(Debug, Clone, PartialEq)]
pub struct StringEvaluation {
    /// The evaluated string (the input unchanged when it is not an
    /// expression), or `None` when evaluation failed —
    /// [`errors`](Self::errors) is then non-empty — or produced the
    /// expression-language `None`, which carries no errors and which callers
    /// skip silently.
    pub value: Option<String>,
    /// Errors encountered while parsing or evaluating the expression.
    pub errors: Vec<String>,
    /// See [`Evaluation::used_variables`]; empty for a non-expression.
    pub used_variables: HashSet<String>,
}

/// Tokens for USD variable expressions.
#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\n\f]+")]
pub enum Token<'source> {
    /// Double-quoted string: `"hello world"`. The slice is raw — enclosing
    /// quotes and escape sequences included — and is decoded into segments at
    /// parse time.
    #[regex(r#""([^"\\]|\\.)*""#, |lex| lex.slice())]
    /// Single-quoted string: `'hello world'`, raw as above.
    #[regex(r#"'([^'\\]|\\.)*'"#, |lex| lex.slice())]
    String(&'source str),

    /// Integer literal: 42, -100
    #[regex(r"-?[0-9]+", |lex| lex.slice())]
    Integer(&'source str),

    /// Boolean true
    #[token("True")]
    #[token("true")]
    True,

    /// Boolean false
    #[token("False")]
    #[token("false")]
    False,

    /// None value
    #[token("None")]
    #[token("none")]
    None,

    // Variable substitution
    /// Variable reference: ${varName}
    #[regex(r"\$\{[a-zA-Z_][a-zA-Z0-9_]*\}", |lex| {
        let s = lex.slice();
        // Strip ${ and }
        &s[2..s.len()-1]
    })]
    Variable(&'source str),

    /// Identifier: a function name. A bare identifier anywhere else is a
    /// parse error (a variable reference is always written `${name}`).
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*")]
    Identifier(&'source str),

    // Punctuation
    /// Opening parenthesis
    #[token("(")]
    LParen,

    /// Closing parenthesis
    #[token(")")]
    RParen,

    /// Opening bracket
    #[token("[")]
    LBracket,

    /// Closing bracket
    #[token("]")]
    RBracket,

    /// Comma separator
    #[token(",")]
    Comma,
}

/// Supported functions in USD variable expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Display, EnumString)]
#[strum(serialize_all = "snake_case")]
pub enum Func {
    /// `defined("var1", "var2", ...)` - Tests if all named variables are
    /// defined. Each argument must evaluate to a string naming a variable.
    Defined,
    /// `if(cond, trueVal, falseVal?)` - Conditional expression. Both branches
    /// are evaluated and must produce the same type (or `None`).
    If,
    /// `and(x, y, ...)` - Logical AND (short-circuit).
    And,
    /// `or(x, y, ...)` - Logical OR (short-circuit).
    Or,
    /// `not(x)` - Logical NOT.
    Not,
    /// `eq(x, y)` - Equality comparison.
    Eq,
    /// `neq(x, y)` - Inequality comparison.
    Neq,
    /// `lt(x, y)` - Less than.
    Lt,
    /// `leq(x, y)` - Less than or equal.
    Leq,
    /// `gt(x, y)` - Greater than.
    Gt,
    /// `geq(x, y)` - Greater than or equal.
    Geq,
    /// `contains(list_or_string, value)` - Membership test.
    Contains,
    /// `matches_regex(string_or_list, pattern)` - Unanchored regular-expression
    /// search: whether the string (or any element of the string list) matches
    /// `pattern`. Patterns use Rust regex syntax (`regex-lite`) as a practical
    /// stand-in for the POSIX extended dialect C++'s `TfPatternMatcher` uses:
    /// the common constructs (POSIX character classes like `[[:digit:]]`,
    /// alternation, repetition, anchors) behave identically, but the dialects
    /// differ at the edges (e.g. backslash-escaped interval braces).
    MatchesRegex,
    /// `at(list_or_string, index)` - Element access (0-based, negative indices
    /// count from the end); strings index by character.
    At,
    /// `len(list_or_string)` - Returns length; strings count characters.
    Len,
}

impl Func {
    /// Validates the parsed argument count against the function's arity, with
    /// the C++ parse-time messages.
    fn validate_arg_count(self, count: usize) -> Result<()> {
        match self {
            Func::Defined => ensure!(count >= 1, "Function '{self}' requires at least 1 arguments."),
            Func::And | Func::Or => ensure!(count >= 2, "Function '{self}' requires at least 2 arguments."),
            Func::If => ensure!(
                count == 2 || count == 3,
                "Function '{self}' does not take {count} arguments."
            ),
            Func::Not | Func::Len => ensure!(count == 1, "Function '{self}' does not take {count} arguments."),
            _ => ensure!(count == 2, "Function '{self}' does not take {count} arguments."),
        }
        Ok(())
    }
}

/// Expression tree node representing a parsed USD variable expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Quoted string literal, split into literal text and embedded `${var}`
    /// reference segments at parse time.
    String(Vec<StringSegment>),
    /// 64-bit signed integer literal.
    Integer(i64),
    /// Boolean literal.
    Bool(bool),
    /// None value.
    None,
    /// Variable reference: `${varName}`.
    Variable(String),
    /// Array literal: `[elem1, elem2, ...]`.
    Array(Vec<Expr>),
    /// Function call.
    Call { func: Func, args: Vec<Expr> },
}

/// One segment of a quoted string literal (C++ `StringNode::Part`): literal
/// text with escapes already processed, or an embedded `${var}` reference. An
/// escaped reference (`\${var}`) is literal text, which is what lets it
/// survive evaluation as the characters `${var}`.
#[derive(Debug, Clone, PartialEq)]
pub enum StringSegment {
    /// Literal text.
    Literal(String),
    /// An embedded `${var}` reference, holding the variable name.
    Variable(String),
}

impl FromStr for Expr {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        let mut parser = Parser::new(s);
        parser.parse_expr()
    }
}

impl Expr {
    /// Parse an expression string into an expression tree.
    pub fn parse(s: &str) -> Result<Self> {
        s.parse()
    }

    /// Evaluate the expression against `vars` (C++
    /// `SdfVariableExpression::Evaluate`).
    pub fn evaluate(&self, vars: &HashMap<String, sdf::Value>) -> Evaluation {
        let mut ctx = EvalContext {
            vars,
            used: HashSet::new(),
            stack: Vec::new(),
        };
        let result = self.eval_in(&mut ctx);
        Evaluation {
            value: result.value,
            errors: result.errors,
            used_variables: ctx.used,
        }
    }

    /// Evaluate one node within a shared context.
    fn eval_in(&self, ctx: &mut EvalContext) -> EvalResult {
        match self {
            Expr::String(segments) => eval_string(segments, ctx),
            Expr::Integer(n) => EvalResult::ok(sdf::Value::Int64(*n)),
            Expr::Bool(b) => EvalResult::ok(sdf::Value::Bool(*b)),
            Expr::None => EvalResult::none(),
            Expr::Variable(name) => {
                let (result, has_value) = ctx.lookup(name);
                if !has_value {
                    return EvalResult::error(format!("No value for variable '{name}'"));
                }
                result
            }
            Expr::Array(elements) => eval_array(elements, ctx),
            Expr::Call { func, args } => eval_func(*func, args, ctx),
        }
    }
}

/// Shared state threaded through one evaluation (C++ `EvalContext`): the
/// variables, the names requested so far, and the stack of variables whose
/// expression values are currently being recursively evaluated (the circular
/// substitution guard).
struct EvalContext<'a> {
    vars: &'a HashMap<String, sdf::Value>,
    used: HashSet<String>,
    stack: Vec<String>,
}

impl EvalContext<'_> {
    /// Resolves a variable (C++ `EvalContext::GetVariable`): cycle-checks,
    /// records the request in [`used`](Self::used) before lookup, coerces
    /// `Int`/`IntVec` values to their 64-bit forms, and recursively parses and
    /// evaluates an expression-valued string value in this same context.
    /// Returns the result and whether the variable had a value at all.
    fn lookup(&mut self, name: &str) -> (EvalResult, bool) {
        if self.stack.iter().any(|n| n == name) {
            let mut names: Vec<String> = self.stack.iter().map(|n| format!("'{n}'")).collect();
            names.push(format!("'{name}'"));
            let message = format!("Encountered circular variable substitutions: [{}]", names.join(", "));
            return (EvalResult::error(message), true);
        }
        if !self.used.contains(name) {
            self.used.insert(name.to_string());
        }

        let Some(value) = self.vars.get(name) else {
            return (EvalResult::none(), false);
        };
        // TODO(perf): a list-valued variable is cloned per reference; threading
        // borrows (`Cow`) through `EvalResult` would avoid the copy.
        let result = match value {
            sdf::Value::None => EvalResult::none(),
            sdf::Value::Int(i) => EvalResult::ok(sdf::Value::Int64(i64::from(*i))),
            sdf::Value::IntVec(v) => EvalResult::ok(sdf::Value::Int64Vec(v.iter().map(|&i| i64::from(i)).collect())),
            sdf::Value::String(s) if is_expression(s) => match Expr::parse(s) {
                Ok(sub_expr) => {
                    self.stack.push(name.to_string());
                    let result = sub_expr.eval_in(self);
                    self.stack.pop();
                    result
                }
                Err(err) => EvalResult::error(format!("{err:#} (in variable '{name}')")),
            },
            sdf::Value::String(_)
            | sdf::Value::Bool(_)
            | sdf::Value::Int64(_)
            | sdf::Value::StringVec(_)
            | sdf::Value::BoolVec(_)
            | sdf::Value::Int64Vec(_) => EvalResult::ok(value.clone()),
            other => EvalResult::error(format!(
                "Variable '{name}' has unsupported type {}",
                value_type_name(other)
            )),
        };
        (result, true)
    }
}

/// The outcome of evaluating one expression node (C++ `EvalResult`). An
/// errored result carries no value; a `None` value with no errors is the
/// expression-language `None`.
struct EvalResult {
    value: Option<EvaluationValue>,
    errors: Vec<String>,
}

impl EvalResult {
    fn ok(value: sdf::Value) -> Self {
        Self {
            value: Some(EvaluationValue::Value(value)),
            errors: Vec::new(),
        }
    }

    fn empty_list() -> Self {
        Self {
            value: Some(EvaluationValue::EmptyList),
            errors: Vec::new(),
        }
    }

    fn none() -> Self {
        Self {
            value: None,
            errors: Vec::new(),
        }
    }

    fn error(message: String) -> Self {
        Self {
            value: None,
            errors: vec![message],
        }
    }

    fn errors(errors: Vec<String>) -> Self {
        Self { value: None, errors }
    }
}

/// Drains and concatenates the errors of two operand results, the shape every
/// two-argument function uses to aggregate before type-checking.
fn combined_errors(x: &mut EvalResult, y: &mut EvalResult) -> Vec<String> {
    let mut errors = mem::take(&mut x.errors);
    errors.append(&mut y.errors);
    errors
}

/// The expression-language name of a value's type, as used in error messages
/// (C++ `GetValueTypeName`): `string`, `int`, `bool`, `list`, or `None`. A
/// type the language does not support reports its lowercased variant name
/// (e.g. `double`).
fn value_type_name(value: &sdf::Value) -> Cow<'static, str> {
    match value {
        sdf::Value::None => "None".into(),
        sdf::Value::Bool(_) => "bool".into(),
        sdf::Value::Int(_) | sdf::Value::Int64(_) => "int".into(),
        sdf::Value::String(_) => "string".into(),
        sdf::Value::StringVec(_) | sdf::Value::IntVec(_) | sdf::Value::Int64Vec(_) | sdf::Value::BoolVec(_) => {
            "list".into()
        }
        other => <&'static str>::from(other).to_lowercase().into(),
    }
}

/// [`value_type_name`] over an evaluation result: `None` results are `None`,
/// the empty list is `list`.
fn result_type_name(value: &Option<EvaluationValue>) -> Cow<'static, str> {
    match value {
        None => "None".into(),
        Some(EvaluationValue::EmptyList) => "list".into(),
        Some(EvaluationValue::Value(v)) => value_type_name(v),
    }
}

/// Whether two results hold the same expression-language type (C++ compares
/// the held `VtValue` types): `None` matches only `None`, the empty list only
/// the empty list, and typed values their own variant.
fn same_type(x: &Option<EvaluationValue>, y: &Option<EvaluationValue>) -> bool {
    match (x, y) {
        (None, None) => true,
        (Some(EvaluationValue::EmptyList), Some(EvaluationValue::EmptyList)) => true,
        (Some(EvaluationValue::Value(a)), Some(EvaluationValue::Value(b))) => {
            mem::discriminant(a) == mem::discriminant(b)
        }
        _ => false,
    }
}

/// Evaluates a quoted string's segments (C++ `StringNode::Evaluate`),
/// substituting each `${var}` reference. An undefined variable substitutes as
/// its own name (not an error — C++ leaves the substitution in place for
/// downstream clients); a `None` value substitutes as the empty string; a
/// non-string value is an error.
fn eval_string(segments: &[StringSegment], ctx: &mut EvalContext) -> EvalResult {
    let mut result = String::new();
    for segment in segments {
        match segment {
            StringSegment::Literal(s) => result.push_str(s),
            StringSegment::Variable(name) => {
                let (sub, has_value) = ctx.lookup(name);
                if !has_value {
                    result.push_str(name);
                } else if !sub.errors.is_empty() {
                    return EvalResult::errors(sub.errors);
                } else {
                    match sub.value {
                        Some(EvaluationValue::Value(sdf::Value::String(s))) => result.push_str(&s),
                        None => {}
                        other => {
                            return EvalResult::error(format!(
                                "String value required for substituting variable '{name}', got {}.",
                                result_type_name(&other)
                            ))
                        }
                    }
                }
            }
        }
    }
    EvalResult::ok(sdf::Value::String(result))
}

/// Evaluates a list literal (C++ `ListNode::Evaluate`): every element is
/// evaluated (errors aggregate), the first valid element fixes the list type,
/// and an element of any other type — including `None` and nested lists — is
/// an error. An empty result is the untyped
/// [`EmptyList`](EvaluationValue::EmptyList).
fn eval_array(elements: &[Expr], ctx: &mut EvalContext) -> EvalResult {
    let mut errors = Vec::new();
    let mut list: Option<sdf::Value> = None;
    for (i, element) in elements.iter().enumerate() {
        let mut result = element.eval_in(ctx);
        if !result.errors.is_empty() {
            errors.append(&mut result.errors);
            continue;
        }
        match (&mut list, result.value) {
            (None, Some(EvaluationValue::Value(sdf::Value::String(s)))) => {
                list = Some(sdf::Value::StringVec(vec![s]));
            }
            (None, Some(EvaluationValue::Value(sdf::Value::Int64(n)))) => {
                list = Some(sdf::Value::Int64Vec(vec![n]));
            }
            (None, Some(EvaluationValue::Value(sdf::Value::Bool(b)))) => {
                list = Some(sdf::Value::BoolVec(vec![b]));
            }
            (Some(sdf::Value::StringVec(v)), Some(EvaluationValue::Value(sdf::Value::String(s)))) => v.push(s),
            (Some(sdf::Value::Int64Vec(v)), Some(EvaluationValue::Value(sdf::Value::Int64(n)))) => v.push(n),
            (Some(sdf::Value::BoolVec(v)), Some(EvaluationValue::Value(sdf::Value::Bool(b)))) => v.push(b),
            (_, other) => errors.push(format!(
                "Unexpected value of type {} in list at element {i}",
                result_type_name(&other)
            )),
        }
    }
    if !errors.is_empty() {
        return EvalResult::errors(errors);
    }
    match list {
        Some(v) => EvalResult::ok(v),
        None => EvalResult::empty_list(),
    }
}

/// Evaluate a function call.
fn eval_func(func: Func, args: &[Expr], ctx: &mut EvalContext) -> EvalResult {
    match func {
        Func::Defined => {
            let mut errors = Vec::new();
            let mut result: Option<bool> = None;
            for (i, arg) in args.iter().enumerate() {
                let mut r = arg.eval_in(ctx);
                if !r.errors.is_empty() {
                    errors.append(&mut r.errors);
                    continue;
                }
                match r.value {
                    Some(EvaluationValue::Value(sdf::Value::String(name))) => {
                        let defined = ctx.vars.contains_key(&name);
                        ctx.used.insert(name);
                        result = Some(result.unwrap_or(true) && defined);
                    }
                    other => errors.push(format!(
                        "{func}: Invalid type {} for argument {i}",
                        result_type_name(&other)
                    )),
                }
            }
            finish_bool_fold(result, errors)
        }

        Func::If => {
            let condition = args[0].eval_in(ctx);
            if !condition.errors.is_empty() {
                return EvalResult::errors(condition.errors);
            }
            let Some(EvaluationValue::Value(sdf::Value::Bool(condition))) = condition.value else {
                return EvalResult::error(format!("{func}: Condition must be a boolean value"));
            };
            // Both branches are evaluated so their types can be checked, even
            // though only one is returned (C++ imposes the same requirement).
            // The unchosen branch's errors are discarded with it — C++ returns
            // the chosen branch's result as-is, so a guarded branch like
            // `if(${USE_A}, ${A}, ${B})` succeeds with only `A` defined —
            // while its variable lookups stay recorded in `used_variables`.
            let if_result = args[1].eval_in(ctx);
            let else_result = match args.get(2) {
                Some(arg) => arg.eval_in(ctx),
                None => EvalResult::none(),
            };
            if !same_type(&if_result.value, &else_result.value)
                && if_result.value.is_some()
                && else_result.value.is_some()
            {
                return EvalResult::error(format!(
                    "{func}: if-value and else-value must evaluate to the same type or None."
                ));
            }
            if condition {
                if_result
            } else {
                else_result
            }
        }

        Func::And | Func::Or => {
            let mut errors = Vec::new();
            let mut result: Option<bool> = None;
            for (i, arg) in args.iter().enumerate() {
                let mut r = arg.eval_in(ctx);
                if !r.errors.is_empty() {
                    errors.append(&mut r.errors);
                    continue;
                }
                match r.value {
                    Some(EvaluationValue::Value(sdf::Value::Bool(value))) => {
                        // A non-decisive value is the operation's identity, so
                        // the fold reduces to keeping the latest value; a
                        // decisive one short-circuits.
                        result = Some(value);
                        let decisive = if func == Func::And { !value } else { value };
                        if decisive {
                            break;
                        }
                    }
                    other => errors.push(format!(
                        "{func}: Invalid type {} for argument {i}",
                        result_type_name(&other)
                    )),
                }
            }
            finish_bool_fold(result, errors)
        }

        Func::Not => {
            let condition = args[0].eval_in(ctx);
            if !condition.errors.is_empty() {
                return EvalResult::errors(condition.errors);
            }
            match condition.value {
                Some(EvaluationValue::Value(sdf::Value::Bool(b))) => EvalResult::ok(sdf::Value::Bool(!b)),
                other => EvalResult::error(format!(
                    "{func}: Invalid type {} for argument",
                    result_type_name(&other)
                )),
            }
        }

        Func::Eq | Func::Neq | Func::Lt | Func::Leq | Func::Gt | Func::Geq => {
            let mut x = args[0].eval_in(ctx);
            let mut y = args[1].eval_in(ctx);
            let errors = combined_errors(&mut x, &mut y);
            if !errors.is_empty() {
                return EvalResult::errors(errors);
            }
            eval_comparison(func, x.value, y.value)
        }

        Func::Contains => {
            let mut search_in = args[0].eval_in(ctx);
            let mut search_for = args[1].eval_in(ctx);
            let errors = combined_errors(&mut search_in, &mut search_for);
            if !errors.is_empty() {
                return EvalResult::errors(errors);
            }
            use EvaluationValue::Value as V;
            let found = match (search_in.value, search_for.value) {
                (Some(EvaluationValue::EmptyList), _) => false,
                (Some(V(sdf::Value::String(s))), Some(V(sdf::Value::String(n)))) => s.contains(n.as_str()),
                (Some(V(sdf::Value::StringVec(v))), Some(V(sdf::Value::String(n)))) => v.contains(&n),
                (Some(V(sdf::Value::Int64Vec(v))), Some(V(sdf::Value::Int64(n)))) => v.contains(&n),
                (Some(V(sdf::Value::BoolVec(v))), Some(V(sdf::Value::Bool(n)))) => v.contains(&n),
                (
                    Some(V(
                        sdf::Value::String(_)
                        | sdf::Value::StringVec(_)
                        | sdf::Value::Int64Vec(_)
                        | sdf::Value::BoolVec(_),
                    )),
                    _,
                ) => return EvalResult::error(format!("{func}: Invalid search value")),
                _ => return EvalResult::error(format!("{func}: Value to search must be a list or string")),
            };
            EvalResult::ok(sdf::Value::Bool(found))
        }

        Func::MatchesRegex => {
            let mut search_in = args[0].eval_in(ctx);
            let mut pattern = args[1].eval_in(ctx);
            let errors = combined_errors(&mut search_in, &mut pattern);
            if !errors.is_empty() {
                return EvalResult::errors(errors);
            }
            let strings: &[String] = match &search_in.value {
                Some(EvaluationValue::EmptyList) => return EvalResult::ok(sdf::Value::Bool(false)),
                Some(EvaluationValue::Value(sdf::Value::String(s))) => slice::from_ref(s),
                Some(EvaluationValue::Value(sdf::Value::StringVec(v))) => v,
                _ => return EvalResult::error(format!("{func}: Value to search must be string[] or string")),
            };
            let Some(EvaluationValue::Value(sdf::Value::String(p))) = pattern.value else {
                return EvalResult::error(format!("{func}: Pattern to match must be a string"));
            };
            let regex = match Regex::new(&p) {
                Ok(regex) => regex,
                Err(err) => return EvalResult::error(format!("{func}: Invalid match pattern: {err}")),
            };
            EvalResult::ok(sdf::Value::Bool(strings.iter().any(|s| regex.is_match(s))))
        }

        Func::At => {
            let mut source = args[0].eval_in(ctx);
            let mut index = args[1].eval_in(ctx);
            let errors = combined_errors(&mut source, &mut index);
            if !errors.is_empty() {
                return EvalResult::errors(errors);
            }
            let Some(EvaluationValue::Value(sdf::Value::Int64(index))) = index.value else {
                return EvalResult::error(format!("{func}: Index must be an integer"));
            };
            let element = match source.value {
                Some(EvaluationValue::EmptyList) => None,
                Some(EvaluationValue::Value(sdf::Value::String(s))) => normalize_index(index, s.chars().count())
                    .map(|i| sdf::Value::String(s.chars().nth(i).expect("index is in range").to_string())),
                Some(EvaluationValue::Value(sdf::Value::StringVec(mut v))) => {
                    normalize_index(index, v.len()).map(|i| sdf::Value::String(v.swap_remove(i)))
                }
                Some(EvaluationValue::Value(sdf::Value::Int64Vec(v))) => {
                    normalize_index(index, v.len()).map(|i| sdf::Value::Int64(v[i]))
                }
                Some(EvaluationValue::Value(sdf::Value::BoolVec(v))) => {
                    normalize_index(index, v.len()).map(|i| sdf::Value::Bool(v[i]))
                }
                _ => return EvalResult::error(format!("{func}: Only supported for lists or strings")),
            };
            match element {
                Some(value) => EvalResult::ok(value),
                None => EvalResult::error(format!("{func}: Index out of range")),
            }
        }

        Func::Len => {
            let source = args[0].eval_in(ctx);
            if !source.errors.is_empty() {
                return EvalResult::errors(source.errors);
            }
            let len = match source.value {
                Some(EvaluationValue::EmptyList) => 0,
                Some(EvaluationValue::Value(sdf::Value::String(s))) => s.chars().count(),
                Some(EvaluationValue::Value(sdf::Value::StringVec(v))) => v.len(),
                Some(EvaluationValue::Value(sdf::Value::Int64Vec(v))) => v.len(),
                Some(EvaluationValue::Value(sdf::Value::BoolVec(v))) => v.len(),
                _ => return EvalResult::error(format!("{func}: Unsupported type")),
            };
            EvalResult::ok(sdf::Value::Int64(len as i64))
        }
    }
}

/// Finishes a `defined`/`and`/`or` argument fold: errors win, and a fold that
/// never saw a valid argument (only possible alongside errors) has no value.
fn finish_bool_fold(result: Option<bool>, errors: Vec<String>) -> EvalResult {
    if !errors.is_empty() {
        EvalResult::errors(errors)
    } else {
        match result {
            Some(b) => EvalResult::ok(sdf::Value::Bool(b)),
            None => EvalResult::none(),
        }
    }
}

/// Evaluates a comparison over two already-evaluated operands (C++
/// `ComparisonNode`): the types must match, `None` supports only equality,
/// and typed lists support no comparison. A pair of untyped empty lists
/// compares like `None` (equality only) — C++'s `EmptyList` falls through
/// `VtVisitValue`'s generic overload to the `None` comparison path.
fn eval_comparison(func: Func, x: Option<EvaluationValue>, y: Option<EvaluationValue>) -> EvalResult {
    if !same_type(&x, &y) {
        return EvalResult::error(format!(
            "{func}: Cannot compare values of type {} and {}",
            result_type_name(&x),
            result_type_name(&y)
        ));
    }
    let ordering = match (x, y) {
        (None, None) | (Some(EvaluationValue::EmptyList), Some(EvaluationValue::EmptyList)) => {
            return match func {
                Func::Eq => EvalResult::ok(sdf::Value::Bool(true)),
                Func::Neq => EvalResult::ok(sdf::Value::Bool(false)),
                _ => EvalResult::error(format!("{func}: Comparison operation not supported for None")),
            }
        }
        (Some(EvaluationValue::Value(a)), Some(EvaluationValue::Value(b))) => match (a, b) {
            (sdf::Value::String(a), sdf::Value::String(b)) => a.cmp(&b),
            (sdf::Value::Int64(a), sdf::Value::Int64(b)) => a.cmp(&b),
            (sdf::Value::Bool(a), sdf::Value::Bool(b)) => a.cmp(&b),
            _ => return EvalResult::error(format!("{func}: Unsupported type for comparison")),
        },
        _ => unreachable!("same_type only matches identical shapes"),
    };
    let result = match func {
        Func::Eq => ordering.is_eq(),
        Func::Neq => ordering.is_ne(),
        Func::Lt => ordering.is_lt(),
        Func::Leq => !ordering.is_gt(),
        Func::Gt => ordering.is_gt(),
        Func::Geq => !ordering.is_lt(),
        _ => unreachable!("eval_comparison is called only for comparison functions"),
    };
    EvalResult::ok(sdf::Value::Bool(result))
}

/// Normalize a possibly-negative index to a valid array/string index.
fn normalize_index(index: i64, len: usize) -> Option<usize> {
    let idx = if index < 0 { index + len as i64 } else { index };
    (0..len as i64).contains(&idx).then_some(idx as usize)
}

/// Parser for USD variable expressions.
struct Parser<'a> {
    input: &'a str,
    iter: Peekable<SpannedIter<'a, Token<'a>>>,
}

impl<'a> Parser<'a> {
    /// Create a new parser for the given input string.
    /// Backtick delimiters are stripped automatically if present.
    fn new(input: &'a str) -> Self {
        let input = if is_expression(input) {
            &input[1..input.len() - 1]
        } else {
            input
        };
        Self {
            input,
            iter: Token::lexer(input).spanned().peekable(),
        }
    }

    /// Peek at the current token without consuming it. A malformed token peeks
    /// as `None`; consuming it via [`next`](Self::next) reports the error.
    fn peek(&mut self) -> Option<&Token<'a>> {
        self.iter.peek().and_then(|(result, _)| result.as_ref().ok())
    }

    /// Consume and return the current token; a malformed token is a parse
    /// error.
    fn next(&mut self) -> Result<Option<Token<'a>>> {
        match self.iter.next() {
            Some((Ok(token), _)) => Ok(Some(token)),
            Some((Err(()), span)) => bail!("Unexpected character '{}'", &self.input[span]),
            None => Ok(None),
        }
    }

    /// Consume a token if it matches the expected token, otherwise return an error.
    fn expect(&mut self, expected: Token<'a>) -> Result<()> {
        match self.next()? {
            Some(ref token) if *token == expected => Ok(()),
            Some(token) => bail!("Expected {:?}, got {:?}", expected, token),
            None => bail!("Expected {:?}, got end of input", expected),
        }
    }

    /// Parse a complete expression: one expression body spanning all input.
    fn parse_expr(&mut self) -> Result<Expr> {
        let expr = self.parse()?;
        match self.next()? {
            None => Ok(expr),
            Some(token) => bail!("Unexpected token after expression: {token:?}"),
        }
    }

    /// Parse an expression body (C++ `ExpressionBody`): a scalar expression or
    /// a list. List elements are scalar expressions (C++ `ListElement`), so a
    /// nested list is a parse error.
    fn parse(&mut self) -> Result<Expr> {
        if matches!(self.peek(), Some(Token::LBracket)) {
            self.next()?;
            let elements = self.parse_delimited(Token::RBracket, ']', "list", Self::parse_scalar)?;
            return Ok(Expr::Array(elements));
        }
        self.parse_scalar()
    }

    /// Parse a scalar expression (C++ `ScalarExpression`): a literal, a
    /// `${var}` reference, or a function call. A bare identifier not followed
    /// by `(` is a parse error.
    fn parse_scalar(&mut self) -> Result<Expr> {
        let token = self.next()?.ok_or_else(|| anyhow!("Unexpected end of input"))?;

        match token {
            Token::String(raw) => Ok(Expr::String(parse_quoted_string(raw)?)),
            Token::Integer(s) => {
                let value = s.parse::<i64>().map_err(|_| anyhow!("Integer {s} out of range."))?;
                Ok(Expr::Integer(value))
            }
            Token::True => Ok(Expr::Bool(true)),
            Token::False => Ok(Expr::Bool(false)),
            Token::None => Ok(Expr::None),
            Token::Variable(name) => Ok(Expr::Variable(name.to_string())),
            Token::Identifier(name) => {
                if matches!(self.peek(), Some(Token::LParen)) {
                    self.parse_call(name)
                } else {
                    bail!("Unexpected identifier '{name}'");
                }
            }
            other => bail!("Unexpected token: {:?}", other),
        }
    }

    /// Parse a function call: `funcName(arg1, arg2, ...)`. Arguments are full
    /// expression bodies, so a list argument is allowed.
    fn parse_call(&mut self, name: &str) -> Result<Expr> {
        let func: Func = name.parse().map_err(|_| anyhow!("Unknown function {name}"))?;
        self.expect(Token::LParen)?;
        let args = self.parse_delimited(Token::RParen, ')', "function call", Self::parse)?;
        func.validate_arg_count(args.len())?;
        Ok(Expr::Call { func, args })
    }

    /// Parse a possibly-empty comma-separated element sequence up to and
    /// including the `close` token — the shared shape of list elements and
    /// function arguments. `close_char` and `what` name the closer and the
    /// construct in parse-error messages.
    fn parse_delimited(
        &mut self,
        close: Token<'a>,
        close_char: char,
        what: &str,
        parse_element: fn(&mut Self) -> Result<Expr>,
    ) -> Result<Vec<Expr>> {
        let mut elements = Vec::new();
        if self.peek() == Some(&close) {
            self.next()?;
            return Ok(elements);
        }
        loop {
            elements.push(parse_element(self)?);

            match self.peek() {
                Some(Token::Comma) => {
                    self.next()?;
                }
                Some(token) if *token == close => {
                    self.next()?;
                    break;
                }
                _ => match self.next()? {
                    Some(token) => bail!("Expected ',' or '{close_char}' in {what}, got {token:?}"),
                    None => bail!("Missing ending '{close_char}'"),
                },
            }
        }
        Ok(elements)
    }
}

/// Splits the body of a quoted string literal (`raw` includes its enclosing
/// quotes) into literal and `${var}` reference segments, processing escape
/// sequences (C++ recognizes references with the `QuotedStringVariable`
/// grammar rule and unescapes literal parts with `TfEscapeString`). A
/// backslash escapes any character: `\n`, `\r`, and `\t` produce their
/// control characters, and any other escape — including `` \` ``, `\$`, `\\`,
/// and the enclosing quote — produces the character itself, so `\${var}` is
/// the literal text `${var}` rather than a reference. A `$` not starting a
/// `${name}` reference is an ordinary character.
fn parse_quoted_string(raw: &str) -> Result<Vec<StringSegment>> {
    let body = &raw[1..raw.len() - 1];
    let mut segments = Vec::new();
    let mut literal = String::new();
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' => {
                // The lexer only forms a string token from complete escape
                // pairs, so a character always follows.
                let escaped = chars.next().ok_or_else(|| anyhow!("Trailing backslash in string"))?;
                literal.push(match escaped {
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    other => other,
                });
            }
            '$' if chars.peek() == Some(&'{') => {
                chars.next();
                let mut name = String::new();
                loop {
                    match chars.next() {
                        Some('}') => break,
                        Some(c) if c.is_ascii_alphanumeric() || c == '_' => name.push(c),
                        Some(_) => bail!("Variables must be a C identifier"),
                        None => bail!("Missing ending '}}'"),
                    }
                }
                ensure!(
                    name.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_'),
                    "Variables must be a C identifier"
                );
                if !literal.is_empty() {
                    segments.push(StringSegment::Literal(mem::take(&mut literal)));
                }
                segments.push(StringSegment::Variable(name));
            }
            other => literal.push(other),
        }
    }
    if !literal.is_empty() {
        segments.push(StringSegment::Literal(literal));
    }
    Ok(segments)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A single-segment literal string expression.
    fn lit(s: &str) -> Expr {
        Expr::String(vec![StringSegment::Literal(s.to_string())])
    }

    fn make_vars(pairs: &[(&str, sdf::Value)]) -> HashMap<String, sdf::Value> {
        pairs.iter().map(|(k, v)| (k.to_string(), v.clone())).collect()
    }

    /// Evaluates `src` expecting success, returning the value (`None` for the
    /// expression-language `None`).
    fn eval(src: &str, vars: &HashMap<String, sdf::Value>) -> Option<EvaluationValue> {
        let expr = Expr::parse(src).expect("expression parses");
        let result = expr.evaluate(vars);
        assert_eq!(result.errors, Vec::<String>::new(), "evaluating {src}");
        result.value
    }

    /// Evaluates `src` expecting a plain value.
    fn eval_value(src: &str, vars: &HashMap<String, sdf::Value>) -> sdf::Value {
        match eval(src, vars) {
            Some(EvaluationValue::Value(v)) => v,
            other => panic!("expected a value evaluating {src}, got {other:?}"),
        }
    }

    /// Evaluates `src` expecting failure, returning the errors.
    fn eval_errors(src: &str, vars: &HashMap<String, sdf::Value>) -> Vec<String> {
        let expr = Expr::parse(src).expect("expression parses");
        let result = expr.evaluate(vars);
        assert_eq!(result.value, None, "evaluating {src}");
        assert!(!result.errors.is_empty(), "expected errors evaluating {src}");
        result.errors
    }

    #[test]
    fn test_is_expression() {
        assert!(is_expression(r#"`"hello"`"#));
        assert!(is_expression(r#"`if(${VAR}, "a", "b")`"#));

        // C++ requires a non-empty body.
        assert!(!is_expression("``"));
        assert!(!is_expression("hello"));
        assert!(!is_expression("`"));
        assert!(!is_expression("`hello"));
        assert!(!is_expression("hello`"));
        assert!(!is_expression(""));
    }

    #[test]
    fn tokenize_string_literals() {
        let tokens: Vec<_> = Token::lexer(r#""hello world""#).collect();
        assert_eq!(tokens, vec![Ok(Token::String(r#""hello world""#))]);

        let tokens: Vec<_> = Token::lexer(r#"'single quoted'"#).collect();
        assert_eq!(tokens, vec![Ok(Token::String("'single quoted'"))]);
    }

    #[test]
    fn tokenize_escaped_strings() {
        let tokens: Vec<_> = Token::lexer(r#""escaped \"quote\"""#).collect();
        assert_eq!(tokens, vec![Ok(Token::String(r#""escaped \"quote\"""#))]);
    }

    #[test]
    fn tokenize_integers() {
        let tokens: Vec<_> = Token::lexer("42").collect();
        assert_eq!(tokens, vec![Ok(Token::Integer("42"))]);

        let tokens: Vec<_> = Token::lexer("-100").collect();
        assert_eq!(tokens, vec![Ok(Token::Integer("-100"))]);
    }

    #[test]
    fn tokenize_booleans() {
        let tokens: Vec<_> = Token::lexer("True false").collect();
        assert_eq!(tokens, vec![Ok(Token::True), Ok(Token::False)]);

        let tokens: Vec<_> = Token::lexer("true False").collect();
        assert_eq!(tokens, vec![Ok(Token::True), Ok(Token::False)]);
    }

    #[test]
    fn tokenize_none() {
        let tokens: Vec<_> = Token::lexer("None none").collect();
        assert_eq!(tokens, vec![Ok(Token::None), Ok(Token::None)]);
    }

    #[test]
    fn tokenize_variables() {
        let tokens: Vec<_> = Token::lexer("${ASSET_PATH}").collect();
        assert_eq!(tokens, vec![Ok(Token::Variable("ASSET_PATH"))]);

        let tokens: Vec<_> = Token::lexer("${my_var_123}").collect();
        assert_eq!(tokens, vec![Ok(Token::Variable("my_var_123"))]);
    }

    #[test]
    fn tokenize_function_call() {
        let tokens: Vec<_> = Token::lexer("if(${USE_HIGH_RES}, \"high\", \"low\")").collect();
        assert_eq!(
            tokens,
            vec![
                Ok(Token::Identifier("if")),
                Ok(Token::LParen),
                Ok(Token::Variable("USE_HIGH_RES")),
                Ok(Token::Comma),
                Ok(Token::String("\"high\"")),
                Ok(Token::Comma),
                Ok(Token::String("\"low\"")),
                Ok(Token::RParen),
            ]
        );
    }

    #[test]
    fn tokenize_array_literal() {
        let tokens: Vec<_> = Token::lexer("[\"a\", \"b\"]").collect();
        assert_eq!(
            tokens,
            vec![
                Ok(Token::LBracket),
                Ok(Token::String("\"a\"")),
                Ok(Token::Comma),
                Ok(Token::String("\"b\"")),
                Ok(Token::RBracket),
            ]
        );
    }

    #[test]
    fn tokenize_invalid_character() {
        let tokens: Vec<_> = Token::lexer("${FO-O}").collect();
        assert!(tokens.iter().any(|t| t.is_err()));
    }

    // Expr parsing tests

    #[test]
    fn parse_string_literal() {
        let expr: Expr = r#""hello world""#.parse().unwrap();
        assert_eq!(expr, lit("hello world"));
    }

    #[test]
    fn parse_escaped_string() {
        let expr: Expr = r#""say \"hello\"""#.parse().unwrap();
        assert_eq!(expr, lit("say \"hello\""));
    }

    #[test]
    fn parse_string_segments() {
        let expr: Expr = r#""a_${VAR}_b""#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::String(vec![
                StringSegment::Literal("a_".to_string()),
                StringSegment::Variable("VAR".to_string()),
                StringSegment::Literal("_b".to_string()),
            ])
        );
    }

    #[test]
    fn parse_empty_string() {
        let expr: Expr = "''".parse().unwrap();
        assert_eq!(expr, Expr::String(vec![]));

        let expr: Expr = r#""""#.parse().unwrap();
        assert_eq!(expr, Expr::String(vec![]));
    }

    #[test]
    fn parse_bad_string_variable() {
        assert!(Expr::parse(r#""bad_var_${FOO""#).is_err());
        assert!(Expr::parse(r#""bad_var_${FO-O}""#).is_err());
        assert!(Expr::parse(r#""bad_var_${1X}""#).is_err());
    }

    #[test]
    fn parse_integer_literal() {
        let expr: Expr = "42".parse().unwrap();
        assert_eq!(expr, Expr::Integer(42));

        let expr: Expr = "-100".parse().unwrap();
        assert_eq!(expr, Expr::Integer(-100));
    }

    #[test]
    fn parse_integer_range() {
        assert_eq!(Expr::parse("9223372036854775807").unwrap(), Expr::Integer(i64::MAX),);
        assert_eq!(Expr::parse("-9223372036854775808").unwrap(), Expr::Integer(i64::MIN),);
        let err = Expr::parse("9223372036854775808").unwrap_err();
        assert!(err.to_string().contains("out of range"));
    }

    #[test]
    fn parse_boolean_literals() {
        let expr: Expr = "True".parse().unwrap();
        assert_eq!(expr, Expr::Bool(true));

        let expr: Expr = "false".parse().unwrap();
        assert_eq!(expr, Expr::Bool(false));
    }

    #[test]
    fn parse_none_literal() {
        let expr: Expr = "None".parse().unwrap();
        assert_eq!(expr, Expr::None);

        let expr: Expr = "none".parse().unwrap();
        assert_eq!(expr, Expr::None);
    }

    #[test]
    fn parse_keyword_prefix_rejected() {
        for src in ["Truee", "truee", "TRUE", "Falsee", "falsee", "Nonee", "nonee"] {
            assert!(Expr::parse(src).is_err(), "{src} must not parse");
        }
    }

    #[test]
    fn parse_variable() {
        let expr: Expr = "${ASSET_PATH}".parse().unwrap();
        assert_eq!(expr, Expr::Variable("ASSET_PATH".to_string()));
    }

    #[test]
    fn parse_bad_variable() {
        assert!(Expr::parse("`${FO-O}`").is_err());
        assert!(Expr::parse("`${FOO`").is_err());
    }

    #[test]
    fn parse_empty_array() {
        let expr: Expr = "[]".parse().unwrap();
        assert_eq!(expr, Expr::Array(vec![]));
    }

    #[test]
    fn parse_string_array() {
        let expr: Expr = r#"["a", "b", "c"]"#.parse().unwrap();
        assert_eq!(expr, Expr::Array(vec![lit("a"), lit("b"), lit("c")]));
    }

    #[test]
    fn parse_integer_array() {
        let expr: Expr = "[1, 2, 3]".parse().unwrap();
        assert_eq!(
            expr,
            Expr::Array(vec![Expr::Integer(1), Expr::Integer(2), Expr::Integer(3),])
        );
    }

    #[test]
    fn parse_nested_list_rejected() {
        assert!(Expr::parse("[[1, 2]]").is_err());
        assert!(Expr::parse("`[`").is_err());
    }

    #[test]
    fn parse_bare_identifier_rejected() {
        let err = Expr::parse("foo").unwrap_err();
        assert!(err.to_string().contains("Unexpected identifier"));
        assert!(Expr::parse("[foo]").is_err());
        assert!(Expr::parse("defined(RENDER_PASS)").is_err());
    }

    #[test]
    fn parse_simple_function_call() {
        let expr: Expr = "not(True)".parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::Not,
                args: vec![Expr::Bool(true)],
            }
        );
    }

    #[test]
    fn parse_if_function() {
        let expr: Expr = r#"if(${USE_HIGH_RES}, "high", "low")"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::If,
                args: vec![Expr::Variable("USE_HIGH_RES".to_string()), lit("high"), lit("low")],
            }
        );
    }

    #[test]
    fn parse_defined_function() {
        let expr: Expr = r#"defined("RENDER_PASS")"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::Defined,
                args: vec![lit("RENDER_PASS")],
            }
        );
    }

    #[test]
    fn parse_matches_regex() {
        let expr: Expr = r#"matches_regex(${S}, "a.*b")"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::MatchesRegex,
                args: vec![Expr::Variable("S".to_string()), lit("a.*b")],
            }
        );
    }

    #[test]
    fn parse_nested_function() {
        let expr: Expr = r#"if(and(${A}, ${B}), "yes", "no")"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::If,
                args: vec![
                    Expr::Call {
                        func: Func::And,
                        args: vec![Expr::Variable("A".to_string()), Expr::Variable("B".to_string())],
                    },
                    lit("yes"),
                    lit("no"),
                ],
            }
        );
    }

    #[test]
    fn parse_with_backticks() {
        let expr: Expr = r#"`"${ASSET_PATH}/model.usd"`"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::String(vec![
                StringSegment::Variable("ASSET_PATH".to_string()),
                StringSegment::Literal("/model.usd".to_string()),
            ])
        );
    }

    #[test]
    fn parse_contains_function() {
        let expr: Expr = r#"contains(["a", "b"], ${VAR})"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::Contains,
                args: vec![Expr::Array(vec![lit("a"), lit("b")]), Expr::Variable("VAR".to_string()),],
            }
        );
    }

    #[test]
    fn parse_unknown_function_fails() {
        let result: Result<Expr, _> = "unknown_func(1, 2)".parse();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Unknown function unknown_func"));
    }

    #[test]
    fn parse_backtick_any_expression() {
        // Backticks accept any expression, not just strings.
        let expr: Expr = "`42`".parse().unwrap();
        assert_eq!(expr, Expr::Integer(42));

        let expr: Expr = "`if(True, 1, 2)`".parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::If,
                args: vec![Expr::Bool(true), Expr::Integer(1), Expr::Integer(2)],
            }
        );
    }

    #[test]
    fn parse_escaped_backslashes() {
        // Escaped backslashes in function arguments: \\ → \
        let expr: Expr = r#"if(${COND}, "C:\\USD\\test.usd", "D:\\USD\\test.usd")"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::If,
                args: vec![
                    Expr::Variable("COND".to_string()),
                    lit(r"C:\USD\test.usd"),
                    lit(r"D:\USD\test.usd"),
                ],
            }
        );
    }

    #[test]
    fn parse_escaped_dollar_sign() {
        // Escaped $ prevents variable substitution: \$ → $
        let expr: Expr = r#"`"escaped_var_\${X}"`"#.parse().unwrap();
        assert_eq!(expr, lit("escaped_var_${X}"));
    }

    #[test]
    fn parse_escaped_backtick() {
        let expr: Expr = r#""a\`b""#.parse().unwrap();
        assert_eq!(expr, lit("a`b"));
    }

    #[test]
    fn parse_control_escapes() {
        let expr: Expr = r#""a\nb\tc\rd""#.parse().unwrap();
        assert_eq!(expr, lit("a\nb\tc\rd"));
    }

    #[test]
    fn parse_unknown_escape() {
        // An unrecognized escape keeps the character, dropping the backslash
        // (C++ `TfEscapeString`).
        let expr: Expr = r#""a\qb""#.parse().unwrap();
        assert_eq!(expr, lit("aqb"));
    }

    #[test]
    fn parse_bare_dollar_literal() {
        // A '$' not starting a `${name}` reference is an ordinary character.
        let expr: Expr = r#""cost_$5""#.parse().unwrap();
        assert_eq!(expr, lit("cost_$5"));
    }

    #[test]
    fn parse_if_with_two_args() {
        // if() can take 2 arguments (falseVal is optional, returns None)
        let expr: Expr = r#"if(True, "yes")"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::If,
                args: vec![Expr::Bool(true), lit("yes")],
            }
        );
    }

    #[test]
    fn parse_function_arg_count_validation() {
        let cases = [
            ("not()", "Function 'not' does not take 0 arguments."),
            ("not(True, False)", "Function 'not' does not take 2 arguments."),
            ("len()", "Function 'len' does not take 0 arguments."),
            ("eq(1)", "Function 'eq' does not take 1 arguments."),
            ("eq(1, 2, 3)", "Function 'eq' does not take 3 arguments."),
            ("if(True)", "Function 'if' does not take 1 arguments."),
            ("and(True)", "Function 'and' requires at least 2 arguments."),
            ("defined()", "Function 'defined' requires at least 1 arguments."),
            (
                "matches_regex('a')",
                "Function 'matches_regex' does not take 1 arguments.",
            ),
        ];
        for (src, expected) in cases {
            let err = Expr::parse(src).unwrap_err();
            assert_eq!(err.to_string(), expected, "parsing {src}");
        }
    }

    // Eval tests

    #[test]
    fn eval_literals() {
        let vars = HashMap::new();

        assert_eq!(eval_value("42", &vars), sdf::Value::Int64(42));
        assert_eq!(eval_value("True", &vars), sdf::Value::Bool(true));
        assert_eq!(eval_value(r#""hello""#, &vars), sdf::Value::String("hello".to_string()));
        assert_eq!(eval("None", &vars), None);
        assert_eq!(eval("none", &vars), None);
        assert_eq!(eval_value(r#"''"#, &vars), sdf::Value::String(String::new()));
    }

    #[test]
    fn eval_variable_passthrough() {
        // A top-level substitution yields the exact value from the
        // dictionary, for every supported type.
        let cases = [
            sdf::Value::String("string".to_string()),
            sdf::Value::Int64(42),
            sdf::Value::Bool(true),
            sdf::Value::StringVec(vec!["foo".into(), "bar".into()]),
            sdf::Value::Int64Vec(vec![1, 2, 3]),
            sdf::Value::BoolVec(vec![true, false]),
        ];
        for value in cases {
            let vars = make_vars(&[("FOO", value.clone())]);
            assert_eq!(eval_value("${FOO}", &vars), value);
        }

        let vars = make_vars(&[("FOO", sdf::Value::None)]);
        assert_eq!(eval("${FOO}", &vars), None);
    }

    #[test]
    fn int_var_coerced() {
        let vars = make_vars(&[("FOO", sdf::Value::Int(7))]);
        assert_eq!(eval_value("${FOO}", &vars), sdf::Value::Int64(7));

        let vars = make_vars(&[("FOO", sdf::Value::IntVec(vec![1, 2]))]);
        assert_eq!(eval_value("${FOO}", &vars), sdf::Value::Int64Vec(vec![1, 2]));
    }

    #[test]
    fn eval_undefined_variable() {
        let vars = HashMap::new();
        assert_eq!(eval_errors("${FOO}", &vars), vec!["No value for variable 'FOO'"]);
    }

    #[test]
    fn eval_unsupported_type() {
        let vars = make_vars(&[("FOO", sdf::Value::Double(1.234))]);
        assert_eq!(
            eval_errors("${FOO}", &vars),
            vec!["Variable 'FOO' has unsupported type double"]
        );
        assert_eq!(
            eval_errors(r#"'test_${FOO}'"#, &vars),
            vec!["Variable 'FOO' has unsupported type double"]
        );
    }

    #[test]
    fn eval_string_interpolation() {
        let vars = make_vars(&[
            ("A", sdf::Value::String("substitution".to_string())),
            ("B", sdf::Value::String("works".to_string())),
        ]);
        assert_eq!(
            eval_value(r#""string_${A}_${B}""#, &vars),
            sdf::Value::String("string_substitution_works".to_string())
        );
        assert_eq!(
            eval_value(r#"'string_${A}_${B}'"#, &vars),
            sdf::Value::String("string_substitution_works".to_string())
        );
    }

    #[test]
    fn eval_none_interpolates_empty() {
        let vars = make_vars(&[("A", sdf::Value::None)]);
        assert_eq!(
            eval_value(r#"'none_sub_${A}'"#, &vars),
            sdf::Value::String("none_sub_".to_string())
        );
    }

    #[test]
    fn interpolate_nonstring_rejected() {
        let vars = make_vars(&[("A", sdf::Value::Int64(0))]);
        assert_eq!(
            eval_errors(r#"'bad_sub_${A}'"#, &vars),
            vec!["String value required for substituting variable 'A', got int."]
        );

        let vars = make_vars(&[("A", sdf::Value::Bool(true))]);
        assert_eq!(
            eval_errors(r#"'bad_sub_${A}'"#, &vars),
            vec!["String value required for substituting variable 'A', got bool."]
        );
    }

    #[test]
    fn interpolate_undefined_keeps_name() {
        // An undefined variable in a string substitutes as its own name and
        // is not an error (C++ leaves the substitution in place).
        let vars = HashMap::new();
        let expr = Expr::parse(r#"'x_${FOO}_y'"#).unwrap();
        let result = expr.evaluate(&vars);
        assert_eq!(result.errors, Vec::<String>::new());
        assert_eq!(
            result.value,
            Some(EvaluationValue::Value(sdf::Value::String("x_FOO_y".to_string())))
        );
        assert!(result.used_variables.contains("FOO"));
    }

    #[test]
    fn escaped_ref_survives_eval() {
        let vars = make_vars(&[
            ("A", sdf::Value::String("substitution".to_string())),
            ("B", sdf::Value::String("works".to_string())),
        ]);
        let expr = Expr::parse(r#""nosubs_\${A}_\${B}""#).unwrap();
        let result = expr.evaluate(&vars);
        assert_eq!(result.errors, Vec::<String>::new());
        assert_eq!(
            result.value,
            Some(EvaluationValue::Value(sdf::Value::String(
                "nosubs_${A}_${B}".to_string()
            )))
        );
        assert!(result.used_variables.is_empty());
    }

    #[test]
    fn eval_lists() {
        let vars = make_vars(&[("FOO", sdf::Value::Int64(2))]);
        assert_eq!(eval("[]", &vars), Some(EvaluationValue::EmptyList));
        assert_eq!(eval_value("[1, 2, 3]", &vars), sdf::Value::Int64Vec(vec![1, 2, 3]));
        assert_eq!(eval_value("[1, ${FOO}, 3]", &vars), sdf::Value::Int64Vec(vec![1, 2, 3]));
        assert_eq!(
            eval_value(r#"['a', 'b']"#, &vars),
            sdf::Value::StringVec(vec!["a".into(), "b".into()])
        );
        assert_eq!(
            eval_value("[True, False]", &vars),
            sdf::Value::BoolVec(vec![true, false])
        );

        let vars = make_vars(&[("FOO", sdf::Value::String("a".to_string()))]);
        assert_eq!(
            eval_value(r#"['${FOO}a', 'b']"#, &vars),
            sdf::Value::StringVec(vec!["aa".into(), "b".into()])
        );
    }

    #[test]
    fn eval_list_type_errors() {
        let vars = HashMap::new();
        assert_eq!(
            eval_errors("[None]", &vars),
            vec!["Unexpected value of type None in list at element 0"]
        );
        assert_eq!(
            eval_errors("[None, 2, 3]", &vars),
            vec!["Unexpected value of type None in list at element 0"]
        );

        let vars = make_vars(&[("FOO", sdf::Value::None)]);
        assert_eq!(
            eval_errors("[1, ${FOO}, 3]", &vars),
            vec!["Unexpected value of type None in list at element 1"]
        );

        // A list-valued variable cannot nest in a list.
        let vars = make_vars(&[("L", sdf::Value::String("`[]`".to_string()))]);
        assert_eq!(
            eval_errors("[${L}]", &vars),
            vec!["Unexpected value of type list in list at element 0"]
        );
        let vars = make_vars(&[("L", sdf::Value::IntVec(vec![1, 2]))]);
        assert_eq!(
            eval_errors("[${L}]", &vars),
            vec!["Unexpected value of type list in list at element 0"]
        );

        // Mixed types report one error per offending element.
        let vars = make_vars(&[("L", sdf::Value::String("`[]`".to_string()))]);
        assert_eq!(
            eval_errors(r#"[1, 'foo', False, ${L}]"#, &vars),
            vec![
                "Unexpected value of type string in list at element 1",
                "Unexpected value of type bool in list at element 2",
                "Unexpected value of type list in list at element 3",
            ]
        );
    }

    #[test]
    fn eval_if_function() {
        let vars = HashMap::new();
        assert_eq!(
            eval_value(r#"if(True, 'true', 'false')"#, &vars),
            sdf::Value::String("true".to_string())
        );
        assert_eq!(
            eval_value(r#"if(False, 'true', 'false')"#, &vars),
            sdf::Value::String("false".to_string())
        );
        assert_eq!(
            eval_value(r#"if(True, 'true')"#, &vars),
            sdf::Value::String("true".to_string())
        );
        assert_eq!(eval(r#"if(False, 'true')"#, &vars), None);

        let vars = make_vars(&[
            ("B", sdf::Value::Bool(true)),
            ("X", sdf::Value::Bool(false)),
            ("Y", sdf::Value::Bool(true)),
        ]);
        assert_eq!(
            eval_value("if(${B}, if(${X}, 1, 2), if(${Y}, 3, 4))", &vars),
            sdf::Value::Int64(2)
        );
    }

    #[test]
    fn eval_if_condition_errors() {
        let vars = HashMap::new();
        assert_eq!(
            eval_errors(r#"if('non_bool', 1, 0)"#, &vars),
            vec!["if: Condition must be a boolean value"]
        );
        // A subexpression error in the condition propagates as-is.
        assert_eq!(
            eval_errors(r#"if(eq(1, '1'), 1, 0)"#, &vars),
            vec!["eq: Cannot compare values of type int and string"]
        );
    }

    #[test]
    fn if_unchosen_error_dropped() {
        // The unchosen branch's errors are discarded (C++ returns the chosen
        // branch's result as-is), but its lookups still count as used.
        let vars = make_vars(&[("A", sdf::Value::String("ok".to_string()))]);
        let expr = Expr::parse("if(True, ${A}, ${MISSING})").unwrap();
        let result = expr.evaluate(&vars);
        assert_eq!(result.errors, Vec::<String>::new());
        assert_eq!(
            result.value,
            Some(EvaluationValue::Value(sdf::Value::String("ok".to_string())))
        );
        assert!(result.used_variables.contains("MISSING"));

        // Choosing the failing branch surfaces its error.
        let expr = Expr::parse("if(False, ${A}, ${MISSING})").unwrap();
        let result = expr.evaluate(&vars);
        assert_eq!(result.value, None);
        assert_eq!(result.errors, vec!["No value for variable 'MISSING'"]);
    }

    #[test]
    fn eval_if_branch_types() {
        // Both branches are type-checked even when untaken; None is
        // compatible with anything.
        let vars = HashMap::new();
        assert_eq!(eval("if(False, 1, None)", &vars), None);
        assert_eq!(eval_value("if(False, None, 1)", &vars), sdf::Value::Int64(1));
        assert_eq!(
            eval_errors(r#"if(False, 1, 'foo')"#, &vars),
            vec!["if: if-value and else-value must evaluate to the same type or None."]
        );
        assert_eq!(
            eval_errors(r#"if(False, 'foo', 1)"#, &vars),
            vec!["if: if-value and else-value must evaluate to the same type or None."]
        );
    }

    #[test]
    fn eval_comparisons() {
        let vars = HashMap::new();
        let cases = [
            ("eq(1, 1)", true),
            ("eq(1, 2)", false),
            ("neq(1, 2)", true),
            ("neq(1, 1)", false),
            ("lt(1, 2)", true),
            ("lt(2, 2)", false),
            ("leq(2, 2)", true),
            ("leq(3, 2)", false),
            ("gt(3, 2)", true),
            ("gt(2, 2)", false),
            ("geq(2, 2)", true),
            ("geq(1, 2)", false),
            (r#"eq('a', 'a')"#, true),
            (r#"lt('a', 'b')"#, true),
            (r#"lt('b', 'a')"#, false),
            ("eq(True, True)", true),
            ("neq(True, False)", true),
            ("lt(False, True)", true),
            ("eq(None, None)", true),
            ("neq(None, None)", false),
        ];
        for (src, expected) in cases {
            assert_eq!(eval_value(src, &vars), sdf::Value::Bool(expected), "evaluating {src}");
        }
    }

    #[test]
    fn eval_comparison_errors() {
        let vars = HashMap::new();
        assert_eq!(
            eval_errors(r#"eq(0, 'a')"#, &vars),
            vec!["eq: Cannot compare values of type int and string"]
        );
        assert_eq!(
            eval_errors("lt(0, False)", &vars),
            vec!["lt: Cannot compare values of type int and bool"]
        );
        assert_eq!(
            eval_errors("gt(0, None)", &vars),
            vec!["gt: Cannot compare values of type int and None"]
        );
        assert_eq!(
            eval_errors("lt(None, None)", &vars),
            vec!["lt: Comparison operation not supported for None"]
        );
        assert_eq!(
            eval_errors("eq([1], [1])", &vars),
            vec!["eq: Unsupported type for comparison"]
        );
    }

    #[test]
    fn empty_list_comparisons() {
        // A pair of untyped empty lists compares like `None` (C++'s
        // `EmptyList` reaches the generic equality overloads).
        let vars = HashMap::new();
        assert_eq!(eval_value("eq([], [])", &vars), sdf::Value::Bool(true));
        assert_eq!(eval_value("neq([], [])", &vars), sdf::Value::Bool(false));
        assert_eq!(
            eval_errors("lt([], [])", &vars),
            vec!["lt: Comparison operation not supported for None"]
        );
        assert_eq!(
            eval_errors("eq([], [1])", &vars),
            vec!["eq: Cannot compare values of type list and list"]
        );
    }

    #[test]
    fn eval_and_or_not() {
        let vars = HashMap::new();
        let cases = [
            ("and(True, True)", true),
            ("and(True, False)", false),
            ("and(True, True, False)", false),
            ("or(False, True)", true),
            ("or(False, False)", false),
            ("or(False, False, True)", true),
            ("not(True)", false),
            ("not(False)", true),
        ];
        for (src, expected) in cases {
            assert_eq!(eval_value(src, &vars), sdf::Value::Bool(expected), "evaluating {src}");
        }
    }

    #[test]
    fn eval_logical_type_errors() {
        let vars = HashMap::new();
        for func in ["and", "or"] {
            assert_eq!(
                eval_errors(&format!("{func}(1, 'foo', None)"), &vars),
                vec![
                    format!("{func}: Invalid type int for argument 0"),
                    format!("{func}: Invalid type string for argument 1"),
                    format!("{func}: Invalid type None for argument 2"),
                ]
            );
        }
        assert_eq!(eval_errors("not(1)", &vars), vec!["not: Invalid type int for argument"]);
        assert_eq!(
            eval_errors("not(None)", &vars),
            vec!["not: Invalid type None for argument"]
        );
    }

    #[test]
    fn eval_short_circuit() {
        // A decisive value stops evaluation before the invalid argument.
        let vars = HashMap::new();
        assert_eq!(eval_value("and(False, 1)", &vars), sdf::Value::Bool(false));
        assert_eq!(eval_value("and(True, False, 1)", &vars), sdf::Value::Bool(false));
        assert_eq!(eval_value("or(True, 1)", &vars), sdf::Value::Bool(true));
        assert_eq!(eval_value("or(False, True, 1)", &vars), sdf::Value::Bool(true));
    }

    #[test]
    fn matches_regex_string() {
        let vars = make_vars(&[("S", sdf::Value::String("shot_10.usd".to_string()))]);
        assert_eq!(
            eval_value(r#"matches_regex(${S}, 'shot_[[:digit:]]{2}\.usd')"#, &vars),
            sdf::Value::Bool(true)
        );

        let vars = make_vars(&[("S", sdf::Value::String("Shot_10.usd".to_string()))]);
        assert_eq!(
            eval_value(r#"matches_regex(${S}, 'shot_[[:digit:]]{2}\.usd')"#, &vars),
            sdf::Value::Bool(false)
        );

        // Unanchored search; explicit anchors simulate starts/ends-with.
        let vars = make_vars(&[("S", sdf::Value::String("shot_101_final.usd".to_string()))]);
        assert_eq!(
            eval_value(r#"matches_regex(${S}, '^shot.*')"#, &vars),
            sdf::Value::Bool(true)
        );
        assert_eq!(
            eval_value(r#"matches_regex(${S}, '.*final.usd$')"#, &vars),
            sdf::Value::Bool(true)
        );
        assert_eq!(
            eval_value(r#"matches_regex(${S}, '101')"#, &vars),
            sdf::Value::Bool(true)
        );
    }

    #[test]
    fn matches_regex_list_any() {
        let vars = make_vars(&[
            ("A", sdf::Value::String("shot1.usd".to_string())),
            ("B", sdf::Value::String("layer1.usd".to_string())),
        ]);
        assert_eq!(
            eval_value(r#"matches_regex([${A}, ${B}], 'layer.*')"#, &vars),
            sdf::Value::Bool(true)
        );
        assert_eq!(
            eval_value(r#"matches_regex([${A}, ${A}], 'layer.*')"#, &vars),
            sdf::Value::Bool(false)
        );
        assert_eq!(
            eval_value(r#"matches_regex([], 'layer.*')"#, &vars),
            sdf::Value::Bool(false)
        );
    }

    #[test]
    fn matches_regex_invalid_pattern() {
        let vars = make_vars(&[("S", sdf::Value::String("x".to_string()))]);
        let errors = eval_errors(r#"matches_regex(${S}, '(unclosed')"#, &vars);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].starts_with("matches_regex: Invalid match pattern: "));
    }

    #[test]
    fn matches_regex_nonstring_pattern() {
        let vars = HashMap::new();
        assert_eq!(
            eval_errors(r#"matches_regex('shot1', 7)"#, &vars),
            vec!["matches_regex: Pattern to match must be a string"]
        );
        assert_eq!(
            eval_errors(r#"matches_regex(['shot1'], 7)"#, &vars),
            vec!["matches_regex: Pattern to match must be a string"]
        );
        assert_eq!(
            eval_errors(r#"matches_regex(1, 'a')"#, &vars),
            vec!["matches_regex: Value to search must be string[] or string"]
        );
    }

    #[test]
    fn empty_list_skips_checks() {
        // An empty-list input answers `false` before the pattern or needle is
        // examined (C++ returns ahead of its argument-validating visitor).
        let vars = HashMap::new();
        assert_eq!(
            eval_value(r#"matches_regex([], '(unclosed')"#, &vars),
            sdf::Value::Bool(false)
        );
        assert_eq!(eval_value("contains([], None)", &vars), sdf::Value::Bool(false));
    }

    #[test]
    fn eval_contains() {
        let vars = make_vars(&[("L", sdf::Value::IntVec(vec![]))]);
        assert_eq!(eval_value("contains([], 1)", &vars), sdf::Value::Bool(false));
        assert_eq!(eval_value("contains(${L}, 1)", &vars), sdf::Value::Bool(false));

        let vars = make_vars(&[("A", sdf::Value::Int64(2))]);
        assert_eq!(eval_value("contains([1, 2, 3], 1)", &vars), sdf::Value::Bool(true));
        assert_eq!(eval_value("contains([1, 2, 3], 0)", &vars), sdf::Value::Bool(false));
        assert_eq!(eval_value("contains([1, 2, 3], ${A})", &vars), sdf::Value::Bool(true));

        let vars = HashMap::new();
        assert_eq!(eval_value(r#"contains('abc', 'a')"#, &vars), sdf::Value::Bool(true));
        assert_eq!(eval_value(r#"contains('abc', 'z')"#, &vars), sdf::Value::Bool(false));
        assert_eq!(eval_value(r#"contains('', 'a')"#, &vars), sdf::Value::Bool(false));
        assert_eq!(
            eval_value("contains([True, False], False)", &vars),
            sdf::Value::Bool(true)
        );
    }

    #[test]
    fn eval_contains_errors() {
        let vars = HashMap::new();
        assert_eq!(
            eval_errors(r#"contains([1, 2, 3], 'a')"#, &vars),
            vec!["contains: Invalid search value"]
        );
        assert_eq!(
            eval_errors("contains([1, 2, 3], None)", &vars),
            vec!["contains: Invalid search value"]
        );
        assert_eq!(
            eval_errors(r#"contains('abcd', 1)"#, &vars),
            vec!["contains: Invalid search value"]
        );
        assert_eq!(
            eval_errors("contains(1, 1)", &vars),
            vec!["contains: Value to search must be a list or string"]
        );
        assert_eq!(
            eval_errors("contains(None, 1)", &vars),
            vec!["contains: Value to search must be a list or string"]
        );
    }

    #[test]
    fn eval_at() {
        let vars = HashMap::new();
        assert_eq!(eval_value("at([1, 2, 3], 0)", &vars), sdf::Value::Int64(1));
        assert_eq!(eval_value("at([1, 2, 3], 2)", &vars), sdf::Value::Int64(3));
        assert_eq!(eval_value("at([1, 2, 3], -1)", &vars), sdf::Value::Int64(3));
        assert_eq!(eval_value("at([1, 2, 3], -3)", &vars), sdf::Value::Int64(1));
        assert_eq!(
            eval_value(r#"at('abc', 1)"#, &vars),
            sdf::Value::String("b".to_string())
        );
        assert_eq!(
            eval_value(r#"at('abc', -1)"#, &vars),
            sdf::Value::String("c".to_string())
        );
    }

    #[test]
    fn eval_at_errors() {
        let vars = HashMap::new();
        assert_eq!(eval_errors("at([1, 2, 3], 3)", &vars), vec!["at: Index out of range"]);
        assert_eq!(eval_errors("at([1, 2, 3], -4)", &vars), vec!["at: Index out of range"]);
        assert_eq!(eval_errors("at([], 0)", &vars), vec!["at: Index out of range"]);
        assert_eq!(eval_errors(r#"at('', 0)"#, &vars), vec!["at: Index out of range"]);
        assert_eq!(
            eval_errors(r#"at([1, 2, 3], 'foo')"#, &vars),
            vec!["at: Index must be an integer"]
        );
        assert_eq!(
            eval_errors("at([1, 2, 3], None)", &vars),
            vec!["at: Index must be an integer"]
        );
    }

    #[test]
    fn eval_len() {
        let vars = HashMap::new();
        assert_eq!(eval_value("len([])", &vars), sdf::Value::Int64(0));
        assert_eq!(eval_value("len([1, 2, 3])", &vars), sdf::Value::Int64(3));
        assert_eq!(eval_value(r#"len('')"#, &vars), sdf::Value::Int64(0));
        assert_eq!(eval_value(r#"len('abc')"#, &vars), sdf::Value::Int64(3));
        assert_eq!(eval_errors("len(1)", &vars), vec!["len: Unsupported type"]);
        assert_eq!(eval_errors("len(None)", &vars), vec!["len: Unsupported type"]);
    }

    #[test]
    fn defined_quoted_names() {
        let vars = make_vars(&[("X", sdf::Value::Int64(0)), ("Y", sdf::Value::Int64(1))]);
        assert_eq!(eval_value(r#"defined('X')"#, &vars), sdf::Value::Bool(true));
        assert_eq!(eval_value(r#"defined('Z')"#, &vars), sdf::Value::Bool(false));
        assert_eq!(eval_value(r#"defined('X', 'Y')"#, &vars), sdf::Value::Bool(true));
        assert_eq!(eval_value(r#"defined('X', 'Z')"#, &vars), sdf::Value::Bool(false));
    }

    #[test]
    fn defined_nonstring_arg() {
        let vars = HashMap::new();
        assert_eq!(
            eval_errors("defined(1)", &vars),
            vec!["defined: Invalid type int for argument 0"]
        );
        assert_eq!(
            eval_errors("defined(None)", &vars),
            vec!["defined: Invalid type None for argument 0"]
        );
    }

    #[test]
    fn defined_records_names() {
        let vars = make_vars(&[("X", sdf::Value::Int64(0))]);
        let expr = Expr::parse(r#"defined('X', 'Y')"#).unwrap();
        let result = expr.evaluate(&vars);
        assert_eq!(result.value, Some(EvaluationValue::Value(sdf::Value::Bool(false))));
        assert!(result.used_variables.contains("X"));
        assert!(result.used_variables.contains("Y"));
    }

    #[test]
    fn eval_recursive_variable() {
        let vars = make_vars(&[
            ("FOO", sdf::Value::String("`${BAR}`".to_string())),
            ("BAR", sdf::Value::String("ok".to_string())),
        ]);
        assert_eq!(eval_value("${FOO}", &vars), sdf::Value::String("ok".to_string()));

        let vars = make_vars(&[
            ("FOO", sdf::Value::String("`'subexpression_${BAR}'`".to_string())),
            ("BAR", sdf::Value::String("`'${BAZ}'`".to_string())),
            ("BAZ", sdf::Value::String("`'works_ok'`".to_string())),
        ]);
        assert_eq!(
            eval_value("${FOO}", &vars),
            sdf::Value::String("subexpression_works_ok".to_string())
        );

        let vars = make_vars(&[
            ("A", sdf::Value::String("`'subexpression_${FOO}'`".to_string())),
            ("FOO", sdf::Value::String("`'${BAR}'`".to_string())),
            ("BAR", sdf::Value::String("`'works_ok'`".to_string())),
            ("B", sdf::Value::String("`${A}`".to_string())),
        ]);
        assert_eq!(
            eval_value(r#"'${A}_${B}'"#, &vars),
            sdf::Value::String("subexpression_works_ok_subexpression_works_ok".to_string())
        );
    }

    #[test]
    fn eval_circular_error() {
        let vars = make_vars(&[
            ("FOO", sdf::Value::String("`${BAR}`".to_string())),
            ("BAR", sdf::Value::String("`${BAZ}`".to_string())),
            ("BAZ", sdf::Value::String("`${FOO}`".to_string())),
        ]);
        assert_eq!(
            eval_errors("${FOO}", &vars),
            vec!["Encountered circular variable substitutions: ['FOO', 'BAR', 'BAZ', 'FOO']"]
        );
    }

    #[test]
    fn eval_nested_parse_error() {
        // A parse error in a variable's expression value names the variable.
        let vars = make_vars(&[
            ("FOO", sdf::Value::String("`'${BAR}'`".to_string())),
            ("BAR", sdf::Value::String("`${BAZ`".to_string())),
        ]);
        let errors = eval_errors("${FOO}", &vars);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].ends_with("(in variable 'BAR')"), "got {:?}", errors[0]);
    }

    #[test]
    fn used_vars_reported() {
        let vars = make_vars(&[
            ("A", sdf::Value::String("`'${B}'`".to_string())),
            ("B", sdf::Value::String("x".to_string())),
        ]);
        let expr = Expr::parse(r#"'${A}'"#).unwrap();
        let result = expr.evaluate(&vars);
        assert_eq!(result.errors, Vec::<String>::new());
        assert_eq!(result.used_variables, HashSet::from(["A".to_string(), "B".to_string()]));
    }

    #[test]
    fn used_vars_on_failure() {
        // Invalidation depends on used variables being reported even when
        // evaluation fails.
        let vars = HashMap::new();
        let expr = Expr::parse("eq(${A}, ${B})").unwrap();
        let result = expr.evaluate(&vars);
        assert!(result.value.is_none());
        assert!(!result.errors.is_empty());
        assert_eq!(result.used_variables, HashSet::from(["A".to_string(), "B".to_string()]));
    }

    #[test]
    fn eval_error_aggregation() {
        let vars = HashMap::new();
        assert_eq!(
            eval_errors("eq(${A}, ${B})", &vars),
            vec!["No value for variable 'A'", "No value for variable 'B'"]
        );
    }

    #[test]
    fn evaluate_string_passthrough() {
        let vars = HashMap::new();
        let result = evaluate_string("plain/path.usd", &vars);
        assert_eq!(result.value.as_deref(), Some("plain/path.usd"));
        assert!(result.errors.is_empty());
        assert!(result.used_variables.is_empty());
    }

    #[test]
    fn evaluate_string_expression() {
        let vars = make_vars(&[("PATH", sdf::Value::String("/assets".to_string()))]);
        let result = evaluate_string(r#"`"${PATH}/model.usd"`"#, &vars);
        assert_eq!(result.value.as_deref(), Some("/assets/model.usd"));
        assert!(result.errors.is_empty());
        assert_eq!(result.used_variables, HashSet::from(["PATH".to_string()]));
    }

    #[test]
    fn evaluate_string_nonstring() {
        let vars = HashMap::new();
        let result = evaluate_string("`42`", &vars);
        assert_eq!(result.value, None);
        assert_eq!(
            result.errors,
            vec!["Expression evaluated to 'int' but expected 'string'"]
        );
    }

    #[test]
    fn evaluate_string_none_silent() {
        // The expression-language None yields no value and no errors.
        let vars = HashMap::new();
        let result = evaluate_string(r#"`if(False, "x")`"#, &vars);
        assert_eq!(result.value, None);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn evaluate_string_parse_error() {
        let vars = HashMap::new();
        let result = evaluate_string("`${FO-O}`", &vars);
        assert_eq!(result.value, None);
        assert!(!result.errors.is_empty());
    }

    #[test]
    fn evaluate_string_reports_used_on_failure() {
        let vars = HashMap::new();
        let result = evaluate_string("`${MISSING}`", &vars);
        assert_eq!(result.value, None);
        assert_eq!(result.errors, vec!["No value for variable 'MISSING'"]);
        assert_eq!(result.used_variables, HashSet::from(["MISSING".to_string()]));
    }
}
