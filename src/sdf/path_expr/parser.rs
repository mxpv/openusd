//! The recursive-descent parser behind [`PathExpression::parse`] and
//! [`PredicateExpression::parse`], mirroring the C++ PEG grammar in
//! `pathExpressionParser.h` / `pathPatternParser.h` /
//! `predicateExpressionParser.h`, including its commitment points: once a
//! construct's opening token is consumed, a malformed continuation is an
//! error rather than a backtrack.

use crate::sdf::Path;

use super::pattern::PathPattern;
use super::predicate::{FnArg, FnCall, FnCallKind, PredNode, PredOp, PredRepr, PredicateArg, PredicateExpression};
use super::{ExpressionReference, PathExpression, SetOp};

/// How deep groups and `not` chains may nest. The recursive-descent parser
/// consumes native stack per level, and expressions arrive from arbitrary
/// files, so nesting is bounded rather than crashing on crafted input.
const MAX_NESTING: usize = 128;

/// Parses a full path expression, capturing a failure as the empty
/// expression plus its error text.
pub(super) fn parse_path_expression(input: &str) -> PathExpression {
    let mut cursor = Cursor::new(input);
    let parsed = (|| {
        cursor.skip_blanks();
        let expr = parse_expr(&mut cursor, 0, 0)?;
        cursor.skip_blanks();
        if !cursor.at_end() {
            return Err(cursor.fail("expected end of path expression"));
        }
        Ok(expr)
    })();
    match parsed {
        Ok(expr) => expr,
        Err(fail) => PathExpression::invalid(input.to_string(), fail.format("path expression", input)),
    }
}

/// Parses a standalone predicate expression, capturing a failure as the
/// empty expression plus its error text.
pub(super) fn parse_predicate_expression(input: &str) -> PredicateExpression {
    let mut cursor = Cursor::new(input);
    let parsed = (|| {
        cursor.skip_blanks();
        if cursor.at_end() {
            return Ok(None);
        }
        let node = parse_pred_expr(&mut cursor, 0, 0)?;
        cursor.skip_blanks();
        if !cursor.at_end() {
            return Err(cursor.fail("expected end of predicate expression"));
        }
        Ok(Some(node))
    })();
    match parsed {
        Ok(Some(root)) => PredicateExpression(PredRepr::Expr(root)),
        Ok(None) => PredicateExpression::default(),
        Err(fail) => PredicateExpression(PredRepr::Invalid {
            text: input.to_string(),
            message: fail.format("predicate expression", input),
        }),
    }
}

/// Whether `text` reads back as the same bare (unquoted) string argument, so
/// the printer may skip the quotes.
pub(super) fn is_bare_argument_token(text: &str) -> bool {
    !text.is_empty()
        && text.chars().all(|c| c.is_alphanumeric() || c == '_')
        && text != "true"
        && text != "false"
        && text.parse::<i64>().is_err()
        && text.parse::<f64>().is_err()
}

/// A char-indexed cursor over the input, cheap to save and restore for the
/// grammar's ordered-choice backtracking.
struct Cursor {
    chars: Vec<char>,
    pos: usize,
}

/// A parse failure at a character position; the position is 1-based in the
/// formatted message.
struct ParseFail {
    pos: usize,
    message: String,
}

impl ParseFail {
    fn format(&self, what: &str, input: &str) -> String {
        let at = input
            .chars()
            .nth(self.pos)
            .unwrap_or_else(|| input.chars().last().unwrap_or(' '));
        format!(
            "Ill-formed {what} <{input}> at character {} ('{at}'): {}",
            self.pos + 1,
            self.message
        )
    }
}

impl Cursor {
    fn new(input: &str) -> Self {
        Cursor {
            chars: input.chars().collect(),
            pos: 0,
        }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.chars.len()
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<char> {
        self.chars.get(self.pos + offset).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn at_str(&self, s: &str) -> bool {
        s.chars().enumerate().all(|(i, c)| self.peek_at(i) == Some(c))
    }

    fn eat_str(&mut self, s: &str) -> bool {
        if self.at_str(s) {
            self.pos += s.chars().count();
            true
        } else {
            false
        }
    }

    fn skip_blanks(&mut self) -> usize {
        let start = self.pos;
        while matches!(self.peek(), Some(' ' | '\t' | '\n' | '\r')) {
            self.pos += 1;
        }
        self.pos - start
    }

    fn fail(&self, message: &str) -> ParseFail {
        ParseFail {
            pos: self.pos.min(self.chars.len().saturating_sub(1)),
            message: message.to_string(),
        }
    }
}

/// Whether `c` may appear in an identifier (a prim-name character).
fn is_identifier_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Whether `c` may start an identifier.
fn is_identifier_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

/// Consumes one identifier, or fails with `message`.
fn parse_identifier(cursor: &mut Cursor, message: &str) -> Result<String, ParseFail> {
    if !cursor.peek().is_some_and(is_identifier_start) {
        return Err(cursor.fail(message));
    }
    let mut out = String::new();
    while let Some(c) = cursor.peek() {
        if !is_identifier_char(c) {
            break;
        }
        out.push(c);
        cursor.pos += 1;
    }
    Ok(out)
}

// Path-expression grammar

/// Binding power per operator; higher binds tighter. Left associativity
/// comes from re-entering with `bp + 1`.
fn binding_power(op: SetOp) -> u8 {
    match op {
        SetOp::ImpliedUnion => 40,
        SetOp::Union => 30,
        SetOp::Intersection => 20,
        SetOp::Difference => 10,
    }
}

fn parse_expr(cursor: &mut Cursor, min_bp: u8, depth: usize) -> Result<PathExpression, ParseFail> {
    let mut lhs = parse_factor(cursor, depth)?;
    loop {
        let save = cursor.pos;
        let blanks = cursor.skip_blanks();
        let op = match cursor.peek() {
            Some('+') => Some(SetOp::Union),
            Some('&') => Some(SetOp::Intersection),
            Some('-') => Some(SetOp::Difference),
            // Whitespace joins two factors as an implied union; trailing
            // whitespace is not an operator.
            _ if blanks > 0 && at_factor_start(cursor) => Some(SetOp::ImpliedUnion),
            _ => None,
        };
        let Some(op) = op else {
            cursor.pos = save;
            return Ok(lhs);
        };
        if binding_power(op) < min_bp {
            cursor.pos = save;
            return Ok(lhs);
        }
        if op != SetOp::ImpliedUnion {
            cursor.pos += 1;
            cursor.skip_blanks();
            if !at_factor_start(cursor) {
                return Err(cursor.fail("expected path expression after operator"));
            }
        }
        let rhs = parse_expr(cursor, binding_power(op) + 1, depth)?;
        lhs = PathExpression::make_op(op, lhs, rhs);
    }
}

/// Whether the cursor sits at the start of a factor: a complement, a group,
/// a reference, or a pattern.
fn at_factor_start(cursor: &Cursor) -> bool {
    match cursor.peek() {
        Some('~' | '(' | '%' | '/' | '.' | '?' | '*' | '[' | '{') => true,
        Some(c) => is_identifier_char(c),
        None => false,
    }
}

fn parse_factor(cursor: &mut Cursor, depth: usize) -> Result<PathExpression, ParseFail> {
    if cursor.eat('~') {
        cursor.skip_blanks();
        let atom = parse_atom(cursor, depth)?;
        return Ok(PathExpression::make_complement(atom));
    }
    parse_atom(cursor, depth)
}

fn parse_atom(cursor: &mut Cursor, depth: usize) -> Result<PathExpression, ParseFail> {
    if cursor.eat('(') {
        if depth >= MAX_NESTING {
            return Err(cursor.fail("expression nesting too deep"));
        }
        cursor.skip_blanks();
        if !at_factor_start(cursor) {
            return Err(cursor.fail("expected path expression after '('"));
        }
        let inner = parse_expr(cursor, 0, depth + 1)?;
        cursor.skip_blanks();
        if !cursor.eat(')') {
            return Err(cursor.fail("expected ')' to close expression group"));
        }
        return Ok(inner);
    }
    if cursor.eat('%') {
        return Ok(PathExpression::make_atom_reference(parse_reference(cursor)?));
    }
    if let Some(pattern) = parse_pattern(cursor)? {
        return Ok(PathExpression::make_atom_pattern(pattern));
    }
    Err(cursor.fail("expected path expression"))
}

/// Parses an expression reference, with the leading `%` already consumed.
fn parse_reference(cursor: &mut Cursor) -> Result<ExpressionReference, ParseFail> {
    // `%_` is the weaker reference only when nothing identifier-like (or a
    // collection `:`) continues it.
    if cursor.peek() == Some('_') && !cursor.peek_at(1).is_some_and(|c| is_identifier_char(c) || c == ':') {
        cursor.pos += 1;
        return Ok(ExpressionReference::weaker());
    }

    let mut path = String::new();
    if cursor.eat('/') {
        // Absolute: `/ident(/ident)*:name`.
        parse_reference_elements(cursor, &mut path, "expected expression reference path after '/'")?;
    } else {
        // Relative: an optional `..(/..)*` chain, then either `/ident...` or
        // directly the `:name`.
        while cursor.at_str("..") {
            cursor.pos += 2;
            path.push_str("..");
            if cursor.at_str("/..") {
                cursor.pos += 1;
                path.push('/');
            } else {
                break;
            }
        }
        if cursor.eat('/') {
            parse_reference_elements(cursor, &mut path, "expected identifier")?;
        } else if path.is_empty() && !cursor.at_str(":") {
            // Bare `%name` has no form: a relative reference needs `..`, a
            // `/`, or an immediate `:`.
            return Err(cursor.fail("expected identifier"));
        }
    }

    if !cursor.eat(':') {
        return Err(cursor.fail("expected identifier"));
    }
    let name = parse_identifier(cursor, "expected identifier")?;
    // A bare `%:name` carries no path — the reference resolves against the
    // expression's own prim — represented as the empty path.
    let path = if path.is_empty() {
        Path::default()
    } else {
        Path::new(&path).map_err(|_| cursor.fail("invalid expression reference path"))?
    };
    Ok(ExpressionReference { path, name })
}

/// Appends the `ident('/'ident)*` run of a reference path to `path`, each
/// element with its leading `/`; the opening `/` is already consumed.
/// `first` is the failure message for the leading identifier.
fn parse_reference_elements(cursor: &mut Cursor, path: &mut String, first: &str) -> Result<(), ParseFail> {
    path.push('/');
    path.push_str(&parse_identifier(cursor, first)?);
    while cursor.eat('/') {
        path.push('/');
        path.push_str(&parse_identifier(cursor, "expected identifier")?);
    }
    Ok(())
}

/// Parses one path pattern, or `None` when the cursor does not sit at one.
fn parse_pattern(cursor: &mut Cursor) -> Result<Option<PathPattern>, ParseFail> {
    let mut pattern = PathPattern::default();

    if cursor.eat('/') {
        pattern.set_prefix(Path::abs_root());
        if cursor.eat('/') {
            // `//` — a leading stretch, optionally followed by elements.
            pattern.append_stretch_if_possible();
            if at_element_start(cursor) {
                parse_elements(cursor, &mut pattern)?;
            }
        } else if at_element_start(cursor) {
            parse_elements(cursor, &mut pattern)?;
        }
        return Ok(Some(pattern));
    }

    if cursor.at_str("..") {
        while cursor.at_str("..") {
            cursor.pos += 2;
            pattern.append_child("..", None);
            if cursor.at_str("/..") {
                cursor.pos += 1;
            } else {
                break;
            }
        }
        if cursor.eat_str("//") {
            pattern.append_stretch_if_possible();
            if at_element_start(cursor) {
                parse_elements(cursor, &mut pattern)?;
            }
        } else if cursor.eat('/') {
            parse_elements(cursor, &mut pattern)?;
        }
        return Ok(Some(pattern));
    }

    if cursor.peek() == Some('.') {
        // The reflexive `.`, optionally opening a stretch.
        cursor.pos += 1;
        pattern.set_prefix(Path::new(".").expect("the reflexive relative path is valid"));
        if cursor.eat_str("//") {
            pattern.append_stretch_if_possible();
            if at_element_start(cursor) {
                parse_elements(cursor, &mut pattern)?;
            }
        }
        return Ok(Some(pattern));
    }

    if at_element_start(cursor) {
        parse_elements(cursor, &mut pattern)?;
        return Ok(Some(pattern));
    }

    Ok(None)
}

/// Whether the cursor sits at the start of a prim pattern element.
fn at_element_start(cursor: &Cursor) -> bool {
    match cursor.peek() {
        Some('?' | '*' | '[' | '{') => true,
        Some(c) => is_identifier_char(c),
        None => false,
    }
}

/// Parses the element run of a pattern: the first prim element, `/` and `//`
/// separated successors, and the optional trailing `.property` element or
/// trailing stretch.
fn parse_elements(cursor: &mut Cursor, pattern: &mut PathPattern) -> Result<(), ParseFail> {
    let (text, predicate) = parse_element(cursor, false, "expected path pattern element")?;
    pattern.append_child(text, predicate);
    loop {
        if cursor.at_str("//") {
            cursor.pos += 2;
            pattern.append_stretch_if_possible();
            if at_element_start(cursor) {
                let (text, predicate) = parse_element(cursor, false, "expected path pattern element")?;
                pattern.append_child(text, predicate);
            } else {
                // Trailing stretch.
                return Ok(());
            }
        } else if cursor.peek() == Some('/') {
            cursor.pos += 1;
            let (text, predicate) = parse_element(cursor, false, "expected path pattern element after '/'")?;
            pattern.append_child(text, predicate);
        } else if cursor.peek() == Some('.') {
            cursor.pos += 1;
            let (text, predicate) = parse_element(cursor, true, "expected property pattern element after '.'")?;
            pattern.append_property(text, predicate);
            return Ok(());
        } else {
            return Ok(());
        }
    }
}

/// Parses one element: glob text, a `{predicate}`, or both; `property`
/// widens the text charset with `:`.
fn parse_element(
    cursor: &mut Cursor,
    property: bool,
    message: &str,
) -> Result<(String, Option<PredicateExpression>), ParseFail> {
    let mut text = String::new();
    loop {
        match cursor.peek() {
            Some('?' | '*') => text.push(cursor.bump().expect("peeked")),
            Some(':') if property => text.push(cursor.bump().expect("peeked")),
            Some('[') => {
                cursor.pos += 1;
                text.push('[');
                let mut any = false;
                while let Some(c) = cursor.peek() {
                    if is_identifier_char(c) || matches!(c, '!' | '-' | '?' | '*') {
                        text.push(c);
                        cursor.pos += 1;
                        any = true;
                    } else {
                        break;
                    }
                }
                if !any || !cursor.eat(']') {
                    return Err(cursor.fail("expected ']' to close bracket class"));
                }
                text.push(']');
            }
            Some(c) if is_identifier_char(c) => {
                text.push(c);
                cursor.pos += 1;
            }
            _ => break,
        }
    }

    let predicate = if cursor.eat('{') {
        cursor.skip_blanks();
        let node = parse_pred_expr(cursor, 0, 0)?;
        cursor.skip_blanks();
        if !cursor.eat('}') {
            return Err(cursor.fail("expected '}' to close predicate expression"));
        }
        Some(PredicateExpression(PredRepr::Expr(node)))
    } else {
        None
    };

    if text.is_empty() && predicate.is_none() {
        return Err(cursor.fail(message));
    }
    Ok((text, predicate))
}

// Predicate-expression grammar

/// Whether the keyword `word` sits at the cursor as a whole word.
fn at_keyword(cursor: &Cursor, word: &str) -> bool {
    cursor.at_str(word) && !cursor.peek_at(word.chars().count()).is_some_and(is_identifier_char)
}

/// The infix operator keywords; whitespace alone spells
/// [`PredOp::ImpliedAnd`], which no keyword introduces.
const PRED_KEYWORDS: [(&str, PredOp); 2] = [("or", PredOp::Or), ("and", PredOp::And)];

/// Binding power per predicate operator; higher binds tighter, as in
/// [`binding_power`] on the path-expression side.
fn pred_binding_power(op: PredOp) -> u8 {
    match op {
        PredOp::ImpliedAnd => 30,
        PredOp::And => 20,
        PredOp::Or => 10,
    }
}

/// Parses a chain of unary operands joined by `and`, `or`, or the
/// whitespace that spells an implied and, loosest operator first. Left
/// associativity comes from re-entering with `bp + 1`.
fn parse_pred_expr(cursor: &mut Cursor, min_bp: u8, depth: usize) -> Result<PredNode, ParseFail> {
    let mut lhs = parse_pred_unary(cursor, depth)?;
    loop {
        let save = cursor.pos;
        let blanks = cursor.skip_blanks();
        // A keyword wins over the implied-and reading of the whitespace that
        // precedes it.
        let op = PRED_KEYWORDS
            .iter()
            .find(|(word, _)| at_keyword(cursor, word))
            .map(|&(word, op)| (op, word.chars().count()))
            .or_else(|| (blanks > 0 && at_pred_unary_start(cursor)).then_some((PredOp::ImpliedAnd, 0)));
        let Some((op, keyword)) = op else {
            cursor.pos = save;
            return Ok(lhs);
        };
        if pred_binding_power(op) < min_bp {
            cursor.pos = save;
            return Ok(lhs);
        }
        cursor.pos += keyword;
        cursor.skip_blanks();
        let rhs = parse_pred_expr(cursor, pred_binding_power(op) + 1, depth)?;
        lhs = PredNode::Op(op, Box::new(lhs), Box::new(rhs));
    }
}

fn at_pred_unary_start(cursor: &Cursor) -> bool {
    cursor.peek() == Some('(') || cursor.peek().is_some_and(is_identifier_start)
}

fn parse_pred_unary(cursor: &mut Cursor, depth: usize) -> Result<PredNode, ParseFail> {
    if depth >= MAX_NESTING {
        return Err(cursor.fail("expression nesting too deep"));
    }
    if at_keyword(cursor, "not") {
        cursor.pos += 3;
        cursor.skip_blanks();
        let operand = parse_pred_unary(cursor, depth + 1)?;
        return Ok(PredNode::Not(Box::new(operand)));
    }
    if cursor.eat('(') {
        cursor.skip_blanks();
        // A group resets precedence, as its parentheses spell out.
        let inner = parse_pred_expr(cursor, 0, depth + 1)?;
        cursor.skip_blanks();
        if !cursor.eat(')') {
            return Err(cursor.fail("expected ')' to close predicate group"));
        }
        return Ok(inner);
    }
    Ok(PredNode::Call(parse_pred_call(cursor)?))
}

fn parse_pred_call(cursor: &mut Cursor) -> Result<FnCall, ParseFail> {
    let name = parse_identifier(cursor, "expected predicate function name")?;

    if cursor.eat(':') {
        // Colon call: comma-separated positional values, no spaces.
        let mut args = vec![FnArg {
            name: None,
            value: parse_pred_value(cursor)?,
        }];
        while cursor.eat(',') {
            args.push(FnArg {
                name: None,
                value: parse_pred_value(cursor)?,
            });
        }
        return Ok(FnCall {
            kind: FnCallKind::Colon,
            name,
            args,
        });
    }

    if cursor.eat('(') {
        let mut args = Vec::new();
        cursor.skip_blanks();
        if !cursor.eat(')') {
            loop {
                args.push(parse_pred_paren_arg(cursor, args.last())?);
                cursor.skip_blanks();
                if cursor.eat(',') {
                    cursor.skip_blanks();
                    continue;
                }
                if cursor.eat(')') {
                    break;
                }
                return Err(cursor.fail("expected ')' to close argument list"));
            }
        }
        return Ok(FnCall {
            kind: FnCallKind::Paren,
            name,
            args,
        });
    }

    Ok(FnCall {
        kind: FnCallKind::Bare,
        name,
        args: Vec::new(),
    })
}

/// Parses one paren-call argument; keyword arguments must follow every
/// positional one.
fn parse_pred_paren_arg(cursor: &mut Cursor, previous: Option<&FnArg>) -> Result<FnArg, ParseFail> {
    // A keyword argument is an identifier followed by `=`; anything else is a
    // positional value (which may itself be a bare identifier).
    let save = cursor.pos;
    if cursor.peek().is_some_and(is_identifier_start) {
        if let Ok(keyword) = parse_identifier(cursor, "expected identifier") {
            cursor.skip_blanks();
            if cursor.eat('=') {
                cursor.skip_blanks();
                return Ok(FnArg {
                    name: Some(keyword),
                    value: parse_pred_value(cursor)?,
                });
            }
        }
        cursor.pos = save;
    }
    if previous.is_some_and(|arg| arg.name.is_some()) {
        return Err(cursor.fail("expected keyword argument after keyword argument"));
    }
    Ok(FnArg {
        name: None,
        value: parse_pred_value(cursor)?,
    })
}

/// Parses one argument value: a double-quoted string, or a bare token typed
/// as bool, integer, float, or string.
fn parse_pred_value(cursor: &mut Cursor) -> Result<PredicateArg, ParseFail> {
    if cursor.eat('"') {
        let mut out = String::new();
        loop {
            match cursor.bump() {
                Some('"') => return Ok(PredicateArg::String(out)),
                Some('\\') => match cursor.bump() {
                    Some(escaped) => out.push(escaped),
                    None => return Err(cursor.fail("expected '\"' to close string")),
                },
                Some(c) => out.push(c),
                None => return Err(cursor.fail("expected '\"' to close string")),
            }
        }
    }

    let mut token = String::new();
    while let Some(c) = cursor.peek() {
        if c.is_whitespace() || matches!(c, ',' | ')' | '}' | '(' | '=' | '"') {
            break;
        }
        token.push(c);
        cursor.pos += 1;
    }
    if token.is_empty() {
        return Err(cursor.fail("expected argument value"));
    }
    Ok(match token.as_str() {
        "true" => PredicateArg::Bool(true),
        "false" => PredicateArg::Bool(false),
        _ => {
            if let Ok(int) = token.parse::<i64>() {
                PredicateArg::Int(int)
            } else if let Ok(float) = token.parse::<f64>() {
                PredicateArg::Float(float)
            } else {
                PredicateArg::String(token)
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::super::{ExpressionReference, PathExpression, PredicateExpression};

    /// Parses and asserts the canonical text form.
    fn round_trip(input: &str, expected: &str) {
        let expr = PathExpression::parse(input);
        assert!(expr.parse_error().is_none(), "{input}: {:?}", expr.parse_error());
        assert_eq!(expr.to_string(), expected, "for {input}");
    }

    /// Parses and asserts the input is already canonical.
    fn canonical(input: &str) {
        round_trip(input, input);
    }

    #[test]
    fn patterns_round_trip() {
        canonical("/foo/bar/baz");
        canonical("//");
        canonical("/foo//bar");
        canonical("/foo//");
        canonical("//Robot*");
        canonical("/World/anim/chars/[Mm]ike*");
        canonical(".//");
        canonical("foo/bar");
        canonical("../../sib");
        canonical("/foo.attr");
        canonical("/foo.attr:ns");
        canonical("//*.rel");
        canonical("/");
        canonical(".");
    }

    #[test]
    fn operators_and_precedence() {
        canonical("/a// + /b//");
        canonical("/a// - /b//");
        canonical("/a// & /b//");
        canonical("/a// /b//");
        canonical("~/a//");
        // Whitespace binds tighter than `+`, which binds tighter than `&`,
        // which binds tighter than `-` — so the canonical form of a
        // left-to-right chain adds no parentheses.
        canonical("/a /b + /c & /d - /e");
        // Grouping against precedence keeps its parentheses.
        canonical("/a - (/b - /c)");
        canonical("~(/a + /b)");
        round_trip("(/a + /b) - /c", "/a + /b - /c");
        // The C++ header's worked example.
        canonical("/foo/bar// /foo/baz// & ~/foo/bar/qux// %_");
    }

    #[test]
    fn references_round_trip() {
        canonical("%_");
        canonical("%:name");
        canonical("%/World/Sets:big");
        canonical("%../up:sel");
        canonical("%..:sel");
        canonical("/a// %/Sets:b");
    }

    #[test]
    fn weaker_ref_lookahead() {
        // `%_x` and `%_:x` are not the weaker reference, and since a bare
        // identifier is no reference path either, both are ill-formed rather
        // than silently splitting after `%_`.
        assert!(PathExpression::parse("%_x").parse_error().is_some());
        assert!(PathExpression::parse("%_:x").parse_error().is_some());
        // Whitespace after `%_` ends the reference normally.
        assert!(PathExpression::parse("%_ /a//").parse_error().is_none());
    }

    #[test]
    fn predicates_round_trip() {
        canonical("//{isa:Imageable}");
        canonical("//Robot*{kind:component}");
        canonical("//{isa:Scope and defined}");
        canonical("//{not abstract}");
        canonical("//{a b or c}");
        canonical("//{(a or b) and c}");
        // Left associativity: a right-leaning tree of equal-rank operators
        // would print its right operand parenthesized.
        canonical("//{a or b or c}");
        canonical("//{a and b and c}");
        canonical("//{isClose(1.23, tolerance=0.01)}");
        canonical("//{variant(standin=render)}");
        round_trip("//{ isa:Imageable }", "//{isa:Imageable}");
    }

    #[test]
    fn predicate_arg_typing() {
        use super::super::{FnCallKind, PredicateArg};
        let expr = PredicateExpression::parse("f(1, 2.5, true, name, kw=\"quo ted\")");
        assert!(expr.parse_error().is_none(), "{:?}", expr.parse_error());
        let super::PredRepr::Expr(super::PredNode::Call(call)) = &expr.0 else {
            panic!("expected a single call");
        };
        assert_eq!(call.kind, FnCallKind::Paren);
        assert_eq!(call.args[0].value, PredicateArg::Int(1));
        assert_eq!(call.args[1].value, PredicateArg::Float(2.5));
        assert_eq!(call.args[2].value, PredicateArg::Bool(true));
        assert_eq!(call.args[3].value, PredicateArg::String("name".to_string()));
        assert_eq!(call.args[4].name.as_deref(), Some("kw"));
        assert_eq!(call.args[4].value, PredicateArg::String("quo ted".to_string()));
        assert_eq!(expr.to_string(), "f(1, 2.5, true, name, kw=\"quo ted\")");
    }

    #[test]
    fn constants_and_algebra() {
        assert_eq!(PathExpression::parse("//"), PathExpression::everything());
        assert_eq!(PathExpression::parse(".//"), PathExpression::every_descendant());
        assert_eq!(PathExpression::parse(""), PathExpression::nothing());
        // The constructor algebra folds constants during parsing.
        assert_eq!(PathExpression::parse("~//"), PathExpression::nothing());
        assert_eq!(PathExpression::parse("/a// + //"), PathExpression::everything());
        assert_eq!(PathExpression::parse("// & /a//"), PathExpression::parse("/a//"));
    }

    #[test]
    fn parse_errors() {
        for (input, fragment) in [
            ("/a +", "expected path expression after operator"),
            ("(/a", "expected ')' to close expression group"),
            ("()", "expected path expression after '('"),
            ("/a !", "expected end of path expression"),
            ("//{unclosed", "expected '}' to close predicate expression"),
            ("/a/[b", "expected ']' to close bracket class"),
            ("%name", "expected identifier"),
            ("/a/", "expected path pattern element after '/'"),
            // The parser has no `*`-insertion: a property directly after a
            // stretch is spelled `//*.foo`, not `//.foo`.
            ("/x//.foo", "expected end of path expression"),
        ] {
            let expr = PathExpression::parse(input);
            let error = expr.parse_error().unwrap_or_else(|| panic!("{input} should fail"));
            assert!(error.contains(fragment), "{input}: {error}");
            assert!(expr.is_empty());
            // A failed parse is distinguishable from the empty expression.
            assert_ne!(expr, PathExpression::nothing());
        }
    }

    #[test]
    fn invalid_keeps_text() {
        // A failed parse keeps the authored text: it round-trips through
        // Display, so re-serializing a layer preserves the opinion.
        let expr = PathExpression::parse("(/broken");
        assert!(expr.parse_error().is_some());
        assert_eq!(expr.to_string(), "(/broken");
    }

    #[test]
    fn nesting_depth_limited() {
        let ok = format!("{}/a{}", "(".repeat(100), ")".repeat(100));
        assert!(PathExpression::parse(&ok).parse_error().is_none());
        let deep = format!("{}/a{}", "(".repeat(200), ")".repeat(200));
        let error = PathExpression::parse(&deep)
            .parse_error()
            .expect("depth error")
            .to_string();
        assert!(error.contains("nesting too deep"), "{error}");
        // The predicate grammar guards its own recursion.
        let pred = format!("//{{{}a{}}}", "(".repeat(200), ")".repeat(200));
        let error = PathExpression::parse(&pred)
            .parse_error()
            .expect("depth error")
            .to_string();
        assert!(error.contains("nesting too deep"), "{error}");
    }

    #[test]
    fn float_args_canonical() {
        // An integral float keeps a fractional digit so it re-parses as a
        // float rather than an int.
        canonical("//{isClose(1.0, tolerance=2.0)}");
        round_trip("//{f(3.50)}", "//{f(3.5)}");
    }

    #[test]
    fn underscore_collection_name() {
        // `_` marks the weaker expression only when bare; a pathed reference
        // may name a collection `_`.
        canonical("%/Sets:_");
    }

    #[test]
    fn completeness_queries() {
        let complete = PathExpression::parse("/a// & ~/a/b//");
        assert!(complete.is_complete());
        assert!(complete.is_absolute());

        let relative = PathExpression::parse("child// other*");
        assert!(!relative.is_absolute());
        assert!(!relative.is_complete());

        let with_ref = PathExpression::parse("/a// %/Sets:b");
        assert!(with_ref.is_absolute());
        assert!(!with_ref.is_complete());
        assert!(with_ref.contains_expression_references());
        assert!(!with_ref.contains_weaker_reference());
        assert!(PathExpression::parse("/a// %_").contains_weaker_reference());
    }

    #[test]
    fn make_absolute_anchors() {
        let anchored = PathExpression::parse("child// ../sib .// %:local")
            .make_absolute(&crate::sdf::path("/World/Anchor").unwrap());
        assert_eq!(
            anchored.to_string(),
            "/World/Anchor/child// /World/sib /World/Anchor// %:local"
        );
        assert!(anchored.is_absolute());
    }

    #[test]
    fn compose_over_weaker() {
        let strong = PathExpression::parse("/add// %_");
        let weak = PathExpression::parse("/base//");
        assert_eq!(strong.compose_over(&weak).to_string(), "/add// /base//");

        // Composing over nothing drops the slot entirely.
        let strong = PathExpression::parse("/add// %_");
        assert_eq!(strong.compose_over(&PathExpression::nothing()).to_string(), "/add//");

        // Nothing stays nothing: an absent opinion has no weaker slot.
        assert_eq!(
            PathExpression::nothing().compose_over(&PathExpression::parse("/x//")),
            PathExpression::nothing()
        );

        // Only `%_` is substituted; named references stay.
        let strong = PathExpression::parse("%/Sets:b %_");
        assert_eq!(
            strong.compose_over(&PathExpression::parse("/w//")).to_string(),
            "%/Sets:b /w//"
        );

        // A failed parse participates in the algebra as the empty
        // expression: composing over it drops the slot, error and all.
        let invalid = PathExpression::parse("(/broken");
        assert!(invalid.parse_error().is_some());
        let strong = PathExpression::parse("/add// %_");
        assert_eq!(strong.compose_over(&invalid).to_string(), "/add//");
    }

    #[test]
    fn resolve_references_collapses() {
        let expr = PathExpression::parse("/a// %/Sets:b");
        let resolved = expr.resolve_references(&mut |reference: &ExpressionReference| {
            assert_eq!(reference.name, "b");
            PathExpression::nothing()
        });
        // Substituting nothing collapses the union around it.
        assert_eq!(resolved.to_string(), "/a//");
    }

    #[test]
    fn map_paths_translates() {
        let expr = PathExpression::parse("/Ref/geo// %/Ref/Sets:b + /Other//");
        let mapped = expr.map_paths(|path| {
            path.as_str()
                .strip_prefix("/Ref")
                .map(|tail| crate::sdf::path(format!("/Root{tail}")).unwrap())
        });
        // The unmappable atom collapses to nothing under the union.
        assert_eq!(mapped.to_string(), "/Root/geo// %/Root/Sets:b");
    }
}
