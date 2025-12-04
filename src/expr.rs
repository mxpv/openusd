//! Variable expression tokenizer and parser.
//!
//! Implements USD variable expressions as described in:
//! <https://openusd.org/dev/user_guides/variable_expressions.html>
//!
//! Expressions are strings enclosed in backticks that are evaluated at runtime
//! to produce a final value. They support variable substitution, function calls,
//! and various literal types.
//!
//! # Example
//!
//! ```
//! use openusd::expr::Expr;
//!
//! let expr: Expr = r#"if(${USE_HIGH_RES}, "high", "low")"#.parse().unwrap();
//! ```

use anyhow::{anyhow, bail, ensure, Result};
use logos::{Logos, SpannedIter};
use std::iter::Peekable;
use std::str::FromStr;

/// Tokens for USD variable expressions.
#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\n\f]+")]
pub enum Token<'source> {
    // Literals
    /// Double-quoted string: "hello world"
    #[regex(r#""([^"\\]|\\.)*""#, |lex| trim_quotes(lex.slice()))]
    /// Single-quoted string: 'hello world'
    #[regex(r#"'([^'\\]|\\.)*'"#, |lex| trim_quotes(lex.slice()))]
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
    None,

    // Variable substitution
    /// Variable reference: ${varName}
    #[regex(r"\$\{[a-zA-Z_][a-zA-Z0-9_]*\}", |lex| {
        let s = lex.slice();
        // Strip ${ and }
        &s[2..s.len()-1]
    })]
    Variable(&'source str),

    // Identifiers (function names, variable names in defined())
    /// Identifier for function names or bare variable references
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

    /// Backtick (expression delimiter)
    #[token("`")]
    Backtick,
}

/// Trims quote characters from both ends of a string slice.
fn trim_quotes(s: &str) -> &str {
    &s[1..s.len() - 1]
}

/// Tokenize an expression string into tokens.
pub fn tokenize(input: &str) -> impl Iterator<Item = Result<Token<'_>, ()>> {
    Token::lexer(input).map(|result| result.map_err(|_| ()))
}

/// Supported functions in USD variable expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Func {
    /// `defined(var1, var2, ...)` - Tests if all variables are defined.
    Defined,
    /// `if(cond, trueVal, falseVal?)` - Conditional expression.
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
    /// `at(list_or_string, index)` - Element access (0-based, negative wraps).
    At,
    /// `len(list_or_string)` - Returns length.
    Len,
}

impl Func {
    /// Returns the expected argument count as (min, max).
    const fn arg_count(self) -> (usize, usize) {
        match self {
            Func::Defined => (1, usize::MAX),
            Func::If => (2, 3),
            Func::And | Func::Or => (2, usize::MAX),
            Func::Not | Func::Len => (1, 1),
            Func::Eq | Func::Neq | Func::Lt | Func::Leq | Func::Gt | Func::Geq | Func::Contains | Func::At => (2, 2),
        }
    }

    /// Validates that the given argument count is valid for this function.
    fn validate_arg_count(self, count: usize) -> Result<()> {
        let (min, max) = self.arg_count();
        if count < min || count > max {
            if min == max {
                bail!("{:?} requires exactly {} argument(s), got {}", self, min, count);
            } else if max == usize::MAX {
                bail!("{:?} requires at least {} argument(s), got {}", self, min, count);
            } else {
                bail!("{:?} requires {} to {} arguments, got {}", self, min, max, count);
            }
        }
        Ok(())
    }
}

impl FromStr for Func {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "defined" => Ok(Func::Defined),
            "if" => Ok(Func::If),
            "and" => Ok(Func::And),
            "or" => Ok(Func::Or),
            "not" => Ok(Func::Not),
            "eq" => Ok(Func::Eq),
            "neq" => Ok(Func::Neq),
            "lt" => Ok(Func::Lt),
            "leq" => Ok(Func::Leq),
            "gt" => Ok(Func::Gt),
            "geq" => Ok(Func::Geq),
            "contains" => Ok(Func::Contains),
            "at" => Ok(Func::At),
            "len" => Ok(Func::Len),
            _ => bail!("Unknown function: {}", s),
        }
    }
}

/// Expression tree node representing a parsed USD variable expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// String literal, may contain embedded `${var}` references for interpolation.
    String(String),
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
}

/// Parser for USD variable expressions.
struct Parser<'a> {
    iter: Peekable<SpannedIter<'a, Token<'a>>>,
}

impl<'a> Parser<'a> {
    /// Create a new parser for the given input string.
    fn new(input: &'a str) -> Self {
        Self {
            iter: Token::lexer(input).spanned().peekable(),
        }
    }

    /// Peek at the current token without consuming it.
    fn peek(&mut self) -> Option<&Token<'a>> {
        self.iter.peek().and_then(|(result, _)| result.as_ref().ok())
    }

    /// Consume and return the current token.
    fn next(&mut self) -> Option<Token<'a>> {
        loop {
            match self.iter.next() {
                Some((Ok(token), _)) => return Some(token),
                Some((Err(_), _)) => continue, // Skip invalid tokens
                None => return None,
            }
        }
    }

    /// Check if we've reached the end of tokens.
    fn is_eof(&mut self) -> bool {
        self.peek().is_none()
    }

    /// Consume a token if it matches the expected token, otherwise return an error.
    fn expect(&mut self, expected: Token<'a>) -> Result<()> {
        match self.next() {
            Some(ref token) if *token == expected => Ok(()),
            Some(token) => bail!("Expected {:?}, got {:?}", expected, token),
            None => bail!("Expected {:?}, got end of input", expected),
        }
    }

    /// Parse a complete expression.
    fn parse_expr(&mut self) -> Result<Expr> {
        // Handle backtick-delimited string expressions
        if matches!(self.peek(), Some(Token::Backtick)) {
            self.next();
            let expr = match self.next() {
                Some(Token::String(s)) => Expr::String(unescape_string(s)),
                Some(other) => bail!("Expected string after backtick, got {:?}", other),
                None => bail!("Expected string after backtick, got end of input"),
            };
            self.expect(Token::Backtick)?;
            ensure!(self.is_eof(), "Unexpected token after expression: {:?}", self.peek());
            return Ok(expr);
        }

        let expr = self.parse()?;
        ensure!(self.is_eof(), "Unexpected token after expression: {:?}", self.peek());
        Ok(expr)
    }

    /// Parse a primary expression (literals, variables, arrays, function calls).
    fn parse(&mut self) -> Result<Expr> {
        let token = self.next().ok_or_else(|| anyhow!("Unexpected end of input"))?;

        match token {
            Token::String(s) => Ok(Expr::String(unescape_string(s))),
            Token::Integer(s) => {
                let value = s.parse::<i64>().map_err(|e| anyhow!("Invalid integer: {}", e))?;
                Ok(Expr::Integer(value))
            }
            Token::True => Ok(Expr::Bool(true)),
            Token::False => Ok(Expr::Bool(false)),
            Token::None => Ok(Expr::None),
            Token::Variable(name) => Ok(Expr::Variable(name.to_string())),
            Token::LBracket => self.parse_array(),
            Token::Identifier(name) => {
                // Check if this is a function call
                if matches!(self.peek(), Some(Token::LParen)) {
                    self.parse_call(name)
                } else {
                    // Bare identifier (used in `defined(VAR_NAME)`)
                    Ok(Expr::Variable(name.to_string()))
                }
            }
            other => bail!("Unexpected token: {:?}", other),
        }
    }

    /// Parse an array literal: `[elem1, elem2, ...]`.
    fn parse_array(&mut self) -> Result<Expr> {
        let mut elements = Vec::new();

        // Handle empty array
        if matches!(self.peek(), Some(Token::RBracket)) {
            self.next();
            return Ok(Expr::Array(elements));
        }

        loop {
            elements.push(self.parse()?);

            match self.peek() {
                Some(Token::Comma) => {
                    self.next();
                    // Allow trailing comma
                    if matches!(self.peek(), Some(Token::RBracket)) {
                        self.next();
                        break;
                    }
                }
                Some(Token::RBracket) => {
                    self.next();
                    break;
                }
                other => bail!("Expected ',' or ']' in array, got {:?}", other),
            }
        }

        Ok(Expr::Array(elements))
    }

    /// Parse a function call: `funcName(arg1, arg2, ...)`.
    fn parse_call(&mut self, name: &str) -> Result<Expr> {
        let func: Func = name.parse()?;
        self.expect(Token::LParen)?;

        let mut args = Vec::new();

        // Handle empty argument list
        if matches!(self.peek(), Some(Token::RParen)) {
            self.next();
            func.validate_arg_count(args.len())?;
            return Ok(Expr::Call { func, args });
        }

        loop {
            args.push(self.parse()?);

            match self.peek() {
                Some(Token::Comma) => {
                    self.next();
                }
                Some(Token::RParen) => {
                    self.next();
                    break;
                }
                other => bail!("Expected ',' or ')' in function call, got {:?}", other),
            }
        }

        func.validate_arg_count(args.len())?;
        Ok(Expr::Call { func, args })
    }
}

/// Unescape a string literal, processing escape sequences.
fn unescape_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some('\'') => result.push('\''),
                Some('$') => result.push('$'),
                Some('n') => result.push('\n'),
                Some('r') => result.push('\r'),
                Some('t') => result.push('\t'),
                Some(other) => {
                    // Keep unrecognized escapes as-is
                    result.push('\\');
                    result.push(other);
                }
                None => result.push('\\'),
            }
        } else {
            result.push(c);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenize_string_literals() {
        let tokens: Vec<_> = tokenize(r#""hello world""#).collect();
        assert_eq!(tokens, vec![Ok(Token::String("hello world"))]);

        let tokens: Vec<_> = tokenize(r#"'single quoted'"#).collect();
        assert_eq!(tokens, vec![Ok(Token::String("single quoted"))]);
    }

    #[test]
    fn tokenize_escaped_strings() {
        let tokens: Vec<_> = tokenize(r#""escaped \"quote\"""#).collect();
        assert_eq!(tokens, vec![Ok(Token::String(r#"escaped \"quote\""#))]);
    }

    #[test]
    fn tokenize_integers() {
        let tokens: Vec<_> = tokenize("42").collect();
        assert_eq!(tokens, vec![Ok(Token::Integer("42"))]);

        let tokens: Vec<_> = tokenize("-100").collect();
        assert_eq!(tokens, vec![Ok(Token::Integer("-100"))]);
    }

    #[test]
    fn tokenize_booleans() {
        let tokens: Vec<_> = tokenize("True false").collect();
        assert_eq!(tokens, vec![Ok(Token::True), Ok(Token::False)]);

        let tokens: Vec<_> = tokenize("true False").collect();
        assert_eq!(tokens, vec![Ok(Token::True), Ok(Token::False)]);
    }

    #[test]
    fn tokenize_none() {
        let tokens: Vec<_> = tokenize("None").collect();
        assert_eq!(tokens, vec![Ok(Token::None)]);
    }

    #[test]
    fn tokenize_variables() {
        let tokens: Vec<_> = tokenize("${ASSET_PATH}").collect();
        assert_eq!(tokens, vec![Ok(Token::Variable("ASSET_PATH"))]);

        let tokens: Vec<_> = tokenize("${my_var_123}").collect();
        assert_eq!(tokens, vec![Ok(Token::Variable("my_var_123"))]);
    }

    #[test]
    fn tokenize_function_call() {
        let tokens: Vec<_> = tokenize("if(${USE_HIGH_RES}, \"high\", \"low\")").collect();
        assert_eq!(
            tokens,
            vec![
                Ok(Token::Identifier("if")),
                Ok(Token::LParen),
                Ok(Token::Variable("USE_HIGH_RES")),
                Ok(Token::Comma),
                Ok(Token::String("high")),
                Ok(Token::Comma),
                Ok(Token::String("low")),
                Ok(Token::RParen),
            ]
        );
    }

    #[test]
    fn tokenize_defined_function() {
        let tokens: Vec<_> = tokenize("defined(RENDER_PASS)").collect();
        assert_eq!(
            tokens,
            vec![
                Ok(Token::Identifier("defined")),
                Ok(Token::LParen),
                Ok(Token::Identifier("RENDER_PASS")),
                Ok(Token::RParen),
            ]
        );
    }

    #[test]
    fn tokenize_array_literal() {
        let tokens: Vec<_> = tokenize("[\"a\", \"b\", \"c\"]").collect();
        assert_eq!(
            tokens,
            vec![
                Ok(Token::LBracket),
                Ok(Token::String("a")),
                Ok(Token::Comma),
                Ok(Token::String("b")),
                Ok(Token::Comma),
                Ok(Token::String("c")),
                Ok(Token::RBracket),
            ]
        );
    }

    #[test]
    fn tokenize_nested_function() {
        let tokens: Vec<_> = tokenize("if(and(${A}, ${B}), \"yes\", \"no\")").collect();
        assert_eq!(
            tokens,
            vec![
                Ok(Token::Identifier("if")),
                Ok(Token::LParen),
                Ok(Token::Identifier("and")),
                Ok(Token::LParen),
                Ok(Token::Variable("A")),
                Ok(Token::Comma),
                Ok(Token::Variable("B")),
                Ok(Token::RParen),
                Ok(Token::Comma),
                Ok(Token::String("yes")),
                Ok(Token::Comma),
                Ok(Token::String("no")),
                Ok(Token::RParen),
            ]
        );
    }

    #[test]
    fn tokenize_backtick_delimited() {
        // In USD, expressions inside backticks use quoted strings for interpolation
        let tokens: Vec<_> = tokenize("`\"${ASSET_PATH}/model.usd\"`").collect();
        assert_eq!(
            tokens,
            vec![
                Ok(Token::Backtick),
                Ok(Token::String("${ASSET_PATH}/model.usd")),
                Ok(Token::Backtick),
            ]
        );
    }

    #[test]
    fn tokenize_comparison_functions() {
        let tokens: Vec<_> = tokenize("lt(${VALUE}, 10)").collect();
        assert_eq!(
            tokens,
            vec![
                Ok(Token::Identifier("lt")),
                Ok(Token::LParen),
                Ok(Token::Variable("VALUE")),
                Ok(Token::Comma),
                Ok(Token::Integer("10")),
                Ok(Token::RParen),
            ]
        );
    }

    // Expr parsing tests

    #[test]
    fn parse_string_literal() {
        let expr: Expr = r#""hello world""#.parse().unwrap();
        assert_eq!(expr, Expr::String("hello world".to_string()));
    }

    #[test]
    fn parse_escaped_string() {
        let expr: Expr = r#""say \"hello\"""#.parse().unwrap();
        assert_eq!(expr, Expr::String("say \"hello\"".to_string()));
    }

    #[test]
    fn parse_integer_literal() {
        let expr: Expr = "42".parse().unwrap();
        assert_eq!(expr, Expr::Integer(42));

        let expr: Expr = "-100".parse().unwrap();
        assert_eq!(expr, Expr::Integer(-100));
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
    }

    #[test]
    fn parse_variable() {
        let expr: Expr = "${ASSET_PATH}".parse().unwrap();
        assert_eq!(expr, Expr::Variable("ASSET_PATH".to_string()));
    }

    #[test]
    fn parse_empty_array() {
        let expr: Expr = "[]".parse().unwrap();
        assert_eq!(expr, Expr::Array(vec![]));
    }

    #[test]
    fn parse_string_array() {
        let expr: Expr = r#"["a", "b", "c"]"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Array(vec![
                Expr::String("a".to_string()),
                Expr::String("b".to_string()),
                Expr::String("c".to_string()),
            ])
        );
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
                args: vec![
                    Expr::Variable("USE_HIGH_RES".to_string()),
                    Expr::String("high".to_string()),
                    Expr::String("low".to_string()),
                ],
            }
        );
    }

    #[test]
    fn parse_defined_function() {
        let expr: Expr = "defined(RENDER_PASS)".parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::Defined,
                args: vec![Expr::Variable("RENDER_PASS".to_string())],
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
                    Expr::String("yes".to_string()),
                    Expr::String("no".to_string()),
                ],
            }
        );
    }

    #[test]
    fn parse_comparison_function() {
        let expr: Expr = "lt(${VALUE}, 10)".parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::Lt,
                args: vec![Expr::Variable("VALUE".to_string()), Expr::Integer(10)],
            }
        );
    }

    #[test]
    fn parse_with_backticks() {
        let expr: Expr = r#"`"${ASSET_PATH}/model.usd"`"#.parse().unwrap();
        assert_eq!(expr, Expr::String("${ASSET_PATH}/model.usd".to_string()));
    }

    #[test]
    fn parse_contains_function() {
        let expr: Expr = r#"contains(["a", "b"], ${VAR})"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::Contains,
                args: vec![
                    Expr::Array(vec![Expr::String("a".to_string()), Expr::String("b".to_string())]),
                    Expr::Variable("VAR".to_string()),
                ],
            }
        );
    }

    #[test]
    fn parse_complex_nested_expression() {
        let expr: Expr = r#"if(or(eq(${MODE}, "debug"), defined(DEBUG)), "dbg", "rel")"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::If,
                args: vec![
                    Expr::Call {
                        func: Func::Or,
                        args: vec![
                            Expr::Call {
                                func: Func::Eq,
                                args: vec![Expr::Variable("MODE".to_string()), Expr::String("debug".to_string())],
                            },
                            Expr::Call {
                                func: Func::Defined,
                                args: vec![Expr::Variable("DEBUG".to_string())],
                            },
                        ],
                    },
                    Expr::String("dbg".to_string()),
                    Expr::String("rel".to_string()),
                ],
            }
        );
    }

    #[test]
    fn parse_unknown_function_fails() {
        let result: Result<Expr, _> = "unknown_func(1, 2)".parse();
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Unknown function"));
    }

    #[test]
    fn parse_backtick_requires_string() {
        // Non-string after backtick should fail
        let result: Result<Expr, _> = "`42`".parse();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Expected string after backtick"));

        // Function call after backtick should fail
        let result: Result<Expr, _> = "`if(True, 1, 2)`".parse();
        assert!(result.is_err());
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
                    Expr::String(r"C:\USD\test.usd".to_string()),
                    Expr::String(r"D:\USD\test.usd".to_string()),
                ],
            }
        );
    }

    #[test]
    fn parse_escaped_dollar_sign() {
        // Escaped $ prevents variable substitution: \$ → $
        let expr: Expr = r#"`"escaped_var_\${X}"`"#.parse().unwrap();
        assert_eq!(expr, Expr::String("escaped_var_${X}".to_string()));
    }

    #[test]
    fn parse_if_with_two_args() {
        // if() can take 2 arguments (falseVal is optional, returns None)
        let expr: Expr = r#"if(True, "yes")"#.parse().unwrap();
        assert_eq!(
            expr,
            Expr::Call {
                func: Func::If,
                args: vec![Expr::Bool(true), Expr::String("yes".to_string())],
            }
        );
    }

    #[test]
    fn parse_function_arg_count_validation() {
        // not() requires exactly 1 argument
        let result: Result<Expr, _> = "not()".parse();
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("exactly 1"));

        let result: Result<Expr, _> = "not(True, False)".parse();
        assert!(result.is_err());

        // len() requires exactly 1 argument
        let result: Result<Expr, _> = "len()".parse();
        assert!(result.is_err());

        // eq() requires exactly 2 arguments
        let result: Result<Expr, _> = "eq(1)".parse();
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("exactly 2"));

        let result: Result<Expr, _> = "eq(1, 2, 3)".parse();
        assert!(result.is_err());

        // if() requires 2 or 3 arguments
        let result: Result<Expr, _> = "if(True)".parse();
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("2 to 3"));

        // and() requires at least 2 arguments
        let result: Result<Expr, _> = "and(True)".parse();
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("at least 2"));

        // defined() requires at least 1 argument
        let result: Result<Expr, _> = "defined()".parse();
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("at least 1"));
    }
}
