//! Variable expression tokenizer and parser.
//!
//! Implements USD variable expressions as described in:
//! <https://openusd.org/dev/user_guides/variable_expressions.html>

use logos::Logos;

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
}
