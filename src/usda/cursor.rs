//! Token-stream mechanics for the `usda` text parser.

use std::borrow::Cow;
use std::iter::Peekable;
use std::ops::Range;

use anyhow::{Result, anyhow, bail, ensure};
use logos::{Logos, SpannedIter};

use super::token::Token;

// TODO: `sdf::expr` drives its own `Peekable<SpannedIter>` with the same
// peek/next/expect shape. A `Cursor<'source, T: Logos<'source>>` generic over
// the token type would serve both, once they agree on whether a lex error is
// an error at lookahead or only at consume.

/// A one-token-lookahead view over the `usda` token stream.
///
/// Owns the lexer and the byte span of the most recently observed position.
/// Parsing records byte offsets alone; a line and column are derived from
/// [`source`] and [`diagnostic_span`] once a parse has failed.
///
/// [`source`]: Cursor::source
/// [`diagnostic_span`]: Cursor::diagnostic_span
pub(super) struct Cursor<'source> {
    iter: Peekable<SpannedIter<'source, Token<'source>>>,
    source: &'source str,
    last_span: Option<Range<usize>>,
}

impl<'source> Cursor<'source> {
    pub(super) fn new(source: &'source str) -> Self {
        Self {
            iter: Token::lexer(source).spanned().peekable(),
            source,
            last_span: None,
        }
    }

    /// The full input this cursor reads from.
    pub(super) fn source(&self) -> &'source str {
        self.source
    }

    /// The span an error should point at.
    ///
    /// Every observation records its span — a consumed token, a peeked one, a
    /// lexeme that failed to lex, or the end of the input — so an error points
    /// at whatever the parser was looking at, whether or not it consumed it.
    /// This accessor reads that state rather than advancing the lexer.
    pub(super) fn diagnostic_span(&self) -> Range<usize> {
        self.last_span.clone().unwrap_or(self.source.len()..self.source.len())
    }

    /// Returns the next token without consuming it, or `None` at the end of the
    /// stream.
    #[inline]
    pub(super) fn peek(&mut self) -> Result<Option<&Token<'source>>> {
        match self.iter.peek() {
            Some((Ok(token), span)) => {
                self.last_span = Some(span.start..span.end);
                Ok(Some(token))
            }
            Some((Err(_), span)) => {
                self.last_span = Some(span.start..span.end);
                bail!("Logos error")
            }
            None => {
                self.last_span = Some(self.source.len()..self.source.len());
                Ok(None)
            }
        }
    }

    /// Whether the next token equals `expected`, without consuming it.
    #[inline]
    fn at(&mut self, expected: &Token<'_>) -> Result<bool> {
        Ok(matches!(self.peek()?, Some(token) if token == expected))
    }

    /// Consumes and returns the next token.
    #[inline]
    pub(super) fn bump(&mut self) -> Result<Token<'source>> {
        let Some((token, span)) = self.iter.next() else {
            self.last_span = Some(self.source.len()..self.source.len());
            bail!("Unexpected end of tokens");
        };
        self.last_span = Some(span);
        token.map_err(|_| anyhow!("Logos error"))
    }

    /// Consumes the next token if it equals `expected`, reporting whether it
    /// was consumed.
    #[inline]
    pub(super) fn eat(&mut self, expected: &Token<'_>) -> Result<bool> {
        if self.at(expected)? {
            self.bump()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Consumes the next token, requiring it to equal `expected`.
    fn expect(&mut self, expected: Token<'_>) -> Result<()> {
        let token = self.bump()?;
        ensure!(
            token == expected,
            "Unexpected token (want: {expected:?}, got {token:?})"
        );
        Ok(())
    }

    /// Whether the next token is the punctuation `value`, without consuming it.
    #[inline]
    pub(super) fn at_punctuation(&mut self, value: char) -> Result<bool> {
        self.at(&Token::Punctuation(value))
    }

    /// Consumes the punctuation `value` if it is next.
    #[inline]
    pub(super) fn eat_punctuation(&mut self, value: char) -> Result<bool> {
        self.eat(&Token::Punctuation(value))
    }

    /// Consumes the next token, requiring it to be the punctuation `value`.
    #[inline]
    pub(super) fn expect_punctuation(&mut self, value: char) -> Result<()> {
        self.expect(Token::Punctuation(value))
    }

    /// Consumes a quoted string, borrowed from the source unless it carried an
    /// escape sequence.
    pub(super) fn expect_string(&mut self) -> Result<Cow<'source, str>> {
        match self.bump()? {
            Token::String(text) => Ok(text),
            other => bail!("Unexpected token {other:?} (want String)"),
        }
    }

    /// Consumes a plain or namespaced identifier.
    pub(super) fn expect_identifier(&mut self) -> Result<&'source str> {
        match self.bump()? {
            Token::Identifier(name) | Token::NamespacedIdentifier(name) => Ok(name),
            other => bail!("expected identifier, got {other:?}"),
        }
    }

    /// Consumes an asset reference (`@...@`) and returns its body.
    pub(super) fn expect_asset_ref(&mut self) -> Result<&'source str> {
        match self.bump()? {
            Token::AssetRef(asset_path) => Ok(asset_path),
            other => bail!("Asset reference expected, got {other:?}"),
        }
    }

    /// Consumes a path reference (`<...>`) and returns its body.
    pub(super) fn expect_path_ref(&mut self) -> Result<&'source str> {
        match self.bump()? {
            Token::PathRef(path) => Ok(path),
            other => bail!("Path reference expected, got {other:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn peek_leaves_token() {
        let mut cursor = Cursor::new("def over");
        assert_eq!(cursor.peek().unwrap(), Some(&Token::Def));
        assert_eq!(cursor.peek().unwrap(), Some(&Token::Def));
        assert_eq!(cursor.bump().unwrap(), Token::Def);
        assert_eq!(cursor.peek().unwrap(), Some(&Token::Over));
    }

    #[test]
    fn at_does_not_consume() {
        let mut cursor = Cursor::new("def");
        assert!(cursor.at(&Token::Def).unwrap());
        assert!(!cursor.at(&Token::Over).unwrap());
        assert_eq!(cursor.bump().unwrap(), Token::Def);
    }

    #[test]
    fn bump_returns_owned() {
        let mut cursor = Cursor::new("\"text\"");
        let token = cursor.bump().expect("string token");
        // The token's payload borrows the source, so it outlives the cursor.
        drop(cursor);
        assert_eq!(token, Token::String(Cow::Borrowed("text")));
    }

    #[test]
    fn bump_at_eof() {
        let mut cursor = Cursor::new("");
        let error = cursor.bump().expect_err("empty input has no tokens");
        assert!(format!("{error:#}").contains("Unexpected end of tokens"));
    }

    #[test]
    fn eat_matching() {
        let mut cursor = Cursor::new("( )");
        assert!(cursor.eat_punctuation('(').unwrap());
        assert!(cursor.eat_punctuation(')').unwrap());
        assert_eq!(cursor.peek().unwrap(), None);
    }

    #[test]
    fn eat_non_matching() {
        let mut cursor = Cursor::new("(");
        assert!(!cursor.eat_punctuation(')').unwrap());
        assert!(cursor.at_punctuation('(').unwrap());
    }

    #[test]
    fn expect_mismatch_errors() {
        let mut cursor = Cursor::new("over");
        let error = cursor.expect(Token::Def).expect_err("over is not def");
        let message = format!("{error:#}");
        assert!(message.contains("Unexpected token"), "got: {message}");
        assert!(message.contains("Over"), "got: {message}");
    }

    #[test]
    fn expect_punctuation_names_want() {
        let mut cursor = Cursor::new("def");
        let error = cursor.expect_punctuation('(').expect_err("def is not a paren");
        let message = format!("{error:#}");
        assert!(message.contains("Punctuation('(')"), "got: {message}");
        assert!(message.contains("Def"), "got: {message}");
    }

    #[test]
    fn string_stays_borrowed() {
        let mut cursor = Cursor::new("\"plain\"");
        let text = cursor.expect_string().expect("string");
        assert!(
            matches!(text, Cow::Borrowed("plain")),
            "escape-free strings must not allocate"
        );
    }

    #[test]
    fn string_owned_on_escape() {
        let mut cursor = Cursor::new("\"a\\nb\"");
        let text = cursor.expect_string().expect("string");
        assert_eq!(text, "a\nb");
        assert!(matches!(text, Cow::Owned(_)));
    }

    #[test]
    fn identifier_or_namespaced() {
        let mut cursor = Cursor::new("shader inputs:diffuse");
        assert_eq!(cursor.expect_identifier().unwrap(), "shader");
        assert_eq!(cursor.expect_identifier().unwrap(), "inputs:diffuse");
    }

    #[test]
    fn path_ref_extracted() {
        let mut cursor = Cursor::new("</Root/Child>");
        assert_eq!(cursor.expect_path_ref().unwrap(), "/Root/Child");
    }

    #[test]
    fn asset_ref_extracted() {
        let mut cursor = Cursor::new("@./model.usda@");
        assert_eq!(cursor.expect_asset_ref().unwrap(), "./model.usda");
    }

    #[test]
    fn span_at_lex_error() {
        let mut cursor = Cursor::new("def %");
        assert_eq!(cursor.bump().unwrap(), Token::Def);
        let error = cursor.peek().expect_err("% does not lex");
        assert!(format!("{error:#}").contains("Logos error"));
        // The span covers the invalid lexeme.
        assert_eq!(cursor.diagnostic_span(), 4..5);
    }

    #[test]
    fn span_at_eof() {
        let mut cursor = Cursor::new("def");
        assert_eq!(cursor.bump().unwrap(), Token::Def);
        assert_eq!(cursor.peek().unwrap(), None);
        assert_eq!(cursor.diagnostic_span(), 3..3);
    }

    #[test]
    fn span_after_consume() {
        let mut cursor = Cursor::new("def over");
        assert_eq!(cursor.bump().unwrap(), Token::Def);
        assert_eq!(cursor.diagnostic_span(), 0..3);
    }

    #[test]
    fn span_follows_lookahead() {
        let mut cursor = Cursor::new("def over");
        assert_eq!(cursor.bump().unwrap(), Token::Def);
        // A rule that rejects what it only peeked at must still be located on
        // that token, not on the one consumed before it.
        assert_eq!(cursor.peek().unwrap(), Some(&Token::Over));
        assert_eq!(cursor.diagnostic_span(), 4..8);
    }
}
