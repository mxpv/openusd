//! Tokenizer receives usda file as input and outputs tokens for
//! further analysis.

use std::ops::Range;

use anyhow::{anyhow, bail, Context, Result};

use crate::sdf;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Type {
    Magic,
    String,
    Number,
    PathRef,
    AssetRef,
    Identifier,
    NamespacedIdentifier,

    /// Various single char punctuation.
    Punctuation,

    /*
        Literal keywords.

        See <https://github.com/PixarAnimationStudios/OpenUSD/blob/release/pxr/usd/sdf/textFileFormat.ll#L124>
    */
    Add,
    Append,
    Class,
    Config,
    Connect,
    Custom,
    CustomData,
    Default,
    Def,
    Delete,
    Dictionary,
    DisplayUnit,
    Doc,
    Inherits,
    Kind,
    NameChildren,
    None,
    Offset,
    Over,
    Payload,
    Permission,
    PrefixSubstitutions,
    Prepend,
    Properties,
    References,
    Relocates,
    Rel,
    Reorder,
    RootPrims,
    Scale,
    SubLayers,
    SuffixSubstitutions,
    Specializes,
    SymmetryArguments,
    SymmetryFunction,
    TimeSamples,
    Uniform,
    VariantSet,
    VariantSets,
    Variants,
    Varying,
}

static KEYWORDS: &[(&str, Type)] = &[
    ("add", Type::Add),
    ("append", Type::Append),
    ("class", Type::Class),
    ("config", Type::Config),
    ("connect", Type::Connect),
    ("custom", Type::Custom),
    ("customData", Type::CustomData),
    ("default", Type::Default),
    ("def", Type::Def),
    ("delete", Type::Delete),
    ("dictionary", Type::Dictionary),
    ("displayUnit", Type::DisplayUnit),
    ("doc", Type::Doc),
    ("inherits", Type::Inherits),
    ("kind", Type::Kind),
    ("nameChildren", Type::NameChildren),
    ("None", Type::None),
    ("offset", Type::Offset),
    ("over", Type::Over),
    ("payload", Type::Payload),
    ("permission", Type::Permission),
    ("prefixSubstitutions", Type::PrefixSubstitutions),
    ("prepend", Type::Prepend),
    ("properties", Type::Properties),
    ("references", Type::References),
    ("relocates", Type::Relocates),
    ("rel", Type::Rel),
    ("reorder", Type::Reorder),
    ("rootPrims", Type::RootPrims),
    ("scale", Type::Scale),
    ("subLayers", Type::SubLayers),
    ("suffixSubstitutions", Type::SuffixSubstitutions),
    ("specializes", Type::Specializes),
    ("symmetryArguments", Type::SymmetryArguments),
    ("symmetryFunction", Type::SymmetryFunction),
    ("timeSamples", Type::TimeSamples),
    ("uniform", Type::Uniform),
    ("variantSet", Type::VariantSet),
    ("variantSets", Type::VariantSets),
    ("variants", Type::Variants),
    ("varying", Type::Varying),
];

/// Punctuation characters. These will match `Type::Punctuation` token type.
static PUN: &[&str] = &["=", ",", "(", ")", "{", "}", "[", "]"];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    /// Token type.
    pub ty: Type,
    /// Range in the owned buffer.
    pub range: Range<usize>,
}

impl Token {
    pub fn new(ty: Type, range: Range<usize>) -> Self {
        Self { ty, range }
    }
}

/// Tokenizer implements an iterator that yields a new token on each call.
///
/// Under the hood it borrows a string buffer with data.
/// On each `next` call, the tokenizer extracts next token and advanced buffer pointer.
pub struct Tokenizer<'a> {
    /// Current buffer.
    ///
    /// This will be trimmed on every token request.
    buffer: &'a str,
    /// Whether already seen header.
    header: bool,
    /// Original buffer size.
    total: usize,
    /// Start of the current token.
    start: usize,
}

impl<'a> Tokenizer<'a> {
    pub fn new(buffer: &'a str) -> Self {
        Self {
            buffer,
            header: true,
            total: buffer.len(),
            start: 0,
        }
    }

    /// Advance to next line
    fn skip_line(&mut self) {
        let line = self.buffer.lines().next().unwrap_or_default();
        self.buffer = self.buffer.trim_start_matches(line).trim_start();
    }

    fn trim_spaces(&mut self) {
        self.buffer = self.buffer.trim_start();
    }

    fn token(&self, ty: Type, tok: &str) -> Result<Token> {
        let start = self.start;
        let end = start + tok.len();

        let token = Token::new(ty, start..end);

        Ok(token)
    }

    pub(super) fn extract_quoted_string(&mut self) -> Result<&'a str> {
        let end = if self.buffer.starts_with("@@@") {
            Some("@@@")
        } else if self.buffer.starts_with("\"\"\"") {
            Some("\"\"\"")
        } else {
            None
        };

        if let Some(end) = end {
            if let Some((str, rem)) = self.buffer.trim_start_matches(end).split_once(end) {
                self.start = self.total - rem.len() - str.len() - end.len();
                self.buffer = rem;

                return Ok(str);
            }

            bail!("Unable to find closing {}", end);
        }

        let mut chars = self.buffer.char_indices().peekable();
        let mut escape = false;

        // Empty string
        let Some((_, ch)) = chars.next() else {
            return Ok("");
        };

        let end = if ch == '\'' {
            '\''
        } else if ch == '"' {
            '"'
        } else if ch == '<' {
            // Scene path
            '>'
        } else if ch == '@' {
            // Single '@'-delimited asset references
            '@'
        } else {
            bail!("Invalid quoted string");
        };

        while let Some((pos, ch)) = chars.peek().copied() {
            if escape {
                escape = false;
            } else if ch == '\\' {
                escape = true;
            } else if ch == '\n' {
                bail!("Found newline inside of quoted string");
            } else if ch == end {
                let (str, rem) = self.buffer.split_at(pos + 1);

                self.start = self.total - rem.len() - str.len() + 1;
                self.buffer = rem;

                // Remove quotes
                let mut str = str.trim_matches(end);

                // Special case needed for scene paths.
                if end == '>' {
                    str = str.trim_matches('<');
                }

                return Ok(str);
            }

            chars.next();
        }

        bail!("Unable to find closing {}", end);
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Result<Token>;

    fn next(&mut self) -> Option<Self::Item> {
        self.trim_spaces();

        if self.buffer.is_empty() {
            return None;
        }

        // Parse header
        if self.header {
            let line = self.buffer.lines().next().unwrap_or_default();
            if !line.starts_with("#usda") {
                return Err(anyhow!("Text files expected to start with #usda")).into();
            }

            self.skip_line();
            self.header = false;

            return Some(self.token(Type::Magic, line));
        }

        // Skip comments
        while self.buffer.trim_start().starts_with('#') {
            self.skip_line();
        }

        // Parse quoted string.
        if self.buffer.starts_with('"') || self.buffer.starts_with('\'') {
            let token = self
                .extract_quoted_string()
                .context("Failed to parse quoted string")
                .and_then(|tok| self.token(Type::String, tok));

            return Some(token);
        }

        // Asset reference.
        if self.buffer.starts_with('@') {
            let token = self
                .extract_quoted_string()
                .context("Failed to parse asset ref")
                .and_then(|asset| self.token(Type::AssetRef, asset));

            return Some(token);
        }

        // Path reference.
        if self.buffer.starts_with('<') {
            let token = self
                .extract_quoted_string()
                .context("Failed to parse path ref")
                .and_then(|path| self.token(Type::PathRef, path));

            return Some(token);
        }

        // It's not a quoted string at this point, so separate next word
        let word = {
            let mut iter = self.buffer.split_whitespace();
            let next_word = iter.next()?;

            self.buffer = self.buffer.strip_prefix(next_word).unwrap_or_default();
            self.start = self.total - self.buffer.len() - next_word.len();

            next_word
        };

        // Parse keywords.
        for (keyword, ty) in KEYWORDS {
            if keyword.eq(&word) {
                return Some(self.token(*ty, keyword));
            }
        }

        // Parse punctuation.
        for ch in PUN {
            if ch.eq(&word) {
                return Some(self.token(Type::Punctuation, ch));
            }
        }

        // Try parse as number.
        if word.parse::<f64>().is_ok() {
            return Some(self.token(Type::Number, word));
        }

        // Namespace identifier
        if word.contains(sdf::Path::NS_DELIMITER_CHAR) {
            if !sdf::Path::is_valid_namespace_identifier(word) {
                return Err(anyhow!("Invalid ns identifier: {}", word)).into();
            }

            return Some(self.token(Type::NamespacedIdentifier, word));
        }

        // Identifier
        if sdf::Path::is_valid_identifier(word) {
            return Some(self.token(Type::Identifier, word));
        }

        Err(anyhow!("Unable to parse token: {}", word)).into()
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn empty_file() {
        assert!(Tokenizer::new("").next().is_none());
        assert!(Tokenizer::new(" ").next().is_none());
        assert!(Tokenizer::new(
            "

            "
        )
        .next()
        .is_none());
    }

    #[test]
    fn extract_quoted_string() -> Result<()> {
        assert_eq!(Tokenizer::new("").extract_quoted_string()?, "");

        assert_eq!(Tokenizer::new("''").extract_quoted_string()?, "");
        assert_eq!(Tokenizer::new("\"\"").extract_quoted_string()?, "");

        assert_eq!(
            Tokenizer::new("'I am a string'").extract_quoted_string()?,
            "I am a string"
        );
        assert_eq!(
            Tokenizer::new("\"I am a string\"").extract_quoted_string()?,
            "I am a string"
        );

        assert_eq!(
            Tokenizer::new("'A \"quote escaped\" string'").extract_quoted_string()?,
            "A \"quote escaped\" string"
        );

        assert_eq!(
            Tokenizer::new("\"\"\"Another \"escaped\" string\"\"\"").extract_quoted_string()?,
            "Another \"escaped\" string"
        );

        assert!(Tokenizer::new("\" invalid string ").extract_quoted_string().is_err());

        // Error cases

        assert!(Tokenizer::new("\" invalid \nstring\" ")
            .extract_quoted_string()
            .is_err());

        assert!(Tokenizer::new("\" invalid ").extract_quoted_string().is_err());
        assert!(Tokenizer::new("\"invalid' ").extract_quoted_string().is_err());

        Ok(())
    }

    #[test]
    fn parse_payload() -> Result<()> {
        let f = fs::read_to_string("fixtures/payload.usda")?;
        let mut tok = Tokenizer::new(&f);

        let tokens = [
            (Type::Magic, "#usda 1.0"),
            // MySphere1
            (Type::Def, "def"),
            (Type::Identifier, "Sphere"),
            (Type::String, "MySphere1"),
            (Type::Punctuation, "("),
            (Type::Payload, "payload"),
            (Type::Punctuation, "="),
            (Type::AssetRef, "./payload.usda"),
            (Type::PathRef, "/MySphere"),
            (Type::Punctuation, ")"),
            (Type::Punctuation, "{"),
            (Type::Punctuation, "}"),
            // MySphere2
            (Type::Def, "def"),
            (Type::Identifier, "Sphere"),
            (Type::String, "MySphere2"),
            (Type::Punctuation, "("),
            (Type::Prepend, "prepend"),
            (Type::Payload, "payload"),
            (Type::Punctuation, "="),
            (Type::AssetRef, "./cube_payload.usda"),
            (Type::PathRef, "/PayloadCube"),
            (Type::Punctuation, ")"),
            (Type::Punctuation, "{"),
            (Type::Punctuation, "}"),
        ];

        for (ty, expected) in tokens {
            let token = tok
                .next()
                .with_context(|| format!("Unexpected end of token stream, expected token of type {:?}", ty))??;

            assert_eq!(ty, token.ty);
            assert_eq!(expected, &f[token.range]);
        }

        assert!(tok.next().is_none());

        Ok(())
    }

    #[test]
    fn parse_connection() -> Result<()> {
        let f = fs::read_to_string("fixtures/connection.usda")?;
        let mut tok = Tokenizer::new(&f);

        let tokens = [
            (Type::Magic, "#usda 1.0"),
            // def Material "boardMat"
            (Type::Def, "def"),
            (Type::Identifier, "Material"),
            (Type::String, "boardMat"),
            (Type::Punctuation, "{"),
            // token inputs:frame:stPrimvarName = "st"
            (Type::Identifier, "token"),
            (Type::NamespacedIdentifier, "inputs:frame:stPrimvarName"),
            (Type::Punctuation, "="),
            (Type::String, "st"),
            // token outputs:surface.connect = </TexModel/boardMat/PBRShader.outputs:surface>
            (Type::Identifier, "token"),
            (Type::NamespacedIdentifier, "outputs:surface.connect"),
            (Type::Punctuation, "="),
            (Type::PathRef, "/TexModel/boardMat/PBRShader.outputs:surface"),
        ];

        for (ty, expected) in tokens {
            let token = tok
                .next()
                .with_context(|| format!("Unexpected end of token stream, expected token of type {:?}", ty))??;

            assert_eq!(ty, token.ty);
            assert_eq!(expected, &f[token.range]);
        }

        Ok(())
    }

    #[test]
    fn parse_fields() -> Result<()> {
        let f = fs::read_to_string("fixtures/fields.usda")?;
        let mut tok = Tokenizer::new(&f);

        let tokens = [
            (Type::Magic, "#usda 1.0"),
            (Type::Punctuation, "("),
            // doc = """test string"""
            (Type::Doc, "doc"),
            (Type::Punctuation, "="),
            (Type::String, "test string"),
            // customLayerData = { string test = "Test string" }
            (Type::Identifier, "customLayerData"),
            (Type::Punctuation, "="),
            (Type::Punctuation, "{"),
            (Type::Identifier, "string"),
            (Type::Identifier, "test"),
            (Type::Punctuation, "="),
            (Type::String, "Test string"),
            (Type::Punctuation, "}"),
            // upAxis = "Y"
            (Type::Identifier, "upAxis"),
            (Type::Punctuation, "="),
            (Type::String, "Y"),
            // metersPerUnit = 0.01
            (Type::Identifier, "metersPerUnit"),
            (Type::Punctuation, "="),
            (Type::Number, "0.01"),
        ];

        for (ty, expected) in tokens {
            let token = tok
                .next()
                .with_context(|| format!("Unexpected end of token stream, expected token of type {:?}", ty))??;

            assert_eq!(ty, token.ty);
            assert_eq!(expected, &f[token.range]);
        }

        Ok(())
    }

    #[test]
    fn peekable_iter() {
        let f = fs::read_to_string("fixtures/fields.usda").unwrap();
        let tok = Tokenizer::new(&f);

        let expected = Token::new(Type::Magic, 0..9);

        let mut peekable = tok.peekable();
        assert_eq!(peekable.peek().unwrap().as_ref().unwrap().clone(), expected);

        let next = peekable.next().unwrap().unwrap();
        assert_eq!(next, expected);
    }
}
