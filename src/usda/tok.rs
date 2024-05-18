//! Tokenizer receives usda file as input and outputs tokens for
//! further analysis.

use anyhow::{bail, ensure, Context, Result};

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

#[derive(Debug, PartialEq, Eq)]
pub struct Token<'a> {
    /// Token type.
    pub ty: Type,
    /// Token substring.
    pub token: &'a str,
}

impl<'a> Token<'a> {
    pub fn new(ty: Type, token: &'a str) -> Self {
        Self { ty, token }
    }

    pub fn str(str: &'a str) -> Self {
        Self::new(Type::String, str)
    }

    pub fn ty(ty: Type) -> Self {
        Self::new(ty, "")
    }
}

pub struct Tokenizer<'a> {
    buffer: &'a str,
    header: bool,
}

impl<'a> Tokenizer<'a> {
    pub fn new(buffer: &'a str) -> Self {
        Self { buffer, header: true }
    }

    /// Advance to next line
    fn skip_line(&mut self) {
        let line = self.buffer.lines().next().unwrap_or_default();
        self.buffer = self.buffer.trim_start_matches(line).trim_start();
    }

    fn trim_spaces(&mut self) {
        self.buffer = self.buffer.trim_start();
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

    fn next_word(&mut self) -> Option<&str> {
        if self.buffer.is_empty() {
            return None;
        }

        let mut iter = self.buffer.split_whitespace();
        let next_word = iter.next()?;

        self.buffer = self.buffer.strip_prefix(next_word).unwrap_or_default();

        Some(next_word)
    }

    /// Attempts to extract next token from string.
    pub fn parse_next(&mut self) -> Result<Option<Token>> {
        self.trim_spaces();

        if self.buffer.is_empty() {
            return Ok(None);
        }

        // Parse header
        if self.header {
            let line = self.buffer.lines().next().unwrap_or_default();
            ensure!(line.starts_with("#usda"), "Text files expected to start with #usda");

            self.skip_line();
            self.header = false;

            return Ok(Some(Token::new(Type::Magic, line)));
        }

        // Skip comments
        while self.buffer.trim_start().starts_with('#') {
            self.skip_line();
        }

        // Parse quoted string.
        if self.buffer.starts_with('"') || self.buffer.starts_with('\'') {
            let str = self.extract_quoted_string().context("Failed to parse quoted string")?;
            return Ok(Token::str(str).into());
        }

        // Asset reference.
        if self.buffer.starts_with('@') {
            let asset = self.extract_quoted_string().context("Failed to parse asset ref")?;
            return Ok(Token::new(Type::AssetRef, asset).into());
        }

        // Path reference.
        if self.buffer.starts_with('<') {
            let path = self.extract_quoted_string().context("Failed to parse path ref")?;
            return Ok(Token::new(Type::PathRef, path).into());
        }

        // It's not a quoted string at this point, so separate next word
        let Some(word) = self.next_word() else {
            return Ok(None);
        };

        // Parse keywords.
        for (keyword, ty) in KEYWORDS {
            if keyword.eq(&word) {
                return Ok(Token::new(*ty, "").into());
            }
        }

        // Parse punctuation.
        for ch in PUN {
            if ch.eq(&word) {
                return Ok(Token::new(Type::Punctuation, ch).into());
            }
        }

        // Try parse as number.
        if word.parse::<f64>().is_ok() {
            return Ok(Token::new(Type::Number, word).into());
        }

        // Namespace identifier
        if word.contains(sdf::Path::NS_DELIMITER_CHAR) {
            ensure!(
                sdf::Path::is_valid_namespace_identifier(word),
                "Invalid ns identifier: {}",
                word
            );
            return Ok(Token::new(Type::NamespacedIdentifier, word).into());
        }

        // Identifier
        if sdf::Path::is_valid_identifier(word) {
            return Ok(Token::new(Type::Identifier, word).into());
        }

        bail!("Unable to parse token: {}", word);
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn empty_file() {
        assert_eq!(Tokenizer::new("").parse_next().unwrap(), None);
        assert_eq!(Tokenizer::new(" ").parse_next().unwrap(), None);
        assert_eq!(
            Tokenizer::new(
                "

            "
            )
            .parse_next()
            .unwrap(),
            None
        );
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
            Token::new(Type::Magic, "#usda 1.0"),
            // MySphere1
            Token::ty(Type::Def),
            Token::new(Type::Identifier, "Sphere"),
            Token::str("MySphere1"),
            Token::new(Type::Punctuation, "("),
            Token::ty(Type::Payload),
            Token::new(Type::Punctuation, "="),
            Token::new(Type::AssetRef, "./payload.usda"),
            Token::new(Type::PathRef, "/MySphere"),
            Token::new(Type::Punctuation, ")"),
            Token::new(Type::Punctuation, "{"),
            Token::new(Type::Punctuation, "}"),
            // MySphere2
            Token::ty(Type::Def),
            Token::new(Type::Identifier, "Sphere"),
            Token::str("MySphere2"),
            Token::new(Type::Punctuation, "("),
            Token::ty(Type::Prepend),
            Token::ty(Type::Payload),
            Token::new(Type::Punctuation, "="),
            Token::new(Type::AssetRef, "./cube_payload.usda"),
            Token::new(Type::PathRef, "/PayloadCube"),
            Token::new(Type::Punctuation, ")"),
            Token::new(Type::Punctuation, "{"),
            Token::new(Type::Punctuation, "}"),
        ];

        for token in tokens {
            let next = tok.parse_next()?;

            assert_eq!(next, Some(token));
        }

        assert!(tok.parse_next()?.is_none());

        Ok(())
    }

    #[test]
    fn parse_connection() -> Result<()> {
        let f = fs::read_to_string("fixtures/connection.usda")?;
        let mut tok = Tokenizer::new(&f);

        let tokens = [
            Token::new(Type::Magic, "#usda 1.0"),
            // def Material "boardMat"
            Token::ty(Type::Def),
            Token::new(Type::Identifier, "Material"),
            Token::str("boardMat"),
            Token::new(Type::Punctuation, "{"),
            // token inputs:frame:stPrimvarName = "st"
            Token::new(Type::Identifier, "token"),
            Token::new(Type::NamespacedIdentifier, "inputs:frame:stPrimvarName"),
            Token::new(Type::Punctuation, "="),
            Token::str("st"),
            // token outputs:surface.connect = </TexModel/boardMat/PBRShader.outputs:surface>
            Token::new(Type::Identifier, "token"),
            Token::new(Type::NamespacedIdentifier, "outputs:surface.connect"),
            Token::new(Type::Punctuation, "="),
            Token::new(Type::PathRef, "/TexModel/boardMat/PBRShader.outputs:surface"),
        ];

        for token in tokens {
            let next = tok.parse_next()?;

            assert_eq!(next, Some(token));
        }

        Ok(())
    }

    #[test]
    fn parse_fields() -> Result<()> {
        let f = fs::read_to_string("fixtures/fields.usda")?;
        let mut tok = Tokenizer::new(&f);

        let tokens = [
            Token::new(Type::Magic, "#usda 1.0"),
            Token::new(Type::Punctuation, "("),
            // doc = """test string"""
            Token::new(Type::Doc, ""),
            Token::new(Type::Punctuation, "="),
            Token::str("test string"),
            // customLayerData = { string test = "Test string" }
            Token::new(Type::Identifier, "customLayerData"),
            Token::new(Type::Punctuation, "="),
            Token::new(Type::Punctuation, "{"),
            Token::new(Type::Identifier, "string"),
            Token::new(Type::Identifier, "test"),
            Token::new(Type::Punctuation, "="),
            Token::str("Test string"),
            Token::new(Type::Punctuation, "}"),
            // upAxis = "Y"
            Token::new(Type::Identifier, "upAxis"),
            Token::new(Type::Punctuation, "="),
            Token::str("Y"),
            // metersPerUnit = 0.01
            Token::new(Type::Identifier, "metersPerUnit"),
            Token::new(Type::Punctuation, "="),
            Token::new(Type::Number, "0.01"),
        ];

        for token in tokens {
            let next = tok.parse_next()?;

            assert_eq!(next, Some(token));
        }

        Ok(())
    }
}
