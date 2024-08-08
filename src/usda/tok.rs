//! Tokenizer receives usda file as input and outputs tokens for
//! further analysis.

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
static PUN: &[&str] = &["=", ",", ";", "(", ")", "{", "}", "[", "]"];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    /// Token type.
    pub ty: Type,
    /// Substring in the buffer.
    pub str: &'a str,
}

impl<'a> Token<'a> {
    pub fn new(ty: Type, str: &'a str) -> Self {
        Self { ty, str }
    }

    #[inline]
    pub fn str(str: &'a str) -> Self {
        Self { ty: Type::String, str }
    }

    #[inline]
    pub fn is_punctuation(&self, p: &str) -> bool {
        self.ty == Type::Punctuation && self.str == p
    }

    #[inline]
    pub fn is_ident(&self, t: &str) -> bool {
        self.ty == Type::Identifier && self.str == t
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
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Result<Token<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.trim_spaces();

        if self.buffer.is_empty() {
            return None;
        }

        // Parse header
        if self.header {
            self.header = false;

            let line = self.buffer.lines().next().unwrap_or_default();

            // Extract magic token, but don't error if it's not there, leave it for the parser.
            if line.starts_with("#usda") {
                self.skip_line();
                return Ok(Token::new(Type::Magic, line)).into();
            }
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
                .map(Token::str);

            return Some(token);
        }

        // Asset reference.
        if self.buffer.starts_with('@') {
            let token = self
                .extract_quoted_string()
                .context("Failed to parse asset ref")
                .map(|asset| Token::new(Type::AssetRef, asset));

            return Some(token);
        }

        // Path reference.
        if self.buffer.starts_with('<') {
            let token = self
                .extract_quoted_string()
                .context("Failed to parse path ref")
                .map(|path| Token::new(Type::PathRef, path));

            return Some(token);
        }

        // Parse punctuation.
        // Note: there is a corner case with arrays like [1], where these are actually 3 different tokens.
        for ch in PUN {
            if let Some(buffer) = self.buffer.strip_prefix(ch) {
                self.buffer = buffer;
                return Ok(Token::new(Type::Punctuation, ch)).into();
            }
        }

        // It's not a quoted string at this point, so separate next word by space.
        let word = {
            let mut iter = self.buffer.split_whitespace();
            let mut next_word = iter.next()?;

            // Make sure "true," or "true)" recognized as two separate tokens: 'true' and ',' or ')'.
            // But also that "bool[]" is recognized as one token.
            if !next_word.ends_with("[]") {
                next_word = next_word.trim_end_matches(&[',', ';', ']', ')']);
            }

            self.buffer = self.buffer.strip_prefix(next_word).unwrap_or_default();

            next_word
        };

        // Try parse number
        if word.parse::<f32>().is_ok() {
            return Ok(Token::new(Type::Number, word)).into();
        }

        // Parse keywords.
        for (keyword, ty) in KEYWORDS {
            if keyword.eq(&word) {
                return Ok(Token::new(*ty, keyword)).into();
            }
        }

        // Namespace identifier
        if word.contains(':') {
            if !sdf::Path::is_valid_namespace_identifier(word) {
                return Err(anyhow!("Invalid ns identifier: {}", word)).into();
            }

            return Ok(Token::new(Type::NamespacedIdentifier, word)).into();
        }

        let mut ident = word;
        // Array identifier (like "bool[]") is still valid identifier
        // See https://github.com/PixarAnimationStudios/OpenUSD/blob/59992d2178afcebd89273759f2bddfe730e59aa8/pxr/usd/sdf/textFileFormat.yy#L2314
        if ident.ends_with("[]") {
            ident = ident.strip_suffix("[]").unwrap_or_default();
        }
        if sdf::Path::is_valid_identifier(ident) {
            return Ok(Token::new(Type::Identifier, word)).into();
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
    fn parse_payload() {
        let f = fs::read_to_string("fixtures/payload.usda").unwrap();

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

        assert_tokens(&f, &tokens);
    }

    #[test]
    fn parse_connection() {
        let f = fs::read_to_string("fixtures/connection.usda").unwrap();

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

        assert_tokens(&f, &tokens);
    }

    #[test]
    fn parse_fields() {
        let f = fs::read_to_string("fixtures/fields.usda").expect("Failed to read fields.usda");

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

        assert_tokens(&f, &tokens);
    }

    #[test]
    fn parse_empty_array() {
        let mut tok = Tokenizer::new("[]");

        let open = tok.next().unwrap().unwrap();
        assert_eq!(open, Token::new(Type::Punctuation, "["));

        let close = tok.next().unwrap().unwrap();
        assert_eq!(close, Token::new(Type::Punctuation, "]"));
    }

    #[test]
    fn parse_array_with_one_element() {
        let tokens = [(Type::Punctuation, "["), (Type::Number, "1"), (Type::Punctuation, "]")];
        assert_tokens("[1]", &tokens);
    }

    #[test]
    fn peekable_iter() {
        let f = fs::read_to_string("fixtures/fields.usda").unwrap();
        let tok = Tokenizer::new(&f);

        let expected = Token::new(Type::Magic, "#usda 1.0");

        let mut peekable = tok.peekable();
        assert_eq!(peekable.peek().unwrap().as_ref().unwrap().clone(), expected);

        let next = peekable.next().unwrap().unwrap();
        assert_eq!(next, expected);
    }

    #[test]
    fn parse_bool_array() {
        let str = "[true, false]";

        let tokens = [
            (Type::Punctuation, "["),
            (Type::Identifier, "true"),
            (Type::Punctuation, ","),
            (Type::Identifier, "false"),
            (Type::Punctuation, "]"),
        ];

        assert_tokens(str, &tokens);
    }

    #[test]
    fn parse_array_type() {
        let str = "bool[]";

        let tokens = [(Type::Identifier, "bool[]")];

        assert_tokens(str, &tokens);
    }

    #[test]
    fn parse_float_tuple() {
        let str = "(1.0, 2.0)";

        let tokens = [
            (Type::Punctuation, "("),
            (Type::Number, "1.0"),
            (Type::Punctuation, ","),
            (Type::Number, "2.0"),
            (Type::Punctuation, ")"),
        ];

        assert_tokens(str, &tokens);
    }

    fn assert_tokens(input: &str, tokens: &[(Type, &str)]) {
        let mut tok = Tokenizer::new(input);

        for (ty, expected) in tokens {
            let token = tok.next().expect("Unexpected end of tokens").unwrap();

            assert_eq!(*ty, token.ty);
            assert_eq!(*expected, token.str);
        }
    }
}
