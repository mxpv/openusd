//! Tokenizer receives usda file as input and outputs tokens for
//! further analysis.
//!
//! It uses `logos` crate under the hood to provide efficient and
//! robust tokenization.

use std::borrow::Cow;
use std::iter::Peekable;
use std::str::Chars;

use logos::Logos;

#[derive(Logos, Debug, Clone, PartialEq, Eq, Hash, strum::Display, strum::EnumIs, strum::EnumTryAs)]
#[logos(skip r"[ \t\r\n\f]+")] // Skip whitespace
#[logos(skip(r"#[^\r\n]*", allow_greedy = true))] // Skip line and block comments
#[logos(skip r"/\*[^*]*\*+(?:[^/*][^*]*\*+)*/")]
pub enum Token<'source> {
    /// Magic header - extract version number.
    /// Example: "#usda 1.0" -> "1.0", "#usda 1.0.32" -> "1.0.32"
    #[regex(r"#usda ([0-9]+\.[0-9]+(\.[0-9]+)?)", |lex| {
        let s = lex.slice();
        // Extract version after "#usda "
        &s[6..]
    })]
    Magic(&'source str),

    /// Double-quoted strings
    /// Example: "hello world" -> hello world
    #[regex(r#""([^"\\]|\\.)*""#, |lex| unquote(lex.slice(), 1))]
    /// Single-quoted strings
    /// Example: 'hello world' -> hello world
    #[regex(r#"'([^'\\]|\\.)*'"#, |lex| unquote(lex.slice(), 1))]
    /// Triple-quoted strings
    /// Example: """multi-line string""" -> multi-line string
    #[regex(r#""""([^"]|"[^"]|""[^"])*""""#, |lex| unquote(lex.slice(), 3))]
    /// Triple-single-quoted strings
    /// Example: '''multi-line string''' -> multi-line string
    #[regex(r"'''([^']|'[^']|''[^'])*'''", |lex| unquote(lex.slice(), 3))]
    String(Cow<'source, str>),

    // Keywords must come before Number to ensure "inf" is matched as a keyword, not an identifier
    #[token("add")]
    Add,
    #[token("append")]
    Append,
    #[token("class")]
    Class,
    #[token("config")]
    Config,
    #[token("connect")]
    Connect,
    #[token("custom")]
    Custom,
    #[token("customData")]
    CustomData,
    #[token("default")]
    Default,
    #[token("def")]
    Def,
    #[token("delete")]
    Delete,
    #[token("dictionary")]
    Dictionary,
    #[token("displayUnit")]
    DisplayUnit,
    #[token("doc")]
    Doc,
    #[token("inf")]
    Inf,
    #[token("inherits")]
    Inherits,
    #[token("kind")]
    Kind,
    #[token("nameChildren")]
    NameChildren,
    #[token("None")]
    None,
    #[token("offset")]
    Offset,
    #[token("over")]
    Over,
    #[token("payload")]
    Payload,
    #[token("permission")]
    Permission,
    #[token("prefixSubstitutions")]
    PrefixSubstitutions,
    #[token("prepend")]
    Prepend,
    #[token("properties")]
    Properties,
    #[token("references")]
    References,
    #[token("relocates")]
    Relocates,
    #[token("rel")]
    Rel,
    #[token("reorder")]
    Reorder,
    #[token("rootPrims")]
    RootPrims,
    #[token("scale")]
    Scale,
    #[token("subLayers")]
    SubLayers,
    #[token("suffixSubstitutions")]
    SuffixSubstitutions,
    #[token("specializes")]
    Specializes,
    #[token("spline")]
    Spline,
    #[token("symmetryArguments")]
    SymmetryArguments,
    #[token("symmetryFunction")]
    SymmetryFunction,
    #[token("timeSamples")]
    TimeSamples,
    #[token("uniform")]
    Uniform,
    #[token("variantSet")]
    VariantSet,
    #[token("variantSets")]
    VariantSets,
    #[token("variants")]
    Variants,
    #[token("varying")]
    Varying,

    /// Numbers (int, float, scientific notation)
    /// Examples: "42", "3.14", "1.23e-4", "-42", "+3.14", "-.67"
    /// Matches unsigned numbers OR signed numbers (sign may be followed by dot)
    #[regex(r"[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?|[+-]([0-9]+(\.[0-9]+)?|\.[0-9]+)([eE][+-]?[0-9]+)?", |lex| lex.slice())]
    Number(&'source str),

    /// Path references
    /// Example: "</World/Sphere/material:surface>" -> /World/Sphere/material:surface
    #[regex(r"<[^>]*>", |lex| trim_chars(lex.slice(), 1))]
    PathRef(&'source str),

    /// Asset references
    /// Example: "@./textures/wood.jpg@" -> ./textures/wood.jpg
    #[regex(r"@[^@]*@", |lex| trim_chars(lex.slice(), 1))]
    #[regex(r#"@@@([^@]|@[^@]|@@[^@])*@@@"#, |lex| trim_chars(lex.slice(), 3))]
    AssetRef(&'source str),

    /// Punctuation characters
    #[regex(r"[=,:;&.()\{\}\[\]+\-]", |lex| lex.slice().chars().next().unwrap())]
    Punctuation(char),

    /// Namespaced identifiers (contains colon)
    /// Examples: "inputs:diffuseColor", "outputs:surface"
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*:[a-zA-Z0-9_:]*", |lex| lex.slice())]
    NamespacedIdentifier(&'source str),

    /// Regular identifiers.
    /// Examples: "Sphere", "Material", "bool", "float3"
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice())]
    Identifier(&'source str),
}

impl Token<'_> {
    /// Returns the keyword's string representation, or `None` for non-keyword tokens.
    pub fn keyword_lexeme(&self) -> Option<&'static str> {
        match self {
            Token::Add => Some("add"),
            Token::Append => Some("append"),
            Token::Class => Some("class"),
            Token::Config => Some("config"),
            Token::Connect => Some("connect"),
            Token::Custom => Some("custom"),
            Token::CustomData => Some("customData"),
            Token::Default => Some("default"),
            Token::Def => Some("def"),
            Token::Delete => Some("delete"),
            Token::Dictionary => Some("dictionary"),
            Token::DisplayUnit => Some("displayUnit"),
            Token::Doc => Some("doc"),
            Token::Inf => Some("inf"),
            Token::Inherits => Some("inherits"),
            Token::Kind => Some("kind"),
            Token::NameChildren => Some("nameChildren"),
            Token::None => Some("None"),
            Token::Offset => Some("offset"),
            Token::Over => Some("over"),
            Token::Payload => Some("payload"),
            Token::Permission => Some("permission"),
            Token::PrefixSubstitutions => Some("prefixSubstitutions"),
            Token::Prepend => Some("prepend"),
            Token::Properties => Some("properties"),
            Token::References => Some("references"),
            Token::Relocates => Some("relocates"),
            Token::Rel => Some("rel"),
            Token::Reorder => Some("reorder"),
            Token::RootPrims => Some("rootPrims"),
            Token::Scale => Some("scale"),
            Token::SubLayers => Some("subLayers"),
            Token::SuffixSubstitutions => Some("suffixSubstitutions"),
            Token::Specializes => Some("specializes"),
            Token::Spline => Some("spline"),
            Token::SymmetryArguments => Some("symmetryArguments"),
            Token::SymmetryFunction => Some("symmetryFunction"),
            Token::TimeSamples => Some("timeSamples"),
            Token::Uniform => Some("uniform"),
            Token::VariantSet => Some("variantSet"),
            Token::VariantSets => Some("variantSets"),
            Token::Variants => Some("variants"),
            Token::Varying => Some("varying"),
            _ => None,
        }
    }
}

/// Strips `n` delimiter characters from each end of a token's text, for the
/// delimited forms that carry no escapes — a path reference or an asset path.
fn trim_chars(s: &str, n: usize) -> Option<&str> {
    if s.len() < 2 * n {
        // Handle cases where the string is too short to trim `n` characters from both ends.
        // This might indicate an unexpected input or regex issue.
        None
    } else {
        Some(&s[n..s.len() - n])
    }
}

/// Strips `n` delimiter characters from each end of a quoted string and expands
/// the escape sequences in what is left. Borrowed unless an escape was found.
fn unquote(s: &str, n: usize) -> Option<Cow<'_, str>> {
    if s.len() < 2 * n {
        // Too short to carry its own delimiters: an unexpected input, or a regex
        // that matched more loosely than it should.
        return None;
    }
    Some(unescape(&s[n..s.len() - n]))
}

/// Expands a quoted string's escape sequences (C++ `TfEscapeString`, which the
/// text parser applies to every quoted string).
///
/// `\a` `\b` `\f` `\n` `\r` `\t` `\v` are the C control characters, `\xNN` is up
/// to two hex digits and `\NNN` up to three octal digits, and any other escape
/// is the character itself — so `\"` is a quote and `\\` a backslash. A numeric
/// escape names a Unicode scalar rather than C++'s raw byte, since a Rust `str`
/// is UTF-8; the two agree over the ASCII range they are used in.
fn unescape(body: &str) -> Cow<'_, str> {
    if !body.contains('\\') {
        return Cow::Borrowed(body);
    }
    let mut out = String::with_capacity(body.len());
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        // A single-quoted string's regex only forms a token from complete escape
        // pairs; a triple-quoted one is not so constrained, and drops a trailing
        // backslash.
        let Some(escaped) = chars.next() else { break };
        match escaped {
            'a' => out.push('\u{7}'),
            'b' => out.push('\u{8}'),
            'f' => out.push('\u{c}'),
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            'v' => out.push('\u{b}'),
            'x' => push_numeric(&mut out, &mut chars, 16, 2, 0),
            '0'..='7' => push_numeric(&mut out, &mut chars, 8, 3, escaped.to_digit(8).unwrap_or_default()),
            other => out.push(other),
        }
    }
    Cow::Owned(out)
}

/// Consumes up to `max` further digits of `radix`, folds them into `seed`, and
/// pushes the character they name.
///
/// `\x` with no digit at all names nothing, so it yields a NUL and the character
/// after it is read as ordinary text — C++ runs the same accumulator over zero
/// digits and emits the zero it started with.
fn push_numeric(out: &mut String, chars: &mut Peekable<Chars<'_>>, radix: u32, max: u32, seed: u32) {
    let mut value = seed;
    let mut digits = if radix == 8 { 1 } else { 0 };
    while digits < max
        && let Some(digit) = chars.peek().and_then(|c| c.to_digit(radix))
    {
        value = value * radix + digit;
        chars.next();
        digits += 1;
    }
    if let Some(c) = char::from_u32(value) {
        out.push(c);
    }
}

#[cfg(test)]
mod escape_tests {
    use super::*;

    /// Lexes `source` and returns the single string token's content.
    fn lex_one(source: &str) -> String {
        let mut lexer = Token::lexer(source);
        match lexer.next().expect("a token").expect("lexes") {
            Token::String(s) => s.into_owned(),
            other => panic!("expected a string, got {other:?}"),
        }
    }

    /// Every escape C++ `TfEscapeStringReplaceChar` expands, and the rule for
    /// one it has no meaning for: the backslash goes, the character stays.
    #[test]
    fn expands_escapes() {
        assert_eq!(lex_one(r#""a\nb""#), "a\nb");
        assert_eq!(lex_one(r#""a\tb""#), "a\tb");
        assert_eq!(lex_one(r#""a\rb""#), "a\rb");
        assert_eq!(lex_one(r#""a\\b""#), "a\\b");
        assert_eq!(lex_one(r#""a\"b""#), "a\"b", "an escaped delimiter is the delimiter");
        assert_eq!(lex_one(r#""a\qb""#), "aqb", "an unknown escape drops the backslash");
        assert_eq!(lex_one(r#""\x41""#), "A", "hex");
        assert_eq!(
            lex_one(r#""a\xzb""#),
            "a\0zb",
            "`\\x` with no digit names nothing; the next character is ordinary text"
        );
        assert_eq!(lex_one(r#""\101""#), "A", "octal");
        assert_eq!(lex_one(r#""\a\b\f\v""#), "\u{7}\u{8}\u{c}\u{b}");
    }

    /// A string with no backslash is handed back borrowed, so the ordinary case
    /// allocates nothing.
    #[test]
    fn plain_string_borrows() {
        let source = r#""no escapes here""#;
        let mut lexer = Token::lexer(source);
        match lexer.next().expect("a token").expect("lexes") {
            Token::String(Cow::Borrowed(_)) => {}
            other => panic!("expected a borrowed string, got {other:?}"),
        }
    }

    /// A triple-quoted string is expanded the same way (C++
    /// `Sdf_EvalQuotedString` applies one rule to both forms).
    #[test]
    fn triple_quoted_expands() {
        assert_eq!(lex_one(r#""""a\'b""""#), "a'b");
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    // Helper function for asserting token sequences
    fn assert_tokens(input: &str, expected_tokens: &[(Token<'_>, &str)]) {
        let mut lexer = Token::lexer(input);

        for (expected_token, expected_str) in expected_tokens {
            let token = lexer.next().expect("Unexpected end of tokens").unwrap();

            // For string-bearing tokens, check the string content matches
            match &token {
                Token::String(s) => {
                    assert_eq!(s.as_ref(), *expected_str, "String content mismatch for token {token:?}");
                }
                Token::Magic(s)
                | Token::Number(s)
                | Token::PathRef(s)
                | Token::AssetRef(s)
                | Token::NamespacedIdentifier(s)
                | Token::Identifier(s) => {
                    assert_eq!(*s, *expected_str, "String content mismatch for token {token:?}");
                }
                Token::Punctuation(c) => {
                    let expected_char = expected_str.chars().next().unwrap();
                    assert_eq!(*c, expected_char, "Punctuation char mismatch for token {token:?}");
                }
                _ => {
                    // For keywords, just check the type matches (we'll check discriminant below)
                }
            }

            // Check token type matches using discriminant comparison
            assert_eq!(
                std::mem::discriminant(expected_token),
                std::mem::discriminant(&token),
                "Token type mismatch: expected {expected_token:?}, got {token:?}"
            );
        }
    }

    #[test]
    fn empty_file() {
        let mut lexer = Token::lexer("");
        assert!(lexer.next().is_none());

        let mut lexer = Token::lexer(" ");
        assert!(lexer.next().is_none());

        let mut lexer = Token::lexer(
            "

            ",
        );
        assert!(lexer.next().is_none());
    }

    #[test]
    fn parse_payload() {
        let f = fs::read_to_string("fixtures/payload.usda").unwrap();

        let tokens = [
            (Token::Magic("1.0"), "1.0"),
            // MySphere1
            (Token::Def, "def"),
            (Token::Identifier("Sphere"), "Sphere"),
            (Token::String("MySphere1".into()), "MySphere1"),
            (Token::Punctuation('('), "("),
            (Token::Payload, "payload"),
            (Token::Punctuation('='), "="),
            (Token::AssetRef("./payload.usda"), "./payload.usda"),
            (Token::PathRef("/MySphere"), "/MySphere"),
            (Token::Punctuation(')'), ")"),
            (Token::Punctuation('{'), "{"),
            (Token::Punctuation('}'), "}"),
            // MySphere2
            (Token::Def, "def"),
            (Token::Identifier("Sphere"), "Sphere"),
            (Token::String("MySphere2".into()), "MySphere2"),
            (Token::Punctuation('('), "("),
            (Token::Prepend, "prepend"),
            (Token::Payload, "payload"),
            (Token::Punctuation('='), "="),
            (Token::AssetRef("./cube_payload.usda"), "./cube_payload.usda"),
            (Token::PathRef("/PayloadCube"), "/PayloadCube"),
            (Token::Punctuation(')'), ")"),
            (Token::Punctuation('{'), "{"),
            (Token::Punctuation('}'), "}"),
        ];

        assert_tokens(&f, &tokens);
    }

    #[test]
    fn parse_connection() {
        let f = fs::read_to_string("fixtures/connection.usda").unwrap();

        let tokens = [
            (Token::Magic("1.0"), "1.0"),
            // def Material "boardMat"
            (Token::Def, "def"),
            (Token::Identifier("Material"), "Material"),
            (Token::String("boardMat".into()), "boardMat"),
            (Token::Punctuation('{'), "{"),
            // token inputs:frame:stPrimvarName = "st"
            (Token::Identifier("token"), "token"),
            (
                Token::NamespacedIdentifier("inputs:frame:stPrimvarName"),
                "inputs:frame:stPrimvarName",
            ),
            (Token::Punctuation('='), "="),
            (Token::String("st".into()), "st"),
            // token outputs:surface.connect = </TexModel/boardMat/PBRShader.outputs:surface>
            (Token::Identifier("token"), "token"),
            (Token::NamespacedIdentifier("outputs:surface"), "outputs:surface"),
            (Token::Punctuation('.'), "."),
            (Token::Connect, "connect"),
            (Token::Punctuation('='), "="),
            (
                Token::PathRef("/TexModel/boardMat/PBRShader.outputs:surface"),
                "/TexModel/boardMat/PBRShader.outputs:surface",
            ),
        ];

        assert_tokens(&f, &tokens);
    }

    #[test]
    fn parse_fields() {
        let f = fs::read_to_string("fixtures/fields.usda").expect("Failed to read fields.usda");

        let tokens = [
            (Token::Magic("1.0"), "1.0"),
            (Token::Punctuation('('), "("),
            // doc = """test string"""
            (Token::Doc, "doc"),
            (Token::Punctuation('='), "="),
            (Token::String("test string".into()), "test string"),
            // customLayerData = { string test = "Test string" }
            (Token::Identifier("customLayerData"), "customLayerData"),
            (Token::Punctuation('='), "="),
            (Token::Punctuation('{'), "{"),
            (Token::Identifier("string"), "string"),
            (Token::Identifier("test"), "test"),
            (Token::Punctuation('='), "="),
            (Token::String("Test string".into()), "Test string"),
            (Token::Punctuation('}'), "}"),
            // upAxis = "Y"
            (Token::Identifier("upAxis"), "upAxis"),
            (Token::Punctuation('='), "="),
            (Token::String("Y".into()), "Y"),
            // metersPerUnit = 0.01
            (Token::Identifier("metersPerUnit"), "metersPerUnit"),
            (Token::Punctuation('='), "="),
            (Token::Number("0.01"), "0.01"),
        ];

        assert_tokens(&f, &tokens);
    }

    #[test]
    fn parse_empty_array() {
        let mut lexer = Token::lexer("[]");

        let open = lexer.next().unwrap().unwrap();
        assert_eq!(open, Token::Punctuation('['));

        let close = lexer.next().unwrap().unwrap();
        assert_eq!(close, Token::Punctuation(']'));
    }

    #[test]
    fn parse_array_with_one_element() {
        let tokens = [
            (Token::Punctuation('['), "["),
            (Token::Number("1"), "1"),
            (Token::Punctuation(']'), "]"),
        ];
        assert_tokens("[1]", &tokens);
    }

    #[test]
    fn parse_bool_array() {
        let input = "[true, false]";

        let tokens = [
            (Token::Punctuation('['), "["),
            (Token::Identifier("true"), "true"),
            (Token::Punctuation(','), ","),
            (Token::Identifier("false"), "false"),
            (Token::Punctuation(']'), "]"),
        ];

        assert_tokens(input, &tokens);
    }

    #[test]
    fn parse_array_type() {
        let input = "bool[]";
        let tokens = [
            (Token::Identifier("bool"), "bool"),
            (Token::Punctuation('['), "["),
            (Token::Punctuation(']'), "]"),
        ];
        assert_tokens(input, &tokens);
    }

    #[test]
    fn parse_float_tuple() {
        let input = "(1.0, 2.0)";

        let tokens = [
            (Token::Punctuation('('), "("),
            (Token::Number("1.0"), "1.0"),
            (Token::Punctuation(','), ","),
            (Token::Number("2.0"), "2.0"),
            (Token::Punctuation(')'), ")"),
        ];

        assert_tokens(input, &tokens);
    }

    #[test]
    fn test_token_helpers() {
        let punct_token = Token::Punctuation('=');
        assert!(punct_token.is_punctuation()); // EnumIs generated method
        assert_eq!(punct_token.clone().try_as_punctuation(), Some('=')); // EnumTryAs generated method

        let ident_token = Token::Identifier("test");
        assert!(ident_token.is_identifier()); // EnumIs generated method
        assert_eq!(ident_token.clone().try_as_identifier(), Some("test")); // EnumTryAs generated method

        // Test that wrong types return None
        assert_eq!(punct_token.try_as_identifier(), None);
        assert_eq!(ident_token.try_as_punctuation(), None);
    }

    #[test]
    fn test_string_content_access() {
        // Test direct access to string content in tokens
        let token = Token::String("test".into());
        if let Token::String(s) = token {
            assert_eq!(s, "test");
        } else {
            panic!("Expected String token");
        }

        let token = Token::Number("123.45");
        if let Token::Number(s) = token {
            assert_eq!(s, "123.45");
        } else {
            panic!("Expected Number token");
        }

        // Test that keyword tokens don't have string content
        let token = Token::Def;
        assert!(matches!(token, Token::Def));
    }

    #[test]
    fn test_string_processing() {
        let input = r#""test string" 'single' """triple quote""" @@@asset@@@"#;
        let mut lexer = Token::lexer(input);

        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::String("test string".into()));

        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::String("single".into()));

        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::String("triple quote".into()));

        // Triple-@ is an asset reference, not a string.
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::AssetRef("asset"));
    }

    #[test]
    fn test_magic_version_extraction() {
        let input = "#usda 1.0";
        let mut lexer = Token::lexer(input);

        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::Magic("1.0"));

        let input2 = "#usda 2.1";
        let mut lexer2 = Token::lexer(input2);

        let token2 = lexer2.next().unwrap().unwrap();
        assert_eq!(token2, Token::Magic("2.1"));

        // Patch version.
        let input3 = "#usda 1.0.32";
        let mut lexer3 = Token::lexer(input3);
        let token3 = lexer3.next().unwrap().unwrap();
        assert_eq!(token3, Token::Magic("1.0.32"));
    }

    #[test]
    fn test_magic_with_crlf() {
        // Windows line endings: \r\n must not interfere with magic detection.
        let input = "#usda 1.0\r\n(\r\n)\r\n";
        let mut lexer = Token::lexer(input);
        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::Magic("1.0"));
    }

    #[test]
    fn test_trim_chars_function() {
        // Test normal cases
        assert_eq!(trim_chars("\"hello\"", 1), Some("hello"));
        assert_eq!(trim_chars("'world'", 1), Some("world"));
        assert_eq!(trim_chars("\"\"\"test\"\"\"", 3), Some("test"));
        assert_eq!(trim_chars("@@@asset@@@", 3), Some("asset"));
        assert_eq!(trim_chars("</path>", 1), Some("/path"));
        assert_eq!(trim_chars("@file@", 1), Some("file"));

        // Test edge cases
        assert_eq!(trim_chars("\"\"", 1), Some(""));
        assert_eq!(trim_chars("''", 1), Some(""));
        assert_eq!(trim_chars("\"", 1), None); // Too short
        assert_eq!(trim_chars("ab", 2), None); // Exactly 2*n characters
    }

    #[test]
    fn test_punctuation_char() {
        // Test that punctuation tokens correctly store single characters
        let input = "=,;(){}[]";
        let mut lexer = Token::lexer(input);

        let expected_chars = ['=', ',', ';', '(', ')', '{', '}', '[', ']'];
        for expected_char in expected_chars {
            let token = lexer.next().unwrap().unwrap();
            assert_eq!(token, Token::Punctuation(expected_char));
            assert!(token.is_punctuation()); // EnumIs generated method
            assert_eq!(token.try_as_punctuation(), Some(expected_char)); // EnumTryAs generated method
        }
    }

    #[test]
    fn test_tokenize_inf() {
        let input = "inf -inf +inf";
        let mut lexer = Token::lexer(input);

        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::Inf, "Expected Inf token");

        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::Punctuation('-'), "Expected '-' punctuation");

        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::Inf, "Expected Inf token after '-'");

        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::Punctuation('+'), "Expected '+' punctuation");

        let token = lexer.next().unwrap().unwrap();
        assert_eq!(token, Token::Inf, "Expected Inf token after '+'");

        assert!(lexer.next().is_none(), "Expected no more tokens");
    }

    /// Block comments (`/* ... */`) are skipped, preserving surrounding tokens.
    #[test]
    fn block_comments() {
        assert_tokens(
            "int /* padding */ a:b",
            &[
                (Token::Identifier("int"), "int"),
                (Token::NamespacedIdentifier("a:b"), "a:b"),
            ],
        );

        // Multiline block comment.
        assert_tokens(
            "float /* multi\nline\ncomment */ x",
            &[(Token::Identifier("float"), "float"), (Token::Identifier("x"), "x")],
        );

        // Adjacent block comments.
        assert_tokens(
            "a /* one */ /* two */ b",
            &[(Token::Identifier("a"), "a"), (Token::Identifier("b"), "b")],
        );
    }
}

#[test]
fn test_rel_token() {
    let input = "rel physics:test";
    let mut lexer = Token::lexer(input);

    let token = lexer.next().unwrap().unwrap();
    assert!(matches!(token, Token::Rel), "Expected Rel token, got {:?}", token);

    let token = lexer.next().unwrap().unwrap();
    assert!(
        matches!(token, Token::NamespacedIdentifier(_)),
        "Expected NamespacedIdentifier, got {:?}",
        token
    );
}
