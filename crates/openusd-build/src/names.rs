//! Turning schema names into the identifiers generated code uses.
//!
//! Two conventions meet here. Token identifiers follow `usdGenSchema`
//! exactly — [`proper_case`], [`camel_case`], [`valid_identifier`] and
//! [`token_id`] are ports of its `_ProperCase`, `_CamelCase`,
//! `TfMakeValidIdentifier` and `_AddToken`, so a token this crate emits is
//! spelled the way the C++ generator spells it. Rust's own conventions are
//! [`screaming_snake`] for constants and [`snake_case`] for methods, which C++
//! has no counterpart for.

/// Words a token identifier may not be, so one that lands on any of them gains
/// a trailing underscore (`default` becomes `default_`).
///
/// Exactly what `usdGenSchema` reserves: the C++ and Python keywords, plus
/// `interface` (a macro in a Windows COM header) and `None`. Rust's own
/// keywords are absent on purpose — a token reaches Rust as the screaming-snake
/// constant [`screaming_snake`] spells, which no keyword can collide with, and
/// escaping them here would spell a shipped token (`loop`) differently from
/// every other OpenUSD generator.
const RESERVED: &[&str] = &[
    // C++ keywords, as usdGenSchema lists them.
    "alignas",
    "alignof",
    "and",
    "and_eq",
    "asm",
    "atomic_cancel",
    "atomic_commit",
    "atomic_noexcept",
    "auto",
    "bitand",
    "bitor",
    "bool",
    "break",
    "case",
    "catch",
    "char",
    "char8_t",
    "char16_t",
    "char32_t",
    "class",
    "compl",
    "concept",
    "const",
    "consteval",
    "constexpr",
    "constinit",
    "const_cast",
    "continue",
    "co_await",
    "co_return",
    "co_yield",
    "decltype",
    "default",
    "delete",
    "do",
    "double",
    "dynamic_cast",
    "else",
    "enum",
    "explicit",
    "export",
    "extern",
    "false",
    "float",
    "for",
    "friend",
    "goto",
    "if",
    "inline",
    "int",
    "long",
    "mutable",
    "namespace",
    "new",
    "noexcept",
    "not",
    "not_eq",
    "nullptr",
    "operator",
    "or",
    "or_eq",
    "private",
    "protected",
    "public",
    "reflexpr",
    "register",
    "reinterpret_cast",
    "requires",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "static_assert",
    "static_cast",
    "struct",
    "switch",
    "synchronized",
    "template",
    "this",
    "thread_local",
    "throw",
    "true",
    "try",
    "typedef",
    "typeid",
    "typename",
    "union",
    "unsigned",
    "using",
    "virtual",
    "void",
    "volatile",
    "wchar_t",
    "while",
    "xor",
    "xor_eq",
    // Python keywords, which usdGenSchema adds through `keyword.kwlist`.
    "False",
    "None",
    "True",
    "as",
    "assert",
    "async",
    "await",
    "def",
    "del",
    "elif",
    "except",
    "finally",
    "from",
    "global",
    "import",
    "in",
    "is",
    "lambda",
    "nonlocal",
    "pass",
    "raise",
    "with",
    "yield",
    // `interface` is a COM macro on Windows, which usdGenSchema also reserves.
    "interface",
];

/// The identifier a token is emitted under (C++ `_AddToken`).
///
/// [`valid_token`] does the shaping: a name keeps its spelling when the library
/// asks for literal identifiers and is camel-cased otherwise. A reserved word
/// then gains a trailing underscore.
pub fn token_id(name: &str, literal_identifiers: bool) -> String {
    let mut id = valid_token(name, literal_identifiers);
    if RESERVED.contains(&id.as_str()) {
        id.push('_');
    }
    id
}

/// A name made into a token identifier (C++ `_MakeValidToken`).
///
/// A leading digit takes an underscore rather than losing the digit, which is
/// what [`valid_identifier`] alone would do. A namespaced name is camel-cased
/// whatever the library asked for, since `:` cannot survive in an identifier.
pub fn valid_token(name: &str, literal_identifiers: bool) -> String {
    let mut id = if name.starts_with(|c: char| c.is_ascii_digit()) {
        format!("_{name}")
    } else {
        name.to_owned()
    };

    if !literal_identifiers || id.contains(':') {
        id = camel_case(&id);
    }
    if !is_identifier(&id) {
        id = valid_identifier(&id);
    }
    id
}

/// `aString` in `ProperCase`, dropping every non-word run
/// (C++ `_ProperCase`).
///
/// A single character is simply uppercased, as C++ does.
pub fn proper_case(name: &str) -> String {
    if name.chars().count() <= 1 {
        return name.to_uppercase();
    }

    let mut out = String::with_capacity(name.len());
    for word in name.split(|c: char| !c.is_alphanumeric() && c != '_') {
        let mut chars = word.chars();
        if let Some(first) = chars.next() {
            out.extend(first.to_uppercase());
            out.push_str(chars.as_str());
        }
    }
    out
}

/// `aString` in camelCase, dropping every non-word run (C++ `_CamelCase`).
pub fn camel_case(name: &str) -> String {
    if name.chars().count() <= 1 {
        return name.to_lowercase();
    }

    let proper = proper_case(name);
    let mut chars = proper.chars();
    match chars.next() {
        Some(first) => first.to_lowercase().chain(chars).collect(),
        None => proper,
    }
}

/// Whether `name` is already an identifier: a letter or underscore, then
/// letters, digits or underscores (C++ `TfIsValidIdentifier`).
///
/// ASCII-strict, where `sdf::Path::is_valid_identifier` admits any character
/// that is not a control or a space, so that no asset is rejected on read. A
/// name that passes here reaches generated Rust unchanged, so the strict rule
/// is the one that applies.
pub fn is_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    is_identifier_start(first) && chars.all(is_identifier_cont)
}

/// Whether `name` is an identifier Rust would accept: one this crate's own
/// rules admit, that is not a keyword and not the placeholder `_`.
///
/// A schema names its own types and accessors through `className` and
/// `apiName`, so a name Rust has taken has to be reported against the schema
/// that wrote it. The list is Rust's own reserved words, the editions'
/// together, since a generated file is compiled under the consumer's edition.
pub fn is_rust_identifier(name: &str) -> bool {
    is_identifier(name) && name != "_" && !RUST_KEYWORDS.contains(&name)
}

/// `name` with every character an identifier cannot hold replaced by an
/// underscore (C++ `TfMakeValidIdentifier`).
///
/// A leading digit becomes an underscore, losing the digit.
pub fn valid_identifier(name: &str) -> String {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return "_".to_owned();
    };

    let mut out = String::with_capacity(name.len());
    out.push(if is_identifier_start(first) { first } else { '_' });
    out.extend(chars.map(|c| if is_identifier_cont(c) { c } else { '_' }));
    out
}

/// A token identifier as the constant that holds it: `modelDrawMode` becomes
/// `MODEL_DRAW_MODE`.
///
/// The mapping is lossy — `hwPrimvar` and `hw_primvar` reach one `HW_PRIMVAR`
/// — so the emitter checks the constants it mints and reports the pair that
/// collided rather than leaving rustc to report a duplicate definition.
pub fn screaming_snake(id: &str) -> String {
    snake_case(id).to_ascii_uppercase()
}

/// A property's `apiName` as the method that reads it: `faceVertexCounts`
/// becomes `face_vertex_counts`.
///
/// A word breaks at an uppercase letter following a lowercase or a digit
/// (`drawMode`), or at one that opens a word inside a run of them
/// (`NDCWindow`). An underscore already in the name is a break, and never
/// doubles, so `default_` stays one word.
// TODO: a method name minted here is not checked against Rust's keywords. The
// emitter suffixes every accessor (`_attr`, `_rel`), which keeps its output
// clear of them; a bare method name would need the escape `token_id` applies.
pub fn snake_case(name: &str) -> String {
    let mut out = String::with_capacity(name.len() + 4);
    let mut previous: Option<char> = None;
    let mut chars = name.chars().peekable();

    while let Some(c) = chars.next() {
        let opens_word = c.is_uppercase()
            && previous.is_some_and(|p| {
                p.is_lowercase()
                    || p.is_ascii_digit()
                    || (p.is_uppercase() && chars.peek().is_some_and(|n| n.is_lowercase()))
            });
        if opens_word && !out.ends_with('_') {
            out.push('_');
        }
        out.push(c.to_ascii_lowercase());
        previous = Some(c);
    }
    out
}

/// The words Rust reserves, which no generated identifier may be: the strict
/// keywords of every edition, then the ones reserved for later use.
const RUST_KEYWORDS: &[&str] = &[
    "Self", "abstract", "as", "async", "await", "become", "box", "break", "const", "continue", "crate", "do", "dyn",
    "else", "enum", "extern", "false", "final", "fn", "for", "gen", "if", "impl", "in", "let", "loop", "macro",
    "match", "mod", "move", "mut", "override", "priv", "pub", "ref", "return", "self", "static", "struct", "super",
    "trait", "true", "try", "type", "typeof", "unsafe", "unsized", "use", "virtual", "where", "while", "yield",
];

/// Whether `c` may open an identifier: an ASCII letter or an underscore.
fn is_identifier_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

/// Whether `c` may continue one: that, or an ASCII digit.
fn is_identifier_cont(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A name Rust has taken is no identifier here, however well it reads as
    /// one to USD.
    #[test]
    fn keywords_are_not_identifiers() {
        assert!(is_identifier("type") && !is_rust_identifier("type"));
        assert!(is_identifier("_") && !is_rust_identifier("_"));
        assert!(is_rust_identifier("Sphere") && is_rust_identifier("type_"));
    }

    /// Non-word runs are dropped and each fragment is capitalized, as
    /// `usdGenSchema` does; a lone character is just uppercased.
    #[test]
    fn proper_case_words() {
        assert_eq!(proper_case("myFooBar"), "MyFooBar");
        assert_eq!(proper_case("my-foo bar"), "MyFooBar");
        assert_eq!(proper_case("a"), "A");
        assert_eq!(
            proper_case("hw_primvar"),
            "Hw_primvar",
            "an underscore is a word character"
        );
    }

    #[test]
    fn camel_case_words() {
        assert_eq!(camel_case("MyFooBar"), "myFooBar");
        assert_eq!(camel_case("my:foo:bar"), "myFooBar");
        assert_eq!(camel_case("A"), "a");
    }

    /// A leading digit is kept behind an underscore rather than replaced.
    #[test]
    fn valid_token_digit() {
        assert_eq!(valid_token("1stName", true), "_1stName");
        assert_eq!(valid_identifier("1stName"), "_stName", "the raw rule loses the digit");
    }

    /// A namespaced name is camel-cased even when the library asked for
    /// literal identifiers, since `:` cannot survive in an identifier.
    #[test]
    fn valid_token_namespaced() {
        assert_eq!(valid_token("inputs:file", true), "inputsFile");
        assert_eq!(token_id("inputs:file", true), "inputsFile");
    }

    /// A reserved word in either language takes a trailing underscore.
    #[test]
    fn token_id_reserved() {
        assert_eq!(token_id("default", true), "default_");
        assert_eq!(token_id("None", true), "None_");
        assert_eq!(token_id("interface", true), "interface_");
        assert_eq!(
            token_id("match", true),
            "match",
            "a Rust keyword is left alone: the constant it reaches is MATCH"
        );
        assert_eq!(
            screaming_snake(&token_id("loop", true)),
            "LOOP",
            "a shipped token keeps the spelling every other generator gives it"
        );
    }

    /// Without literal identifiers every token is camel-cased, which is the
    /// default `usdGenSchema` convention.
    #[test]
    fn token_id_camel() {
        assert_eq!(token_id("MyToken", false), "myToken");
        assert_eq!(token_id("MyToken", true), "MyToken");
    }

    #[test]
    fn identifier_shape() {
        assert!(is_identifier("_foo9"));
        assert!(!is_identifier("9foo"));
        assert!(!is_identifier("foo:bar"));
        assert!(!is_identifier(""));
        assert_eq!(valid_identifier(""), "_");
    }

    /// The constant spelling breaks words the way Rust does, keeps the
    /// underscores a token already has, and never doubles one.
    #[test]
    fn screaming_words() {
        assert_eq!(screaming_snake("modelDrawMode"), "MODEL_DRAW_MODE");
        assert_eq!(screaming_snake("default_"), "DEFAULT_");
        assert_eq!(
            screaming_snake("collection_MultipleApplyTemplate_ExpansionRule"),
            "COLLECTION_MULTIPLE_APPLY_TEMPLATE_EXPANSION_RULE"
        );
    }

    /// A run of capitals is one word, so an initialism does not become one
    /// letter per underscore.
    #[test]
    fn snake_initialisms() {
        assert_eq!(snake_case("faceVertexCounts"), "face_vertex_counts");
        assert_eq!(snake_case("dataWindowNDC"), "data_window_ndc");
        assert_eq!(snake_case("NDCWindow"), "ndc_window");
        assert_eq!(snake_case("localPos0"), "local_pos0");
    }
}
