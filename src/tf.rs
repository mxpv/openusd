//! Tools Foundation (C++ `Tf`): foundational utility types shared across the
//! crate. Currently [`Token`], the interned-identifier string (C++ `TfToken`).

use std::cmp::Ordering;
use std::convert::Infallible;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::str::FromStr;
use std::sync::Arc;

/// An immutable identifier string.
///
/// Tokens name prims, properties, and variants, and carry the values of
/// `token`-typed attributes and metadata such as `typeName` and `kind`.
/// Mirrors C++ [`TfToken`](https://openusd.org/dev/api/class_tf_token.html):
/// the text is immutable, and tokens holding equal text compare and hash equal.
///
/// A compile-time token built with [`new`](Token::new) borrows a `&'static str`
/// and allocates nothing — the analog of `TfToken`'s immortal tokens, usable in
/// `const` (`const KIND: Token = Token::new("Xform")`). A runtime token built
/// from owned text (`from`) holds a shared `Arc<str>`, so cloning bumps a
/// refcount rather than copying. A `Token` is a distinct type, not a string:
/// read its text with [`as_str`](Token::as_str) and convert back with
/// `String::from`.
#[derive(Clone)]
pub struct Token(Repr);

/// The two token storages — a static literal or refcounted runtime text. Equal
/// text compares and hashes equal regardless of which storage holds it (see the
/// manual [`PartialEq`] / [`Hash`] on [`Token`]).
#[derive(Clone)]
enum Repr {
    Static(&'static str),
    Shared(Arc<str>), // TODO(perf): intern shared tokens in a global table for O(1) equality, like TfToken.
}

impl Token {
    /// Creates a compile-time token from a string literal — no allocation, and
    /// usable in `const` context.
    pub const fn new(text: &'static str) -> Self {
        Token(Repr::Static(text))
    }

    /// Borrows the token's text.
    pub fn as_str(&self) -> &str {
        match &self.0 {
            Repr::Static(s) => s,
            Repr::Shared(s) => s,
        }
    }
}

impl Default for Token {
    fn default() -> Self {
        Token(Repr::Static(""))
    }
}

/// Tokens read as their text, like `String` derefs to `str`: `str` methods
/// (`starts_with`, `strip_prefix`, …) apply directly, and a `&Token` coerces to
/// `&str` where a name is expected.
impl Deref for Token {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<str> for Token {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl From<&str> for Token {
    fn from(text: &str) -> Self {
        Token(Repr::Shared(Arc::from(text)))
    }
}

impl From<String> for Token {
    fn from(text: String) -> Self {
        Token(Repr::Shared(Arc::from(text)))
    }
}

impl From<&String> for Token {
    fn from(text: &String) -> Self {
        Token(Repr::Shared(Arc::from(text.as_str())))
    }
}

impl From<&Token> for Token {
    fn from(token: &Token) -> Self {
        token.clone()
    }
}

impl From<Token> for String {
    fn from(token: Token) -> Self {
        token.as_str().to_owned()
    }
}

/// Parsing a token is infallible: any string is a valid token. Lets callers
/// that decode text generically (e.g. the USDA parser's `parse_token::<T>`)
/// produce a `Token` without an intermediate `String`.
impl FromStr for Token {
    type Err = Infallible;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        Ok(Token::from(text))
    }
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for Token {}

impl PartialEq<str> for Token {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&str> for Token {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl PartialEq<Token> for str {
    fn eq(&self, other: &Token) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<Token> for &str {
    fn eq(&self, other: &Token) -> bool {
        *self == other.as_str()
    }
}

impl Hash for Token {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl PartialOrd for Token {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Token {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Token {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const KIND: Token = Token::new("Xform");

    #[test]
    fn const_static_equals_runtime() {
        // A `const` static token and a runtime (`Arc`-backed) token with the
        // same text are equal and hash equal, so either storage works as a map
        // key or in a comparison.
        let runtime = Token::from("Xform".to_string());
        assert_eq!(KIND, runtime);
        assert_eq!(KIND.as_str(), "Xform");

        let mut set = std::collections::HashSet::new();
        set.insert(runtime);
        assert!(set.contains(&KIND));
    }

    #[test]
    fn compares_with_str() {
        assert_eq!(KIND, "Xform");
        assert_eq!("Xform", KIND);
        assert_ne!(KIND, "Mesh");
        let name: &str = "Xform";
        assert!(KIND == name);
        assert!(name == KIND);
    }
}
