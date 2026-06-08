use std::borrow::Borrow;
use std::hash::{Hash, Hasher};
use std::ops::Deref;

use super::{Value, ValueConversionError};

/// A reference to an external asset — the value of an `asset` attribute or
/// metadatum, authored in `@...@` syntax.
///
/// This is the Rust analog of USD's
/// [`SdfAssetPath`](https://openusd.org/release/api/class_sdf_asset_path.html).
/// It carries the authored path always, and the resolved path once value
/// resolution has anchored and resolved it (C++ also carries an evaluated
/// path with `expressionVariables` substituted — see the TODO below).
///
/// As layer data an asset path holds only its authored path; the resolved
/// path is filled in by value resolution ([`Attribute::get`](crate::usd::Attribute::get)),
/// anchored to the layer of the strongest opinion. Identity — equality,
/// hashing, and ordering — is therefore the authored path alone; the resolved
/// path is a derived annotation that does not affect it (this differs from
/// C++ `operator==`, which compares both).
///
/// The string-like traits ([`Deref`] to `str`, [`AsRef`], [`Borrow`],
/// [`Display`](std::fmt::Display), and `PartialEq` against string types) let
/// it stand in for its authored path: `&asset` coerces to `&str`, and
/// `asset == "foo.usd"` compares directly.
///
// TODO: C++ `SdfAssetPath` also carries an evaluated path (the authored path
// with `expressionVariables` substituted), exposed via `GetEvaluatedPath` /
// `SetEvaluatedPath` and preferred by `GetAssetPath` as the input to
// resolution. Add it once value resolution evaluates expressions into the
// asset path — until then it would be an inert field with no source of truth.
#[derive(Debug, Clone, Default)]
pub struct AssetPath {
    /// The path as authored in the layer, before asset resolution.
    pub authored_path: String,
    /// The result of asset resolution, set by value resolution; `None` for an
    /// asset path that has not been resolved (e.g. raw layer data).
    resolved_path: Option<String>,
}

impl AssetPath {
    /// Creates an asset path from its authored path string, with no resolved
    /// path yet.
    pub fn new(authored_path: impl Into<String>) -> Self {
        Self {
            authored_path: authored_path.into(),
            resolved_path: None,
        }
    }

    /// Creates an asset path with both its authored and resolved paths set
    /// (C++ `SdfAssetPath(authoredPath, resolvedPath)`).
    pub fn with_resolved_path(authored_path: impl Into<String>, resolved_path: impl Into<String>) -> Self {
        Self {
            authored_path: authored_path.into(),
            resolved_path: Some(resolved_path.into()),
        }
    }

    /// Borrows the authored path, before resolution.
    pub fn as_str(&self) -> &str {
        &self.authored_path
    }

    /// The resolved path if value resolution has set it, else `None`
    /// (C++ `GetResolvedPath`).
    pub fn resolved_path(&self) -> Option<&str> {
        self.resolved_path.as_deref()
    }

    /// Sets the resolved path (C++ `SetResolvedPath`).
    pub fn set_resolved_path(&mut self, resolved_path: impl Into<String>) {
        self.resolved_path = Some(resolved_path.into());
    }

    /// Returns `true` if the authored path is empty.
    pub fn is_empty(&self) -> bool {
        self.authored_path.is_empty()
    }

    /// Consumes the asset path, returning the owned authored path string.
    pub fn into_string(self) -> String {
        self.authored_path
    }
}

// Identity is the authored path alone; the resolved path is a derived cache.
impl PartialEq for AssetPath {
    fn eq(&self, other: &Self) -> bool {
        self.authored_path == other.authored_path
    }
}

impl Eq for AssetPath {}

impl Hash for AssetPath {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.authored_path.hash(state);
    }
}

impl PartialOrd for AssetPath {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AssetPath {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.authored_path.cmp(&other.authored_path)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for AssetPath {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.authored_path.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for AssetPath {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(AssetPath::new(String::deserialize(deserializer)?))
    }
}

impl Deref for AssetPath {
    type Target = str;

    fn deref(&self) -> &str {
        &self.authored_path
    }
}

impl AsRef<str> for AssetPath {
    fn as_ref(&self) -> &str {
        &self.authored_path
    }
}

impl Borrow<str> for AssetPath {
    fn borrow(&self) -> &str {
        &self.authored_path
    }
}

impl std::fmt::Display for AssetPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.authored_path)
    }
}

impl From<String> for AssetPath {
    fn from(authored_path: String) -> Self {
        Self::new(authored_path)
    }
}

impl From<&str> for AssetPath {
    fn from(authored_path: &str) -> Self {
        Self::new(authored_path)
    }
}

impl From<AssetPath> for String {
    fn from(asset: AssetPath) -> Self {
        asset.authored_path
    }
}

impl PartialEq<str> for AssetPath {
    fn eq(&self, other: &str) -> bool {
        self.authored_path == other
    }
}

impl PartialEq<&str> for AssetPath {
    fn eq(&self, other: &&str) -> bool {
        self.authored_path == *other
    }
}

impl PartialEq<String> for AssetPath {
    fn eq(&self, other: &String) -> bool {
        self.authored_path == *other
    }
}

impl PartialEq<AssetPath> for str {
    fn eq(&self, other: &AssetPath) -> bool {
        other.authored_path == *self
    }
}

impl PartialEq<AssetPath> for &str {
    fn eq(&self, other: &AssetPath) -> bool {
        other.authored_path == *self
    }
}

impl PartialEq<AssetPath> for String {
    fn eq(&self, other: &AssetPath) -> bool {
        other.authored_path == *self
    }
}

impl TryFrom<Value> for AssetPath {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::AssetPath(asset) => Ok(asset),
            other => ValueConversionError::err("AssetPath", &other),
        }
    }
}

impl TryFrom<Value> for Vec<AssetPath> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::AssetPathVec(assets) => Ok(assets),
            other => ValueConversionError::err("AssetPathVec", &other),
        }
    }
}

impl From<AssetPath> for Value {
    fn from(asset: AssetPath) -> Self {
        Value::AssetPath(asset)
    }
}

impl From<Vec<AssetPath>> for Value {
    fn from(assets: Vec<AssetPath>) -> Self {
        Value::AssetPathVec(assets)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_from_value() {
        let scalar = AssetPath::try_from(Value::AssetPath("./tex.png".into())).unwrap();
        assert_eq!(scalar, AssetPath::new("./tex.png"));

        let array = Vec::<AssetPath>::try_from(Value::AssetPathVec(vec!["a.png".into(), "b.png".into()])).unwrap();
        assert_eq!(array, vec![AssetPath::new("a.png"), AssetPath::new("b.png")]);

        // A plain string is not an asset path.
        assert!(AssetPath::try_from(Value::String("a.png".into())).is_err());

        // Round-trips back through the authoring `From` impls.
        assert_eq!(Value::from(scalar), Value::AssetPath("./tex.png".into()));
        assert_eq!(
            Value::from(array),
            Value::AssetPathVec(vec!["a.png".into(), "b.png".into()])
        );
    }

    #[test]
    fn string_like() {
        let asset = AssetPath::new("./tex.png");

        // Deref / AsRef coercion to &str.
        assert_eq!(asset.len(), "./tex.png".len());
        assert!(asset.ends_with(".png"));
        assert_eq!(asset.as_ref() as &str, "./tex.png");

        // Direct comparison against string types, both orderings.
        assert_eq!(asset, "./tex.png");
        assert_eq!("./tex.png", asset);
        assert_eq!(asset, String::from("./tex.png"));

        assert_eq!(asset.to_string(), "./tex.png");
        assert_eq!(String::from(asset), "./tex.png");

        assert!(!AssetPath::new("./tex.png").is_empty());
        assert!(AssetPath::default().is_empty());
    }
}
