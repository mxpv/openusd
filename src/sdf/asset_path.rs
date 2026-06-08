use std::borrow::Borrow;
use std::ops::Deref;

use super::{Value, ValueConversionError};

/// A reference to an external asset — the value of an `asset` attribute or
/// metadatum, authored in `@...@` syntax.
///
/// This is the Rust analog of USD's
/// [`SdfAssetPath`](https://openusd.org/release/api/class_sdf_asset_path.html),
/// simplified to the authored path alone (C++ also carries the resolved path
/// and the evaluated variable expression).
///
/// The string-like traits ([`Deref`] to `str`, [`AsRef`], [`Borrow`],
/// [`Display`](std::fmt::Display), and `PartialEq` against string types) let
/// it stand in for its authored path: `&asset` coerces to `&str`, and
/// `asset == "foo.usd"` compares directly.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize), serde(transparent))]
pub struct AssetPath {
    /// The path as authored in the layer, before asset resolution.
    pub authored_path: String,
}

impl AssetPath {
    /// Creates an asset path from its authored path string.
    pub fn new(authored_path: impl Into<String>) -> Self {
        Self {
            authored_path: authored_path.into(),
        }
    }

    /// Borrows the authored path, before resolution.
    pub fn as_str(&self) -> &str {
        &self.authored_path
    }

    /// Consumes the asset path, returning the owned authored path string.
    pub fn into_string(self) -> String {
        self.authored_path
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
        Self { authored_path }
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
    }
}
