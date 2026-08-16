use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::ops::Deref;

use crate::{ar, sdf};

/// A reference to an external asset — the value of an `asset` attribute or
/// metadatum, authored in `@...@` syntax.
///
/// This is the Rust analog of USD's
/// [`SdfAssetPath`](https://openusd.org/release/api/class_sdf_asset_path.html).
/// It carries the authored path always, plus — once value resolution has
/// processed it — the evaluated path (the authored path with its
/// `expressionVariables` substituted) and the resolved path (the result of
/// anchoring and resolving the evaluated path).
///
/// As layer data an asset path holds only its authored path; the evaluated and
/// resolved paths are filled in by value resolution
/// ([`Attribute::get`](crate::usd::Attribute::get)), which evaluates any
/// variable expression and anchors the result to the layer of the strongest
/// opinion. Identity — equality, hashing, and ordering — is therefore the
/// authored path alone; the evaluated and resolved paths are derived
/// annotations that do not affect it (this differs from C++ `operator==`,
/// which compares all three).
///
/// The string-like traits ([`Deref`] to `str`, [`AsRef`], [`Borrow`],
/// [`Display`](std::fmt::Display), and `PartialEq` against string types) let
/// it stand in for its authored path: `&asset` coerces to `&str`, and
/// `asset == "foo.usd"` compares directly.
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize), serde(transparent))]
pub struct AssetPath {
    /// The path as authored in the layer, before expression evaluation or
    /// asset resolution.
    pub authored_path: String,
    /// The authored path with its variable expression evaluated, set by value
    /// resolution; `None` when the authored path is not an expression or has
    /// not been evaluated (e.g. raw layer data). A derived annotation, not
    /// serialized.
    #[cfg_attr(feature = "serde", serde(skip))]
    evaluated_path: Option<String>,
    /// The result of asset resolution, set by value resolution; `None` for an
    /// asset path that has not been resolved (e.g. raw layer data). A derived
    /// annotation, not serialized.
    #[cfg_attr(feature = "serde", serde(skip))]
    resolved_path: Option<String>,
}

impl AssetPath {
    /// Creates an asset path from its authored path string, with no resolved
    /// path yet.
    pub fn new(authored_path: impl Into<String>) -> Self {
        Self {
            authored_path: authored_path.into(),
            evaluated_path: None,
            resolved_path: None,
        }
    }

    /// Creates an asset path with both its authored and resolved paths set
    /// (C++ `SdfAssetPath(authoredPath, resolvedPath)`).
    pub fn with_resolved_path(authored_path: impl Into<String>, resolved_path: impl Into<String>) -> Self {
        Self {
            authored_path: authored_path.into(),
            evaluated_path: None,
            resolved_path: Some(resolved_path.into()),
        }
    }

    /// Borrows the authored path, before expression evaluation or resolution.
    pub fn as_str(&self) -> &str {
        &self.authored_path
    }

    /// The path used as input to asset resolution: the evaluated path if value
    /// resolution has substituted an expression, otherwise the authored path
    /// (C++ `GetAssetPath`).
    pub fn asset_path(&self) -> &str {
        self.evaluated_path.as_deref().unwrap_or(&self.authored_path)
    }

    /// The authored path with its variable expression evaluated, if value
    /// resolution has set it, else `None` (C++ `GetEvaluatedPath`).
    pub fn evaluated_path(&self) -> Option<&str> {
        self.evaluated_path.as_deref()
    }

    /// Sets the evaluated path (C++ `SetEvaluatedPath`).
    pub fn set_evaluated_path(&mut self, evaluated_path: impl Into<String>) {
        self.evaluated_path = Some(evaluated_path.into());
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

/// How the expressions in an `asset` / `asset[]` value came out.
///
/// Ordered worst first, so the outcome of a whole value is the minimum over its
/// elements: one bad element makes the value untrustworthy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum AssetOutcome {
    /// An element's expression failed and the diagnostic was recorded.
    Failed,
    /// An element named nothing: it evaluated to the expression-language
    /// `None`, or there was no variable scope to evaluate against. No
    /// diagnostic either way — an author asking for nothing gets nothing, and
    /// an absent scope is the caller's own omission rather than the author's
    /// mistake.
    None,
    /// Every element yielded a path to resolve, whether or not it was authored
    /// as an expression.
    Evaluated,
}

/// An expression that failed to evaluate, for a caller that knows the site it
/// was authored at and can name that site in a diagnostic. Not an error type:
/// it carries the two strings such a diagnostic needs and nothing else.
#[derive(Debug)]
pub(crate) struct AssetExpressionFailure {
    /// The expression as authored.
    pub(crate) expression: String,
    /// What the engine reported, joined into one message.
    pub(crate) message: String,
}

/// Fills the evaluated and resolved paths on an `asset` / `asset[]` value,
/// recording any expression failure in `errors` (C++ `SdfResolveAssetPaths`).
/// A value holding no asset paths passes through untouched.
///
/// `variables` is the expression scope in effect where the value was authored.
/// `None` means there is no scope at all, which leaves an expression element
/// unevaluated and unresolved and records nothing — there are no variables for
/// the author to have been wrong about. `anchor` is the location a relative
/// path resolves against; `None` leaves that to the resolver's own default, as
/// it does for a value authored in an anonymous layer.
///
/// TODO(perf): each asset read re-runs `Resolver::resolve` (a filesystem hit);
/// a per-(anchor, path) resolution cache would avoid repeating it.
pub(crate) fn resolve_asset_paths(
    registry: &sdf::LayerRegistry,
    anchor: Option<&ar::ResolvedPath>,
    variables: Option<&HashMap<String, sdf::Value>>,
    value: sdf::Value,
    errors: &mut Vec<AssetExpressionFailure>,
) -> sdf::Value {
    map_paths(value, |asset| resolve_path(registry, anchor, variables, asset, errors)).0
}

/// Fills the evaluated path on an `asset` / `asset[]` value without resolving
/// it, recording any expression failure in `errors` (C++ `SdfAnchorAssetPaths`
/// stops short of resolution the same way) — and says how it came out.
///
/// For a caller that anchors the result itself, or one whose value is not a
/// file name at all: a `templateAssetPath` is a `#`-pattern expanded into a
/// sequence of clip paths, so resolving the pattern would name nothing.
pub(crate) fn evaluate_asset_paths(
    variables: Option<&HashMap<String, sdf::Value>>,
    value: sdf::Value,
    errors: &mut Vec<AssetExpressionFailure>,
) -> (sdf::Value, AssetOutcome) {
    map_paths(value, |asset| evaluate_path(variables, asset, errors))
}

/// Whether `value` holds an asset path that needs evaluating, so a caller can
/// skip assembling the scope and anchor for the ordinary literal case.
pub(crate) fn holds_asset_expression(value: &sdf::Value) -> bool {
    match value {
        sdf::Value::AssetPath(asset) => sdf::expr::is_expression(asset.as_str()),
        sdf::Value::AssetPathVec(assets) => assets.iter().any(|a| sdf::expr::is_expression(a.as_str())),
        _ => false,
    }
}

/// Rebuilds an `asset` / `asset[]` value through `f`, reporting the worst
/// outcome over its elements. A value holding no asset paths passes through
/// untouched, as [`Value::is_asset_valued`](sdf::Value::is_asset_valued)
/// defines the set.
fn map_paths(
    value: sdf::Value,
    mut f: impl FnMut(AssetPath) -> (AssetPath, AssetOutcome),
) -> (sdf::Value, AssetOutcome) {
    let mut outcome = AssetOutcome::Evaluated;
    let value = match value {
        sdf::Value::AssetPath(asset) => {
            let (asset, element) = f(asset);
            outcome = element;
            sdf::Value::AssetPath(asset)
        }
        sdf::Value::AssetPathVec(assets) => sdf::Value::AssetPathVec(
            assets
                .into_iter()
                .map(|asset| {
                    let (asset, element) = f(asset);
                    outcome = outcome.min(element);
                    asset
                })
                .collect(),
        ),
        other => other,
    };
    (value, outcome)
}

/// Evaluates a variable expression in `asset` and returns it with the evaluated
/// path recorded, leaving the resolved path for a caller that anchors.
///
/// The expression is evaluated against `variables` to the path used as input to
/// resolution (C++ `SdfAssetPath::GetAssetPath`). A malformed or non-string
/// expression pushes an [`AssetExpressionFailure`] and leaves the evaluated path unset;
/// one evaluating to the expression-language `None` is left unset silently, and
/// so is any expression with no scope to evaluate against. Evaluation owns the
/// derived paths: the result is rebuilt from the authored path so any prior
/// evaluated or resolved path is discarded.
fn evaluate_path(
    variables: Option<&HashMap<String, sdf::Value>>,
    asset: AssetPath,
    errors: &mut Vec<AssetExpressionFailure>,
) -> (AssetPath, AssetOutcome) {
    let mut asset = AssetPath::new(asset.into_string());
    // The per-element `is_expression` is load-bearing for `asset[]`: a plain
    // element in a mixed array must still skip evaluation.
    if asset.is_empty() || !sdf::expr::is_expression(asset.as_str()) {
        return (asset, AssetOutcome::Evaluated);
    }
    let Some(variables) = variables else {
        return (asset, AssetOutcome::None);
    };
    let evaluated = sdf::expr::evaluate_string(asset.as_str(), variables);
    match evaluated.value {
        Some(path) => {
            asset.set_evaluated_path(path);
            (asset, AssetOutcome::Evaluated)
        }
        None if evaluated.errors.is_empty() => (asset, AssetOutcome::None),
        None => {
            errors.push(AssetExpressionFailure {
                expression: asset.as_str().to_string(),
                message: evaluated.errors.join("; "),
            });
            (asset, AssetOutcome::Failed)
        }
    }
}

/// Evaluates `asset` as [`evaluate_path`] does, then anchors the result against
/// `anchor` and records the location it resolves to.
fn resolve_path(
    registry: &sdf::LayerRegistry,
    anchor: Option<&ar::ResolvedPath>,
    variables: Option<&HashMap<String, sdf::Value>>,
    asset: AssetPath,
    errors: &mut Vec<AssetExpressionFailure>,
) -> (AssetPath, AssetOutcome) {
    let (mut asset, outcome) = evaluate_path(variables, asset, errors);
    // An expression that yielded no path has none to anchor: resolving the
    // authored spelling would treat the expression itself as a file name.
    if asset.is_empty() || outcome != AssetOutcome::Evaluated {
        return (asset, outcome);
    }
    let identifier = registry.create_identifier(asset.asset_path(), anchor);
    if let Some(resolved) = registry.resolve(&identifier) {
        asset.set_resolved_path(resolved.to_string_lossy().into_owned());
    }
    (asset, outcome)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

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

    /// Without a variable scope an expression is left exactly as authored — no
    /// evaluated path, no resolution of the expression as a file name, and no
    /// diagnostic, since there are no variables to have been wrong about.
    #[test]
    fn no_scope_skips_expression() {
        let registry = sdf::LayerRegistry::default();
        let mut errors = Vec::new();
        let value = sdf::Value::AssetPath(AssetPath::new("`${A}`"));

        let value = resolve_asset_paths(&registry, None, None, value, &mut errors);

        let asset = value.try_as_asset_path().expect("an asset value stays one");
        assert_eq!(asset.as_str(), "`${A}`");
        assert_eq!(asset.evaluated_path(), None);
        assert_eq!(asset.resolved_path(), None);
        assert!(errors.is_empty());
    }

    /// A path that needs no anchor still resolves without one, which is what
    /// lets a value authored in an anonymous layer resolve at all.
    #[test]
    fn absolute_resolves_unanchored() {
        let dir = tempfile::tempdir().expect("tempdir");
        let texture = dir.path().join("tex.png");
        fs::write(&texture, b"png").expect("write texture");
        let authored = texture.to_string_lossy().replace('\\', "/");

        let registry = sdf::LayerRegistry::default();
        let mut errors = Vec::new();
        let value = sdf::Value::AssetPath(AssetPath::new(authored));

        let value = resolve_asset_paths(&registry, None, None, value, &mut errors);

        let asset = value.try_as_asset_path().expect("an asset value stays one");
        assert!(asset.resolved_path().is_some(), "an absolute path needs no anchor");
        assert!(errors.is_empty());
    }
}
