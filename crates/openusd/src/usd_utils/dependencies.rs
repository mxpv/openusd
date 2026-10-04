//! Dependency discovery (C++ `UsdUtilsComputeAllDependencies`).

use std::collections::{HashSet, VecDeque};
use std::ops::Deref;

use super::DependencyError;
use crate::pcp::clip::keys;
use crate::sdf::{self, AbstractData, FieldKey, Value};
use crate::usd::Stage;
use crate::{Error, Result, ar, pcp};

/// The layers and assets a layer depends on, as C++
/// `UsdUtilsComputeAllDependencies` reports them.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Dependencies {
    /// The layers reached through sublayers, references, payloads and
    /// layer-valued asset paths, by identifier, the root first.
    pub layers: Vec<String>,
    /// The other assets the layers name, by resolved path.
    pub assets: Vec<String>,
    /// The asset paths that did not resolve, anchored to the layer authoring
    /// them.
    pub unresolved: Vec<String>,
}

/// Computes every layer and asset `asset_path` depends on through `stage`'s
/// resolver, as C++ `UsdUtilsComputeAllDependencies` does through the global
/// one.
///
/// Every variant is followed, not only the selected one, and deleted reference
/// and payload items are left out. A layer `stage` already holds is read as it
/// is in memory, unsaved edits included, as C++ reads a layer already open in
/// its layer registry; any other is read through the resolver without joining
/// the stage. Layers and assets inside a package are reported by their
/// package-relative path.
///
/// Variable expressions, UDIM and UV-tile patterns and clip templates, which
/// C++ expands, return [`DependencyError::Unsupported`].
pub fn compute_all_dependencies(stage: &Stage, asset_path: &str) -> Result<Dependencies> {
    let graph = stage.layers();
    let registry = graph.layer_registry();
    let root = root_identifier(&graph, asset_path);
    let mut dependencies = Dependencies::default();
    let mut seen = HashSet::from([root.clone()]);
    let mut queue = VecDeque::from([root.clone()]);
    let mut found = HashSet::new();
    while let Some(identifier) = queue.pop_front() {
        let Some(layer) = SourceLayer::open(&graph, &identifier)? else {
            if identifier == root {
                return Err(Error::UnresolvedAsset(asset_path.to_owned()));
            }
            dependencies.unresolved.push(identifier);
            continue;
        };
        let anchor = layer.anchor_location();
        visit_asset_paths(layer.data(), layer.identifier(), |asset| {
            if !asset.applied {
                return Ok(None);
            }
            let target = registry.create_identifier(asset.path, anchor.as_ref());
            if asset.layer {
                if seen.insert(target.clone()) {
                    queue.push_back(target);
                }
            } else if found.insert(target.clone()) {
                match registry.resolve(&target) {
                    Some(resolved) => dependencies.assets.push(resolved.to_string()),
                    None => dependencies.unresolved.push(target),
                }
            }
            Ok(None)
        })?;
        dependencies.layers.push(identifier);
    }
    Ok(dependencies)
}

/// The identifier of the root layer `asset_path` names: a layer `graph`
/// holds under that exact identifier, otherwise the canonical identifier.
pub(super) fn root_identifier(graph: &pcp::LayerGraph, asset_path: &str) -> String {
    if graph.id_of(asset_path).is_some() {
        return asset_path.to_owned();
    }
    graph.layer_registry().create_identifier(asset_path, None)
}

/// A layer read for the dependency walk: one the stage holds, or one read
/// through its resolver.
pub(super) enum SourceLayer<'a> {
    Live(&'a sdf::Layer),
    Read(sdf::Layer),
}

impl<'a> SourceLayer<'a> {
    /// The layer at `identifier`, or `None` when it does not resolve.
    pub(super) fn open(graph: &'a pcp::LayerGraph, identifier: &str) -> Result<Option<Self>> {
        if let Some(id) = graph.id_of(identifier) {
            return Ok(Some(Self::Live(graph.layer(id))));
        }
        let opened = graph.layer_registry().open(identifier)?;
        Ok(opened.map(|(resolved, data)| Self::Read(sdf::Layer::new_resolved(identifier, &resolved, data))))
    }
}

impl Deref for SourceLayer<'_> {
    type Target = sdf::Layer;

    fn deref(&self) -> &sdf::Layer {
        match self {
            Self::Live(layer) => layer,
            Self::Read(layer) => layer,
        }
    }
}

/// An asset path a layer authors, as [`visit_asset_paths`] reports it.
pub(super) struct AssetRef<'a> {
    /// The authored path.
    pub path: &'a str,
    /// Whether it names a layer: a sublayer, reference or payload, or an
    /// asset value with a layer file extension.
    pub layer: bool,
    /// Whether it adds an opinion: `false` for a deleted or reordered
    /// reference or payload list-op item.
    pub applied: bool,
}

/// Calls `visit` with every asset path `data` authors, across every spec,
/// variants included: sublayers, reference and payload list-op items, and
/// asset values in fields, dictionaries, arrays and time samples. A path
/// `visit` returns a replacement for is rewritten, and the rewritten fields
/// are returned for the caller to apply to a copy. `layer` names the layer in
/// errors.
pub(super) fn visit_asset_paths(
    data: &dyn AbstractData,
    layer: &str,
    mut visit: impl FnMut(AssetRef<'_>) -> Result<Option<String>>,
) -> Result<Vec<(sdf::Path, String, Value)>> {
    let mut edits = Vec::new();
    let mut paths = data.spec_paths();
    paths.sort();
    for path in paths {
        let mut fields = data.list_fields(&path).unwrap_or_default();
        fields.sort();
        for field in fields {
            let mut value = data.get_field(&path, &field)?.into_owned();
            let mut walk = Walk {
                layer,
                visit: &mut visit,
                changed: false,
            };
            match &mut value {
                Value::StringVec(sublayers) if field == FieldKey::SubLayers.as_str() => {
                    for sublayer in sublayers {
                        walk.path(sublayer, true, true)?;
                    }
                }
                value => {
                    if field == FieldKey::Clips.as_str() {
                        walk.reject_clip_templates(value)?;
                    }
                    walk.value(value)?;
                }
            }
            if walk.changed {
                edits.push((path.clone(), field, value));
            }
        }
    }
    Ok(edits)
}

/// One field's walk for [`visit_asset_paths`].
struct Walk<'a, F> {
    layer: &'a str,
    visit: &'a mut F,
    changed: bool,
}

impl<F: FnMut(AssetRef<'_>) -> Result<Option<String>>> Walk<'_, F> {
    fn path(&mut self, path: &mut String, layer: bool, applied: bool) -> Result<()> {
        if path.is_empty() {
            return Ok(());
        }
        let kind = if sdf::expr::is_expression(path) {
            Some("variable expression")
        } else if path.contains("<UDIM>") || path.contains("<UVTILE>") {
            Some("UDIM pattern")
        } else {
            None
        };
        if let Some(kind) = kind {
            return Err(self.unsupported(kind, path));
        }
        let layer = layer || is_layer_path(path);
        if let Some(rewritten) = (self.visit)(AssetRef { path, layer, applied })? {
            *path = rewritten;
            self.changed = true;
        }
        Ok(())
    }

    fn asset(&mut self, asset: &mut sdf::AssetPath) -> Result<()> {
        let mut path = asset.authored_path.clone();
        self.path(&mut path, false, true)?;
        if path != asset.authored_path {
            *asset = sdf::AssetPath::new(path);
        }
        Ok(())
    }

    fn list_op<T: Default + Clone + PartialEq>(
        &mut self,
        op: &mut sdf::ListOp<T>,
        mut item: impl FnMut(&mut Self, &mut T, bool) -> Result<()>,
    ) -> Result<()> {
        let applied = [
            &mut op.explicit_items,
            &mut op.added_items,
            &mut op.prepended_items,
            &mut op.appended_items,
        ];
        for items in applied {
            for entry in items {
                item(self, entry, true)?;
            }
        }
        for items in [&mut op.deleted_items, &mut op.ordered_items] {
            for entry in items {
                item(self, entry, false)?;
            }
        }
        Ok(())
    }

    fn value(&mut self, value: &mut Value) -> Result<()> {
        match value {
            Value::AssetPath(asset) => self.asset(asset)?,
            Value::AssetPathVec(assets) => {
                for asset in assets {
                    self.asset(asset)?;
                }
            }
            Value::Dictionary(entries) | Value::UnregisteredDictionary(entries) => {
                let mut keys: Vec<_> = entries.keys().cloned().collect();
                keys.sort();
                for key in keys {
                    if let Some(entry) = entries.get_mut(&key) {
                        self.value(entry)?;
                    }
                }
            }
            Value::ValueVec(values) => {
                for value in values {
                    self.value(value)?;
                }
            }
            Value::TimeSamples(samples) => {
                for (_, value) in samples {
                    self.value(value)?;
                }
            }
            Value::ReferenceListOp(op) => self.list_op(op, |walk, reference, applied| {
                walk.path(&mut reference.asset_path, true, applied)?;
                let mut keys: Vec<_> = reference.custom_data.keys().cloned().collect();
                keys.sort();
                for key in keys {
                    if let Some(entry) = reference.custom_data.get_mut(&key) {
                        walk.value(entry)?;
                    }
                }
                Ok(())
            })?,
            Value::PayloadListOp(op) => self.list_op(op, |walk, payload, applied| {
                walk.path(&mut payload.asset_path, true, applied)
            })?,
            Value::Payload(payload) => self.path(&mut payload.asset_path, true, true)?,
            _ => {}
        }
        Ok(())
    }

    /// Refuses a clip set that derives its clips from a template.
    fn reject_clip_templates(&self, clips: &Value) -> Result<()> {
        let Value::Dictionary(sets) = clips else {
            return Ok(());
        };
        for set in sets.values() {
            if let Value::Dictionary(set) = set
                && let Some(Value::String(template)) = set.get(keys::TEMPLATE_ASSET_PATH)
            {
                return Err(self.unsupported("clip template", template));
            }
        }
        Ok(())
    }

    fn unsupported(&self, kind: &'static str, path: &str) -> Error {
        DependencyError::Unsupported {
            kind,
            path: path.to_owned(),
            layer: self.layer.to_owned(),
        }
        .into()
    }
}

/// Whether `path` names a layer by its file extension, looking inside the
/// innermost package bracket.
fn is_layer_path(path: &str) -> bool {
    let inner = ar::split_package_relative_path_inner(path).map_or_else(|| path.to_owned(), |(_, inner)| inner);
    let extension = std::path::Path::new(&inner)
        .extension()
        .and_then(|extension| extension.to_str())
        .unwrap_or_default();
    sdf::LayerRegistry::find_by_extension(extension).is_some()
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    use super::*;
    use crate::usdz::ArchiveWriter;

    fn write(dir: &Path, path: &str, contents: &str) {
        let path = dir.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    const ROOT: &str = r#"#usda 1.0
(
    customLayerData = {
        asset icon = @./meta.png@
    }
    subLayers = [@./layers/sub.usda@]
)

def "A" (
    delete references = @./deleted.usda@
    prepend references = @./ref.usda@</A>
)
{
    asset sampled.timeSamples = {
        1: @./sample.png@,
    }
    asset[] textures = [@./tex.png@, @./missing.png@]
}

def "P" (
    prepend payload = @../outside/payload.usda@</P>
)
{
}

def "V" (
    variants = {
        string v = "one"
    }
    prepend variantSets = "v"
)
{
    variantSet "v" = {
        "one" (
            prepend references = @./one.usda@</V>
        ) {
        }
        "two" (
            prepend references = @./two.usda@</V>
        ) {
        }
    }
}

def "M" (
    prepend references = @./missing.usda@
)
{
}

def "N" (
    prepend references = @./pkg.usdz@
)
{
}
"#;

    /// The scene `compute_all_dependencies_matches_cpp` walks: every kind of
    /// dependency, a missing layer and texture, a layer outside the root's
    /// directory and a package.
    fn scene(dir: &Path) -> String {
        write(dir, "scene/root.usda", ROOT);
        write(
            dir,
            "scene/layers/sub.usda",
            "#usda 1.0\ndef \"S\" {\n    asset t = @../sub_tex.png@\n}\n",
        );
        write(
            dir,
            "scene/ref.usda",
            "#usda 1.0\ndef \"A\" {\n    asset t = @./ref_tex.png@\n}\n",
        );
        for name in ["deleted", "one", "two"] {
            write(dir, &format!("scene/{name}.usda"), "#usda 1.0\ndef \"V\" {\n}\n");
        }
        write(dir, "outside/payload.usda", "#usda 1.0\ndef \"P\" {\n}\n");
        for name in ["meta", "sample", "tex", "sub_tex", "ref_tex"] {
            write(dir, &format!("scene/{name}.png"), "PNG");
        }
        let mut package = ArchiveWriter::create(dir.join("scene/pkg.usdz")).unwrap();
        package
            .add_layer(
                "inner.usda",
                b"#usda 1.0\n(defaultPrim = \"N\")\ndef \"N\" {\n    asset t = @./inside.png@\n}\n",
            )
            .unwrap();
        package.add_layer("inside.png", b"PNG").unwrap();
        package.finish().unwrap();
        dir.join("scene/root.usda").to_str().unwrap().to_owned()
    }

    fn relative(dir: &Path, paths: &[String]) -> Vec<String> {
        let base = format!(
            "{}{}",
            fs::canonicalize(dir).unwrap().display(),
            std::path::MAIN_SEPARATOR
        );
        let mut paths: Vec<_> = paths
            .iter()
            .map(|path| path.replace(&base, "").replace('\\', "/"))
            .collect();
        paths.sort();
        paths
    }

    /// The fixture C++ 25.05 was run on gives these sets from
    /// `UsdUtils.ComputeAllDependencies("scene/root.usda")`.
    #[test]
    fn compute_all_dependencies_matches_cpp() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = scene(dir.path());
        let stage = Stage::open(&root)?;
        let dependencies = compute_all_dependencies(&stage, &root)?;
        assert_eq!(
            relative(dir.path(), &dependencies.layers),
            [
                "outside/payload.usda",
                "scene/layers/sub.usda",
                "scene/one.usda",
                "scene/pkg.usdz",
                "scene/ref.usda",
                "scene/root.usda",
                "scene/two.usda",
            ]
        );
        assert!(Path::new(&dependencies.layers[0]).ends_with("scene/root.usda"));
        assert_eq!(
            relative(dir.path(), &dependencies.assets),
            [
                "scene/meta.png",
                "scene/pkg.usdz[inside.png]",
                "scene/ref_tex.png",
                "scene/sample.png",
                "scene/sub_tex.png",
                "scene/tex.png",
            ]
        );
        assert_eq!(
            relative(dir.path(), &dependencies.unresolved),
            ["scene/missing.png", "scene/missing.usda"]
        );
        Ok(())
    }

    /// A layer the stage holds is walked as it is in memory, so an unsaved
    /// edit's dependency is found.
    #[test]
    fn unsaved_edits_are_walked() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(dir.path(), "root.usda", "#usda 1.0\ndef \"A\" {\n}\n");
        write(dir.path(), "extra.usda", "#usda 1.0\ndef \"E\" {\n}\n");
        let root = dir.path().join("root.usda").to_str().unwrap().to_owned();
        let stage = Stage::open(&root)?;
        let identifier = stage.root_layer().identifier().to_owned();
        stage.layer_mut(&identifier).unwrap().edit(|edit| {
            edit.data_mut().set_field(
                &sdf::Path::abs_root(),
                FieldKey::SubLayers.as_str(),
                Value::StringVec(vec!["./extra.usda".into()]),
            );
            Ok(())
        })?;
        let dependencies = compute_all_dependencies(&stage, &identifier)?;
        assert_eq!(relative(dir.path(), &dependencies.layers), ["extra.usda", "root.usda"]);
        Ok(())
    }

    /// Paths C++ expands before following are refused, naming the path.
    #[test]
    fn expansions_are_unsupported() -> Result<()> {
        let dir = tempfile::tempdir()?;
        for (body, kind) in [
            ("asset t = @./tex.<UDIM>.png@", "UDIM pattern"),
            ("asset t = @`\"./${NAME}.png\"`@", "variable expression"),
        ] {
            write(
                dir.path(),
                "root.usda",
                &format!("#usda 1.0\ndef \"A\" {{\n    {body}\n}}\n"),
            );
            let root = dir.path().join("root.usda").to_str().unwrap().to_owned();
            let stage = Stage::open(&root)?;
            let error = compute_all_dependencies(&stage, &root).unwrap_err();
            assert!(
                matches!(&error, Error::Dependency(DependencyError::Unsupported { kind: k, .. }) if *k == kind),
                "{error}"
            );
        }
        Ok(())
    }
}
