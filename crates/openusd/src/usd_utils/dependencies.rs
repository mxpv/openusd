//! Dependency discovery (C++ `UsdUtilsComputeAllDependencies`).

use std::collections::{HashMap, HashSet, VecDeque};
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
        visit_asset_paths(layer.data(), layer.identifier(), Visit::STRICT, |asset| {
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

/// Rewrites every asset path `layer` authors with `modify`, as C++
/// `UsdUtilsModifyAssetPaths` does: sublayers, reference and payload list-op
/// items (deleted ones included), clip template paths, and asset values in
/// fields, dictionaries, arrays and time samples, across every spec.
/// Variable expressions and patterns reach `modify` as authored, and each
/// distinct path reaches it once.
///
/// An empty result removes the path from the sublayers (with its layer
/// offset), from reference and payload lists and, unless
/// `keep_empty_paths_in_arrays`, from asset arrays, and clears an
/// asset-valued field. C++ 25.05 drops every sublayer offset once a sublayer
/// path changes; here the offsets stay with their sublayers.
pub fn modify_asset_paths(
    layer: &mut sdf::Layer,
    mut modify: impl FnMut(&str) -> String,
    keep_empty_paths_in_arrays: bool,
) -> Result<()> {
    let mode = Visit {
        strict: false,
        keep_empty_paths_in_arrays,
    };
    let mut modified = HashMap::new();
    let edits = visit_asset_paths(layer.data(), layer.identifier(), mode, |asset| {
        let path = modified
            .entry(asset.path.to_owned())
            .or_insert_with(|| modify(asset.path));
        Ok((path != asset.path).then(|| path.clone()))
    })?;
    if edits.is_empty() {
        return Ok(());
    }
    layer.edit(|edit| {
        let data = edit.data_mut();
        for (path, field, value) in edits {
            match value {
                Some(value) => data.set_field(&path, &field, value),
                None => data.erase_field(&path, &field),
            }
        }
        Ok(())
    })?;
    Ok(())
}

/// An asset path a layer authors, as [`visit_asset_paths`] reports it.
pub(super) struct AssetRef<'a> {
    /// The authored path.
    pub path: &'a str,
    /// Whether it names a layer: a sublayer, reference or payload, a clip
    /// template, or an asset value with a layer file extension.
    pub layer: bool,
    /// Whether it adds an opinion: `false` for a deleted or reordered
    /// reference or payload list-op item.
    pub applied: bool,
}

/// How [`visit_asset_paths`] treats the paths it meets.
#[derive(Clone, Copy)]
pub(super) struct Visit {
    /// Refuse the paths C++ expands before following (variable expressions,
    /// UDIM and UV-tile patterns, clip templates) instead of visiting them.
    pub strict: bool,
    /// Keep an asset array entry `visit` empties instead of removing it.
    pub keep_empty_paths_in_arrays: bool,
}

impl Visit {
    /// The dependency walk's mode.
    pub(super) const STRICT: Self = Self {
        strict: true,
        keep_empty_paths_in_arrays: true,
    };
}

/// A field [`visit_asset_paths`] rewrote: its new value, or `None` to erase it.
pub(super) type FieldEdit = (sdf::Path, String, Option<Value>);

/// Calls `visit` with every asset path `data` authors, across every spec,
/// variants included: sublayers, reference and payload list-op items, clip
/// template paths, and asset values in fields, dictionaries, arrays and time
/// samples. A path `visit` returns a replacement for is rewritten, an emptied
/// one removed as [`modify_asset_paths`] describes, and the rewritten fields
/// are returned for the caller to apply. `layer` names the layer in errors.
pub(super) fn visit_asset_paths(
    data: &dyn AbstractData,
    layer: &str,
    mode: Visit,
    mut visit: impl FnMut(AssetRef<'_>) -> Result<Option<String>>,
) -> Result<Vec<FieldEdit>> {
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
                mode,
                visit: &mut visit,
                changed: false,
            };
            let mut erase = false;
            match &mut value {
                Value::StringVec(sublayers) if field == FieldKey::SubLayers.as_str() => {
                    let removed = walk.sublayers(sublayers)?;
                    let offsets = FieldKey::SubLayerOffsets.as_str();
                    if !removed.is_empty()
                        && let Ok(Value::LayerOffsetVec(all)) =
                            data.get_field(&path, offsets).map(|value| value.into_owned())
                    {
                        let kept = all
                            .into_iter()
                            .enumerate()
                            .filter(|(index, _)| !removed.contains(index))
                            .map(|(_, offset)| offset)
                            .collect();
                        edits.push((path.clone(), offsets.to_owned(), Some(Value::LayerOffsetVec(kept))));
                    }
                }
                Value::AssetPath(asset) => erase = walk.asset(asset)?,
                value => {
                    if field == FieldKey::Clips.as_str() {
                        walk.clip_templates(value)?;
                    }
                    walk.value(value)?;
                }
            }
            if walk.changed {
                edits.push((path.clone(), field, (!erase).then_some(value)));
            }
        }
    }
    Ok(edits)
}

/// One field's walk for [`visit_asset_paths`].
struct Walk<'a, F> {
    layer: &'a str,
    mode: Visit,
    visit: &'a mut F,
    changed: bool,
}

impl<F: FnMut(AssetRef<'_>) -> Result<Option<String>>> Walk<'_, F> {
    /// Visits one path, returning whether `visit` emptied it.
    fn path(&mut self, path: &mut String, layer: bool, applied: bool) -> Result<bool> {
        if path.is_empty() {
            return Ok(false);
        }
        if self.mode.strict {
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
        }
        let layer = layer || is_layer_path(path);
        let Some(rewritten) = (self.visit)(AssetRef { path, layer, applied })? else {
            return Ok(false);
        };
        *path = rewritten;
        self.changed = true;
        Ok(path.is_empty())
    }

    /// Visits the sublayers, removing the emptied ones and returning their
    /// indices.
    fn sublayers(&mut self, sublayers: &mut Vec<String>) -> Result<Vec<usize>> {
        let mut removed = Vec::new();
        for (index, sublayer) in sublayers.iter_mut().enumerate() {
            if self.path(sublayer, true, true)? {
                removed.push(index);
            }
        }
        let mut index = 0;
        sublayers.retain(|_| {
            index += 1;
            !removed.contains(&(index - 1))
        });
        Ok(removed)
    }

    /// Visits an asset value, returning whether `visit` emptied it.
    fn asset(&mut self, asset: &mut sdf::AssetPath) -> Result<bool> {
        let mut path = asset.authored_path.clone();
        let emptied = self.path(&mut path, false, true)?;
        if path != asset.authored_path {
            *asset = sdf::AssetPath::new(path);
        }
        Ok(emptied)
    }

    /// Visits every item of `op` with `item`, removing the ones it reports
    /// emptied.
    fn list_op<T: Default + Clone + PartialEq>(
        &mut self,
        op: &mut sdf::ListOp<T>,
        mut item: impl FnMut(&mut Self, &mut T, bool) -> Result<bool>,
    ) -> Result<()> {
        let lists = [
            (&mut op.explicit_items, true),
            (&mut op.added_items, true),
            (&mut op.prepended_items, true),
            (&mut op.appended_items, true),
            (&mut op.deleted_items, false),
            (&mut op.ordered_items, false),
        ];
        for (items, applied) in lists {
            let mut kept = Vec::with_capacity(items.len());
            for mut entry in std::mem::take(items) {
                if !item(self, &mut entry, applied)? {
                    kept.push(entry);
                }
            }
            *items = kept;
        }
        Ok(())
    }

    fn value(&mut self, value: &mut Value) -> Result<()> {
        match value {
            Value::AssetPath(asset) => {
                self.asset(asset)?;
            }
            Value::AssetPathVec(assets) => {
                let mut kept = Vec::with_capacity(assets.len());
                for mut asset in std::mem::take(assets) {
                    if !self.asset(&mut asset)? || self.mode.keep_empty_paths_in_arrays {
                        kept.push(asset);
                    }
                }
                *assets = kept;
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
                if walk.path(&mut reference.asset_path, true, applied)? {
                    return Ok(true);
                }
                let mut keys: Vec<_> = reference.custom_data.keys().cloned().collect();
                keys.sort();
                for key in keys {
                    if let Some(entry) = reference.custom_data.get_mut(&key) {
                        walk.value(entry)?;
                    }
                }
                Ok(false)
            })?,
            Value::PayloadListOp(op) => self.list_op(op, |walk, payload, applied| {
                walk.path(&mut payload.asset_path, true, applied)
            })?,
            Value::Payload(payload) => {
                self.path(&mut payload.asset_path, true, true)?;
            }
            _ => {}
        }
        Ok(())
    }

    /// Visits each clip set's template path, which C++ expands into clip
    /// paths, or refuses it when strict.
    fn clip_templates(&mut self, clips: &mut Value) -> Result<()> {
        let Value::Dictionary(sets) = clips else {
            return Ok(());
        };
        let mut names: Vec<_> = sets.keys().cloned().collect();
        names.sort();
        for name in names {
            if let Some(Value::Dictionary(set)) = sets.get_mut(&name)
                && let Some(Value::String(template)) = set.get_mut(keys::TEMPLATE_ASSET_PATH)
            {
                if self.mode.strict {
                    return Err(self.unsupported("clip template", template));
                }
                self.path(template, true, true)?;
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

    const MODIFY: &str = r#"#usda 1.0
(
    customLayerData = {
        asset icon = @./meta.png@
    }
    subLayers = [
        @./a.usda@ (offset = 1),
        @./drop.usda@ (offset = 2),
        @./b.usda@ (offset = 3)
    ]
)

def "A" (
    delete references = @./deleted.usda@
    prepend references = [@./ref.usda@</A>, @./drop.usda@</A>]
    prepend payload = @./pay.usda@</P>
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/A"
            string templateAssetPath = "./clip.#.usda"
        }
    }
)
{
    asset expression = @`"./${X}.png"`@
    asset sampled.timeSamples = {
        1: @./sample.png@,
    }
    asset single = @./drop.png@
    asset[] textures = [@./tex.png@, @./drop.png@]
}

def "I" (
    prepend references = </A>
)
{
}
"#;

    /// The paths C++ 25.05 hands `UsdUtils.ModifyAssetPaths` on the same
    /// layer, and the layer it leaves when the callback empties the `drop`
    /// paths and moves the rest, except that the remaining sublayers keep
    /// their offsets.
    #[test]
    fn modify_asset_paths_matches_cpp() -> Result<()> {
        for keep_empty in [false, true] {
            let mut layer = sdf::Layer::from_bytes("modify.usda", MODIFY.as_bytes().to_vec())?;
            let mut seen = Vec::new();
            let modify = |path: &str| {
                seen.push(path.to_owned());
                if path.contains("drop") {
                    String::new()
                } else {
                    path.replacen("./", "./moved/", 1)
                }
            };
            modify_asset_paths(&mut layer, modify, keep_empty)?;
            seen.sort();
            assert_eq!(
                seen,
                [
                    "./a.usda",
                    "./b.usda",
                    "./clip.#.usda",
                    "./clip.usda",
                    "./deleted.usda",
                    "./drop.png",
                    "./drop.usda",
                    "./manifest.usda",
                    "./meta.png",
                    "./pay.usda",
                    "./ref.usda",
                    "./sample.png",
                    "./tex.png",
                    "`\"./${X}.png\"`",
                ]
            );

            let text = layer.export_to_string()?;
            for path in [
                "@./moved/a.usda@ (offset = 1.0",
                "@./moved/b.usda@ (offset = 3.0",
                "@./moved/meta.png@",
                "@./moved/clip.usda@",
                "@./moved/manifest.usda@",
                "\"./moved/clip.#.usda\"",
                "delete references = @./moved/deleted.usda@",
                "prepend references = @./moved/ref.usda@</A>",
                "prepend payload = @./moved/pay.usda@</P>",
                "@./moved/sample.png@",
                "@`\"./moved/${X}.png\"`@",
                "prepend references = </A>",
            ] {
                assert!(text.contains(path), "{path} in {text}");
            }
            assert!(!text.contains("drop"), "{text}");
            assert!(!text.contains("asset single ="), "{text}");
            let textures = if keep_empty {
                "[@./moved/tex.png@, @@]"
            } else {
                "[@./moved/tex.png@]"
            };
            assert!(text.contains(textures), "{text}");
        }
        Ok(())
    }
}
