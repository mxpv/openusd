//! Dependency discovery (C++ `UsdUtilsComputeAllDependencies`): the walk from
//! a root layer over every file it reaches.

use std::collections::{BTreeSet, HashMap, VecDeque};
use std::ops::Deref;

use super::walk::{AssetKind, Visit, visit_asset_paths};
use crate::sdf;
use crate::usd::Stage;
use crate::{Error, Result, ar, pcp};

/// The layers and assets a layer depends on, as C++
/// `UsdUtilsComputeAllDependencies` reports them.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Dependencies {
    /// The layers reached through sublayers, references, payloads and
    /// layer-valued asset paths, by identifier: the root first, the rest
    /// sorted.
    pub layers: Vec<String>,
    /// The other assets the layers name, by resolved path, sorted.
    pub assets: Vec<String>,
    /// The asset paths that did not resolve, anchored to the layer authoring
    /// them, sorted.
    pub unresolved: Vec<String>,
}

/// Computes every layer and asset `asset_path` depends on through `stage`'s
/// resolver, as C++ `UsdUtilsComputeAllDependencies` does through the global
/// one.
///
/// Every variant is followed, not only the selected one, and deleted reference
/// and payload items are left out, as is the `assetInfo:identifier` of a prim,
/// which names the asset itself. A layer `stage` already holds is read as it
/// is in memory, unsaved edits included, as C++ reads a layer already open in
/// its layer registry; any other is read through the resolver without joining
/// the stage. A package is opened at its default layer and followed like any
/// layer. The layers and assets inside it are reported by their
/// package-relative path.
///
/// UDIM patterns and clip templates, which C++ expands by listing the
/// filesystem, and variable expressions, which C++ anchors unevaluated and
/// reports unresolved, return [`DependencyError`](super::DependencyError).
pub fn compute_all_dependencies(stage: &Stage, asset_path: &str) -> Result<Dependencies> {
    let graph = stage.layers();
    let policy = Discover {
        inactive: false,
        open_packages: true,
    };
    let discovery = discover(&graph, asset_path, policy)?;
    let mut dependencies = Dependencies::default();
    for source in &discovery.sources {
        match &source.content {
            Content::Layer { .. } | Content::Package { .. } => dependencies.layers.push(source.identifier.clone()),
            Content::Asset(resolved) => dependencies.assets.push(resolved.to_string()),
        }
    }
    dependencies.unresolved = discovery
        .unresolved
        .into_iter()
        .map(|(identifier, _)| identifier)
        .collect();
    dependencies.layers[1..].sort();
    dependencies.assets.sort();
    dependencies.unresolved.sort();
    Ok(dependencies)
}

/// What [`discover`] does with the paths it meets, beyond the walk's own
/// choices in [`Visit::DISCOVER`].
#[derive(Clone, Copy)]
pub(super) struct Discover {
    /// Record the targets of deleted and reordered list-op items too: they
    /// add no opinion, but a delete must still find its target once both are
    /// packaged.
    pub inactive: bool,
    /// Open a package at its default layer and follow what it authors, as C++
    /// `SdfLayer::FindOrOpen` does with one. Off, a package is taken whole,
    /// with the layers the stage holds inside it walked in their own scope.
    pub open_packages: bool,
}

/// Every file reachable from the roots of one scope, in the order found: the
/// scope of a root layer, or of a package, whose scope holds the layers the
/// stage has inside it and what they reach outside it.
pub(super) struct Discovery<'a> {
    /// The files found, the roots first; a layer's uses index into here.
    pub sources: Vec<Source<'a>>,
    /// The identifiers that did not resolve, each once, with what it was
    /// taken for; a package's scope reports into its enclosing one too.
    pub unresolved: Vec<(String, AssetKind)>,
}

/// A file [`discover`] reached, by canonical identifier.
pub(super) struct Source<'a> {
    pub identifier: String,
    pub placement: Placement,
    pub content: Content<'a>,
}

/// Where a [`Source`] goes in its package.
pub(super) enum Placement {
    /// The root layer, at the name the package is given.
    Root,
    /// An existing entry of a package the stage holds a layer in, at its own
    /// name.
    Entry(String),
    /// A file the layer source `by` named as `path` (the package's own path
    /// for a path into a package), placed where that path leads when it can
    /// be.
    Named { by: usize, path: String },
}

/// What a [`Source`] holds.
pub(super) enum Content<'a> {
    /// A layer, with what each path it authors names, by authored path. A
    /// path that did not resolve has no entry.
    Layer {
        layer: SourceLayer<'a>,
        uses: HashMap<String, Use>,
    },
    /// A package taken whole, at its location, with its own scope: the layers
    /// the stage holds inside it and what they reach outside it, empty when
    /// it holds none.
    Package {
        resolved: ar::ResolvedPath,
        inside: Discovery<'a>,
    },
    /// Any other file, at its location.
    Asset(ar::ResolvedPath),
}

/// What a path a layer authors names, as its [`Content::Layer`] records it.
pub(super) struct Use {
    /// The source the path names.
    pub source: usize,
    /// For a path into a package that names the source as that package, the
    /// path inside it, which a rewrite keeps.
    pub packaged: Option<String>,
}

impl Content<'_> {
    /// Where the source was found, or `None` for a layer that was never read
    /// from anywhere.
    pub(super) fn location(&self) -> Option<&str> {
        match self {
            Self::Layer { layer, .. } => layer.resolved_path(),
            Self::Package { resolved, .. } | Self::Asset(resolved) => resolved.to_str(),
        }
    }

    /// The location the paths a layer source authors are anchored to.
    fn anchor(&self) -> Option<ar::ResolvedPath> {
        match self {
            Self::Layer { layer, .. } => layer.anchor_location(),
            Self::Package { .. } | Self::Asset(_) => None,
        }
    }
}

/// Walks from the root layer `asset_path` names over every file it reaches
/// through `graph`'s resolver, breadth first, visiting each layer once. A
/// layer `graph` holds is walked as it is in memory; any other is read
/// through the resolver. The root failing to resolve is an error; any other
/// file failing to is recorded.
pub(super) fn discover<'a>(graph: &'a pcp::LayerGraph, asset_path: &str, policy: Discover) -> Result<Discovery<'a>> {
    // One cache scope spans the discovery. Each package it reads into is
    // opened once.
    let _scope = ar::CacheScope::begin();
    let identifier = root_identifier(graph, asset_path);
    let Some(layer) = SourceLayer::open(graph, &identifier)? else {
        return Err(Error::UnresolvedAsset(asset_path.to_owned()));
    };
    let root = Source {
        identifier,
        placement: Placement::Root,
        content: Content::Layer {
            layer,
            uses: HashMap::new(),
        },
    };
    discover_scope(graph, policy, vec![root], None, Vec::new())
}

/// The identifier of the root layer `asset_path` names: a layer `graph`
/// holds under that exact identifier, otherwise the canonical identifier.
fn root_identifier(graph: &pcp::LayerGraph, asset_path: &str) -> String {
    if graph.id_of(asset_path).is_some() {
        return asset_path.to_owned();
    }
    graph.layer_registry().create_identifier(asset_path, None)
}

/// Walks from `roots` over every file they reach, breadth first. In the scope
/// of `package`, a path leading back inside it names an entry already in
/// place and is left as authored. `unresolved` seeds what the scope reports,
/// with what the scopes nested in its roots found.
fn discover_scope<'a>(
    graph: &'a pcp::LayerGraph,
    policy: Discover,
    roots: Vec<Source<'a>>,
    package: Option<String>,
    unresolved: Vec<(String, AssetKind)>,
) -> Result<Discovery<'a>> {
    let mut discoverer = Discoverer {
        graph,
        policy,
        package: package.map(|package| {
            let prefix = format!("{}[", package.trim_end_matches(']'));
            (package, prefix)
        }),
        index: roots
            .iter()
            .enumerate()
            .map(|(index, root)| (root.identifier.clone(), index))
            .collect(),
        sources: roots,
        unresolved,
    };
    let mut queue: VecDeque<usize> = (0..discoverer.sources.len())
        .filter(|&index| discoverer.sources[index].is_layer())
        .collect();
    // TODO(rayon): the layers queued at one level open independently of each
    // other; open them in parallel and visit them in queue order.
    while let Some(current) = queue.pop_front() {
        for (path, kind) in discoverer.authored_in(current)? {
            if let Some(found) = discoverer.find_or_add(current, &path, kind)? {
                if found.source == discoverer.sources.len() - 1 && discoverer.sources[found.source].is_layer() {
                    queue.push_back(found.source);
                }
                discoverer.uses_of(current).insert(path, found);
            }
        }
    }
    Ok(Discovery {
        sources: discoverer.sources,
        unresolved: discoverer.unresolved,
    })
}

/// The scope of the package at `package`: the layers `graph` holds directly
/// inside it, at their entries, and the packages nested in it that hold such
/// layers deeper down, each with its own scope; then what those layers reach
/// outside the package. Empty when the stage holds no layer inside it.
fn discover_inside<'a>(graph: &'a pcp::LayerGraph, policy: Discover, package: &str) -> Result<Discovery<'a>> {
    let prefix = format!("{}[", package.trim_end_matches(']'));
    let mut roots = Vec::new();
    let mut nested = BTreeSet::new();
    for &id in graph.all_ids() {
        let layer = graph.layer(id);
        let Some(rest) = layer.resolved_path().and_then(|real| real.strip_prefix(&prefix)) else {
            continue;
        };
        let entry = rest.trim_end_matches(']');
        match entry.split_once('[') {
            Some((package, _)) => {
                nested.insert(package.to_owned());
            }
            None => roots.push(Source {
                identifier: layer.identifier().to_owned(),
                placement: Placement::Entry(entry.to_owned()),
                content: Content::Layer {
                    layer: SourceLayer::Live(layer),
                    uses: HashMap::new(),
                },
            }),
        }
    }
    // What a nested scope could not resolve is this scope's to report too.
    let mut unresolved = Vec::new();
    for name in nested {
        let identifier = ar::nest_packaged_path(package, &name);
        let inside = discover_inside(graph, policy, &identifier)?;
        unresolved.extend(inside.unresolved.iter().cloned());
        roots.push(Source {
            placement: Placement::Entry(name),
            content: Content::Package {
                resolved: ar::ResolvedPath::new(&identifier),
                inside,
            },
            identifier,
        });
    }
    if roots.is_empty() {
        return Ok(Discovery {
            sources: Vec::new(),
            unresolved,
        });
    }
    discover_scope(graph, policy, roots, Some(package.to_owned()), unresolved)
}

/// The state of one [`discover_scope`] walk.
struct Discoverer<'a> {
    graph: &'a pcp::LayerGraph,
    policy: Discover,
    /// The scope's package, with the prefix of every identifier inside it.
    package: Option<(String, String)>,
    /// The source index of each identifier found.
    index: HashMap<String, usize>,
    sources: Vec<Source<'a>>,
    unresolved: Vec<(String, AssetKind)>,
}

impl<'a> Discoverer<'a> {
    /// The paths the layer source `current` authors, each once, with what it
    /// names: every path, or only the ones that add an opinion.
    fn authored_in(&self, current: usize) -> Result<Vec<(String, AssetKind)>> {
        let Content::Layer { layer, uses } = &self.sources[current].content else {
            return Ok(Vec::new());
        };
        let mut found = Vec::new();
        visit_asset_paths(layer.data(), layer.identifier(), Visit::DISCOVER, |asset| {
            if (asset.applied || self.policy.inactive)
                && !uses.contains_key(asset.path)
                && !found.iter().any(|(path, _)| path == asset.path)
            {
                found.push((asset.path.to_owned(), asset.kind));
            }
            Ok(None)
        })?;
        Ok(found)
    }

    /// The uses of the layer source `current`.
    fn uses_of(&mut self, current: usize) -> &mut HashMap<String, Use> {
        match &mut self.sources[current].content {
            Content::Layer { uses, .. } => uses,
            Content::Package { .. } | Content::Asset(_) => unreachable!("only a layer is walked"),
        }
    }

    /// What `path`, authored in the layer source `referrer` as `kind`, names:
    /// a source already found, or one added now; `None` when it does not
    /// resolve, which is recorded. A path into a package names the package
    /// once the whole path resolves, unless packages are opened as layers. A
    /// path leading back inside the scope's package names the entry there,
    /// in place already.
    fn find_or_add(&mut self, referrer: usize, path: &str, kind: AssetKind) -> Result<Option<Use>> {
        let registry = self.graph.layer_registry();
        let anchor = self.sources[referrer].content.anchor();
        let target = registry.create_identifier(path, anchor.as_ref());
        if let Some((package, prefix)) = &self.package
            && let Some(rest) = target.strip_prefix(prefix.as_str())
        {
            // The first packaged part names the entry, deeper ones a path
            // into a package nested there.
            let rest = rest.trim_end_matches(']');
            let (name, packaged) = match rest.split_once('[') {
                Some((name, deeper)) => (name, Some(deeper.to_owned())),
                None => (rest, None),
            };
            let identifier = ar::nest_packaged_path(package, name);
            if let Some(&index) = self.index.get(&identifier) {
                return Ok(Some(Use {
                    source: index,
                    packaged,
                }));
            }
            let Some(resolved) = registry.resolve(&target) else {
                self.record_unresolved(target, kind);
                return Ok(None);
            };
            // An entry the stage holds no layer in, copied as it is; a package
            // nested there has nothing live inside it.
            let content = if packaged.is_some() || AssetKind::of(name, false) == AssetKind::Package {
                Content::Package {
                    resolved: ar::ResolvedPath::new(&identifier),
                    inside: Discovery {
                        sources: Vec::new(),
                        unresolved: Vec::new(),
                    },
                }
            } else {
                Content::Asset(resolved)
            };
            let index = self.sources.len();
            self.index.insert(identifier.clone(), index);
            self.sources.push(Source {
                identifier,
                placement: Placement::Entry(name.to_owned()),
                content,
            });
            return Ok(Some(Use {
                source: index,
                packaged,
            }));
        }
        let (identifier, to_source, kind, packaged) = match ar::split_package_relative_path_outer(path) {
            Some((package, inner)) if !self.policy.open_packages => {
                if registry.resolve(&target).is_none() {
                    self.record_unresolved(target, kind);
                    return Ok(None);
                }
                (
                    registry.create_identifier(&package, anchor.as_ref()),
                    package,
                    AssetKind::Package,
                    Some(inner),
                )
            }
            _ if self.policy.open_packages && kind == AssetKind::Package => {
                (target, path.to_owned(), AssetKind::Layer, None)
            }
            _ => (target, path.to_owned(), kind, None),
        };
        if let Some(&index) = self.index.get(&identifier) {
            return Ok(Some(Use {
                source: index,
                packaged,
            }));
        }
        let content = match kind {
            AssetKind::Layer => {
                let Some(layer) = SourceLayer::open(self.graph, &identifier)? else {
                    self.record_unresolved(identifier, kind);
                    return Ok(None);
                };
                Content::Layer {
                    layer,
                    uses: HashMap::new(),
                }
            }
            AssetKind::Package | AssetKind::Asset => {
                let Some(resolved) = registry.resolve(&identifier) else {
                    self.record_unresolved(identifier, kind);
                    return Ok(None);
                };
                if kind == AssetKind::Package {
                    let inside = discover_inside(self.graph, self.policy, &identifier)?;
                    for (unresolved, kind) in &inside.unresolved {
                        self.record_unresolved(unresolved.clone(), *kind);
                    }
                    Content::Package { resolved, inside }
                } else {
                    Content::Asset(resolved)
                }
            }
        };
        let index = self.sources.len();
        self.index.insert(identifier.clone(), index);
        self.sources.push(Source {
            identifier,
            placement: Placement::Named {
                by: referrer,
                path: to_source,
            },
            content,
        });
        Ok(Some(Use {
            source: index,
            packaged,
        }))
    }

    fn record_unresolved(&mut self, identifier: String, kind: AssetKind) {
        if !self.unresolved.iter().any(|(found, _)| *found == identifier) {
            self.unresolved.push((identifier, kind));
        }
    }
}

impl Source<'_> {
    fn is_layer(&self) -> bool {
        matches!(self.content, Content::Layer { .. })
    }
}

/// A layer read for the dependency walk: one the stage holds, or one read
/// through its resolver.
///
/// TODO: a ref-counted `LayerRegistry::find_or_open` (C++
/// `SdfLayer::FindOrOpen`) would serve both cases and let a layer read here be
/// read once across walks; this lookup stands in until it exists.
pub(super) enum SourceLayer<'a> {
    Live(&'a sdf::Layer),
    Read(sdf::Layer),
}

impl<'a> SourceLayer<'a> {
    /// The layer at `identifier`, or `None` when it does not resolve.
    fn open(graph: &'a pcp::LayerGraph, identifier: &str) -> Result<Option<Self>> {
        if let Some(id) = graph.id_of(identifier) {
            return Ok(Some(Self::Live(graph.layer(id))));
        }
        Ok(graph.layer_registry().open_layer(identifier)?.map(Self::Read))
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

#[cfg(test)]
pub(crate) mod tests {
    use std::fs;
    use std::path::{MAIN_SEPARATOR, Path};

    use super::*;
    use crate::sdf::{FieldKey, Value};
    use crate::usd_utils::{DependencyError, modify_asset_paths};
    use crate::usdz::ArchiveWriter;

    /// Writes `contents` to `path` under `dir`, creating its directories.
    pub(crate) fn write(dir: &Path, path: &str, contents: &str) {
        let path = dir.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    /// Opens a stage on the file at `path` under `dir`, returning the root's
    /// path with it.
    pub(crate) fn open(dir: &Path, path: &str) -> Result<(String, Stage)> {
        let root = dir.join(path).to_str().unwrap().to_owned();
        let stage = Stage::open(&root)?;
        Ok((root, stage))
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

    /// The scene `dependencies_match_cpp` walks: every kind of dependency, a
    /// missing layer and texture, a layer outside the root's directory and a
    /// package.
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
        let base = format!("{}{}", fs::canonicalize(dir).unwrap().display(), MAIN_SEPARATOR);
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
    fn dependencies_match_cpp() -> Result<()> {
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
        let (_, stage) = open(dir.path(), "root.usda")?;
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

    /// A prim's `assetInfo:identifier` names the asset itself. The walk skips
    /// it while the rest of the `assetInfo` is followed; a rewrite still
    /// visits it.
    #[test]
    fn asset_info_identifier_skipped() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    assetInfo = {\n        asset identifier = @./nowhere.usda@\n        asset icon = @./missing.png@\n    }\n)\n{\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        let dependencies = compute_all_dependencies(&stage, &root)?;
        assert_eq!(relative(dir.path(), &dependencies.layers), ["root.usda"]);
        assert_eq!(relative(dir.path(), &dependencies.unresolved), ["missing.png"]);

        let mut seen = Vec::new();
        modify_asset_paths(
            &mut stage.layer_mut(&dependencies.layers[0]).unwrap(),
            |path| {
                seen.push(path.to_owned());
                path.to_owned()
            },
            true,
        )?;
        seen.sort();
        assert_eq!(seen, ["./missing.png", "./nowhere.usda"]);
        Ok(())
    }

    /// A deleted item adds no dependency. An expression in one is left alone.
    #[test]
    fn deleted_expression_ignored() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    delete references = @`\"./${NAME}.usda\"`@\n)\n{\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        let dependencies = compute_all_dependencies(&stage, &root)?;
        assert_eq!(relative(dir.path(), &dependencies.layers), ["root.usda"]);
        assert!(dependencies.unresolved.is_empty(), "{:?}", dependencies.unresolved);
        Ok(())
    }

    /// A deleted reference adds no dependency, its metadata included: an
    /// expression in its `customData` is neither reported nor refused.
    #[test]
    fn deleted_reference_metadata_ignored() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    delete references = @./gone.usda@ (\n        customData = {\n            asset icon = @`\"./${X}.png\"`@\n        }\n    )\n)\n{\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        let dependencies = compute_all_dependencies(&stage, &root)?;
        assert!(dependencies.assets.is_empty(), "{:?}", dependencies.assets);
        assert!(dependencies.unresolved.is_empty(), "{:?}", dependencies.unresolved);
        Ok(())
    }

    /// An empty clip template, which C++ skips, is not refused.
    #[test]
    fn empty_clip_template_allowed() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    clips = {\n        dictionary default = {\n            string templateAssetPath = \"\"\n        }\n    }\n)\n{\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        assert_eq!(compute_all_dependencies(&stage, &root)?.layers.len(), 1);
        Ok(())
    }

    /// Paths that need expanding or evaluating before they can be followed
    /// are refused, naming the path.
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
            let (root, stage) = open(dir.path(), "root.usda")?;
            let error = compute_all_dependencies(&stage, &root).unwrap_err();
            assert!(
                matches!(&error, Error::Dependency(DependencyError::Unsupported { kind: k, .. }) if *k == kind),
                "{error}"
            );
        }
        Ok(())
    }
}
