//! USDZ packaging (C++ `UsdUtilsCreateNewUsdzPackage`).

use std::collections::{HashMap, VecDeque};
use std::io::Cursor;
use std::path::Path;

use super::dependencies::{AssetRef, SourceLayer, Visit, root_identifier, visit_asset_paths};
use crate::sdf::{self, AbstractData};
use crate::usd::Stage;
use crate::{Error, Result, ar, pcp, usdz};

/// Writes the layer at `asset_path` and everything it depends on into a new
/// USDZ package at `usdz_file_path`, as C++ `UsdUtilsCreateNewUsdzPackage`
/// does. Returns the layer dependencies that did not resolve and were left
/// out, as C++ warns about them.
///
/// The dependencies are the ones [`compute_all_dependencies`] walks, plus
/// deleted reference and payload items, so a delete still matches its target
/// once both are packaged. Layers keep their file format and are read as
/// [`compute_all_dependencies`] reads them, unsaved edits included.
///
/// The root layer is the package's first entry, named `first_layer_name` or
/// the root's file name. A dependency authored as a `./` or `../` path that
/// stays inside the package keeps its path and its place relative to the root.
/// Any other (an absolute path, a search path, or one leading out of the
/// package) moves into a numbered directory per source directory (`0/`, `1/`,
/// ...) and its authored path is rewritten to reach it. A `.usdz` dependency
/// is stored whole, as a package nested in the new one.
///
/// A missing non-layer asset fails the package, as in C++.
///
/// [`compute_all_dependencies`]: super::compute_all_dependencies
pub fn create_new_usdz_package(
    stage: &Stage,
    asset_path: &str,
    usdz_file_path: impl AsRef<Path>,
    first_layer_name: Option<&str>,
) -> Result<Vec<String>> {
    let graph = stage.layers();
    let root = root_identifier(&graph, asset_path);
    let unresolved = || Error::UnresolvedAsset(asset_path.to_owned());
    let layer = SourceLayer::open(&graph, &root)?.ok_or_else(unresolved)?;
    let name = match first_layer_name {
        Some(name) => name.to_owned(),
        None => file_name(layer.resolved_path().ok_or_else(unresolved)?),
    };
    let mut package = Package {
        graph: &graph,
        entries: vec![(name.clone(), Vec::new())],
        owners: HashMap::from([(name.clone(), root.clone())]),
        placed: HashMap::from([(root, name)]),
        directories: HashMap::new(),
        pending: VecDeque::new(),
        skipped: Vec::new(),
    };
    package.write_layer(0, &layer)?;
    while let Some((index, identifier)) = package.pending.pop_front() {
        let layer = SourceLayer::open(&graph, &identifier)?.ok_or(Error::UnresolvedAsset(identifier))?;
        package.write_layer(index, &layer)?;
    }

    let mut archive = usdz::ArchiveWriter::create(usdz_file_path)?;
    for (name, bytes) in &package.entries {
        archive.add_layer(name, bytes)?;
    }
    archive.finish()?;
    Ok(package.skipped)
}

/// How a dependency is stored.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// Serialized from its layer, with its own dependencies followed.
    Layer,
    /// Copied as it is.
    Asset,
    /// A package, copied as it is.
    Package,
}

/// The package being built.
struct Package<'a> {
    graph: &'a pcp::LayerGraph,
    /// Entry names and contents, in archive order.
    entries: Vec<(String, Vec<u8>)>,
    /// The source identifier each entry holds.
    owners: HashMap<String, String>,
    /// The entry each source identifier was first placed at.
    placed: HashMap<String, String>,
    /// The numbered directory each source directory moves into.
    directories: HashMap<String, usize>,
    /// Layer entries whose contents are still to be written.
    pending: VecDeque<(usize, String)>,
    skipped: Vec<String>,
}

impl Package<'_> {
    /// Writes `layer` as entry `index`, placing its dependencies and rewriting
    /// the paths of the ones that move.
    fn write_layer(&mut self, index: usize, layer: &sdf::Layer) -> Result<()> {
        let anchor = layer.anchor_location();
        let location = self.entries[index].0.clone();
        let edits = visit_asset_paths(layer.data(), layer.identifier(), Visit::STRICT, |asset| {
            self.place(&asset, anchor.as_ref(), &location)
        })?;
        let bytes = if edits.is_empty() {
            serialize(layer.data(), &location)?
        } else {
            let mut data = sdf::Data::from_abstract(layer.data())?;
            for (path, field, value) in edits {
                match value {
                    Some(value) => data.set_field(&path, &field, value),
                    None => data.erase_field(&path, &field),
                }
            }
            serialize(&data, &location)?
        };
        self.entries[index].1 = bytes;
        Ok(())
    }

    /// Places the dependency `asset` names from the layer stored at
    /// `location`, returning its rewritten path when it moves. A path into a
    /// package (`inner.usdz[layer.usda]`) places the package whole.
    fn place(
        &mut self,
        asset: &AssetRef<'_>,
        anchor: Option<&ar::ResolvedPath>,
        location: &str,
    ) -> Result<Option<String>> {
        if let Some((package, inner)) = ar::split_package_relative_path_outer(asset.path) {
            let moved = self.place_file(&package, Kind::Package, anchor, location)?;
            return Ok(moved.map(|package| ar::join_package_relative_path(&package, &inner)));
        }
        let kind = if has_extension(asset.path, "usdz") {
            Kind::Package
        } else if asset.layer {
            Kind::Layer
        } else {
            Kind::Asset
        };
        self.place_file(asset.path, kind, anchor, location)
    }

    fn place_file(
        &mut self,
        path: &str,
        kind: Kind,
        anchor: Option<&ar::ResolvedPath>,
        location: &str,
    ) -> Result<Option<String>> {
        let registry = self.graph.layer_registry();
        let source = registry.create_identifier(path, anchor);
        let resolved = registry.resolve(&source);
        if !self.placed.contains_key(&source) {
            let live = kind == Kind::Layer && self.graph.id_of(&source).is_some();
            if resolved.is_none() && !live {
                if kind == Kind::Asset {
                    return Err(Error::UnresolvedAsset(source));
                }
                if !self.skipped.contains(&source) {
                    self.skipped.push(source);
                }
                return Ok(None);
            }
        }

        let kept = kept_entry(location, path);
        let entry = match kept
            .as_ref()
            .filter(|entry| self.owners.get(*entry).is_none_or(|owner| *owner == source))
        {
            Some(entry) => entry.clone(),
            None => match self.placed.get(&source) {
                Some(entry) => entry.clone(),
                None => self.moved_entry(&source),
            },
        };
        if !self.owners.contains_key(&entry) {
            self.owners.insert(entry.clone(), source.clone());
            self.placed.entry(source.clone()).or_insert_with(|| entry.clone());
            let index = self.entries.len();
            let bytes = match (kind, &resolved) {
                (Kind::Asset | Kind::Package, Some(resolved)) => registry.open_asset(resolved)?.read_all()?,
                _ => Vec::new(),
            };
            self.entries.push((entry.clone(), bytes));
            if kind == Kind::Layer {
                self.pending.push_back((index, source));
            }
        }
        Ok((kept.as_ref() != Some(&entry)).then(|| path_to(location, &entry)))
    }

    /// The entry a moved source takes: its file name in the numbered
    /// directory of its source directory.
    fn moved_entry(&mut self, source: &str) -> String {
        let (directory, name) = if let Some((package, inner)) = ar::split_package_relative_path_inner(source) {
            let (directory, name) = inner.rsplit_once('/').unwrap_or(("", &inner));
            (format!("{package}[{directory}"), name.to_owned())
        } else {
            let (directory, name) = source.rsplit_once(['/', '\\']).unwrap_or(("", source));
            (directory.to_owned(), name.to_owned())
        };
        let next = self.directories.len();
        let mut number = *self.directories.entry(directory).or_insert(next);
        let mut entry = format!("{number}/{name}");
        while self.owners.contains_key(&entry) {
            number += 1;
            entry = format!("{number}/{name}");
        }
        entry
    }
}

/// The entry a `./` or `../` path authored in the layer at `location` reaches,
/// or `None` for any other path or one leading out of the package.
fn kept_entry(location: &str, path: &str) -> Option<String> {
    if !path.starts_with("./") && !path.starts_with("../") {
        return None;
    }
    let mut parts: Vec<&str> = location.split('/').collect();
    parts.pop();
    for part in path.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                parts.pop()?;
            }
            part => parts.push(part),
        }
    }
    Some(parts.join("/"))
}

/// The path from the layer at `location` to `entry`.
fn path_to(location: &str, entry: &str) -> String {
    format!("{}{entry}", "../".repeat(location.matches('/').count()))
}

/// The file name of `path`, inside its innermost package bracket.
fn file_name(path: &str) -> String {
    let inner = ar::split_package_relative_path_inner(path).map_or_else(|| path.to_owned(), |(_, inner)| inner);
    inner.rsplit(['/', '\\']).next().unwrap_or_default().to_owned()
}

fn has_extension(path: &str, extension: &str) -> bool {
    Path::new(path)
        .extension()
        .is_some_and(|found| found.eq_ignore_ascii_case(extension))
}

/// Serializes `data` in the format the extension of `location` names.
fn serialize(data: &dyn AbstractData, location: &str) -> Result<Vec<u8>> {
    let extension = Path::new(location)
        .extension()
        .and_then(|extension| extension.to_str())
        .unwrap_or_default();
    let format = sdf::LayerRegistry::find_by_extension(extension)
        .filter(|format| format.caps().can_write())
        .ok_or_else(|| Error::UnsupportedFormat(location.to_owned()))?;
    let mut bytes = Cursor::new(Vec::new());
    format.write(data, &mut bytes)?;
    Ok(bytes.into_inner())
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::io::Read;

    use super::*;
    use crate::usd::TimeCode;
    use crate::usdz::ArchiveWriter;

    fn write(dir: &Path, path: &str, contents: &str) {
        let path = dir.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    /// The archive's entry names in order, and the text of its `.usda` entries.
    fn entries(path: &Path) -> (Vec<String>, HashMap<String, String>) {
        let mut archive = zip::ZipArchive::new(fs::File::open(path).unwrap()).unwrap();
        let mut names = Vec::new();
        let mut texts = HashMap::new();
        for index in 0..archive.len() {
            let mut entry = archive.by_index(index).unwrap();
            let name = entry.name().to_owned();
            if name.ends_with(".usda") {
                let mut text = String::new();
                entry.read_to_string(&mut text).unwrap();
                texts.insert(name.clone(), text);
            }
            names.push(name);
        }
        (names, texts)
    }

    fn probe(stage: &Stage, attr: &str) -> Option<sdf::Value> {
        stage.attribute(attr).unwrap().get_at(TimeCode::new(0.0)).unwrap()
    }

    const ROOT: &str = r#"#usda 1.0
(
    subLayers = [@./layers/s.usda@]
)

def "A" (
    prepend references = @./sub/a.usda@</A>
)
{
}

def "B" (
    prepend references = @../outside/b.usda@</B>
)
{
}

def "C" (
    prepend references = @c.usda@</C>
)
{
}

def "M" (
    prepend references = @./missing.usda@
)
{
}

def "N" (
    prepend references = @../pk/inner.usdz[second.usda]@</Second>
)
{
}

def "T"
{
    asset tex = @./tex/t.png@
}
"#;

    /// The layout C++ gives the same scene, with the paths a layer in a
    /// subdirectory authors made to reach their moved entries: C++ 25.05
    /// writes `0/d.usda` in `sub/a.usda`, which resolves to `sub/0/d.usda`.
    #[test]
    fn packages_dependencies_as_cpp_lays_them_out() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let base = dir.path();
        write(base, "scene/root.usda", ROOT);
        write(
            base,
            "scene/layers/s.usda",
            "#usda 1.0\ndef \"S\" {\n    int probe = 1\n}\n",
        );
        write(
            base,
            "scene/sub/a.usda",
            "#usda 1.0\ndef \"A\" (\n    prepend references = @../../outside/d.usda@</D>\n)\n{\n    asset up = @../tex/t.png@\n}\n",
        );
        write(
            base,
            "outside/b.usda",
            "#usda 1.0\ndef \"B\" {\n    asset t = @../scene/tex/t.png@\n    int probe = 3\n}\n",
        );
        write(base, "outside/d.usda", "#usda 1.0\ndef \"D\" {\n    int probe = 4\n}\n");
        write(base, "scene/c.usda", "#usda 1.0\ndef \"C\" {\n    int probe = 5\n}\n");
        write(base, "scene/tex/t.png", "PNG");
        fs::create_dir_all(base.join("pk"))?;
        let mut inner = ArchiveWriter::create(base.join("pk/inner.usdz"))?;
        inner.add_layer("inner.usda", b"#usda 1.0\ndef \"Inner\" {\n}\n")?;
        inner.add_layer("second.usda", b"#usda 1.0\ndef \"Second\" {\n    int probe = 6\n}\n")?;
        inner.finish()?;

        let root = base.join("scene/root.usda").to_str().unwrap().to_owned();
        let stage = Stage::open(&root)?;
        let output = base.join("out.usdz");
        let skipped = create_new_usdz_package(&stage, &root, &output, None)?;
        assert_eq!(skipped.len(), 1);
        assert!(Path::new(&skipped[0]).ends_with("scene/missing.usda"));

        let (names, texts) = entries(&output);
        assert_eq!(
            names,
            [
                "root.usda",
                "layers/s.usda",
                "sub/a.usda",
                "0/b.usda",
                "1/c.usda",
                "2/inner.usdz",
                "tex/t.png",
                "0/d.usda",
                "scene/tex/t.png",
            ]
        );
        let root_text = &texts["root.usda"];
        for path in [
            "@./layers/s.usda@",
            "@./sub/a.usda@",
            "@0/b.usda@",
            "@1/c.usda@",
            "@./missing.usda@",
            "@2/inner.usdz[second.usda]@",
            "@./tex/t.png@",
        ] {
            assert!(root_text.contains(path), "{path} in {root_text}");
        }
        assert!(texts["sub/a.usda"].contains("@../0/d.usda@"));
        assert!(texts["sub/a.usda"].contains("@../tex/t.png@"));
        assert!(texts["0/b.usda"].contains("@../scene/tex/t.png@"));

        let packaged = Stage::open(output.to_str().unwrap())?;
        assert_eq!(probe(&packaged, "/S.probe"), Some(sdf::Value::Int(1)));
        assert_eq!(probe(&packaged, "/A.probe"), Some(sdf::Value::Int(4)));
        assert_eq!(probe(&packaged, "/B.probe"), Some(sdf::Value::Int(3)));
        assert_eq!(probe(&packaged, "/C.probe"), Some(sdf::Value::Int(5)));
        assert_eq!(probe(&packaged, "/N.probe"), Some(sdf::Value::Int(6)));
        Ok(())
    }

    /// The root keeps its unsaved edits and takes the given first entry name.
    #[test]
    fn packages_unsaved_edits_under_first_layer_name() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(dir.path(), "root.usda", "#usda 1.0\ndef \"A\" {\n}\n");
        let root = dir.path().join("root.usda").to_str().unwrap().to_owned();
        let stage = Stage::open(&root)?;
        stage.define_prim("/Edited")?;
        let output = dir.path().join("out.usdz");
        create_new_usdz_package(&stage, &root, &output, Some("scene.usdc"))?;

        assert_eq!(entries(&output).0, ["scene.usdc"]);
        let packaged = Stage::open(output.to_str().unwrap())?;
        assert!(packaged.prim("/Edited")?.is_valid()?);
        Ok(())
    }

    /// A missing texture fails the package, as in C++.
    #[test]
    fn missing_asset_fails() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" {\n    asset t = @./missing.png@\n}\n",
        );
        let root = dir.path().join("root.usda").to_str().unwrap().to_owned();
        let stage = Stage::open(&root)?;
        let error = create_new_usdz_package(&stage, &root, dir.path().join("out.usdz"), None).unwrap_err();
        assert!(
            matches!(&error, Error::UnresolvedAsset(path) if path.ends_with("missing.png")),
            "{error}"
        );
        Ok(())
    }

    /// A stage opened from a package repackages its entries in place.
    #[test]
    fn repackages_a_package() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let source = dir.path().join("source.usdz");
        let mut writer = ArchiveWriter::create(&source)?;
        writer.add_layer(
            "root.usda",
            b"#usda 1.0\ndef \"A\" (\n    prepend references = @./sub/inner.usda@</I>\n)\n{\n}\n",
        )?;
        writer.add_layer(
            "sub/inner.usda",
            b"#usda 1.0\ndef \"I\" {\n    asset t = @../tex.png@\n    int probe = 7\n}\n",
        )?;
        writer.add_layer("tex.png", b"PNG")?;
        writer.finish()?;

        let stage = Stage::open(source.to_str().unwrap())?;
        let output = dir.path().join("out.usdz");
        create_new_usdz_package(&stage, source.to_str().unwrap(), &output, None)?;
        assert_eq!(entries(&output).0, ["root.usda", "sub/inner.usda", "tex.png"]);
        let packaged = Stage::open(output.to_str().unwrap())?;
        assert_eq!(probe(&packaged, "/A.probe"), Some(sdf::Value::Int(7)));
        Ok(())
    }
}
