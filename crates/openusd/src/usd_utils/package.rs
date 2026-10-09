//! USDZ packaging (C++ `UsdUtilsCreateNewUsdzPackage`): the files
//! [`discover`] finds, each given one entry, rewritten to reach each other
//! there, and written out.

use std::collections::{HashMap, HashSet};
use std::io::{Cursor, Read, Seek, Write};
use std::path::{Component, Path};

use super::discover::{Content, Discover, Discovery, Placement, Source, Use, discover};
use super::walk::{Visit, apply_edits, visit_asset_paths};
use crate::sdf::{self, AbstractData};
use crate::usd::Stage;
use crate::{Error, Result, ar, pcp, tf, usdz};

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
/// the root's file name; either way it must name a native layer (`.usd`,
/// `.usda` or `.usdc`) for the package to open at it. A dependency authored
/// as a `./` or `../` path that stays inside the package keeps its path and
/// its place relative to the root. Any other (an absolute path, a search path,
/// or one leading out of the package) moves into a numbered directory per
/// source directory (`0/`, `1/`, ...) and its authored path is rewritten to
/// reach it. Each source is stored once: a later path to it, from wherever
/// it is authored, is rewritten to the entry it already has. That keeps a
/// reference deleted in one layer matching the one another layer adds.
///
/// A `.usdz` dependency is stored whole, as a package nested in the new one.
/// The layers in it that `stage` holds, at any depth of nesting, are
/// re-serialized from memory so their unsaved edits are packaged too, and
/// whatever they name outside their package is packaged into it the same
/// way, since nothing inside a package can reach outside it. A root that is
/// itself inside a package is repackaged from the entries the walk reaches.
///
/// A missing non-layer asset fails the package, as in C++, before anything is
/// written. The package is written beside its destination and moved there
/// once complete. A source read along the way, the destination itself
/// included, stays intact until then.
///
/// [`compute_all_dependencies`]: super::compute_all_dependencies
pub fn create_new_usdz_package(
    stage: &Stage,
    asset_path: &str,
    usdz_file_path: impl AsRef<Path>,
    first_layer_name: Option<&str>,
) -> Result<Vec<String>> {
    let graph = stage.layers();
    let policy = Discover {
        inactive: true,
        open_packages: false,
    };
    let discovery = discover(&graph, asset_path, policy)?;
    let mut skipped = Vec::new();
    for (identifier, kind) in &discovery.unresolved {
        if *kind == super::walk::AssetKind::Asset {
            return Err(Error::UnresolvedAsset(identifier.clone()));
        }
        skipped.push(identifier.clone());
    }
    let name = if let Some(name) = first_layer_name {
        name.to_owned()
    } else {
        let location = discovery.sources[0]
            .content
            .location()
            .ok_or_else(|| Error::UnresolvedAsset(asset_path.to_owned()))?;
        ar::split_file_name(location).1.to_owned()
    };
    if !usdz::is_layer_name(&name) {
        return Err(usdz::ArchiveError::InvalidEntryName {
            name,
            reason: "must name a native USD layer (.usd, .usda or .usdc) to be the package's default layer",
        }
        .into());
    }
    let entries = assign_entries(&discovery, &name, HashSet::new());

    let mut temp = tf::SafeOutputFile::create(usdz_file_path.as_ref())?;
    let mut archive = usdz::ArchiveWriter::new(temp.file());
    write_entries(&graph, &discovery, &entries, &mut archive)?;
    archive.finish()?;
    temp.persist()?;
    Ok(skipped)
}

/// The entry each source of a scope is stored at, by source index: the root
/// at `first_name`, an existing entry of a package at its own name. A named
/// source keeps the place the layer that first named it reaches by a `./` or
/// `../` path, when that entry is still free; any other moves into the
/// numbered directory of its source directory. `reserved` holds the entry
/// names already in use, every entry of a package being rebuilt.
fn assign_entries(discovery: &Discovery<'_>, first_name: &str, reserved: HashSet<String>) -> Vec<String> {
    let mut entries: Vec<String> = Vec::with_capacity(discovery.sources.len());
    let mut taken = reserved;
    let mut directories = HashMap::new();
    for source in &discovery.sources {
        let entry = match &source.placement {
            Placement::Root => first_name.to_owned(),
            Placement::Entry(name) => name.clone(),
            Placement::Named { by, path } => kept_entry(&entries[*by], path)
                .filter(|entry| !taken.contains(entry))
                .unwrap_or_else(|| moved_entry(&mut directories, &taken, &source.identifier)),
        };
        taken.insert(entry.clone());
        entries.push(entry);
    }
    entries
}

/// The entry a moved source takes: its file name in the numbered directory
/// of its source directory, `directories` numbering them in the order they
/// first move and `taken` holding the entry names in use.
fn moved_entry(directories: &mut HashMap<String, usize>, taken: &HashSet<String>, source: &str) -> String {
    let (directory, name) = ar::split_file_name(source);
    let next = directories.len();
    let mut number = *directories.entry(directory.to_owned()).or_insert(next);
    let mut entry = format!("{number}/{name}");
    while taken.contains(&entry) {
        number += 1;
        entry = format!("{number}/{name}");
    }
    entry
}

/// Writes every source of the root scope to `archive` at its entry, in
/// source order.
///
/// TODO(rayon): each entry's bytes are produced independently of the others;
/// only the writes are in order.
fn write_entries<W: Write + Seek>(
    graph: &pcp::LayerGraph,
    discovery: &Discovery<'_>,
    entries: &[String],
    archive: &mut usdz::ArchiveWriter<W>,
) -> Result<()> {
    for (index, source) in discovery.sources.iter().enumerate() {
        let bytes = source_bytes(graph, source, &entries[index], entries, None)?;
        archive.add_layer(&entries[index], &bytes)?;
    }
    Ok(())
}

/// The bytes `source` is stored as at `location`, its scope's sources at
/// `entries`: a layer with its paths rewritten to reach their entries, a
/// package rebuilt around the layers the stage holds in it from `original`
/// (its bytes as an entry of the enclosing package) or from its location, any
/// other file as it is.
fn source_bytes(
    graph: &pcp::LayerGraph,
    source: &Source<'_>,
    location: &str,
    entries: &[String],
    original: Option<Vec<u8>>,
) -> Result<Vec<u8>> {
    match &source.content {
        Content::Layer { layer, uses } => {
            let edits = visit_asset_paths(layer.data(), layer.identifier(), Visit::DISCOVER, |asset| {
                Ok(rewrite(location, asset.path, uses, entries))
            })?;
            if edits.is_empty() {
                serialize(layer.data(), location)
            } else {
                let mut data = sdf::Data::from_abstract(layer.data())?;
                apply_edits(&mut data, edits);
                serialize(&data, location)
            }
        }
        Content::Package { resolved, inside } => {
            let bytes = match original {
                Some(bytes) => bytes,
                None => read_asset(graph, resolved)?,
            };
            rebuild_package(graph, bytes, inside)
        }
        Content::Asset(resolved) => match original {
            Some(bytes) => Ok(bytes),
            None => read_asset(graph, resolved),
        },
    }
}

/// `bytes`, a package, as they are when the stage holds no layer inside it,
/// otherwise rebuilt from its scope `inside`: each entry the stage holds a
/// layer for re-serialized from memory, each nested package holding one
/// rebuilt the same way, every other entry copied, and whatever those layers
/// named outside the package added at its entry.
fn rebuild_package(graph: &pcp::LayerGraph, bytes: Vec<u8>, inside: &Discovery<'_>) -> Result<Vec<u8>> {
    if inside.sources.is_empty() {
        return Ok(bytes);
    }
    let mut archive = zip::ZipArchive::new(Cursor::new(bytes.as_slice())).map_err(usdz::ArchiveError::from)?;
    let reserved = archive.file_names().map(str::to_owned).collect();
    let entries = assign_entries(inside, "", reserved);
    let existing: HashMap<&str, usize> = inside
        .sources
        .iter()
        .enumerate()
        .filter_map(|(index, source)| match &source.placement {
            Placement::Entry(name) => Some((name.as_str(), index)),
            Placement::Root | Placement::Named { .. } => None,
        })
        .collect();
    let mut rebuilt = usdz::ArchiveWriter::new(Cursor::new(Vec::new()));
    for index in 0..archive.len() {
        let mut entry = archive.by_index(index).map_err(usdz::ArchiveError::from)?;
        let name = entry.name().to_owned();
        let mut contents = Vec::new();
        entry.read_to_end(&mut contents)?;
        let contents = match existing.get(name.as_str()) {
            Some(&source) => source_bytes(graph, &inside.sources[source], &name, &entries, Some(contents))?,
            None => contents,
        };
        rebuilt.add_layer(&name, &contents)?;
    }
    for (index, source) in inside.sources.iter().enumerate() {
        if matches!(source.placement, Placement::Named { .. }) {
            let contents = source_bytes(graph, source, &entries[index], &entries, None)?;
            rebuilt.add_layer(&entries[index], &contents)?;
        }
    }
    Ok(rebuilt.finish()?.into_inner())
}

/// The path the layer at `location` reaches the entry of the source it
/// authored `path` for, when that is not `path` itself; `None` leaves the
/// path as authored, as it is for one that did not resolve. A path into a
/// package keeps the part its use records.
fn rewrite(location: &str, path: &str, uses: &HashMap<String, Use>, entries: &[String]) -> Option<String> {
    let Use { source, packaged } = uses.get(path)?;
    let entry = &entries[*source];
    let to_source = ar::split_package_relative_path_outer(path).map_or_else(|| path.to_owned(), |(package, _)| package);
    if kept_entry(location, &to_source).as_deref() == Some(entry) {
        return None;
    }
    let moved = path_to(location, entry);
    Some(match packaged {
        Some(inner) => ar::join_package_relative_path(&moved, inner),
        None => moved,
    })
}

/// The entry a path authored relative to the layer at `location` (`./a.usda`,
/// `../tex/t.png`) reaches, or `None` for any other path or one leading out
/// of the package.
fn kept_entry(location: &str, path: &str) -> Option<String> {
    let mut components = Path::new(path).components().peekable();
    if !matches!(components.peek(), Some(Component::CurDir | Component::ParentDir)) {
        return None;
    }
    let mut parts: Vec<&str> = location.split('/').collect();
    parts.pop();
    for component in components {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                parts.pop()?;
            }
            Component::Normal(part) => parts.push(part.to_str()?),
            Component::RootDir | Component::Prefix(_) => return None,
        }
    }
    Some(parts.join("/"))
}

/// The path from the layer at `location` to `entry`.
fn path_to(location: &str, entry: &str) -> String {
    format!("{}{entry}", "../".repeat(location.matches('/').count()))
}

/// The bytes of the asset at `resolved`.
fn read_asset(graph: &pcp::LayerGraph, resolved: &ar::ResolvedPath) -> Result<Vec<u8>> {
    Ok(graph.layer_registry().open_asset(resolved)?.read_all()?)
}

/// Serializes `data` in the format the extension of `location` names.
fn serialize(data: &dyn AbstractData, location: &str) -> Result<Vec<u8>> {
    let mut bytes = Cursor::new(Vec::new());
    sdf::LayerRegistry::export_format(location)?.write(data, &mut bytes)?;
    Ok(bytes.into_inner())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    use crate::ar::Resolver;
    use crate::usd::stage::tests::attribute_value;
    use crate::usd_utils::compute_all_dependencies;
    use crate::usd_utils::discover::tests::{open, write};
    use crate::usdz::ArchiveWriter;

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

    /// The entry names of the package at `packaged`, a path into one or more
    /// packages, and the text of its `.usda` entries.
    fn nested_entries(packaged: &str) -> (Vec<String>, HashMap<String, String>) {
        let bytes = ar::DefaultResolver::new()
            .open_asset(&ar::ResolvedPath::new(packaged))
            .unwrap()
            .read_all()
            .unwrap();
        let mut archive = zip::ZipArchive::new(Cursor::new(bytes)).unwrap();
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

    /// The layout C++ gives the same scene, with two differences: the paths a
    /// layer in a subdirectory authors are made to reach their moved entries
    /// (C++ 25.05 writes `0/d.usda` in `sub/a.usda`, which resolves to
    /// `sub/0/d.usda`), and the texture `0/b.usda` reaches by its own
    /// relative path is the one entry it already has (C++ copies it again at
    /// `scene/tex/t.png`).
    #[test]
    fn layout_matches_cpp() -> Result<()> {
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

        let (root, stage) = open(base, "scene/root.usda")?;
        let output = base.join("out.usdz");
        let skipped = create_new_usdz_package(&stage, &root, &output, None)?;
        assert_eq!(skipped.len(), 1);
        assert!(Path::new(&skipped[0]).ends_with("scene/missing.usda"));
        assert_eq!(
            fs::read_dir(base)?.count(),
            4,
            "no staging file left beside the package"
        );

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
        assert!(texts["0/b.usda"].contains("@../tex/t.png@"));

        let packaged = Stage::open(output.to_str().unwrap())?;
        assert_eq!(attribute_value(&packaged, "/S.probe"), Some(sdf::Value::Int(1)));
        assert_eq!(attribute_value(&packaged, "/A.probe"), Some(sdf::Value::Int(4)));
        assert_eq!(attribute_value(&packaged, "/B.probe"), Some(sdf::Value::Int(3)));
        assert_eq!(attribute_value(&packaged, "/C.probe"), Some(sdf::Value::Int(5)));
        assert_eq!(attribute_value(&packaged, "/N.probe"), Some(sdf::Value::Int(6)));
        Ok(())
    }

    /// The root keeps its unsaved edits and takes the given first entry name.
    #[test]
    fn unsaved_edits_first_layer_name() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(dir.path(), "root.usda", "#usda 1.0\ndef \"A\" {\n}\n");
        let (root, stage) = open(dir.path(), "root.usda")?;
        stage.define_prim("/Edited")?;
        let output = dir.path().join("out.usdz");
        create_new_usdz_package(&stage, &root, &output, Some("scene.usdc"))?;

        assert_eq!(entries(&output).0, ["scene.usdc"]);
        let packaged = Stage::open(output.to_str().unwrap())?;
        assert!(packaged.prim("/Edited")?.is_valid()?);
        Ok(())
    }

    /// A source reached by different paths from different entries is stored
    /// once. A reference deleted in one layer and prepended in another still
    /// names the same target after packaging.
    #[test]
    fn one_entry_per_source() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(
            dir.path(),
            "scene/root.usda",
            "#usda 1.0\n(\n    subLayers = [@weak.usda@]\n)\ndef \"A\" (\n    delete references = @./ref.usda@</R>\n)\n{\n}\n",
        );
        write(
            dir.path(),
            "scene/weak.usda",
            "#usda 1.0\ndef \"A\" (\n    prepend references = @./ref.usda@</R>\n)\n{\n}\n",
        );
        write(
            dir.path(),
            "scene/ref.usda",
            "#usda 1.0\ndef \"R\" {\n    int probe = 42\n}\n",
        );
        let (root, stage) = open(dir.path(), "scene/root.usda")?;
        assert_eq!(attribute_value(&stage, "/A.probe"), None);

        let output = dir.path().join("out.usdz");
        create_new_usdz_package(&stage, &root, &output, None)?;
        let (names, texts) = entries(&output);
        assert_eq!(names, ["root.usda", "0/weak.usda", "ref.usda"]);
        assert!(
            texts["0/weak.usda"].contains("@../ref.usda@"),
            "{}",
            texts["0/weak.usda"]
        );
        let packaged = Stage::open(output.to_str().unwrap())?;
        assert_eq!(attribute_value(&packaged, "/A.probe"), None);
        Ok(())
    }

    /// A first layer name the package could not open at is refused before
    /// anything is written.
    #[test]
    fn first_layer_name_not_layer() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(dir.path(), "root.usda", "#usda 1.0\ndef \"A\" {\n}\n");
        let (root, stage) = open(dir.path(), "root.usda")?;
        let output = dir.path().join("out.usdz");
        let error = create_new_usdz_package(&stage, &root, &output, Some("root.usdz")).unwrap_err();
        assert!(
            matches!(&error, Error::Archive(archive) if matches!(**archive, usdz::ArchiveError::InvalidEntryName { .. })),
            "{error}"
        );
        assert!(!output.exists());
        Ok(())
    }

    /// A missing texture fails the package, as in C++, before anything is
    /// written.
    #[test]
    fn missing_asset_fails() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" {\n    asset t = @./missing.png@\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        let output = dir.path().join("out.usdz");
        let error = create_new_usdz_package(&stage, &root, &output, None).unwrap_err();
        assert!(
            matches!(&error, Error::UnresolvedAsset(path) if path.ends_with("missing.png")),
            "{error}"
        );
        assert!(!output.exists());
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
        assert_eq!(attribute_value(&packaged, "/A.probe"), Some(sdf::Value::Int(7)));
        Ok(())
    }

    /// A package written over the package the stage was opened from reads
    /// its sources from the original, which stays until the package is
    /// complete.
    #[test]
    fn repackages_onto_itself() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let source = dir.path().join("scene.usdz");
        let mut writer = ArchiveWriter::create(&source)?;
        writer.add_layer(
            "root.usda",
            b"#usda 1.0\ndef \"A\" {\n    asset t = @./tex.png@\n    int probe = 7\n}\n",
        )?;
        writer.add_layer("tex.png", b"PNG")?;
        writer.finish()?;

        let stage = Stage::open(source.to_str().unwrap())?;
        assert_eq!(attribute_value(&stage, "/A.probe"), Some(sdf::Value::Int(7)));
        create_new_usdz_package(&stage, source.to_str().unwrap(), &source, None)?;
        assert_eq!(fs::read_dir(dir.path())?.count(), 1, "only the package is left");
        assert_eq!(entries(&source).0, ["root.usda", "tex.png"]);
        let packaged = Stage::open(source.to_str().unwrap())?;
        assert_eq!(attribute_value(&packaged, "/A.probe"), Some(sdf::Value::Int(7)));
        Ok(())
    }

    /// The layers the stage holds inside a referenced package, its default
    /// one and one named by entry, are re-serialized from memory with their
    /// unsaved edits, while the other entries are copied.
    #[test]
    fn nested_package_edits_kept() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let mut writer = ArchiveWriter::create(dir.path().join("pkg.usdz"))?;
        writer.add_layer("first.usda", b"#usda 1.0\ndef \"R\" {\n    int probe = 1\n}\n")?;
        writer.add_layer("other.usda", b"#usda 1.0\ndef \"R\" {\n    int probe = 1\n}\n")?;
        writer.add_layer("tex.png", b"PNG")?;
        writer.finish()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    prepend references = @./pkg.usdz@</R>\n)\n{\n}\ndef \"B\" (\n    prepend references = @./pkg.usdz[other.usda]@</R>\n)\n{\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        // Composing the references loads the packaged layers into the stage.
        assert_eq!(attribute_value(&stage, "/A.probe"), Some(sdf::Value::Int(1)));
        assert_eq!(attribute_value(&stage, "/B.probe"), Some(sdf::Value::Int(1)));
        let dependencies = compute_all_dependencies(&stage, &root)?;
        let probe = sdf::path("/R.probe")?;
        for identifier in dependencies.layers.iter().filter(|layer| layer.contains("pkg.usdz")) {
            stage.layer_mut(identifier).unwrap().edit(|edit| {
                edit.data_mut()
                    .set_field(&probe, sdf::FieldKey::Default.as_str(), sdf::Value::Int(42));
                Ok(())
            })?;
        }

        let output = dir.path().join("out.usdz");
        create_new_usdz_package(&stage, &root, &output, None)?;
        assert_eq!(entries(&output).0, ["root.usda", "pkg.usdz"]);
        let nested = ar::join_package_relative_path(output.to_str().unwrap(), "pkg.usdz");
        assert_eq!(nested_entries(&nested).0, ["first.usda", "other.usda", "tex.png"]);

        let packaged = Stage::open(output.to_str().unwrap())?;
        assert_eq!(attribute_value(&packaged, "/A.probe"), Some(sdf::Value::Int(42)));
        assert_eq!(attribute_value(&packaged, "/B.probe"), Some(sdf::Value::Int(42)));
        Ok(())
    }

    /// A package nested in a rebuilt one keeps every entry: the layer the
    /// stage holds in it is re-serialized, the rest copied.
    #[test]
    fn nested_archives_kept() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let mut inner = ArchiveWriter::new(Cursor::new(Vec::new()));
        inner.add_layer(
            "first.usda",
            b"#usda 1.0\ndef \"A\" (\n    prepend references = @./second.usda@</B>\n)\n{\n}\n",
        )?;
        inner.add_layer("second.usda", b"#usda 1.0\ndef \"B\" {\n    int probe = 7\n}\n")?;
        inner.add_layer("tex.png", b"PNG")?;
        let inner = inner.finish()?.into_inner();
        let mut outer = ArchiveWriter::create(dir.path().join("outer.usdz"))?;
        outer.add_layer(
            "root.usda",
            b"#usda 1.0\ndef \"A\" (\n    prepend references = @./inner.usdz@</A>\n)\n{\n}\n",
        )?;
        outer.add_layer("inner.usdz", &inner)?;
        outer.finish()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    prepend references = @./outer.usdz@</A>\n)\n{\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        assert_eq!(attribute_value(&stage, "/A.probe"), Some(sdf::Value::Int(7)));

        let output = dir.path().join("out.usdz");
        create_new_usdz_package(&stage, &root, &output, None)?;
        let nested = ar::join_package_relative_path(output.to_str().unwrap(), "outer.usdz[inner.usdz]");
        assert_eq!(nested_entries(&nested).0, ["first.usda", "second.usda", "tex.png"]);
        let packaged = Stage::open(output.to_str().unwrap())?;
        assert_eq!(attribute_value(&packaged, "/A.probe"), Some(sdf::Value::Int(7)));
        Ok(())
    }

    /// What a layer the stage holds inside a package names outside it is
    /// packaged into that package, and the path rewritten to reach it there.
    #[test]
    fn nested_layer_dependencies_packaged() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(dir.path(), "textures/t.png", "PNG");
        let texture = dir.path().join("textures/t.png");
        let texture = texture.to_str().unwrap().replace('\\', "/");
        let mut writer = ArchiveWriter::create(dir.path().join("pkg.usdz"))?;
        writer.add_layer(
            "first.usda",
            format!("#usda 1.0\ndef \"R\" {{\n    asset tex = @{texture}@\n    int probe = 1\n}}\n").as_bytes(),
        )?;
        writer.finish()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    prepend references = @./pkg.usdz@</R>\n)\n{\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        assert_eq!(attribute_value(&stage, "/A.probe"), Some(sdf::Value::Int(1)));

        let output = dir.path().join("out.usdz");
        create_new_usdz_package(&stage, &root, &output, None)?;
        let nested = ar::join_package_relative_path(output.to_str().unwrap(), "pkg.usdz");
        let (names, texts) = nested_entries(&nested);
        assert_eq!(names, ["first.usda", "0/t.png"]);
        assert!(texts["first.usda"].contains("@0/t.png@"), "{}", texts["first.usda"]);

        let packaged = Stage::open(output.to_str().unwrap())?;
        let dependencies = compute_all_dependencies(&packaged, output.to_str().unwrap())?;
        assert!(
            dependencies
                .assets
                .iter()
                .any(|asset| asset.ends_with("out.usdz[pkg.usdz[0/t.png]]")),
            "{:?}",
            dependencies.assets
        );
        assert!(dependencies.unresolved.is_empty(), "{:?}", dependencies.unresolved);
        Ok(())
    }

    /// A file packaged into a rebuilt package takes an entry none of the
    /// package's own entries has, including those the stage holds no layer
    /// for.
    #[test]
    fn nested_entry_names_reserved() -> Result<()> {
        let dir = tempfile::tempdir()?;
        write(dir.path(), "textures/extra.png", "NEW");
        let texture = dir.path().join("textures/extra.png");
        let texture = texture.to_str().unwrap().replace('\\', "/");
        let mut writer = ArchiveWriter::create(dir.path().join("pkg.usdz"))?;
        writer.add_layer(
            "first.usda",
            format!("#usda 1.0\ndef \"R\" {{\n    asset tex = @{texture}@\n    int probe = 1\n}}\n").as_bytes(),
        )?;
        writer.add_layer("0/extra.png", b"EXISTING")?;
        writer.finish()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    prepend references = @./pkg.usdz@</R>\n)\n{\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        assert_eq!(attribute_value(&stage, "/A.probe"), Some(sdf::Value::Int(1)));

        let output = dir.path().join("out.usdz");
        create_new_usdz_package(&stage, &root, &output, None)?;
        let nested = ar::join_package_relative_path(output.to_str().unwrap(), "pkg.usdz");
        let (names, texts) = nested_entries(&nested);
        assert_eq!(names, ["first.usda", "0/extra.png", "1/extra.png"]);
        assert!(texts["first.usda"].contains("@1/extra.png@"), "{}", texts["first.usda"]);
        Ok(())
    }

    /// A missing asset named by a layer the stage holds two packages deep
    /// fails the package like one named at the top.
    #[test]
    fn deep_missing_asset_fails() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let mut inner = ArchiveWriter::new(Cursor::new(Vec::new()));
        inner.add_layer(
            "first.usda",
            b"#usda 1.0\ndef \"A\" {\n    asset t = @./missing.png@\n    int probe = 7\n}\n",
        )?;
        let inner = inner.finish()?.into_inner();
        let mut outer = ArchiveWriter::create(dir.path().join("outer.usdz"))?;
        outer.add_layer(
            "root.usda",
            b"#usda 1.0\ndef \"A\" (\n    prepend references = @./inner.usdz@</A>\n)\n{\n}\n",
        )?;
        outer.add_layer("inner.usdz", &inner)?;
        outer.finish()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    prepend references = @./outer.usdz@</A>\n)\n{\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        assert_eq!(attribute_value(&stage, "/A.probe"), Some(sdf::Value::Int(7)));

        let output = dir.path().join("out.usdz");
        let error = create_new_usdz_package(&stage, &root, &output, None).unwrap_err();
        assert!(
            matches!(&error, Error::UnresolvedAsset(path) if path.ends_with("outer.usdz[inner.usdz[missing.png]]")),
            "{error}"
        );
        assert!(!output.exists());
        Ok(())
    }

    /// An absolute path into the very package a layer the stage holds is in
    /// names the original archive. It is rewritten to reach the entry inside
    /// the packaged copy, a file or a package nested there alike, and the
    /// original can then go.
    #[test]
    fn absolute_packaged_paths_rewritten() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let package = dir.path().join("pkg.usdz");
        let absolute = package.to_str().unwrap().replace('\\', "/");
        let mut inner = ArchiveWriter::new(Cursor::new(Vec::new()));
        inner.add_layer("a.usda", b"#usda 1.0\ndef \"B\" {\n    int deep = 9\n}\n")?;
        let inner = inner.finish()?.into_inner();
        let mut writer = ArchiveWriter::create(&package)?;
        writer.add_layer(
            "first.usda",
            format!(
                "#usda 1.0\ndef \"R\" (\n    prepend references = @{absolute}[inner.usdz[a.usda]]@</B>\n)\n{{\n    asset tex = @{absolute}[tex.png]@\n    int probe = 1\n}}\n"
            )
            .as_bytes(),
        )?;
        writer.add_layer("inner.usdz", &inner)?;
        writer.add_layer("tex.png", b"PNG")?;
        writer.finish()?;
        write(
            dir.path(),
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    prepend references = @./pkg.usdz@</R>\n)\n{\n}\n",
        );
        let (root, stage) = open(dir.path(), "root.usda")?;
        assert_eq!(attribute_value(&stage, "/A.deep"), Some(sdf::Value::Int(9)));

        let output = dir.path().join("out.usdz");
        create_new_usdz_package(&stage, &root, &output, None)?;
        fs::rename(&package, dir.path().join("moved.usdz"))?;
        let nested = ar::join_package_relative_path(output.to_str().unwrap(), "pkg.usdz");
        let (names, texts) = nested_entries(&nested);
        assert_eq!(names, ["first.usda", "inner.usdz", "tex.png"]);
        assert!(
            texts["first.usda"].contains("@inner.usdz[a.usda]@"),
            "{}",
            texts["first.usda"]
        );
        assert!(texts["first.usda"].contains("@tex.png@"), "{}", texts["first.usda"]);

        let packaged = Stage::open(output.to_str().unwrap())?;
        assert_eq!(attribute_value(&packaged, "/A.deep"), Some(sdf::Value::Int(9)));
        let dependencies = compute_all_dependencies(&packaged, output.to_str().unwrap())?;
        assert!(dependencies.unresolved.is_empty(), "{:?}", dependencies.unresolved);
        Ok(())
    }

    /// A packaged path is checked whole: a missing packaged layer is left out
    /// and reported, a missing packaged asset fails the package.
    #[test]
    fn missing_packaged_entry() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let mut package = ArchiveWriter::create(dir.path().join("assets.usdz"))?;
        package.add_layer("a.usda", b"#usda 1.0\ndef \"A\" {\n}\n")?;
        package.finish()?;
        for (root, missing, layer) in [
            (
                "#usda 1.0\ndef \"A\" (\n    prepend references = @./assets.usdz[missing.usda]@\n)\n{\n}\n",
                "assets.usdz[missing.usda]",
                true,
            ),
            (
                "#usda 1.0\ndef \"A\" {\n    asset t = @./assets.usdz[missing.png]@\n}\n",
                "assets.usdz[missing.png]",
                false,
            ),
        ] {
            write(dir.path(), "root.usda", root);
            let (root, stage) = open(dir.path(), "root.usda")?;
            let result = create_new_usdz_package(&stage, &root, dir.path().join("out.usdz"), None);
            if layer {
                let skipped = result?;
                assert_eq!(skipped.len(), 1, "{skipped:?}");
                assert!(skipped[0].ends_with(missing), "{skipped:?}");
            } else {
                let error = result.unwrap_err();
                assert!(
                    matches!(&error, Error::UnresolvedAsset(path) if path.ends_with(missing)),
                    "{error}"
                );
            }
        }
        Ok(())
    }
}
