//! The walk over the asset paths a layer authors (the core of C++
//! `UsdUtils_LocalizationContext`), and [`modify_asset_paths`] over it.

use std::collections::HashMap;
use std::mem;

use super::DependencyError;
use crate::pcp::clip::{self, keys};
use crate::sdf::{self, AbstractData, FieldKey, Value};
use crate::{Error, Result, ar};

/// Rewrites every asset path `layer` authors with `modify`, as C++
/// `UsdUtilsModifyAssetPaths` does: sublayers, reference and payload list-op
/// items (deleted ones included), clip template paths, and asset values in
/// fields, dictionaries, arrays and time samples, across every spec.
/// Variable expressions and patterns reach `modify` as authored, and each
/// distinct path reaches it once.
///
/// An empty result removes the path: from the sublayers (with its layer
/// offset), from reference and payload lists, from a dictionary, from a clip
/// set's template, from the time samples and, unless
/// `keep_empty_paths_in_arrays`, from an asset array. A dictionary entry or
/// array left empty that way is removed in turn, and a field left empty is
/// erased, as C++ erases them. A sublayer rewritten to the path of an earlier
/// one is dropped as a duplicate. C++ 25.05 drops every sublayer offset once
/// a sublayer path changes; here the offsets stay with their sublayers.
pub fn modify_asset_paths(
    layer: &mut sdf::Layer,
    mut modify: impl FnMut(&str) -> String,
    keep_empty_paths_in_arrays: bool,
) -> Result<()> {
    let mode = Visit {
        refuse_expansions: false,
        skip_asset_identifier: false,
        keep_empty_paths_in_arrays,
    };
    let mut modified: HashMap<String, String> = HashMap::new();
    let edits = visit_asset_paths(layer.data(), layer.identifier(), mode, |asset| {
        if !modified.contains_key(asset.path) {
            modified.insert(asset.path.to_owned(), modify(asset.path));
        }
        let path = &modified[asset.path];
        Ok((path != asset.path).then(|| path.clone()))
    })?;
    if edits.is_empty() {
        return Ok(());
    }
    layer.edit(|edit| {
        apply_edits(edit.data_mut(), edits);
        Ok(())
    })?;
    Ok(())
}

/// An asset path a layer authors, as [`visit_asset_paths`] reports it.
pub(super) struct AssetRef<'a> {
    /// The authored path.
    pub path: &'a str,
    /// What the path names.
    pub kind: AssetKind,
    /// Whether it adds an opinion: `false` inside a deleted or reordered
    /// reference or payload list-op item, its metadata included.
    pub applied: bool,
}

/// What an asset path names, decided by the format registered for its
/// extension (the innermost packaged one for a package-relative path).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum AssetKind {
    /// A layer a format reads, or whatever a sublayer, reference, payload or
    /// clip template names (C++ `UsdStage::IsSupportedFile`).
    Layer,
    /// A package, opened at its default layer and carried whole.
    Package,
    /// Any other file, such as a texture.
    Asset,
}

impl AssetKind {
    /// What `path` names. `arc` marks a path a sublayer, reference, payload
    /// or clip template names, which is a layer whatever its extension.
    pub(super) fn of(path: &str, arc: bool) -> Self {
        match sdf::LayerRegistry::find_by_extension(ar::extension(path)) {
            Some(format) if format.is_package() => Self::Package,
            Some(_) => Self::Layer,
            None if arc => Self::Layer,
            None => Self::Asset,
        }
    }
}

/// How [`visit_asset_paths`] treats the paths it meets. C++ keeps the same
/// choices as separate options on its localization context.
#[derive(Clone, Copy)]
pub(super) struct Visit {
    /// Refuse an applied path that needs expanding or evaluating before it
    /// can be followed: a UDIM pattern, a clip template, a variable
    /// expression. A deleted or reordered item is visited as authored, since
    /// it adds no dependency.
    pub refuse_expansions: bool,
    /// Skip a prim's `assetInfo:identifier`, which names the asset itself, as
    /// C++ does with metadata filtering enabled.
    pub skip_asset_identifier: bool,
    /// Keep an emptied asset array entry in place.
    pub keep_empty_paths_in_arrays: bool,
}

impl Visit {
    /// The dependency walk's choices: every path is followed, none rewritten,
    /// so nothing is emptied and an array keeps its shape.
    pub(super) const DISCOVER: Self = Self {
        refuse_expansions: true,
        skip_asset_identifier: true,
        keep_empty_paths_in_arrays: true,
    };
}

/// A field [`visit_asset_paths`] rewrote: its new value, or `None` to erase it.
pub(super) type FieldEdit = (sdf::Path, String, Option<Value>);

/// Applies the fields [`visit_asset_paths`] rewrote to `data`.
pub(super) fn apply_edits(data: &mut dyn AbstractData, edits: Vec<FieldEdit>) {
    for (path, field, value) in edits {
        match value {
            Some(value) => data.set_field(&path, &field, value),
            None => data.erase_field(&path, &field),
        }
    }
}

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
    let mut walk = Walk {
        layer,
        mode,
        visit: &mut visit,
        changed: false,
        applied: true,
    };
    for path in data.spec_paths() {
        let mut fields = data.list_fields(&path).unwrap_or_default();
        fields.sort();
        for field in fields {
            let value = data.get_field(&path, &field)?;
            // TODO(perf): a crate layer decodes a value to tell its variant,
            // bulk arrays included; a type probe on `AbstractData` would let
            // the walk skip every field that cannot hold an asset path.
            let holds_paths = match &*value {
                Value::StringVec(_) => field == FieldKey::SubLayers.as_str(),
                Value::AssetPath(_)
                | Value::AssetPathVec(_)
                | Value::Dictionary(_)
                | Value::UnregisteredDictionary(_)
                | Value::ValueVec(_)
                | Value::TimeSamples(_)
                | Value::ReferenceListOp(_)
                | Value::PayloadListOp(_)
                | Value::Payload(_) => true,
                _ => false,
            };
            if !holds_paths {
                continue;
            }
            let mut value = value.into_owned();
            let emptied = match &mut value {
                Value::StringVec(sublayers) => {
                    let removed = walk.sublayers(sublayers)?;
                    let offsets = FieldKey::SubLayerOffsets.as_str();
                    if !removed.is_empty()
                        && let Ok(Value::LayerOffsetVec(all)) =
                            data.get_field(&path, offsets).map(|value| value.into_owned())
                    {
                        let kept: Vec<_> = all
                            .into_iter()
                            .enumerate()
                            .filter(|(index, _)| !removed.contains(index))
                            .map(|(_, offset)| offset)
                            .collect();
                        let kept = (!kept.is_empty()).then_some(Value::LayerOffsetVec(kept));
                        edits.push((path.clone(), offsets.to_owned(), kept));
                    }
                    sublayers.is_empty()
                }
                Value::Dictionary(entries)
                    if mode.skip_asset_identifier
                        && field == FieldKey::AssetInfo.as_str()
                        && !path.is_property_path() =>
                {
                    walk.dictionary(entries, Some("identifier"))?
                }
                value => {
                    if field == FieldKey::Clips.as_str() {
                        walk.clip_templates(value)?;
                    }
                    walk.value(value)?
                }
            };
            if mem::take(&mut walk.changed) {
                edits.push((path.clone(), field, (!emptied).then_some(value)));
            }
        }
    }
    Ok(edits)
}

/// The walk over one layer's fields for [`visit_asset_paths`].
struct Walk<'a> {
    layer: &'a str,
    mode: Visit,
    visit: &'a mut dyn FnMut(AssetRef<'_>) -> Result<Option<String>>,
    /// Whether the field being walked was rewritten.
    changed: bool,
    /// Whether the paths being walked add an opinion: `false` inside a
    /// deleted or reordered list-op item, its metadata included.
    applied: bool,
}

impl Walk<'_> {
    /// Visits one path, returning whether `visit` emptied it. `arc` marks a
    /// path a sublayer, reference, payload or clip template names, which is a
    /// layer whatever its extension.
    fn path(&mut self, path: &mut String, arc: bool) -> Result<bool> {
        if path.is_empty() {
            return Ok(false);
        }
        if self.mode.refuse_expansions && self.applied {
            if sdf::expr::is_expression(path) {
                return Err(self.unsupported("variable expression", path));
            }
            if path.contains("<UDIM>") {
                return Err(self.unsupported("UDIM pattern", path));
            }
        }
        let asset = AssetRef {
            path,
            kind: AssetKind::of(path, arc),
            applied: self.applied,
        };
        let Some(rewritten) = (self.visit)(asset)? else {
            return Ok(false);
        };
        *path = rewritten;
        self.changed = true;
        Ok(path.is_empty())
    }

    /// Visits the sublayers, removing the emptied ones and the duplicates a
    /// rewrite made, and returning the removed indices.
    fn sublayers(&mut self, sublayers: &mut Vec<String>) -> Result<Vec<usize>> {
        let mut removed = Vec::new();
        let mut kept = Vec::with_capacity(sublayers.len());
        for (index, mut sublayer) in mem::take(sublayers).into_iter().enumerate() {
            if self.path(&mut sublayer, true)? || kept.contains(&sublayer) {
                removed.push(index);
                self.changed = true;
            } else {
                kept.push(sublayer);
            }
        }
        *sublayers = kept;
        Ok(removed)
    }

    /// Visits an asset value, returning whether `visit` emptied it.
    fn asset(&mut self, asset: &mut sdf::AssetPath) -> Result<bool> {
        let mut path = asset.authored_path.clone();
        let emptied = self.path(&mut path, false)?;
        if path != asset.authored_path {
            *asset = sdf::AssetPath::new(path);
        }
        Ok(emptied)
    }

    /// Visits every item of `items` with `visit`, keeping the ones it does
    /// not report emptied.
    fn retain<T>(
        &mut self,
        items: &mut Vec<T>,
        mut visit: impl FnMut(&mut Self, &mut T) -> Result<bool>,
    ) -> Result<()> {
        let mut kept = Vec::with_capacity(items.len());
        for mut item in mem::take(items) {
            if !visit(self, &mut item)? {
                kept.push(item);
            }
        }
        *items = kept;
        Ok(())
    }

    /// Visits every item of `op` with `item`, removing the ones it reports
    /// emptied, and returns whether that left the list op without an opinion.
    fn list_op<T: Default + Clone + PartialEq>(
        &mut self,
        op: &mut sdf::ListOp<T>,
        mut item: impl FnMut(&mut Self, &mut T) -> Result<bool>,
    ) -> Result<bool> {
        let had = !op.is_empty();
        let applied = self.applied;
        for (items, bucket_applied) in op.buckets_mut() {
            self.applied = applied && bucket_applied;
            self.retain(items, &mut item)?;
        }
        self.applied = applied;
        Ok(had && op.is_empty())
    }

    /// Visits the entries of `entries` in key order, except `skip`, removing
    /// the emptied ones, and returns whether that emptied the dictionary.
    fn dictionary(&mut self, entries: &mut sdf::Dictionary, skip: Option<&str>) -> Result<bool> {
        let had = !entries.is_empty();
        let mut keys: Vec<_> = entries
            .keys()
            .filter(|key| Some(key.as_str()) != skip)
            .cloned()
            .collect();
        keys.sort();
        for key in keys {
            if let Some(entry) = entries.get_mut(&key)
                && self.value(entry)?
            {
                entries.remove(&key);
            }
        }
        Ok(had && entries.is_empty())
    }

    /// Visits the asset paths in `value`, removing the entries of a container
    /// that are emptied, and returns whether `value` itself was emptied: an
    /// asset path `visit` emptied, or a container left with nothing.
    fn value(&mut self, value: &mut Value) -> Result<bool> {
        Ok(match value {
            Value::AssetPath(asset) => self.asset(asset)?,
            Value::AssetPathVec(assets) => {
                let had = !assets.is_empty();
                let keep_empty = self.mode.keep_empty_paths_in_arrays;
                self.retain(assets, |walk, asset| Ok(walk.asset(asset)? && !keep_empty))?;
                had && assets.is_empty()
            }
            Value::Dictionary(entries) | Value::UnregisteredDictionary(entries) => self.dictionary(entries, None)?,
            Value::ValueVec(values) => {
                for value in values {
                    self.value(value)?;
                }
                false
            }
            Value::TimeSamples(samples) => {
                let had = !samples.is_empty();
                self.retain(samples, |walk, (_, value)| walk.value(value))?;
                had && samples.is_empty()
            }
            Value::ReferenceListOp(op) => self.list_op(op, |walk, reference| {
                if walk.path(&mut reference.asset_path, true)? {
                    return Ok(true);
                }
                walk.dictionary(&mut reference.custom_data, None)?;
                Ok(false)
            })?,
            Value::PayloadListOp(op) => self.list_op(op, |walk, payload| walk.path(&mut payload.asset_path, true))?,
            Value::Payload(payload) => self.path(&mut payload.asset_path, true)?,
            _ => false,
        })
    }

    /// Visits each clip set's template path, which C++ expands into clip
    /// paths, or refuses it when expansions are refused. An empty template,
    /// which C++ skips, is left alone, and one `visit` empties leaves its
    /// clip set.
    fn clip_templates(&mut self, clips: &mut Value) -> Result<()> {
        let Value::Dictionary(sets) = clips else {
            return Ok(());
        };
        let names: Vec<String> = clip::effective_set_names(sets, None).into_iter().cloned().collect();
        for name in names {
            let Some(Value::Dictionary(set)) = sets.get_mut(&name) else {
                continue;
            };
            let Some(Value::String(template)) = set.get_mut(keys::TEMPLATE_ASSET_PATH) else {
                continue;
            };
            if template.is_empty() {
                continue;
            }
            if self.mode.refuse_expansions {
                return Err(self.unsupported("clip template", template));
            }
            if self.path(template, true)? {
                set.remove(keys::TEMPLATE_ASSET_PATH);
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

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub(crate) const MODIFY: &str = r#"#usda 1.0
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
    fn modify_matches_cpp() -> Result<()> {
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

    const EMPTIED: &str = r#"#usda 1.0
(
    subLayers = [
        @./a.usda@ (offset = 1),
        @./b.usda@ (offset = 2)
    ]
)

def "A" (
    customData = {
        asset drop = @./drop.png@
        dictionary nested = {
            asset drop = @./drop.png@
        }
        string note = "kept"
    }
    prepend references = @./drop.usda@</A>
)
{
    asset sampled.timeSamples = {
        1: @./drop.png@,
        2: @./keep.png@,
    }
    asset[] textures = [@./drop.png@]
}

def "B" (
    customData = {
        asset drop = @./drop.png@
    }
)
{
}
"#;

    /// An emptied path leaves its container, a container emptied that way
    /// leaves its own, an emptied field is erased, and a sublayer rewritten to
    /// an earlier one's path is dropped with its offset.
    #[test]
    fn emptied_paths_leave_containers() -> Result<()> {
        for keep_empty in [false, true] {
            let mut layer = sdf::Layer::from_bytes("emptied.usda", EMPTIED.as_bytes().to_vec())?;
            let modify = |path: &str| match path {
                "./b.usda" => "./a.usda".to_owned(),
                path if path.contains("drop") => String::new(),
                path => path.to_owned(),
            };
            modify_asset_paths(&mut layer, modify, keep_empty)?;
            let text = layer.export_to_string()?;
            assert!(text.contains("subLayers = [@./a.usda@ (offset = 1.0"), "{text}");
            assert!(text.contains("string note = \"kept\""), "{text}");
            assert!(text.contains("2.0: @./keep.png@"), "{text}");
            assert!(!text.contains("drop"), "{text}");
            assert!(!text.contains("nested"), "{text}");
            assert!(!text.contains("references"), "{text}");
            assert!(text.contains("def \"B\"\n{\n}"), "{text}");
            if keep_empty {
                assert!(text.contains("textures = [@@]"), "{text}");
            } else {
                assert!(!text.contains("textures ="), "{text}");
            }
        }
        Ok(())
    }

    /// An emptied clip template leaves its clip set.
    #[test]
    fn emptied_clip_template_removed() -> Result<()> {
        let mut layer = sdf::Layer::from_bytes("clips.usda", MODIFY.as_bytes().to_vec())?;
        let modify = |path: &str| {
            if path == "./clip.#.usda" {
                String::new()
            } else {
                path.to_owned()
            }
        };
        modify_asset_paths(&mut layer, modify, true)?;
        let text = layer.export_to_string()?;
        assert!(!text.contains("templateAssetPath"), "{text}");
        assert!(text.contains("manifestAssetPath"), "{text}");
        Ok(())
    }

    /// A single payload, the pre-list-op form a crate file can hold, whose
    /// path is emptied is erased; left in place it would read as an internal
    /// arc.
    #[test]
    fn emptied_single_payload_erased() -> Result<()> {
        let mut layer = sdf::Layer::from_bytes("payload.usda", b"#usda 1.0\ndef \"A\" {\n}\n".to_vec())?;
        let prim = sdf::path("/A")?;
        let payload = FieldKey::Payload.as_str();
        layer.edit(|edit| {
            let value = Value::Payload(sdf::Payload {
                asset_path: "./pay.usda".to_owned(),
                prim_path: sdf::path("/P")?,
                ..Default::default()
            });
            edit.data_mut().set_field(&prim, payload, value);
            Ok(())
        })?;
        modify_asset_paths(&mut layer, |_| String::new(), true)?;
        assert!(!layer.data().has_field(&prim, payload));
        Ok(())
    }
}
