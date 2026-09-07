//! Materializing a composed stage as a single layer (C++ `UsdStage::Flatten`).
//!
//! Composition answers what a prim holds by consulting many layers; flattening
//! writes those answers down once, so the result stands alone. Every arc is
//! resolved rather than copied: a reference, an inherit, a variant selection
//! and a sublayer all disappear, and what they contributed is written where it
//! landed.
//!
//! What survives is what a reader would still ask for — the prim tree, each
//! prim's metadata, and each property's declaration, value and targets.

use std::collections::BTreeSet;

use crate::usd::{Attribute, Prim, PrimPredicate, SpecSite, Stage};
use crate::{Result, sdf, tf};

/// Fields flattening does not copy.
///
/// The first group says how a prim composes rather than what it holds:
/// flattening has already applied them, and a reference written into the
/// flattened layer would be composed again by whoever opened it. The second is
/// written from the composed answer instead, so copying it too would write it
/// twice. The clip fields are in the second group because a clip's schedule
/// cannot survive a layer that no longer has the arcs it was scheduled over.
// TODO: `sdf` half-owns this vocabulary already — `FieldKey::folds_list_ops`,
// `is_children_field`, `pcp::clip::CLIP_FIELDS` and
// `SchemaRegistry::is_disallowed_field` each spell a piece of it. Classifying a
// field on `FieldKey` itself would let all five ask one question.
const NOT_COPIED: &[sdf::FieldKey] = &[
    sdf::FieldKey::References,
    sdf::FieldKey::Payload,
    sdf::FieldKey::InheritPaths,
    sdf::FieldKey::Specializes,
    sdf::FieldKey::VariantSetNames,
    sdf::FieldKey::VariantSelection,
    sdf::FieldKey::Relocates,
    // An expanded instance is no longer one, so the flag would promise an arc
    // that is not there.
    sdf::FieldKey::Instanceable,
    sdf::FieldKey::Specifier,
    sdf::FieldKey::TypeName,
    sdf::FieldKey::ApiSchemas,
    sdf::FieldKey::Default,
    sdf::FieldKey::TimeSamples,
    sdf::FieldKey::TargetPaths,
    sdf::FieldKey::ConnectionPaths,
    sdf::FieldKey::Variability,
    sdf::FieldKey::Custom,
    sdf::FieldKey::Clips,
    sdf::FieldKey::ClipSets,
];

/// Fields the layer stack owned, which only its pseudo-root could carry.
const STACK_FIELDS: &[sdf::FieldKey] = &[
    sdf::FieldKey::SubLayers,
    sdf::FieldKey::SubLayerOffsets,
    sdf::FieldKey::LayerRelocates,
    sdf::FieldKey::ExpressionVariables,
];

impl Stage {
    /// The composed stage written into one layer (C++ `UsdStage::Flatten`).
    ///
    /// The result is an anonymous layer, which anchors nothing: an asset path
    /// it carries is the one composition already resolved, so it means the
    /// same read from anywhere.
    // TODO: instancing is not preserved. C++ mints a prototype per master and
    // authors an internal reference on each instance; this writes every
    // instance's contents in full, so N instances become N copies.
    // TODO: a value clip's schedule is dropped and its values are not baked, so
    // a flattened layer loses what the clips supplied. C++ writes the
    // clip-derived samples out instead (`MakeTimeSampleMapForFlatten`).
    pub fn flatten(&self) -> Result<sdf::Layer> {
        let root = sdf::Path::abs_root();
        let mut data = sdf::Data::new();
        data.create_spec(root.clone(), sdf::SpecType::PseudoRoot);
        write_fields(&mut data, &root, stage_fields(self)?);

        // Everything the stage composed, whatever its status: a class prim is
        // abstract and the default predicate skips it, yet a schema library is
        // nothing but class prims. Instance proxies stand where an instance's
        // prototype content belongs, so walking through them writes each
        // instance's contents in place and leaves no prototype to refer to.
        // TODO(perf): the whole namespace is collected before anything is
        // written, because `traverse` borrows the stage for the walk. Each
        // prim's write is independent of every other, so a per-prim sink would
        // let the walk stream — and parallelize.
        let mut paths = Vec::new();
        self.traverse(PrimPredicate::ALL, |path| paths.push(path.clone()))?;
        for path in paths {
            write_prim(&mut data, &self.prim(&path)?)?;
        }

        let tag = format!("flattened {}", self.root_layer().identifier);
        Ok(sdf::Layer::new(sdf::Layer::anonymous_identifier(tag), Box::new(data)))
    }
}

/// Writes one composed prim and every property it carries.
fn write_prim(data: &mut dyn sdf::AbstractData, prim: &Prim) -> Result<()> {
    let stage = prim.stage();
    let specifier = prim.specifier()?.unwrap_or(sdf::Specifier::Def);
    let type_name = prim.type_name()?.unwrap_or_default();
    sdf::PrimSpec::new(data, prim.path(), specifier, type_name.as_str())?;
    write_fields(
        data,
        prim.path(),
        spec_fields(stage, prim.path(), &prim.prim_stack()?, &[])?,
    );

    // The composed list is what the prim has applied, however the layers said
    // so, and an explicit list is how a single layer says it.
    let applied = prim.api_schemas()?;
    if !applied.is_empty() {
        let list_op = sdf::TokenListOp::explicit(applied);
        data.set_field(prim.path(), sdf::FieldKey::ApiSchemas.as_str(), list_op.into());
    }

    for name in prim.authored_property_names()? {
        write_property(data, prim, &name)?;
    }
    Ok(())
}

/// Writes one composed property: its declaration, the fields around it, and
/// what it holds.
fn write_property(data: &mut dyn sdf::AbstractData, prim: &Prim, name: &tf::Token) -> Result<()> {
    let stage = prim.stage();
    let path = prim.path().append_property(name.as_str())?;

    match stage.spec_type(&path)? {
        Some(sdf::SpecType::Attribute) => {
            let attribute = prim.attribute(name.clone());
            let sites = attribute.property_stack()?;
            sdf::AttributeSpec::new(
                data,
                &path,
                attribute.type_name()?.unwrap_or(sdf::ValueTypeName::TOKEN),
                attribute.variability()?.unwrap_or_default(),
                attribute.is_custom()?,
            )?;
            write_fields(data, &path, spec_fields(stage, &path, &sites, &[])?);

            let held = held(stage, &attribute, &sites)?;
            if let Some(value) = held.default {
                data.set_field(&path, sdf::FieldKey::Default.as_str(), value);
            }
            if let Some(samples) = held.samples {
                data.set_field(
                    &path,
                    sdf::FieldKey::TimeSamples.as_str(),
                    sdf::Value::TimeSamples(samples),
                );
            }
            // Connections are composed paths on the flattened stage, so they
            // need no translation; an explicit list is how one layer states
            // them.
            write_explicit_paths(data, &path, sdf::FieldKey::ConnectionPaths, attribute.connections()?);
        }
        Some(sdf::SpecType::Relationship) => {
            let relationship = prim.relationship(name.clone());
            // A relationship carries the field only where it is uniform, that
            // being the spelling `rel` and the reverse of how an attribute
            // reads, so an unauthored one is the `varying rel` a schema wrote.
            let variability = stage
                .field::<sdf::Variability>(&path, sdf::FieldKey::Variability.as_str())?
                .unwrap_or_default();
            sdf::RelationshipSpec::new(data, &path, variability, relationship.is_custom()?)?;
            write_fields(
                data,
                &path,
                spec_fields(stage, &path, &relationship.property_stack()?, &[])?,
            );
            write_explicit_paths(data, &path, sdf::FieldKey::TargetPaths, relationship.targets()?);
        }
        // A property a schema declares but no layer authors has nothing to
        // write; its fallback belongs to the schema, not to this layer.
        _ => {}
    }
    Ok(())
}

/// The stage metadata a standalone layer still carries: what the pseudo-root
/// holds, less the fields that describe the layer stack it came from.
fn stage_fields(stage: &Stage) -> Result<Vec<(String, sdf::Value)>> {
    let root = sdf::Path::abs_root();
    let sites: Vec<SpecSite> = stage
        .layer_stack()
        .into_iter()
        .map(|layer| SpecSite {
            layer,
            path: root.clone(),
            offset: sdf::LayerOffset::default(),
        })
        .collect();
    spec_fields(stage, &root, &sites, STACK_FIELDS)
}

/// The fields one composed spec carries, less what flattening resolved and
/// what is written from a composed answer instead.
///
/// The names come from every site that authors the spec, and the values from
/// the stage, because a per-site value is not the composed one — strongest
/// wins, dictionaries merge, and `variability` takes the weakest opinion.
fn spec_fields(
    stage: &Stage,
    path: &sdf::Path,
    sites: &[SpecSite],
    also_dropped: &[sdf::FieldKey],
) -> Result<Vec<(String, sdf::Value)>> {
    let mut names = BTreeSet::new();
    for site in sites {
        let Some(layer) = stage.layer(&site.layer) else {
            continue;
        };
        names.extend(layer.data().list_fields(&site.path).unwrap_or_default());
    }

    let mut fields = Vec::with_capacity(names.len());
    for name in names {
        if !copied(&name, also_dropped) {
            continue;
        }
        if let Some(value) = stage.field::<sdf::Value>(path, &name)? {
            fields.push((name, bake_asset_paths(value)));
        }
    }
    Ok(fields)
}

/// What an attribute holds, as the one site that answers for it.
#[derive(Default)]
struct Held {
    default: Option<sdf::Value>,
    samples: Option<sdf::TimeSampleMap>,
}

/// What an attribute holds, from the sites that answer for it.
///
/// The two opinions resolve by different walks, so they are asked for
/// separately. A numeric time takes the strongest site holding either, and
/// reads its samples — so a stronger `default` hides weaker samples entirely.
/// The default time skips samples altogether, so the strongest `default` is
/// the answer wherever it sits, even under a site whose samples won above.
/// Writing both is what lets one layer answer the way the stage did.
///
/// Each is then taken from composition rather than from the layer, since
/// composition is what applies a layer offset to a time code, maps a path
/// expression into stage namespace, and anchors an asset path. The authored
/// value is the fallback for the one case composition reports nothing: a
/// block, which resolves to no value and would otherwise be lost along with
/// the weaker opinion it hides.
fn held(stage: &Stage, attribute: &Attribute, sites: &[SpecSite]) -> Result<Held> {
    let numeric = sites
        .iter()
        .find(|site| holds(stage, site, sdf::FieldKey::TimeSamples) || holds(stage, site, sdf::FieldKey::Default));

    let samples = match numeric
        .and_then(|site| Some((site, authored(stage, site, sdf::FieldKey::TimeSamples)?)))
        .and_then(|(site, value)| Some((site, value.try_as_time_samples()?)))
    {
        Some((site, mut raw)) => {
            site.offset.apply_to_samples(&mut raw);
            // The composed map is what a read would use, and is retimed the
            // same way; the authored one answers only when every sample is a
            // block, which resolves to nothing and reports no map at all.
            let mut samples = attribute.time_samples()?.unwrap_or(raw);
            resolve_samples(attribute, &mut samples)?;
            Some(samples)
        }
        None => None,
    };

    let default = match sites
        .iter()
        .find(|site| holds(stage, site, sdf::FieldKey::Default))
        .and_then(|site| authored(stage, site, sdf::FieldKey::Default))
    {
        Some(raw) => Some(attribute.get::<sdf::Value>()?.map_or(raw, bake_asset_paths)),
        None => None,
    };

    Ok(Held { default, samples })
}

/// Anchors every asset path in a sample map.
///
/// A sample map is copied rather than resolved — the value resolver hands one
/// back retimed but otherwise as authored — so each sample is re-read through
/// the resolver at its own time. A block resolves to nothing and is the one
/// sample worth keeping exactly as it was written.
fn resolve_samples(attribute: &Attribute, samples: &mut sdf::TimeSampleMap) -> Result<()> {
    if !samples.iter().any(|(_, value)| value.is_asset_valued()) {
        return Ok(());
    }
    let query = attribute.query();
    for (time, value) in samples {
        if let Some(resolved) = query.get_at::<sdf::Value>(super::TimeCode::from(*time))? {
            *value = bake_asset_paths(resolved);
        }
    }
    Ok(())
}

/// Whether a site authors `key` at all, without copying what it holds — a
/// sample map is answer enough to `is_some` and expensive to clone.
fn holds(stage: &Stage, site: &SpecSite, key: sdf::FieldKey) -> bool {
    stage
        .layer(&site.layer)
        .is_some_and(|layer| layer.data().has_field(&site.path, key.as_str()))
}

/// One field as a single site authored it.
fn authored(stage: &Stage, site: &SpecSite, key: sdf::FieldKey) -> Option<sdf::Value> {
    let layer = stage.layer(&site.layer)?;
    let value = layer.data().try_field(&site.path, key.as_str()).ok()??;
    Some(value.into_owned())
}

/// Every asset path in `value` as it means to be read from anywhere.
///
/// A flattened layer is anonymous, so it anchors nothing: a path left as
/// authored would resolve against whatever opened it, or against nothing.
/// Composition already worked out where each one points, and this writes that
/// answer down. A path nothing resolved is left as written, since there is no
/// better answer and a reader fails on it the way this stage did.
// TODO: composition anchors an asset value and not one nested in a dictionary
// — `is_asset_valued` says so — so a relative path inside `customData` reaches
// here unresolved and stays that way, losing the directory it was authored
// against. C++ anchors those too, over every value it copies.
fn bake_asset_paths(value: sdf::Value) -> sdf::Value {
    value.map_asset_paths(
        &mut |asset| match asset.resolved_path().or_else(|| asset.evaluated_path()) {
            Some(resolved) => sdf::AssetPath::with_resolved_path(resolved, resolved),
            None => asset,
        },
    )
}

/// Whether a field is one flattening writes down rather than resolves away.
///
/// `also_dropped` is what only one kind of spec sheds: the pseudo-root loses
/// the fields its layer stack owned, which no other spec carries.
fn copied(name: &str, also_dropped: &[sdf::FieldKey]) -> bool {
    !sdf::is_children_field(name) && !NOT_COPIED.iter().chain(also_dropped).any(|key| key.as_str() == name)
}

/// Writes every field composition left on a spec.
fn write_fields(data: &mut dyn sdf::AbstractData, path: &sdf::Path, fields: Vec<(String, sdf::Value)>) {
    for (key, value) in fields {
        data.set_field(path, &key, value);
    }
}

/// Writes a path list as the explicit list op one layer states it with.
fn write_explicit_paths(data: &mut dyn sdf::AbstractData, path: &sdf::Path, key: sdf::FieldKey, paths: Vec<sdf::Path>) {
    if paths.is_empty() {
        return;
    }
    data.set_field(path, key.as_str(), sdf::PathListOp::explicit(paths).into());
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use crate::{pcp, usd};

    /// Authors one layer, since every test here builds its input by hand.
    fn layer(name: &str, author: impl FnOnce(&mut dyn sdf::AbstractData)) -> sdf::Layer {
        let mut layer = sdf::Layer::new_in_memory(name);
        layer
            .edit(|edit| {
                author(edit.data_mut());
                Ok(())
            })
            .expect("authored");
        layer
    }

    /// Declares `/Prim.size` with a default.
    fn size_layer(name: &str, size: f64) -> sdf::Layer {
        layer(name, |data| {
            sdf::PrimSpec::new(data, "/Prim", sdf::Specifier::Def, "").expect("prim");
            sdf::AttributeSpec::new(
                data,
                "/Prim.size",
                sdf::ValueTypeName::DOUBLE,
                sdf::Variability::Varying,
                false,
            )
            .expect("attribute");
            data.set_field(
                &sdf::Path::new("/Prim.size").expect("path"),
                "default",
                sdf::Value::Double(size),
            );
        })
    }

    /// The answer composition gives is the one written down, once.
    #[test]
    fn strongest_value_written() {
        let stage = Stage::builder().make_stage(
            vec![size_layer("strong.usda", 2.0), size_layer("weak.usda", 1.0)],
            0,
            pcp::Diagnostics::default(),
        );

        let flattened = stage.flatten().expect("flattens");
        let value = flattened
            .attribute("/Prim.size")
            .expect("a path")
            .expect("the attribute")
            .get::<sdf::Value>("default")
            .expect("a default");
        assert_eq!(
            value,
            sdf::Value::Double(2.0),
            "the weaker layer is not consulted again"
        );
    }

    /// An arc is resolved, not copied: what it contributed is written where it
    /// landed, and the arc itself is gone.
    #[test]
    fn arcs_resolved_not_copied() {
        let root = layer("root.usda", |data| {
            sdf::PrimSpec::new(data, "/Class", sdf::Specifier::Class, "").expect("class");
            sdf::AttributeSpec::new(
                data,
                "/Class.color",
                sdf::ValueTypeName::DOUBLE,
                sdf::Variability::Varying,
                false,
            )
            .expect("attribute");
            data.set_field(
                &sdf::Path::new("/Class.color").expect("path"),
                "default",
                sdf::Value::Double(7.0),
            );

            sdf::PrimSpec::new(data, "/Prim", sdf::Specifier::Def, "").expect("prim");
            let inherits = sdf::PathListOp::explicit([sdf::Path::new("/Class").expect("path")]);
            data.set_field(
                &sdf::Path::new("/Prim").expect("path"),
                sdf::FieldKey::InheritPaths.as_str(),
                sdf::Value::PathListOp(inherits),
            );
        });
        let stage = Stage::builder().make_stage(vec![root], 0, pcp::Diagnostics::default());

        let flattened = stage.flatten().expect("flattens");
        let prim = flattened.prim("/Prim").expect("a path").expect("the prim");
        assert!(
            !prim.has_field(sdf::FieldKey::InheritPaths.as_str()),
            "the inherit would compose a second time"
        );
        let value = flattened
            .attribute("/Prim.color")
            .expect("a path")
            .expect("the inherited attribute is written where it landed")
            .get::<sdf::Value>("default");
        assert_eq!(value, Some(sdf::Value::Double(7.0)));
    }

    /// A relationship keeps its composed targets.
    #[test]
    fn targets_survive() {
        let root = layer("root.usda", |data| {
            sdf::PrimSpec::new(data, "/Target", sdf::Specifier::Def, "").expect("target");
            sdf::PrimSpec::new(data, "/Prim", sdf::Specifier::Def, "").expect("prim");
            sdf::RelationshipSpec::new(data, "/Prim.rel", sdf::Variability::Uniform, false).expect("rel");
            let targets = sdf::PathListOp::explicit([sdf::Path::new("/Target").expect("path")]);
            data.set_field(
                &sdf::Path::new("/Prim.rel").expect("path"),
                sdf::FieldKey::TargetPaths.as_str(),
                sdf::Value::PathListOp(targets),
            );
        });
        let stage = Stage::builder().make_stage(vec![root], 0, pcp::Diagnostics::default());

        let flattened = stage.flatten().expect("flattens");
        let targets = flattened
            .relationship("/Prim.rel")
            .expect("a path")
            .expect("the relationship")
            .get::<sdf::PathListOp>(sdf::FieldKey::TargetPaths.as_str())
            .expect("targets");
        assert_eq!(targets.explicit_items, vec![sdf::Path::new("/Target").expect("path")]);
    }

    /// A relationship keeps the variability it was declared with, either way.
    ///
    /// The field is authored only where it is uniform — the `rel` spelling —
    /// so an unauthored one is a `varying rel` and not an absent opinion.
    #[test]
    fn rel_variability_survives() {
        let root = layer("root.usda", |data| {
            sdf::PrimSpec::new(data, "/Prim", sdf::Specifier::Def, "").expect("prim");
            sdf::RelationshipSpec::new(data, "/Prim.plain", sdf::Variability::Uniform, false).expect("uniform");
            sdf::RelationshipSpec::new(data, "/Prim.loose", sdf::Variability::Varying, false).expect("varying");
        });
        let stage = Stage::builder().make_stage(vec![root], 0, pcp::Diagnostics::default());

        let flattened = stage.flatten().expect("flattens");
        let variability = |path: &str| {
            flattened
                .relationship(path)
                .expect("a path")
                .expect("the relationship")
                .get::<sdf::Variability>(sdf::FieldKey::Variability.as_str())
        };
        assert_eq!(variability("/Prim.plain"), Some(sdf::Variability::Uniform));
        assert_eq!(
            variability("/Prim.loose"),
            None,
            "varying is what an absent field means"
        );
    }

    /// A class prim is abstract, and a schema library is nothing else. The
    /// default traversal predicate skips every one of them.
    #[test]
    fn class_prims_survive() {
        let root = layer("root.usda", |data| {
            sdf::PrimSpec::new(data, "/Schema", sdf::Specifier::Class, "").expect("class");
            sdf::AttributeSpec::new(
                data,
                "/Schema.size",
                sdf::ValueTypeName::DOUBLE,
                sdf::Variability::Varying,
                false,
            )
            .expect("attribute");
            data.set_field(
                &sdf::Path::new("/Schema.size").expect("path"),
                "default",
                sdf::Value::Double(3.0),
            );
        });
        let stage = Stage::builder().make_stage(vec![root], 0, pcp::Diagnostics::default());

        let flattened = stage.flatten().expect("flattens");
        let prim = flattened.prim("/Schema").expect("a path").expect("the class prim");
        assert_eq!(prim.specifier(), Some(sdf::Specifier::Class));
        assert_eq!(
            flattened
                .attribute("/Schema.size")
                .expect("a path")
                .expect("its attribute")
                .get::<sdf::Value>("default"),
            Some(sdf::Value::Double(3.0))
        );
    }

    /// A connected attribute stays connected: nothing else writes the composed
    /// connections back.
    #[test]
    fn connections_survive() {
        let root = layer("root.usda", |data| {
            sdf::PrimSpec::new(data, "/Prim", sdf::Specifier::Def, "").expect("prim");
            for name in ["/Prim.source", "/Prim.sink"] {
                sdf::AttributeSpec::new(data, name, sdf::ValueTypeName::DOUBLE, sdf::Variability::Varying, false)
                    .expect("attribute");
            }
            let connections = sdf::PathListOp::explicit([sdf::Path::new("/Prim.source").expect("path")]);
            data.set_field(
                &sdf::Path::new("/Prim.sink").expect("path"),
                sdf::FieldKey::ConnectionPaths.as_str(),
                sdf::Value::PathListOp(connections),
            );
        });
        let stage = Stage::builder().make_stage(vec![root], 0, pcp::Diagnostics::default());

        let flattened = stage.flatten().expect("flattens");
        let connections = flattened
            .attribute("/Prim.sink")
            .expect("a path")
            .expect("the attribute")
            .get::<sdf::PathListOp>(sdf::FieldKey::ConnectionPaths.as_str())
            .expect("connections");
        assert_eq!(
            connections.explicit_items,
            vec![sdf::Path::new("/Prim.source").expect("path")]
        );
    }

    /// An asset path is written as the one composition resolved, since the
    /// flattened layer anchors nothing and a relative path in it would mean
    /// something else wherever it was read.
    #[test]
    fn asset_paths_anchored() {
        let directory = tempfile::tempdir().expect("tempdir");
        let target = directory.path().join("texture.png");
        fs::write(&target, "").expect("write");
        let root_path = directory.path().join("root.usda");

        let root = layer(&root_path.to_string_lossy(), |data| {
            sdf::PrimSpec::new(data, "/Prim", sdf::Specifier::Def, "").expect("prim");
            sdf::AttributeSpec::new(
                data,
                "/Prim.file",
                sdf::ValueTypeName::ASSET,
                sdf::Variability::Varying,
                false,
            )
            .expect("attribute");
            data.set_field(
                &sdf::Path::new("/Prim.file").expect("path"),
                "default",
                sdf::Value::AssetPath(sdf::AssetPath::new("./texture.png")),
            );
        });
        let stage = Stage::builder().make_stage(vec![root], 0, pcp::Diagnostics::default());

        let flattened = stage.flatten().expect("flattens");
        let value = flattened
            .attribute("/Prim.file")
            .expect("a path")
            .expect("the attribute")
            .get::<sdf::Value>("default")
            .expect("a default");
        let sdf::Value::AssetPath(asset) = value else {
            panic!("an asset value");
        };
        assert!(
            !asset.asset_path().starts_with("./"),
            "a relative path resolves against whatever opens the layer: {}",
            asset.asset_path()
        );
    }

    /// A sample map of nothing but blocks is kept.
    ///
    /// Blocks supply no value, so a read reports no samples at all; taking that
    /// as "none authored" would write the default and let it answer at times
    /// the blocks were hiding it from.
    #[test]
    fn blocked_samples_survive() {
        let root = layer("root.usda", |data| {
            sdf::PrimSpec::new(data, "/Prim", sdf::Specifier::Def, "").expect("prim");
            sdf::AttributeSpec::new(
                data,
                "/Prim.size",
                sdf::ValueTypeName::DOUBLE,
                sdf::Variability::Varying,
                false,
            )
            .expect("attribute");
            let path = sdf::Path::new("/Prim.size").expect("path");
            data.set_field(&path, "default", sdf::Value::Double(1.0));
            let samples: sdf::TimeSampleMap = vec![(0.0, sdf::Value::ValueBlock)];
            data.set_field(&path, "timeSamples", sdf::Value::TimeSamples(samples));
        });
        let stage = Stage::builder().make_stage(vec![root], 0, pcp::Diagnostics::default());

        let flattened = stage.flatten().expect("flattens");
        let reopened = Stage::builder().make_stage(vec![flattened], 0, pcp::Diagnostics::default());
        let value = reopened
            .prim("/Prim")
            .expect("the prim")
            .attribute("size")
            .get_at::<f64>(usd::TimeCode::from(0.0))
            .expect("a read");
        assert_eq!(value, None, "the block still hides the default at that time");
    }

    /// An asset path inside a sample is written as the one composition
    /// resolved, like any other. The map is copied rather than resolved, so
    /// nothing else would anchor it.
    #[test]
    fn sampled_asset_paths_anchored() {
        let directory = tempfile::tempdir().expect("tempdir");
        fs::write(directory.path().join("texture.png"), "").expect("write");
        let root_path = directory.path().join("root.usda");

        let root = layer(&root_path.to_string_lossy(), |data| {
            sdf::PrimSpec::new(data, "/Prim", sdf::Specifier::Def, "").expect("prim");
            sdf::AttributeSpec::new(
                data,
                "/Prim.file",
                sdf::ValueTypeName::ASSET,
                sdf::Variability::Varying,
                false,
            )
            .expect("attribute");
            let samples: sdf::TimeSampleMap = vec![(0.0, sdf::Value::AssetPath(sdf::AssetPath::new("./texture.png")))];
            data.set_field(
                &sdf::Path::new("/Prim.file").expect("path"),
                "timeSamples",
                sdf::Value::TimeSamples(samples),
            );
        });
        let stage = Stage::builder().make_stage(vec![root], 0, pcp::Diagnostics::default());

        let flattened = stage.flatten().expect("flattens");
        let samples = flattened
            .attribute("/Prim.file")
            .expect("a path")
            .expect("the attribute")
            .get::<sdf::TimeSampleMap>("timeSamples")
            .expect("samples");
        let sdf::Value::AssetPath(asset) = &samples[0].1 else {
            panic!("an asset sample");
        };
        assert!(
            !asset.asset_path().starts_with("./"),
            "a relative path resolves against whatever opens the layer: {}",
            asset.asset_path()
        );
    }

    /// Authors a two-layer stack: `root.usda` sublayering `sub.usda`.
    fn stack(root: impl FnOnce(&mut dyn sdf::AbstractData), sub: impl FnOnce(&mut dyn sdf::AbstractData)) -> Stage {
        let sublayer = layer("sub.usda", sub);
        let root = layer("root.usda", |data| {
            data.set_field(
                &sdf::Path::abs_root(),
                sdf::FieldKey::SubLayers.as_str(),
                sdf::Value::StringVec(vec!["sub.usda".to_owned()]),
            );
            root(data);
        });
        Stage::builder().make_stage(vec![root, sublayer], 0, pcp::Diagnostics::default())
    }

    /// Declares `/Prim.size` and authors `field` on it.
    fn size_opinion(field: &'static str, value: sdf::Value) -> impl FnOnce(&mut dyn sdf::AbstractData) {
        move |data: &mut dyn sdf::AbstractData| {
            sdf::PrimSpec::new(data, "/Prim", sdf::Specifier::Def, "").expect("prim");
            sdf::AttributeSpec::new(
                data,
                "/Prim.size",
                sdf::ValueTypeName::DOUBLE,
                sdf::Variability::Varying,
                false,
            )
            .expect("attribute");
            data.set_field(&sdf::Path::new("/Prim.size").expect("path"), field, value);
        }
    }

    /// The two value opinions resolve by different walks, and a flattened
    /// layer has to answer both the way the stage did.
    ///
    /// A numeric time takes the strongest site holding either opinion, so a
    /// stronger `default` hides weaker samples. The default time skips samples
    /// altogether, so a weaker `default` still answers under stronger samples.
    #[test]
    fn both_value_opinions_answer() {
        let hidden = stack(
            size_opinion("default", sdf::Value::Double(1.0)),
            size_opinion(
                "timeSamples",
                sdf::Value::TimeSamples(vec![(0.0, sdf::Value::Double(9.0))]),
            ),
        );
        let flattened = hidden.flatten().expect("flattens");
        let reopened = Stage::builder().make_stage(vec![flattened], 0, pcp::Diagnostics::default());
        assert_eq!(
            reopened
                .prim("/Prim")
                .expect("the prim")
                .attribute("size")
                .get_at::<f64>(usd::TimeCode::from(0.0))
                .expect("a read"),
            Some(1.0),
            "the stronger default hides the weaker samples at every time"
        );

        let both = stack(
            size_opinion(
                "timeSamples",
                sdf::Value::TimeSamples(vec![(0.0, sdf::Value::Double(9.0))]),
            ),
            size_opinion("default", sdf::Value::Double(1.0)),
        );
        let flattened = both.flatten().expect("flattens");
        let reopened = Stage::builder().make_stage(vec![flattened], 0, pcp::Diagnostics::default());
        let attribute = reopened.prim("/Prim").expect("the prim").attribute("size");
        assert_eq!(
            attribute.get_at::<f64>(usd::TimeCode::from(0.0)).expect("a read"),
            Some(9.0),
            "the stronger samples answer a numeric time"
        );
        assert_eq!(
            attribute.get::<f64>().expect("a read"),
            Some(1.0),
            "and the weaker default still answers the default time"
        );
    }

    /// A value is written as composition resolved it, not as its layer wrote
    /// it: an offset retimes a time code on the way through.
    #[test]
    fn defaults_are_composed() {
        let sublayer = layer("sub.usda", |data| {
            sdf::PrimSpec::new(data, "/Prim", sdf::Specifier::Def, "").expect("prim");
            sdf::AttributeSpec::new(
                data,
                "/Prim.frame",
                sdf::ValueTypeName::TIME_CODE,
                sdf::Variability::Varying,
                false,
            )
            .expect("attribute");
            data.set_field(
                &sdf::Path::new("/Prim.frame").expect("path"),
                "default",
                sdf::Value::TimeCode(sdf::TimeCode::from(1.0)),
            );
        });
        let root = layer("root.usda", |data| {
            data.set_field(
                &sdf::Path::abs_root(),
                sdf::FieldKey::SubLayers.as_str(),
                sdf::Value::StringVec(vec!["sub.usda".to_owned()]),
            );
            data.set_field(
                &sdf::Path::abs_root(),
                sdf::FieldKey::SubLayerOffsets.as_str(),
                sdf::Value::LayerOffsetVec(vec![sdf::LayerOffset::new(10.0, 1.0)]),
            );
        });
        let stage = Stage::builder().make_stage(vec![root, sublayer], 0, pcp::Diagnostics::default());

        let composed = stage
            .prim("/Prim")
            .expect("the prim")
            .attribute("frame")
            .get::<sdf::TimeCode>()
            .expect("a read")
            .expect("a value");

        let flattened = stage.flatten().expect("flattens");
        let written = flattened
            .attribute("/Prim.frame")
            .expect("a path")
            .expect("the attribute")
            .get::<sdf::TimeCode>("default")
            .expect("a default");
        assert_eq!(written, composed, "the offset is applied once, by composition");
    }

    /// The flattened layer stands alone: opened by itself it answers what the
    /// stage it came from answered.
    #[test]
    fn stands_alone() {
        let stage = Stage::builder().make_stage(
            vec![size_layer("strong.usda", 2.0), size_layer("weak.usda", 1.0)],
            0,
            pcp::Diagnostics::default(),
        );
        let flattened = stage.flatten().expect("flattens");

        let reopened = Stage::builder().make_stage(vec![flattened], 0, pcp::Diagnostics::default());
        let value = reopened
            .prim("/Prim")
            .expect("the prim")
            .attribute("size")
            .get::<f64>()
            .expect("a read");
        assert_eq!(value, Some(2.0));
    }
}
