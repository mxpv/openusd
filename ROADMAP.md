# Roadmap and Spec Compliance

Feature parity with the [AOUSD Core Specification v1.0.1](docs/aousd_core_spec_1.0.1.pdf) and the C++ reference implementation ([OpenUSD](https://github.com/PixarAnimationStudios/OpenUSD)).

Legend: :white_check_mark: Supported | :construction: Planned | :thinking: Considering

Status is scoped to the feature text in each row. If the implementation covers
only part of the referenced spec section, the notes call out what remains before
that broader spec behavior can be considered fully covered.

## Foundational Data Types (Spec 6)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Scalar types (bool, int, float, double, half, string, token, asset, timecode, int64, uint, uint64, uchar) | `6.2` | :white_check_mark: | `0.1.1` | `sdf::Value` enum |
| Dimensioned types (vectors, matrices, quaternions) | `6.3` | :white_check_mark: | `0.1.2` | float2..4, double2..4, matrix2d..4d, quath/f/d, int2..4, half2..4 |
| Algebraic types (opaque) | `6.4` | :white_check_mark: | `0.2.0` | An `opaque` attribute carries no value and is stored as its `typeName` alone |
| Semantic aliases (color, normal, point, vector, texCoord, frame) | `6.5` | :white_check_mark: | `0.7.0` | `sdf::Role`, `sdf::ValueTypeName::role` / `agrees_with` (§6.5.1), `usd::Attribute::role` |
| Arrays | `6.6.1` | :white_check_mark: | `0.7.0` | Every scalar and dimensioned array form of the §16.3.10.1 type table, round-tripping through both formats |
| Dictionaries | `6.6.2` | :white_check_mark: | `0.1.2` | Including nested dictionaries |
| Dictionary combining | `6.6.2.1` | :white_check_mark: | `0.4.0` | Recursive merge of stronger/weaker dictionaries during value resolution |
| [List operations](https://openusd.org/release/glossary.html#usdglossary-listediting) (explicit, composable) | `6.6.3` | :white_check_mark: | `0.2.0` | int, int64, uint, uint64, token, string, path, reference, payload |
| List op combining | `6.6.3.6` | :white_check_mark: | `0.2.0` | `ListOp::combined_with` |
| List op reducing | `6.6.3.8` | :white_check_mark: | `0.2.0` | `ListOp::reduced` |
| List op chaining | `6.6.3.9` | :white_check_mark: | `0.2.0` | Applied during composition arc evaluation |

## Document Data Model (Spec 7)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Layer structure (specs, paths, fields) | `7.2` | :white_check_mark: | `0.1.1` | `AbstractData` trait |
| Spec forms (layer, prim, attribute, relationship, variant set, variant) | `7.3` | :white_check_mark: | `0.1.1` | `SpecType` enum |
| Core metadata fields (layer spec) | `7.6.1` | :white_check_mark: | `0.1.2` | subLayers, subLayerOffsets, defaultPrim, documentation, etc. |
| Core metadata fields (prim spec) | `7.6.2` | :white_check_mark: | `0.1.2` | specifier, primChildren, propertyChildren, references, payload, inherits, specializes, variantSets, variantSelection, etc. |
| Core metadata fields (attribute spec) | `7.6.3` | :white_check_mark: | `0.1.2` | typeName, default, timeSamples, connectionPaths, variability, custom |
| Core metadata fields (relationship spec) | `7.6.4` | :white_check_mark: | `0.1.2` | targetPaths, variability, custom |
| Core metadata fields (variant set/variant spec) | `7.6.5-7` | :white_check_mark: | `0.2.0` | |
| Spline specialized type | `7.4.2.4` | :construction: | | A USDA `.spline` block round-trips as a dictionary (`usda::types::parse_spline`)<br>Remaining — typed knots, interpolation and extrapolation; USDC encoding; evaluation during value resolution; authoring |
| Retiming specialized type ([layer offsets](https://openusd.org/release/glossary.html#usdglossary-layeroffset)) | `7.6.1.2.2` | :white_check_mark: | `0.1.2` | `0.1.2` — parsed from `subLayerOffsets`<br>`0.4.0` — composed through arcs<br>`0.5.0` — applied during value resolution (§12.3.2.1) |

## Paths (Spec 8)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Absolute/relative paths | `8.1` | :white_check_mark: | `0.1.1` | `sdf::Path` |
| Prim paths | `8.1` | :white_check_mark: | `0.1.1` | |
| Property paths | `8.1` | :white_check_mark: | `0.1.1` | |
| Variant selection paths | `8.1` | :white_check_mark: | `0.2.0` | `{set=selection}` syntax |
| Path grammar (PEG) | `8.5` | :white_check_mark: | `0.1.4` | Parsed from USDA and USDC |
| Element ordering | `8.2` | :white_check_mark: | `0.5.0` | `sdf::element_cmp` |
| Relative path resolution | `8.1` | :white_check_mark: | `0.2.0` | Anchoring via `make_absolute` |
| Legacy path compatibility | `8.7` | :white_check_mark: | `0.7.0` | `sdf::Path` parses `[target]`, `.mapper[..].arg` and `.expression` tails and hyphenated variant set names; `Path::embedded_target_path` |

## Resource Interface (Spec 9)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Resource identifiers (URI) | `9.2` | :white_check_mark: | `0.1.1` | Asset paths via `sdf::AssetPath` (`asset` / `asset[]`) |
| Relative resource identifiers (anchored) | `9.4.1` | :white_check_mark: | `0.2.0` | `./` and `../` resolution relative to containing layer; `ar::DefaultResolver` reads `\` as a separator on every host |
| Non-anchored identifiers (search paths) | `9.4.2` | :white_check_mark: | `0.2.0` | `DefaultResolver` with search paths |
| Resolving identifiers to locations | `9.5` | :white_check_mark: | `0.2.0` | `Resolver` trait |
| Resolving extensions | `9.6` | :white_check_mark: | `0.2.0` | `.usd`/`.usda`/`.usdc`/`.usdz` dispatch |
| Packaged resources | `9.7` | :white_check_mark: | `0.2.0` | `asset.usdz[sublayer.usd]` syntax; a package nested in a package (`outer.usdz[inner.usdz[layer.usd]]`) resolves and reads one bracket at a time |
| `file` URI scheme ([RFC 8089](https://datatracker.ietf.org/doc/html/rfc8089)) | `9.8` | :construction: | | Filesystem paths accepted but not as `file:///` URIs |
| `usd-anon` scheme (in-memory resources) | `9.8.1` | :white_check_mark: | `0.4.0` | `sdf::Layer::new_anonymous` / `is_anonymous`; identifiers spelled `anon:<n>:<tag>` as in C++, never used as an anchor |

## Composition (Spec 10)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [Sublayers](https://openusd.org/release/glossary.html#usdglossary-sublayers) | `10.3.1` | :white_check_mark: | `0.1.2` | Layer stack construction |
| Sublayer offset composition | `10.3.1.1` | :white_check_mark: | `0.4.0` | Effective offsets composed through nested sublayers and applied during value resolution (§12.3.2.1); `scale <= 0` falls back to identity |
| [References](https://openusd.org/release/api/class_usd_references.html) (internal + external) | `10.3.2.1` | :white_check_mark: | `0.1.2` | Including `defaultPrim` fallback |
| Reference [namespace mapping](https://openusd.org/release/api/class_pcp_map_function.html) | `10.3.2.1.1` | :white_check_mark: | `0.3.0` | `MapFunction` with source/target pairs |
| Reference offset composition | `10.3.2.1.2` | :white_check_mark: | `0.4.0` | Reference offsets composed with target layer-stack offsets and applied during value resolution (§12.3.2.1); `scale <= 0` falls back to identity |
| [Payloads](https://openusd.org/release/api/class_usd_payloads.html) | `10.3.2.2` | :white_check_mark: | `0.1.2` | Composed like references through their own `EvalNodePayloads` task, gated by load rules |
| [Payload loading control](https://openusd.org/release/api/class_usd_stage_load_rules.html) | `10.3.2.2` | :white_check_mark: | `0.7.0` | `0.6.0` — `pcp::LoadRules` and `usd::LoadPolicy`, reached through `Stage::load` / `unload` / `set_load_rules` / `find_loadable`; `StageBuilder::load` sets the initial load set<br>`0.7.0` — `pcp::LoadRules::is_loaded_with_all_descendants` / `is_loaded_with_no_descendants`, and per-prim `usd::Prim::load` / `unload` |
| Payload offset composition | `10.3.2.2.2` | :white_check_mark: | `0.4.0` | Loaded payload offsets compose like reference offsets and are applied during value resolution (§12.3.2.1); an unloaded payload contributes none; `scale <= 0` falls back to identity |
| [Inherits](https://openusd.org/release/api/class_usd_inherits.html) | `10.3.2.3` | :white_check_mark: | `0.2.0` | Including implied inherit propagation |
| Inherit namespace mapping (with identity) | `10.3.2.3.1` | :white_check_mark: | `0.3.0` | `from_pair_identity` adds `(/, /)` catch-all |
| [Specializes](https://openusd.org/release/api/class_usd_specializes.html) | `10.3.2.4` | :white_check_mark: | `0.2.0` | |
| Specializes global weakness | `10.4.1` | :white_check_mark: | `0.3.0` | Specializes nodes are copied under the local root (`propagate_node_to_root`, C++ `_PropagateNodeToRoot`); the strength-order DFS then places the globally weak band last |
| [Variants](https://openusd.org/release/api/class_usd_variant_sets.html) | `10.3.2.5` | :white_check_mark: | `0.2.0` | Including deferred evaluation after R/P |
| Variant selection computation | `10.3.2.5.1` | :white_check_mark: | `0.2.0` | Strongest opinion wins, searched strong-to-weak from the strongest mapped node; with no authored selection and no applicable fallback the set stays unselected, as in C++ |
| Variant fallback map | `10.3.2.5.1` | :white_check_mark: | `0.3.0` | `VariantFallbackMap` via `StageBuilder` |
| [Relocates](https://openusd.org/release/glossary.html#usdglossary-relocates) | `10.3.2.6` | :white_check_mark: | `0.3.0` | `layerRelocates`, source path resolution, child remapping |
| Relocates validation rules | `10.3.2.6` | :white_check_mark: | `0.5.0` | `pcp::InvalidRelocateReason`, `pcp::RelocateConflictReason`, and `CompositionDiagnostic::OpinionAtRelocationSource` |
| Relocates namespace mapping | `10.3.2.6.1` | :white_check_mark: | `0.3.0` | Composed with reference arc mappings |
| Arc permissions (`permission = private`) | `10.3.3` | :white_check_mark: | `0.6.0` | `sdf::Permission` is data-only; composition does not enforce it, as in C++'s `Usd`-mode caches |
| [LIVERPS strength ordering](https://openusd.org/release/glossary.html#livrps-strength-ordering) | `10.4` | :white_check_mark: | `0.3.0` | `ArcType` with `Ord` derived from discriminant |
| [Namespace mappings](https://openusd.org/release/api/class_pcp_map_function.html) (MapFunction) | `10.5` | :white_check_mark: | `0.3.0` | Compose, inverse, longest-prefix matching |
| Composition errors (non-fatal) | `10.6` | :white_check_mark: | `0.3.0` | `pcp::CompositionDiagnostic`, read through `Stage::composition_errors`; a missing or unreadable sublayer's diagnostic is suppressed while its branch is muted, and a target severed from composition retires its diagnostics at the next edit seam |
| List op arc computation | `10.3.2` | :white_check_mark: | `0.2.0` | Weakest-to-strongest list-op chaining |

## Stage Population (Spec 11)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Composed stage | `11.2` | :white_check_mark: | `0.2.0` | `Stage::open` with depth-first traversal |
| Populating the stage | `11.3` | :white_check_mark: | `0.2.0` | Lazy per-prim composition via `pcp::IndexCache` (C++ `PcpCache`) |
| [Population mask](https://openusd.org/release/api/class_usd_stage_population_mask.html) | `11.3` | :white_check_mark: | `0.4.0` | `StageBuilder::mask` limits stage queries and traversal to a masked working set; the arc targets of a masked-out prim are never opened, since layers load on composition demand |
| Prim child discovery | `11.3.1` | :white_check_mark: | `0.2.0` | Merged `primChildren` with relocate adjustment. Full normative ordering is tracked in the `primOrder` row below. |
| Ordered prim children (`primOrder` reordering) | `11.3.1` | :white_check_mark: | `0.5.0` | `Prim::children`; weak-to-strong fold reapplying `primOrder` per layer and each node's layer-stack relocates (a renamed child keeps the source's position; relocation sources are prohibited names) |
| Ordered property children | `11.3.2` | :white_check_mark: | `0.2.0` | Merged `propertyChildren` |
| Ordered property children (`propertyOrder` reordering) | `11.3.2` | :white_check_mark: | `0.5.0` | The composed `propertyOrder` is applied once after the `propertyChildren` fold (C++ `UsdPrim::ApplyPropertyOrder`), by `usd::Prim::property_names` / `authored_property_names`; the fold itself keeps authoring order, as C++'s USD mode does |
| Property children include schema declarations | `11.3.2` | :white_check_mark: | `0.7.0` | `usd::Prim::property_names` (C++ `UsdPrim::GetPropertyNames`); `usd::Prim::authored_property_names` for the authored names alone |
| [Scene graph instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) | `11.3.3` | :white_check_mark: | `0.8.0` | `0.5.0` — instances share one composed `/__Prototype_N` prototype, and instance proxies redirect onto it; covers nested instances, target remapping (§12.4), prototypes keyed by variant selection, and the population mask<br>`0.8.0` — a prototype root reads no opinions, as in C++; the instance key follows C++ `PcpInstanceKey` |
| Model hierarchy (kind) | `11.4` | :white_check_mark: | `0.4.0` | Model/group/component/subcomponent queries validate the contiguous kind hierarchy |
| [Stage queries](https://openusd.org/release/api/prim_flags_8h.html) (Active, Loaded, Defined, Abstract, Instance, InPrototype) | `11.5` | :white_check_mark: | `0.8.0` | `0.4.0` — per-prim status flags and `PrimPredicate` traversal filtering<br>`0.5.0` — `IN_PROTOTYPE` and the instance-proxy traversal toggle (see Scene graph instancing, §11.3.3)<br>`0.8.0` — the descendants of an inactive prim are off the stage, as in C++; `usd::PrimIndexRef` reads them at the composition tier |
| [Session layer](https://openusd.org/release/glossary.html#usdglossary-sessionlayer) | `11.2` | :white_check_mark: | `0.3.0` | `StageBuilder::session_layer` |

## Value Resolution (Spec 12)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Metadata resolution (strongest opinion wins) | `12.2` | :white_check_mark: | `0.2.0` | `ValueBlock` supported for scalar fields; the special field classes have their own rows below |
| Specifier resolution | `12.2.1` | :white_check_mark: | `0.4.0` | `def`/`class`/`over` precedence with direct-inherit awareness |
| typeName resolution (from prim definition) | `12.2.2` | :white_check_mark: | `0.7.0` | `usd::Attribute::type_name` (C++ `_GetAttrTypeImpl`); a schema declaration of `typeName`, `variability` or `custom` wins over composed opinions, through `get_metadata` too |
| variability resolution (weakest opinion) | `12.2.3` | :white_check_mark: | `0.4.0` | Weakest authored opinion wins |
| custom field resolution (any-true) | `12.2.4` | :white_check_mark: | `0.4.0` | Logical OR across opinions |
| Dictionary combining | `12.2.5` | :white_check_mark: | `0.4.0` | Recursive merge across dictionary-valued opinions |
| List op resolution | `12.2.6` | :white_check_mark: | `0.7.0` | Composition-arc list ops, `connectionPaths`/`targetPaths` target folding, and `clipSets` order folded across layers; any other list-op-valued field (composed `apiSchemas` included) folds generically during field resolution |
| Layer metadata (root layer only) | `12.2.7` | :white_check_mark: | `0.2.0` | `defaultPrim`, timing fields, etc. |
| Fallback values | `12.2.8` | :white_check_mark: | `0.8.0` | `usd::Attribute::get` / `get_at`, including for a blocked attribute (§12.3.6); `usd::Attribute::resolve_info` reports the source<br>The core `usd` family registers through `usd::SchemaRegistry::builder`, the domain families through `openusd_schemas::schema_registry` |
| Basic attribute resolution | `12.3` | :white_check_mark: | `0.7.0` | `0.2.0` — resolves authored `default`, `timeSamples`, and `ValueBlock`<br>`0.5.0` — layer-offset retiming applied<br>`0.7.0` — `asset` value resolution (`pcp::asset_resolve`)<br>Value clips and splines are tracked separately |
| Time-sample lookup and interpolation | `12.3, 12.5.1-2` | :white_check_mark: | `0.5.0` | `0.1.2` — time-sample parsing<br>`0.4.0` — held/linear interpolation over composed samples, read through `usd::Attribute::get_at`<br>`0.5.0` — per-node retiming and value clips |
| Layer-offset retiming during value resolution | `12.3.2.1` | :white_check_mark: | `0.7.0` | `0.5.0` — each node's sample times mapped to stage time through its composed offset (`stage_t = scale*layer_t + offset`; sublayer/reference/payload); strongest `timeSamples` node wins, `ValueBlock` blocks weaker layers<br>`0.7.0` — `timecode` values retimed through `sdf::LayerOffset::apply_to_value` (C++ `Usd_ApplyLayerOffsetToValue`), and inversely on authoring through `usd::EditTarget::map_to_spec_value`<br>Remaining — a clip-sourced `timecode` still resolves in clip time |
| Spline evaluation | `12.5.3` | :construction: | | Bezier/Hermite curve interpolation |
| Interpolation (Held) | `12.5.1` | :white_check_mark: | `0.4.0` | `usd::Attribute::get_at` under `InterpolationType::Held`, chosen per stage by `Stage::set_interpolation_type` / `StageBuilder::interpolation_type` |
| Interpolation (Linear) | `12.5.2` | :white_check_mark: | `0.4.0` | `usd::Attribute::get_at` under `InterpolationType::Linear` (the default)<br>All §12.5.2 types incl. `quath`/`f`/`d` via slerp<br>Held interpolation for types that cannot interpolate linearly and past the last sample |
| [Value clips](https://openusd.org/release/api/_usd__page__value_clips.html) | `12.3.4` | :white_check_mark: | `0.7.0` | `usd::ClipsAPI` (read + write); explicit and template (§12.3.4.1.3) clip sets, manifest gating, stage-to-clip time mapping with jumps, and `interpolateMissingClipValues`<br>`usd::ClipsAPI::generate_clip_manifest`; a set with no `manifestAssetPath` is gated by a manifest synthesized from its clips (§12.3.4.1.1.2)<br>`usd::Attribute::time_sample_times` includes each clip's activation time (C++ `Usd_Clip::ListTimeSamplesForPath`)<br>Clip-sourced `asset` values resolve through `pcp::AssetSite::in_clip`, and a `${VAR}` in the `clips` asset paths evaluates |
| Relationship targets (raw + forwarded) | `12.4` | :white_check_mark: | `0.5.0` | Composed raw `targetPaths`, folding list-op edits across contributing layers and remapping through arcs<br>Forwarded targets recursively chase relationship-to-relationship chains to prim/attribute terminals with cycle breaking and dedup |
| Attribute connections | `12.4` | :white_check_mark: | `0.5.0` | Composed `connectionPaths` folding list-op edits across contributing layers, with authoring on `Attribute`<br>Stage-wide connection graph indexes every edge and resolves chains to terminal sources |

## Schemas (Spec 13)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [Schema registry](https://openusd.org/release/api/class_usd_schema_registry.html) | `13.3` | :white_check_mark: | `0.8.0` | `usd::SchemaRegistry` over `usd::FamilySource` pairs (schematics + manifest), with `usd::SchemaInfo`, `usd::PrimDefinition` and a `usd::PrimTypeInfo` interner; per-stage through `usd::StageBuilder::schema_registry` |
| [Typed schemas](https://openusd.org/release/api/class_usd_typed.html) (IsA) | `13.3.1` | :white_check_mark: | `0.7.0` | `usd::Prim::is_a` over the whole base chain, `fallbackPrimTypes` resolved; family queries through `usd::VersionFilter` and `usd::Prim::is_in_family` |
| [Applied schemas](https://openusd.org/release/api/class_usd_a_p_i_schema_base.html) (HasA) | `13.3.2` | :white_check_mark: | `0.7.0` | `apiSchemas` list-ops compose into `usd::Prim::prim_definition`; `usd::Prim::apply_api` and `can_apply_api` validate, reporting `usd::ApplyApiError` |
| Schema inclusions (built-ins, auto-applies) | `13.3.2.1` | :white_check_mark: | `0.7.0` | Built-in `apiSchemas` expand recursively and cycle-guarded, multiple-apply templates per instance name; `apiSchemaAutoApplyTo` resolved at registry build |
| Prim definitions (property fallbacks) | `13.3` | :white_check_mark: | `0.7.0` | `usd::PrimDefinition` composes the typed and applied tiers per §13.3.2.3 |
| Core schema types | `13.4` | :white_check_mark: | `0.8.0` | The `usd` family in `usd::SCHEMAS`, registered by `SchemaRegistryBuilder::default`, with generated views: `usd::CollectionAPI`, `usd::ClipsAPI`, `usd::ModelAPI`, `usd::ColorSpaceAPI`, `usd::ColorSpaceDefinitionAPI` |
| [Value type names](https://openusd.org/release/api/class_sdf_value_type_name.html) | `13.3` | :white_check_mark: | `0.7.0` | `sdf::ValueTypeName`, `sdf::ValueKind`, `sdf::Dimensions`, `sdf::Unit`, resolved through one table by the parser, the writer and every setter; an unregistered type or field keeps its literal as `sdf::Value::UnregisteredValue`<br>Verified against usd-core 26.8 in both directions |
| Extension metadata fields (fallbackPrimTypes, apiSchemas, clips, clipSets) | `13.2` | :white_check_mark: | `0.7.0` | `apiSchemas` list-op composition, `clips` / `clipSets` value-clip semantics (§12.3.4), and `fallbackPrimTypes` substitution for a `typeName` the registry does not know |
| [Schema codegen](https://openusd.org/release/tut_generating_new_schema.html) | `13.3` | :white_check_mark: | `0.8.0` | `openusd_build::configure` in a build script, `openusd::include_schema!` at the use site; `openusd_build::TokenEnum` for `allowedTokens`<br>Per property: the reader, the creator, and the declaration itself as a builder (`<name>_attr_builder`) for authoring a value in the same edit. Per multiple-apply schema: `is_schema_property_base_name` and `instance_at_path`, which read an instance back out of a property path (C++ `Is<Name>Path`)<br>`reflectedAPISchemas` across libraries (`Class::reflections`, `Library::reflected`); a redeclaration that changes a property's composed shape is refused (`Violation::IncompatibleRedeclaration`)<br>Doxygen documentation converted to Markdown in `openusd_build`'s `doc`, linking classes of placed libraries under their `libraryPrefix` spelling<br>Typed reads per attribute (`<name>()`, `<name>_at`); metadata fields from `plugInfo.json` (`Builder::plug_info`, generated `AttributeMetadata` and sibling traits); shader-node views from `shaderDefs.usda` (`Builder::shader_defs`) |

## Color (Spec 14)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Supported color spaces | `14.1` | :thinking: | | |
| Core metadata extensions (colorSpace) | `14.2` | :construction: | | `sdf::FieldKey::ColorSpace`, `usd::Attribute::set_color_space`, `usd::ColorSpaceAPI`<br>Remaining — `ComputeColorSpaceName` |
| ColorSpaceDefinitionAPI | `14.3` | :construction: | | `usd::ColorSpaceDefinitionAPI`<br>Remaining — resolving a definition to a color space |

## Collections (Spec 15)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [CollectionAPI](https://openusd.org/release/api/class_usd_collection_a_p_i.html) | `15.1` | :white_check_mark: | `0.8.0` | Multi-apply `usd::CollectionAPI` (generated view); a schema's built-in collections take the fallbacks it declares (`LightAPI` light linking); authoring via `apply_collection` and `include_path` / `exclude_path` with edit minimization<br>Instance names validated by `usd::SchemaRegistry::is_allowed_instance_name`, namespaced ones included; discovery through `CollectionAPI::get_all` and `CollectionAPI::instance_at_path`<br>Pattern-based expression mode: `sdf::PathExpression` + `sdf::path_expr::PathExpressionEval` with `sdf::path_expr::IncrementalSearcher` for traversal-order enumeration, `%_` composition and cross-arc mapping during field resolution, `usd::resolve_complete_membership_expression`, and the collection predicate library |
| Authoring and evaluating collections | `15.2` | :white_check_mark: | `0.7.0` | `MembershipQuery` (closest-ancestor `is_path_included`, rule-map-wins expression dispatch), `compute_membership_query` with nested-collection merge + cycle guard, and `compute_included_paths` stage traversal (excludes precedence, property expansion, constancy-pruned expression enumeration) |

## Core File Formats (Spec 16)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| USDA (text) reading | `16.2` | :white_check_mark: | `0.1.4` | Recursive descent parser with logos tokenizer |
| USDA (text) writing | `16.2` | :white_check_mark: | `0.4.0` | `usda::TextWriter`; round-trips the compliance suite opinion-for-opinion |
| USDC (binary) reading | `16.3` | :white_check_mark: | `0.1.1` | Crate format with LZ4/integer compression |
| USDC (binary) writing | `16.3` | :white_check_mark: | `0.4.0` | `usdc::CrateWriter`; streaming packer with integer compression, LZ4 blocks, DFS path encoder |
| USDZ (package) reading | `16.4` | :white_check_mark: | `0.2.0` | ZIP-based package reader; a nested `.usdz` entry reads as its default layer |
| USDZ (package) writing | `16.4` | :white_check_mark: | `0.4.0` | `usdz::ArchiveWriter`; STORED-only, 64-byte aligned entries |
| Format auto-detection (`.usd`) | `16.1` | :white_check_mark: | `0.2.0` | Magic byte detection |

## Beyond Core Spec

Features from the C++ reference implementation not covered by the core specification.

| Feature | Status | Version | Notes |
|---|---|---|---|
| [Variable expressions](https://openusd.org/release/api/_sdf__page__variable_expressions.html) | :white_check_mark: | `0.7.0` | `sdf::expr`: 13 built-in functions and string interpolation<br>Session and root layer `expressionVariables` compose (`sdf::expr::stack_expression_variables`, C++ `PcpExpressionVariables`), and a session opinion can select the root's `${VAR}` sublayers; a sublayer newly selected by a runtime edit loads on demand<br>Value-time expression failures reach `Stage::composition_errors` (C++ `Usd_AssetPathContext`) |
| Parallelism (Rayon) | :construction: | | Composition graph is `&`-only, ready for parallel execution |
| Memory-mapped layers | :white_check_mark: | `0.8.0` | Mapping is an `unsafe` opt-in, `ar::DefaultResolver::map_files`. See `ar::SharedBuffer`, `ar::CacheScope`, `sdf::Layer::save` |
| [Incremental invalidation](https://openusd.org/release/api/class_pcp_changes.html) | :white_check_mark: | `0.7.0` | `pcp::Changes` over each `sdf::ChangeList`, scoped by `pcp::Dependencies`; an edit drops only the affected indices, a value edit stamps the affected prims with a fresh `pcp::PrimRevision`, and an inert spec add or remove splices the refreshed runs into the memoized spec stack (C++ `Pcp_RescanForSpecs`)<br>Value-time `asset` expressions resync through `CommittedChange::asset_paths_resynced` |
| [UsdGeom](https://openusd.org/release/api/usd_geom_page_front.html) (geometry, transforms, cameras) | :white_check_mark: | `0.8.0` | Generated views behind `geom` for every class, the `PrimvarsAPI`, `VisibilityAPI`, `ModelAPI` and `MotionAPI` schemas included; `geom::Primvar` (C++ `UsdGeomPrimvar`: indexed values, `compute_flattened`) and the `PrimvarsAPI` queries with inheritance down the namespace; `geom::ImageableExt` (C++ `ComputeVisibility` / `ComputeEffectiveVisibility` / `ComputePurpose`), the `geom::MotionAPI` computations, `geom::XformableExt` / `geom::XformQuery` (the `xformOpOrder` evaluator), and `geom::XformCache`<br>Remaining — `ComputeModelDrawMode`; `BBoxCache` |
| [UsdShade](https://openusd.org/release/api/usd_shade_page_front.html) (materials, shaders) | :white_check_mark: | `0.5.0` | Generated views behind `shade`, with `Connectable`, `Input`, `Output`, `ConnectionTarget`, `ConnectedSources`, `ShadingAttribute`, `ProducerFilter`, `ResolvedTerminal`, `InterfaceInputConsumersMap`, `ImplementationSource`, `SdrMetadata`, Shader / NodeGraph / Material, MaterialBindingAPI, and the UsdPreviewSurface reader<br>Remaining — Material base-material; `CoordSysAPI` behavior; the Sdr shader registry behind `GetShaderNodeForSourceType`; renderer shader dialects (MDL / MaterialX) |
| [UsdLux](https://openusd.org/release/api/usd_lux_page_front.html) (lighting) | :white_check_mark: | `0.4.0` | Generated views behind `lux` (built on the `geom` chain); lights are `Xformable` / `Boundable` prims through `BoundableLightBase` / `NonboundableLightBase`, sharing the `LightAPI` interface: the 8 concrete lights and `DomeLight_1`, `PluginLight`, `LightFilter` / `PluginLightFilter`, and the applied `LightAPI` / `MeshLightAPI` / `VolumeLightAPI` / `ShapingAPI` / `ShadowAPI` / `LightListAPI` / `ListAPI` |
| [UsdSkel](https://openusd.org/release/api/usd_skel_page_front.html) (skeletons, skinning) | :white_check_mark: | `0.5.0` | Generated views behind `skel` (enables `geom`): `Root` / `Skeleton` as `Boundable`, `Animation` / `BlendShape` (incl. inbetween shapes), namespace-inherited `BindingAPI`; the object model (Topology, AnimMapper, SkeletonResolver, SkinningResolver, SkelAnimQuery over `Attribute::unioned_time_samples`, `discover_bindings`, pure-math LBS / blend shapes) |
| [UsdVol](https://openusd.org/release/api/usd_vol_page_front.html) (volumes) | :white_check_mark: | `0.8.0` | Generated views behind `vol` (built on the `geom` chain): `Volume` (a `Gprim` with `field:<name>` relationships) and the file-backed `OpenVDBAsset` / `Field3DAsset` (the shared `FieldAsset` attrs)<br>The `ParticleField*` Gaussian-splat schemas, each reflecting the attribute APIs its data comes from, with `vol::SplatData` and `vol::ParticleField3DGaussianSplat::attribute_in_use` / `uses_float` over the pairs they store at two precisions (C++ `UsesFloat*`) |
| [UsdPhysics](https://openusd.org/release/api/usd_physics_page_front.html) | :white_check_mark: | `0.8.0` | Generated views behind `physics`: all 8 typed prims (`Scene` / `CollisionGroup` / `Joint` + 5 joint subtypes sharing the `JointSchema` interface), the 7 single-apply API schemas, and the multi-apply `DriveAPI` / `LimitAPI` (per-DOF instance, with `Get` / `GetAll`)<br>Collision groups: `physics::CollisionGroup::colliders_collection` reaches the built-in collection each group holds, and `physics::compute_collision_group_table` resolves every group's `filteredGroups` / `invertFilteredGroups` / `mergeGroupName` into a `physics::CollisionGroupTable` of which pairs collide |
| [UsdRender](https://openusd.org/release/api/usd_render_page_front.html) | :white_check_mark: | `0.5.0` | Generated views behind `render`: the `SettingsBase` interface with typed `Settings` / `Product` / `Var` / `Pass`, `Settings::stage_settings_path` (C++ `GetStageRenderSettings`), and `compute_render_spec` (product-overrides-settings inheritance, aspect-ratio conform, render-var dedup, per-level `namespacedSettings`)<br>Remaining — RenderPass collection memberships; node-graph-driven namespaced settings; authoring `renderSettingsPrimPath` |
| [UsdMedia](https://openusd.org/release/api/usd_media_page_front.html) | :white_check_mark: | `0.5.0` | Generated views behind `media` (built on the `geom` chain): `SpatialAudio` (an `Xformable`: filePath / auralMode / playbackMode / startTime / endTime / mediaOffset / gain) and the applied `AssetPreviewsAPI` (default thumbnail via `assetInfo.previews`) |
| [UsdUI](https://openusd.org/release/api/usd_u_i_page_front.html) | :white_check_mark: | `0.5.0` | Generated views behind `ui`: the typed `Backdrop` prim, the single-apply `SceneGraphPrimAPI` (displayName / displayGroup) and `NodeGraphNodeAPI` (node-editor layout), and the multiple-apply `AccessibilityAPI` |
| [UsdProc](https://openusd.org/release/api/usd_proc_page_front.html) | :white_check_mark: | `0.5.0` | Generated view behind `proc` (built on the `geom` chain): `GenerativeProcedural` as a `Boundable` prim |
| [UsdSemantics](https://openusd.org/release/api/class_usd_semantics_labels_a_p_i.html) | :white_check_mark: | `0.8.0` | Schema view behind `semantics` feature: the multiple-apply `LabelsAPI`, whose instance name is the taxonomy its `semantics:labels:<taxonomy>` array labels a prim under, with `LabelsAPI::direct_taxonomies` / `inherited_taxonomies` and `LabelsQuery` (C++ `GetDirectTaxonomies` / `ComputeInheritedTaxonomies` / `UsdSemanticsLabelsQuery`) over a `gf::Interval` |
| [Flatten / export](https://openusd.org/release/api/flatten_utils_8h.html) | :white_check_mark: | `0.8.0` | `usd::Stage::flatten`, `sdf::Layer::export`<br>Remaining — preserving instancing (instances flatten to full copies); baking value-clip samples |
| [Namespace editing](https://openusd.org/release/api/class_usd_namespace_editor.html) | :white_check_mark: | `0.6.0` | [`usd::NamespaceEditor`](crates/openusd/src/usd/editor.rs): batched, atomic rename / reparent / delete with target and reference fixup, authoring relocates for cross-arc content |
| [Native instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) (shared representation) | :white_check_mark: | `0.5.0` | Scene-graph instancing (see §11.3.3) — instances share one composed prototype whose `/__Prototype_N` namespace is composed independently, onto which every instance proxy redirects |
| [Asset dependencies](https://openusd.org/release/api/usd_utils_page_front.html) | :white_check_mark: | `0.8.0` | `usd_utils::compute_all_dependencies` (C++ `UsdUtilsComputeAllDependencies`), `usd_utils::modify_asset_paths` (C++ `UsdUtilsModifyAssetPaths`), `usd_utils::create_new_usdz_package` (C++ `UsdUtilsCreateNewUsdzPackage`)<br>Remaining — UDIM tiles, clip templates and variable expressions, which the walk refuses where C++ expands or anchors them |
| [Stage cache](https://openusd.org/release/api/class_usd_utils_stage_cache.html) | :thinking: | | Avoid redundant stage loading |
| [Kind registry](https://openusd.org/release/api/class_kind_registry.html) | :white_check_mark: | `0.8.0` | `kind::Registry`, `kind::Decl`, `usd::SchemaFamily::kinds`, `usd::ModelAPI::is_kind` |
| [Edit targets](https://openusd.org/release/api/class_usd_edit_target.html) | :white_check_mark: | `0.6.0` | `usd::EditTarget` |
| [Change notification](https://openusd.org/release/api/class_usd_notice.html) | :white_check_mark: | `0.7.0` | `sdf::LayerSink` (layer commit seam) and `usd::StageSink` (composed changes, incl. `layer_muting_changed` / `load_rules_changed`); transferable `Diff` via `usd::UndoStage` / `usd::ReplayStage` and `Stage::apply_diff`<br>`CommittedChange::asset_paths_resynced` (C++ `GetResolvedAssetPathsResyncedPaths`) |
| [Property stack queries](https://openusd.org/release/api/class_usd_resolve_info.html) | :white_check_mark: | `0.8.0` | `usd::ResolveInfo` / `usd::ResolveInfoSource` / `pcp::ResolveNode`, via `Attribute::resolve_info` / `resolve_info_at`<br>`Attribute::property_stack_at`; the stack queries and `Prim::prim_stack` return `usd::SpecSite`, one offset-bearing spelling where C++ has two<br>Resolved over `pcp::value_resolve`, with value clips placed by `pcp::ClipAnchor` and gated by `pcp::IndexCache::may_have_clips`<br>`usd::ResolveInfo::spec_site` and `usd::ResolveInfo::weaker_sources` (C++ `GetNextWeakerInfo`), built by `pcp::Composing` across the `default`, `timeSamples` and clip sources and closed at the schema fallback by `pcp::Composing::close` |
