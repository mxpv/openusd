# Spec Compliance

Coverage of the
[AOUSD Core Specification v1.0.1](docs/aousd_core_spec_1.0.1.pdf), section by
section, followed by features of the C++ reference implementation
([OpenUSD](https://github.com/PixarAnimationStudios/OpenUSD)) that the
specification does not cover. The standard schema families (`UsdGeom`,
`UsdShade`, and the rest) are tracked in the
[`openusd-schemas` README](crates/openusd-schemas/README.md#schema-families).

Legend: :white_check_mark: Supported | :construction: Planned | :thinking: Considering

Status is scoped to the feature text in each row. If the implementation covers
only part of the referenced spec section, the notes call out what remains before
that broader spec behavior can be considered fully covered.

## Foundational Data Types (Spec 6)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Scalar types (bool, int, float, double, half, string, token, asset, timecode, int64, uint, uint64, uchar) | `6.2` | :white_check_mark: | `0.1.1` | `vt::Value` enum |
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
| Core metadata fields (variant set/variant spec) | `7.6.5-7` | :white_check_mark: | `0.2.0` | `sdf::PrimSpec::add_variant_set` / `add_variant` / `set_variant_selection` |
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
| Legacy path compatibility | `8.7` | :white_check_mark: | `0.7.0` | `sdf::Path` parses target, mapper and expression tails and hyphenated variant set names |

## Resource Interface (Spec 9)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Resource identifiers (URI) | `9.2` | :white_check_mark: | `0.1.1` | Asset paths via `sdf::AssetPath` (`asset` / `asset[]`) |
| Relative resource identifiers (anchored) | `9.4.1` | :white_check_mark: | `0.2.0` | `sdf::Layer::absolute_path`<br>Remaining — file format arguments (`:SDF_FORMAT_ARGS:`) are anchored as part of the path |
| Non-anchored identifiers (search paths) | `9.4.2` | :white_check_mark: | `0.2.0` | `DefaultResolver` with search paths |
| Resolving identifiers to locations | `9.5` | :white_check_mark: | `0.2.0` | `Resolver` trait |
| Resolving extensions | `9.6` | :white_check_mark: | `0.2.0` | `.usd` / `.usda` / `.usdc` / `.usdz` dispatch; formats added at run time through `sdf::LayerRegistry::add_format`<br>Remaining — a format added to a registry is not found by package anchoring, the `usdz` reader or the `usd_utils` asset walk |
| Packaged resources | `9.7` | :white_check_mark: | `0.9.0` | `asset.usdz[sublayer.usd]` syntax and nested packages; `sdf::PackageFiles` |
| `file` URI scheme ([RFC 8089](https://datatracker.ietf.org/doc/html/rfc8089)) | `9.8` | :construction: | | Filesystem paths accepted but not as `file:///` URIs |
| `usd-anon` scheme (in-memory resources) | `9.8.1` | :white_check_mark: | `0.4.0` | `sdf::Layer::new_anonymous` / `is_anonymous`; identifiers spelled `anon:<n>:<tag>` as in C++ |

## Composition (Spec 10)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [Sublayers](https://openusd.org/release/glossary.html#usdglossary-sublayers) | `10.3.1` | :white_check_mark: | `0.1.2` | Layer stack construction |
| Sublayer offset composition | `10.3.1.1` | :white_check_mark: | `0.4.0` | Offsets compose through nested sublayers; `scale <= 0` falls back to identity |
| [References](https://openusd.org/release/api/class_usd_references.html) (internal + external) | `10.3.2.1` | :white_check_mark: | `0.1.2` | Including `defaultPrim` fallback; authored through `usd::ListEdit` |
| Reference [namespace mapping](https://openusd.org/release/api/class_pcp_map_function.html) | `10.3.2.1.1` | :white_check_mark: | `0.3.0` | `MapFunction` with source/target pairs |
| Reference offset composition | `10.3.2.1.2` | :white_check_mark: | `0.4.0` | Reference offsets compose with the target layer stack's; `scale <= 0` falls back to identity |
| [Payloads](https://openusd.org/release/api/class_usd_payloads.html) | `10.3.2.2` | :white_check_mark: | `0.1.2` | Composed like references, gated by load rules; authored through `usd::ListEdit` |
| [Payload loading control](https://openusd.org/release/api/class_usd_stage_load_rules.html) | `10.3.2.2` | :white_check_mark: | `0.7.0` | `0.6.0` — `pcp::LoadRules`, `usd::LoadPolicy`, `Stage::load` / `unload` / `set_load_rules`, `StageBuilder::load`<br>`0.7.0` — per-prim `usd::Prim::load` / `unload` |
| Payload offset composition | `10.3.2.2.2` | :white_check_mark: | `0.4.0` | Composed like reference offsets; an unloaded payload contributes none |
| [Inherits](https://openusd.org/release/api/class_usd_inherits.html) | `10.3.2.3` | :white_check_mark: | `0.2.0` | Including implied inherit propagation; authored through `usd::ListEdit` |
| Inherit namespace mapping (with identity) | `10.3.2.3.1` | :white_check_mark: | `0.3.0` | `from_pair_identity` adds `(/, /)` catch-all |
| [Specializes](https://openusd.org/release/api/class_usd_specializes.html) | `10.3.2.4` | :white_check_mark: | `0.2.0` | Authored through `usd::ListEdit` |
| Specializes global weakness | `10.4.1` | :white_check_mark: | `0.3.0` | Specializes nodes propagate to the root, where strength ordering places them last |
| [Variants](https://openusd.org/release/api/class_usd_variant_sets.html) | `10.3.2.5` | :white_check_mark: | `0.2.0` | Including deferred evaluation after R/P; `usd::VariantSets` and `usd::VariantSet` |
| Variant selection computation | `10.3.2.5.1` | :white_check_mark: | `0.2.0` | Strongest opinion wins; a set with no selection and no fallback stays unselected, as in C++ |
| Variant fallback map | `10.3.2.5.1` | :white_check_mark: | `0.3.0` | `VariantFallbackMap` via `StageBuilder` |
| [Relocates](https://openusd.org/release/glossary.html#usdglossary-relocates) | `10.3.2.6` | :white_check_mark: | `0.3.0` | `layerRelocates`, source path resolution, child remapping |
| Relocates validation rules | `10.3.2.6` | :white_check_mark: | `0.5.0` | `pcp::InvalidRelocateReason`, `pcp::RelocateConflictReason` |
| Relocates namespace mapping | `10.3.2.6.1` | :white_check_mark: | `0.3.0` | Composed with reference arc mappings |
| Arc permissions (`permission = private`) | `10.3.3` | :white_check_mark: | `0.6.0` | `sdf::Permission` is data-only; composition does not enforce it, as in C++'s `Usd`-mode caches |
| [LIVERPS strength ordering](https://openusd.org/release/glossary.html#livrps-strength-ordering) | `10.4` | :white_check_mark: | `0.3.0` | `ArcType` with `Ord` derived from discriminant |
| [Namespace mappings](https://openusd.org/release/api/class_pcp_map_function.html) (MapFunction) | `10.5` | :white_check_mark: | `0.3.0` | Compose, inverse, longest-prefix matching |
| Composition errors (non-fatal) | `10.6` | :white_check_mark: | `0.3.0` | `pcp::CompositionDiagnostic`, read through `Stage::composition_errors` |
| List op arc computation | `10.3.2` | :white_check_mark: | `0.2.0` | Weakest-to-strongest list-op chaining |

## Stage Population (Spec 11)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Composed stage | `11.2` | :white_check_mark: | `0.2.0` | `Stage::open` with depth-first traversal |
| Populating the stage | `11.3` | :white_check_mark: | `0.2.0` | Lazy per-prim composition via `pcp::IndexCache` (C++ `PcpCache`) |
| [Population mask](https://openusd.org/release/api/class_usd_stage_population_mask.html) | `11.3` | :white_check_mark: | `0.4.0` | `StageBuilder::mask`; the arc targets of a masked-out prim are never opened |
| Prim child discovery | `11.3.1` | :white_check_mark: | `0.2.0` | Merged `primChildren` with relocate adjustment |
| Ordered prim children (`primOrder` reordering) | `11.3.1` | :white_check_mark: | `0.5.0` | `Prim::children`; `primOrder` and relocates applied weak to strong |
| Ordered property children | `11.3.2` | :white_check_mark: | `0.2.0` | Merged `propertyChildren` |
| Ordered property children (`propertyOrder` reordering) | `11.3.2` | :white_check_mark: | `0.9.0` | `usd::Prim::property_names`; `sdf::reorder` |
| Property children include schema declarations | `11.3.2` | :white_check_mark: | `0.7.0` | `usd::Prim::property_names`; `usd::Prim::authored_property_names` for the authored names alone |
| [Scene graph instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) | `11.3.3` | :white_check_mark: | `0.8.0` | `0.5.0` — instances share a composed `/__Prototype_N` prototype that instance proxies redirect onto, nested instances and target remapping included<br>`0.8.0` — the instance key follows C++ `PcpInstanceKey` |
| Model hierarchy (kind) | `11.4` | :white_check_mark: | `0.4.0` | Model/group/component/subcomponent queries validate the contiguous kind hierarchy |
| [Stage queries](https://openusd.org/release/api/prim_flags_8h.html) (Active, Loaded, Defined, Abstract, Instance, InPrototype) | `11.5` | :white_check_mark: | `0.9.0` | `0.4.0` — status flags and `PrimPredicate` traversal filtering<br>`0.5.0` — `IN_PROTOTYPE` and instance-proxy traversal<br>`0.8.0` — the descendants of an inactive prim are off the stage, as in C++<br>`0.9.0` — `usd::PrimRange` |
| [Session layer](https://openusd.org/release/glossary.html#usdglossary-sessionlayer) | `11.2` | :white_check_mark: | `0.3.0` | `StageBuilder::session_layer` |

## Value Resolution (Spec 12)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Metadata resolution (strongest opinion wins) | `12.2` | :white_check_mark: | `0.2.0` | `ValueBlock` supported for scalar fields; the special field classes have their own rows below |
| Specifier resolution | `12.2.1` | :white_check_mark: | `0.4.0` | `def`/`class`/`over` precedence with direct-inherit awareness |
| typeName resolution (from prim definition) | `12.2.2` | :white_check_mark: | `0.7.0` | `usd::Attribute::type_name`; a schema declaration wins over composed opinions |
| variability resolution (weakest opinion) | `12.2.3` | :white_check_mark: | `0.4.0` | Weakest authored opinion wins |
| custom field resolution (any-true) | `12.2.4` | :white_check_mark: | `0.4.0` | Logical OR across opinions |
| Dictionary combining | `12.2.5` | :white_check_mark: | `0.4.0` | Recursive merge across dictionary-valued opinions |
| List op resolution | `12.2.6` | :white_check_mark: | `0.7.0` | Arc lists, connection and relationship targets, `clipSets`, and any other list-op field |
| Layer metadata (root layer only) | `12.2.7` | :white_check_mark: | `0.2.0` | `defaultPrim`, timing fields, etc. |
| Fallback values | `12.2.8` | :white_check_mark: | `0.8.0` | `usd::Attribute::get` / `get_at`, a blocked attribute included; `usd::Attribute::resolve_info` reports the source |
| Basic attribute resolution | `12.3` | :white_check_mark: | `0.7.0` | `0.2.0` — authored `default`, `timeSamples` and `ValueBlock`<br>`0.5.0` — layer-offset retiming<br>`0.7.0` — `asset` value resolution<br>Value clips and splines have their own rows |
| Time-sample lookup and interpolation | `12.3, 12.5.1-2` | :white_check_mark: | `0.5.0` | `usd::Attribute::get_at`: held and linear interpolation over composed samples, with per-node retiming and value clips |
| Layer-offset retiming during value resolution | `12.3.2.1` | :white_check_mark: | `0.7.0` | `0.5.0` — each node's sample times map to stage time through its composed offset<br>`0.7.0` — `timecode` values are retimed (`sdf::LayerOffset::apply_to_value`), and inversely on authoring<br>Remaining — a clip-sourced `timecode` still resolves in clip time |
| Spline evaluation | `12.5.3` | :construction: | | Bezier/Hermite curve interpolation |
| Interpolation (Held) | `12.5.1` | :white_check_mark: | `0.4.0` | `InterpolationType::Held`, chosen per stage by `Stage::set_interpolation` |
| Interpolation (Linear) | `12.5.2` | :white_check_mark: | `0.4.0` | `InterpolationType::Linear` (the default): every §12.5.2 type, quaternions by slerp; held where a type cannot interpolate |
| [Value clips](https://openusd.org/release/api/_usd__page__value_clips.html) | `12.3.4` | :white_check_mark: | `0.7.0` | `usd::ClipsAPI`, read and write: explicit and template clip sets, manifests (authored, synthesized or generated), time mapping with jumps, and `interpolateMissingClipValues` |
| Relationship targets (raw + forwarded) | `12.4` | :white_check_mark: | `0.5.0` | Composed `targetPaths`, remapped through arcs; forwarded targets chase relationship chains with cycle breaking; authored through `usd::Relationship` and `sdf::PathListEdit` |
| Attribute connections | `12.4` | :white_check_mark: | `0.5.0` | Composed `connectionPaths`, with a stage-wide connection graph that resolves chains to their sources; authored through `usd::Attribute` and `sdf::PathListEdit` |

## Schemas (Spec 13)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [Schema registry](https://openusd.org/release/api/class_usd_schema_registry.html) | `13.3` | :white_check_mark: | `0.8.0` | `usd::SchemaRegistry`, built from each family's schematics and manifest and set per stage through `usd::StageBuilder::schema_registry` |
| [Typed schemas](https://openusd.org/release/api/class_usd_typed.html) (IsA) | `13.3.1` | :white_check_mark: | `0.7.0` | `usd::Prim::is_a` over the base chain; `usd::Prim::is_in_family` with `usd::VersionFilter` |
| [Applied schemas](https://openusd.org/release/api/class_usd_a_p_i_schema_base.html) (HasA) | `13.3.2` | :white_check_mark: | `0.7.0` | `usd::Prim::apply_api` / `can_apply_api`; composed `apiSchemas` feed `usd::Prim::prim_definition` |
| Schema inclusions (built-ins, auto-applies) | `13.3.2.1` | :white_check_mark: | `0.7.0` | Built-in API schemas expand recursively, multiple-apply templates per instance name; `apiSchemaAutoApplyTo` |
| Prim definitions (property fallbacks) | `13.3` | :white_check_mark: | `0.7.0` | `usd::PrimDefinition` composes the typed and applied tiers |
| Core schema types | `13.4` | :white_check_mark: | `0.8.0` | The `usd` family (`usd::SCHEMAS`): `usd::CollectionAPI`, `usd::ClipsAPI`, `usd::ModelAPI`, `usd::ColorSpaceAPI`, `usd::ColorSpaceDefinitionAPI` |
| [Value type names](https://openusd.org/release/api/class_sdf_value_type_name.html) | `13.3` | :white_check_mark: | `0.7.0` | `sdf::ValueTypeName`, `vt::ValueKind`; an unregistered type keeps its literal as `vt::Value::UnregisteredValue` |
| Extension metadata fields (fallbackPrimTypes, apiSchemas, clips, clipSets) | `13.2` | :white_check_mark: | `0.7.0` | `apiSchemas` composition, `clips` / `clipSets` value clips (§12.3.4), and `fallbackPrimTypes` substitution |
| [Schema codegen](https://openusd.org/release/tut_generating_new_schema.html) | `13.3` | :white_check_mark: | `0.8.0` | [`openusd-build`](crates/openusd-build) generates typed views, token enums and Markdown docs from a `schema.usda`, with metadata fields from `plugInfo.json` and shader-node views from `shaderDefs.usda` |

## Color (Spec 14)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Supported color spaces | `14.1` | :white_check_mark: | `0.9.0` | `gf::ColorSpace` and `gf::color_space_names` (C++ `GfColorSpace`), `gf::Color` (C++ `GfColor`) |
| Core metadata extensions (colorSpace) | `14.2` | :white_check_mark: | `0.9.0` | `sdf::AttributeSpec::color_space`, `usd::Attribute::color_space` |
| ColorSpaceDefinitionAPI | `14.3` | :white_check_mark: | `0.9.0` | `usd::ColorSpaceDefinitionAPI::color_space` |
| ColorSpaceAPI (inheritance, resolution, default) | `14.4` | :white_check_mark: | `0.9.0` | `usd::ColorSpaceAPI`, `usd::ColorSpaceCache` |

## Collections (Spec 15)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [CollectionAPI](https://openusd.org/release/api/class_usd_collection_a_p_i.html) | `15.1` | :white_check_mark: | `0.8.0` | Multiple-apply `usd::CollectionAPI`: include and exclude authoring, the fallbacks a schema declares for its built-in collections, and pattern-based expression mode (`sdf::PathExpression`) |
| Authoring and evaluating collections | `15.2` | :white_check_mark: | `0.7.0` | `usd::MembershipQuery` over nested and expression collections; `included_paths` enumerates the members on a stage |

## Core File Formats (Spec 16)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| USDA (text) reading | `16.2` | :white_check_mark: | `0.1.4` | Recursive descent parser with logos tokenizer |
| USDA (text) writing | `16.2` | :white_check_mark: | `0.4.0` | `usda::TextWriter`; writes C++ `testSdfParsing` baselines back byte for byte |
| USDC (binary) reading | `16.3` | :white_check_mark: | `0.1.1` | Crate format with LZ4/integer compression |
| USDC (binary) writing | `16.3` | :white_check_mark: | `0.4.0` | `usdc::CrateWriter` |
| USDZ (package) reading | `16.4` | :white_check_mark: | `0.2.0` | ZIP-based package reader; a nested `.usdz` entry reads as its default layer |
| USDZ (package) writing | `16.4` | :white_check_mark: | `0.4.0` | `usdz::ArchiveWriter`; entries are stored uncompressed, aligned to 64 bytes |
| Format auto-detection (`.usd`) | `16.1` | :white_check_mark: | `0.2.0` | Magic byte detection |

## Beyond Core Spec

Features from the C++ reference implementation not covered by the core specification.

| Feature | Status | Version | Notes |
|---|---|---|---|
| [Variable expressions](https://openusd.org/release/api/_sdf__page__variable_expressions.html) | :white_check_mark: | `0.7.0` | `sdf::expr`: 13 built-in functions and string interpolation; session and root layer `expressionVariables` compose; failures reach `Stage::composition_errors` |
| Parallelism (Rayon) | :construction: | | Composition graph is `&`-only, ready for parallel execution |
| Color configuration (`colorConfiguration`, `colorManagementSystem`) | :white_check_mark: | `0.9.0` | `usd::Stage::color_configuration`, with a fallback set on `usd::StageBuilder`<br>Remaining — site fallbacks from a `plugInfo.json` `UsdColorConfigFallbacks` entry |
| Memory-mapped layers | :white_check_mark: | `0.8.0` | An `unsafe` opt-in through `ar::DefaultResolver::map_files` |
| [Shared layers](https://openusd.org/release/api/class_sdf_layer.html) (C++ `SdfLayer::FindOrOpen`) | :construction: | `0.9.0` | `sdf::LayerRegistry::find_or_open` shares one layer between stages through `sdf::LayerHandle`, with live spec handles and reload<br>Remaining:<br>- reloading a layer whose asset moved (C++ `DidChangeLayerResolvedPath`); see the `TODO` in `Layer::reload_due`<br>- shared layers over a lazily decoded backend, and shared layers with an identity; see the `TODO` in `Layer::from_shared` |
| [Incremental invalidation](https://openusd.org/release/api/class_pcp_changes.html) | :white_check_mark: | `0.7.0` | `pcp::Changes` over each `sdf::ChangeList`, scoped by `pcp::Dependencies`; an edit drops only the prim indices it affects |
| [Flatten / export](https://openusd.org/release/api/flatten_utils_8h.html) | :white_check_mark: | `0.9.0` | `usd::Stage::flatten` and `flatten_with` (`usd::FlattenAssets`), `sdf::Layer::export` |
| [Namespace editing](https://openusd.org/release/api/class_usd_namespace_editor.html) | :white_check_mark: | `0.6.0` | [`usd::NamespaceEditor`](crates/openusd/src/usd/editor.rs): batched, atomic rename, reparent and delete, with target and reference fixup |
| [Native instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) (shared representation) | :white_check_mark: | `0.5.0` | See Scene graph instancing (§11.3.3) |
| [Asset dependencies](https://openusd.org/release/api/usd_utils_page_front.html) | :white_check_mark: | `0.9.0` | Dependency discovery, asset path rewriting and `.usdz` packaging in `usd_utils`; UDIM tile sets (`ar::UdimPath`)<br>Remaining — clip templates and variable expressions, which the walk refuses where C++ expands or anchors them |
| [UsdMtlx](https://openusd.org/release/api/usd_mtlx_page_front.html) (MaterialX file format) | :construction: | `main` | See the [`openusd-mtlx`](crates/openusd-mtlx/README.md) crate for supported features |
| [Stage cache](https://openusd.org/release/api/class_usd_utils_stage_cache.html) | :thinking: | | Avoid redundant stage loading |
| [Kind registry](https://openusd.org/release/api/class_kind_registry.html) | :white_check_mark: | `0.8.0` | `kind::Registry`, `kind::Decl`, `usd::SchemaFamily::kinds`, `usd::ModelAPI::is_kind` |
| [Edit targets](https://openusd.org/release/api/class_usd_edit_target.html) | :white_check_mark: | `0.6.0` | `usd::EditTarget`; arc lists and property targets are authored through its mapping |
| Authoring transactions | :white_check_mark: | `0.9.0` | `usd::Stage::edit` batches prim and property writes into one layer transaction; `usd::UndoStage::group` undoes them as one step<br>Remaining:<br>- queued arcs, variants, API-schema apply and spec removal<br>- planning under a prim a batch creates at a site its index erased (a new prim through a variant edit target) |
| [Change notification](https://openusd.org/release/api/class_usd_notice.html) | :white_check_mark: | `0.7.0` | Layer commits through `sdf::LayerSink`, composed changes through `usd::StageSink`; undo and a replayable `usd::Diff` |
| [Property stack queries](https://openusd.org/release/api/class_usd_resolve_info.html) | :white_check_mark: | `0.8.0` | `usd::ResolveInfo` through `Attribute::resolve_info` / `resolve_info_at`, with `weaker_sources`; `Attribute::property_stack_at` and `Prim::prim_stack` return `usd::SpecSite`<br>Remaining:<br>- a manifest the stage synthesizes names no `usd::SpecSite`; see the `TODO` on `pcp::ClipCache`<br>- a `timeSamples` map or clip set that blocks the value is reported by `usd::ResolveInfo::blocked_by`, where C++ names it the source; a map holding only blocks lists no sample times |
