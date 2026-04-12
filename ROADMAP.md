# Roadmap and Spec Compliance

Feature parity with the [AOUSD Core Specification v1.0.1](docs/aousd_core_spec_1.0.1.pdf) and the C++ reference implementation ([OpenUSD](https://github.com/PixarAnimationStudios/OpenUSD)).

Legend: :white_check_mark: Supported | :construction: Planned | :thinking: Considering

## Foundational Data Types (Spec 6)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Scalar types (bool, int, float, double, half, string, token, asset, timecode, int64, uint, uint64, uchar) | 6.2 | :white_check_mark: | 0.1.1 | `sdf::Value` enum |
| Dimensioned types (vectors, matrices, quaternions) | 6.3 | :white_check_mark: | 0.1.2 | float2..4, double2..4, matrix2d..4d, quath/f/d, int2..4, half2..4 |
| Algebraic types (opaque) | 6.4 | :white_check_mark: | 0.2.0 | `Value::Opaque` |
| Semantic aliases (color, normal, point, vector, texCoord, frame) | 6.5 | :thinking: | | Parsed as underlying types; semantic role not tracked separately |
| Arrays | 6.6.1 | :white_check_mark: | 0.1.2 | All scalar and dimensioned array variants |
| Dictionaries | 6.6.2 | :white_check_mark: | 0.1.2 | Including nested dictionaries |
| Dictionary combining | 6.6.2.1 | :construction: | | Recursive merge of stronger/weaker dictionaries during value resolution |
| [List operations](https://openusd.org/release/glossary.html#usdglossary-listediting) (explicit, composable) | 6.6.3 | :white_check_mark: | 0.2.0 | int, int64, uint, uint64, token, string, path, reference, payload |
| List op combining | 6.6.3.6 | :white_check_mark: | 0.2.0 | `ListOp::combined_with` |
| List op reducing | 6.6.3.8 | :white_check_mark: | 0.2.0 | `ListOp::reduced` |
| List op chaining | 6.6.3.9 | :white_check_mark: | 0.2.0 | Applied during composition arc evaluation |

## Document Data Model (Spec 7)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Layer structure (specs, paths, fields) | 7.2 | :white_check_mark: | 0.1.1 | `AbstractData` trait |
| Spec forms (layer, prim, attribute, relationship, variant set, variant) | 7.3 | :white_check_mark: | 0.1.1 | `SpecType` enum |
| Core metadata fields (layer spec) | 7.6.1 | :white_check_mark: | 0.1.2 | subLayers, subLayerOffsets, defaultPrim, documentation, etc. |
| Core metadata fields (prim spec) | 7.6.2 | :white_check_mark: | 0.1.2 | specifier, primChildren, propertyChildren, references, payload, inherits, specializes, variantSets, variantSelection, etc. |
| Core metadata fields (attribute spec) | 7.6.3 | :white_check_mark: | 0.1.2 | typeName, default, timeSamples, connectionPaths, variability, custom |
| Core metadata fields (relationship spec) | 7.6.4 | :white_check_mark: | 0.1.2 | targetPaths, variability, custom |
| Core metadata fields (variant set/variant spec) | 7.6.5-7 | :white_check_mark: | 0.2.0 | |
| Spline specialized type | 7.4.2.4 | :construction: | | SplineKnot, interpolation modes, extrapolation, looping |
| Retiming specialized type ([layer offsets](https://openusd.org/release/glossary.html#usdglossary-layeroffset)) | 7.6.1.2.2 | :white_check_mark: | 0.1.2 | Parsed from subLayerOffsets; not applied during composition |

## Paths (Spec 8)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Absolute/relative paths | 8.1 | :white_check_mark: | 0.1.1 | `sdf::Path` |
| Prim paths | 8.1 | :white_check_mark: | 0.1.1 | |
| Property paths | 8.1 | :white_check_mark: | 0.1.1 | |
| Variant selection paths | 8.1 | :white_check_mark: | 0.2.0 | `{set=selection}` syntax |
| Path grammar (PEG) | 8.5 | :white_check_mark: | 0.1.4 | Parsed from USDA and USDC |
| Element ordering | 8.2 | :construction: | | Normative ordering rules for property/prim names |
| Relative path resolution | 8.1 | :white_check_mark: | 0.2.0 | Anchoring via `make_absolute` |
| Legacy path compatibility | 8.7 | :thinking: | | Extended grammar with `[target]` and `.mapper` paths |

## Resource Interface (Spec 9)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Resource identifiers (URI) | 9.2 | :white_check_mark: | 0.1.1 | Asset paths as strings |
| Relative resource identifiers (anchored) | 9.4.1 | :white_check_mark: | 0.2.0 | `./` and `../` resolution relative to containing layer |
| Non-anchored identifiers (search paths) | 9.4.2 | :white_check_mark: | 0.2.0 | `DefaultResolver` with search paths |
| Resolving identifiers to locations | 9.5 | :white_check_mark: | 0.2.0 | `Resolver` trait |
| Resolving extensions | 9.6 | :white_check_mark: | 0.2.0 | `.usd`/`.usda`/`.usdc`/`.usdz` dispatch |
| Packaged resources | 9.7 | :white_check_mark: | 0.2.0 | `asset.usdz[sublayer.usd]` syntax |
| `file` URI scheme ([RFC 8089](https://datatracker.ietf.org/doc/html/rfc8089)) | 9.8 | :construction: | | Filesystem paths accepted but not as `file:///` URIs |
| `usd-anon` scheme (in-memory resources) | 9.8.1 | :thinking: | | For transient layers not backed by files |

## Composition (Spec 10)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [Sublayers](https://openusd.org/release/glossary.html#usdglossary-sublayers) | 10.3.1 | :white_check_mark: | 0.1.2 | Layer stack construction |
| Sublayer time offsets | 10.3.1.1 | :construction: | | Parsed but not applied during composition |
| [References](https://openusd.org/release/api/class_usd_references.html) (internal + external) | 10.3.2.1 | :white_check_mark: | 0.1.2 | Including `defaultPrim` fallback |
| Reference [namespace mapping](https://openusd.org/release/api/class_pcp_map_function.html) | 10.3.2.1.1 | :white_check_mark: | main | `MapFunction` with source/target pairs |
| Reference time offsets | 10.3.2.1.2 | :construction: | | Parsed but not applied during composition |
| [Payloads](https://openusd.org/release/api/class_usd_payloads.html) | 10.3.2.2 | :white_check_mark: | 0.1.2 | Treated identically to references |
| [Payload loading control](https://openusd.org/release/api/class_usd_stage_load_rules.html) | 10.3.2.2 | :construction: | | No mechanism to exclude payloads |
| Payload time offsets | 10.3.2.2.2 | :construction: | | Parsed but not applied during composition |
| [Inherits](https://openusd.org/release/api/class_usd_inherits.html) | 10.3.2.3 | :white_check_mark: | 0.2.0 | Including implied inherit propagation |
| Inherit namespace mapping (with identity) | 10.3.2.3.1 | :construction: | | Missing `(/, /)` identity pair |
| [Specializes](https://openusd.org/release/api/class_usd_specializes.html) | 10.3.2.4 | :white_check_mark: | 0.2.0 | |
| Specializes global weakness | 10.4.1 | :construction: | | Spec requires specializes opinions to be globally weaker |
| [Variants](https://openusd.org/release/api/class_usd_variant_sets.html) | 10.3.2.5 | :white_check_mark: | 0.2.0 | Including deferred evaluation after R/P |
| Variant selection computation | 10.3.2.5.1 | :white_check_mark: | 0.2.0 | Strongest opinion wins, fallback to first variant |
| Variant fallback map | 10.3.2.5.1 | :white_check_mark: | main | `VariantFallbackMap` via `StageBuilder` |
| [Relocates](https://openusd.org/release/glossary.html#usdglossary-relocates) | 10.3.2.6 | :white_check_mark: | main | `layerRelocates`, source path resolution, child remapping |
| Relocates validation rules | 10.3.2.6 | :construction: | | 7 restriction checks not enforced |
| Relocates namespace mapping | 10.3.2.6.1 | :white_check_mark: | main | Composed with reference arc mappings |
| [LIVERPS strength ordering](https://openusd.org/release/glossary.html#livrps-strength-ordering) | 10.4 | :white_check_mark: | main | `ArcType` with `Ord` derived from discriminant |
| [Namespace mappings](https://openusd.org/release/api/class_pcp_map_function.html) (MapFunction) | 10.5 | :white_check_mark: | main | Compose, inverse, longest-prefix matching |
| Composition errors (non-fatal) | 10.6 | :white_check_mark: | main | `pcp::Error` with `StageBuilder::on_error` callback |
| List op arc computation | 10.3.2 | :white_check_mark: | 0.2.0 | Weakest-to-strongest list-op chaining |

## Stage Population (Spec 11)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Composed stage | 11.2 | :white_check_mark: | 0.2.0 | `Stage::open` with depth-first traversal |
| Populating the stage | 11.3 | :white_check_mark: | 0.2.0 | Lazy per-prim composition via `pcp::Cache` |
| [Population mask](https://openusd.org/release/api/class_usd_stage_population_mask.html) | 11.3 | :construction: | | No subset-of-prims loading |
| Ordered prim children | 11.3.1 | :white_check_mark: | 0.2.0 | Merged `primChildren` with relocate adjustment |
| Ordered prim children (`primOrder` reordering) | 11.3.1 | :construction: | | `primOrder` field not applied |
| Ordered property children | 11.3.2 | :white_check_mark: | 0.2.0 | Merged `propertyChildren` |
| Ordered property children (`propertyOrder` reordering) | 11.3.2 | :construction: | | `propertyOrder` field not applied |
| [Scene graph instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) | 11.3.3 | :construction: | | `instanceable` readable; shared representation not implemented |
| Model hierarchy (kind) | 11.4 | :construction: | | `kind` readable; hierarchy validation not implemented |
| [Stage queries](https://openusd.org/release/api/prim_flags_8h.html) (Active, Loaded, Defined, Abstract, Instance) | 11.5 | :construction: | | Predicate flags for traversal filtering |
| [Session layer](https://openusd.org/release/glossary.html#usdglossary-sessionlayer) | 11.2 | :white_check_mark: | main | `StageBuilder::session_layer` |

## Value Resolution (Spec 12)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Metadata resolution (strongest opinion wins) | 12.2 | :white_check_mark: | 0.2.0 | `PrimIndex::resolve_field` with `ValueBlock` support |
| Specifier resolution | 12.2.1 | :construction: | | Special rules for `def`/`over`/`class` not fully implemented |
| typeName resolution (from prim definition) | 12.2.2 | :construction: | | Uses strongest opinion, not prim definition |
| variability resolution (weakest opinion) | 12.2.3 | :construction: | | Uses strongest opinion instead of weakest |
| custom field resolution (any-true) | 12.2.4 | :construction: | | Uses strongest opinion instead of any-true |
| Dictionary combining | 12.2.5 | :construction: | | Recursive merge across opinions |
| List op resolution | 12.2.6 | :white_check_mark: | 0.2.0 | Combined stack of opinions |
| Layer metadata (root layer only) | 12.2.7 | :white_check_mark: | 0.2.0 | `defaultPrim`, timing fields, etc. |
| Fallback values | 12.2.8 | :construction: | | Requires schema registry |
| Attribute resolution | 12.3 | :white_check_mark: | 0.2.0 | timeSamples, default, ValueBlock |
| Attribute resolution (with time) | 12.3 | :white_check_mark: | 0.1.2 | Time sample lookup |
| Spline evaluation | 12.5.3 | :construction: | | Bezier/Hermite curve interpolation |
| Interpolation (Held) | 12.5.1 | :construction: | | Not implemented at stage level |
| Interpolation (Linear) | 12.5.2 | :construction: | | Not implemented at stage level |
| [Value clips](https://openusd.org/release/api/_usd__page__value_clips.html) | 12.3 | :construction: | | `clips`/`clipSets` for split time samples |
| Relationship targets (raw + forwarded) | 12.4 | :construction: | | `targetPaths` readable; forwarding not implemented |
| Attribute connections | 12.4 | :construction: | | `connectionPaths` readable; not resolved |

## Schemas (Spec 13)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [Schema registry](https://openusd.org/release/api/class_usd_schema_registry.html) | 13.3 | :construction: | | Type hierarchy, prim definitions |
| [Typed schemas](https://openusd.org/release/api/class_usd_typed.html) (IsA) | 13.3.1 | :construction: | | `typeName` readable; registry not implemented |
| [Applied schemas](https://openusd.org/release/api/class_usd_a_p_i_schema_base.html) (HasA) | 13.3.2 | :construction: | | `apiSchemas` readable; definitions not loaded |
| Schema inclusions (built-ins, auto-applies) | 13.3.2.1 | :construction: | | |
| Prim definitions (property fallbacks) | 13.3 | :construction: | | |
| Core schema types | 13.4 | :construction: | | |
| [Value type names](https://openusd.org/release/api/class_sdf_value_type_name.html) | 13.3 | :construction: | | Attribute type validation |
| Extension metadata fields (fallbackPrimTypes, apiSchemas, clips, clipSets) | 13.2 | :construction: | | Fields readable; semantics not applied |
| [Schema codegen](https://openusd.org/release/tut_generating_new_schema.html) | 13.3 | :construction: | | Generate typed APIs from schema definitions |

## Color (Spec 14)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Supported color spaces | 14.1 | :thinking: | | |
| Core metadata extensions (colorSpace) | 14.2 | :thinking: | | |
| ColorSpaceDefinitionAPI | 14.3 | :thinking: | | |

## Collections (Spec 15)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [CollectionAPI](https://openusd.org/release/api/class_usd_collection_a_p_i.html) | 15.1 | :construction: | | |
| Authoring and evaluating collections | 15.2 | :construction: | | |

## Core File Formats (Spec 16)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| USDA (text) reading | 16.2 | :white_check_mark: | 0.1.4 | Recursive descent parser with logos tokenizer |
| USDA (text) writing | 16.2 | :construction: | | |
| USDC (binary) reading | 16.3 | :white_check_mark: | 0.1.1 | Crate format with LZ4/integer compression |
| USDC (binary) writing | 16.3 | :construction: | | |
| USDZ (package) reading | 16.4 | :white_check_mark: | 0.2.0 | ZIP-based package reader |
| USDZ (package) writing | 16.4 | :construction: | | |
| Format auto-detection (`.usd`) | 16.1 | :white_check_mark: | 0.2.0 | Magic byte detection |

## Beyond Core Spec

Features from the C++ reference implementation not covered by the core specification.

| Feature | Status | Version | Notes |
|---|---|---|---|
| [Variable expressions](https://openusd.org/release/api/_sdf__page__variable_expressions.html) | :white_check_mark: | 0.2.0 | 13 built-in functions, string interpolation (`expr` module) |
| Parallelism (Rayon) | :construction: | | Composition graph is `&`-only, ready for parallel execution |
| [Incremental invalidation](https://openusd.org/release/api/class_pcp_changes.html) | :thinking: | | Dependency tracking and change processing |
| [UsdGeom](https://openusd.org/release/api/usd_geom_page_front.html) (geometry, transforms, cameras) | :construction: | | |
| [UsdShade](https://openusd.org/release/api/usd_shade_page_front.html) (materials, shaders) | :construction: | | |
| [UsdLux](https://openusd.org/release/api/usd_lux_page_front.html) (lighting) | :construction: | | |
| [UsdSkel](https://openusd.org/release/api/usd_skel_page_front.html) (skeletons, skinning) | :construction: | | |
| [UsdVol](https://openusd.org/release/api/usd_vol_page_front.html) (volumes) | :construction: | | |
| [UsdPhysics](https://openusd.org/release/api/usd_physics_page_front.html) | :construction: | | |
| [UsdRender](https://openusd.org/release/api/usd_render_page_front.html) | :construction: | | |
| UsdMedia, UsdUI, UsdProc | :construction: | | |
| [Flatten / export](https://openusd.org/release/api/flatten_utils_8h.html) | :construction: | | |
| [Namespace editing](https://openusd.org/release/api/class_usd_namespace_editor.html) | :construction: | | |
| [Native instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) (shared representation) | :construction: | | |
| [Stage cache](https://openusd.org/release/api/class_usd_utils_stage_cache.html) | :thinking: | | Avoid redundant stage loading |
| [Kind registry](https://openusd.org/release/api/class_kind_registry.html) | :thinking: | | Model/group/assembly/component taxonomy |
| [Edit targets](https://openusd.org/release/api/class_usd_edit_target.html) | :thinking: | | Direct opinions to a specific layer |
| [Change notification](https://openusd.org/release/api/class_usd_notice.html) | :thinking: | | Listeners for live scene updates |
| [Property stack queries](https://openusd.org/release/api/class_usd_resolve_info.html) | :thinking: | | Inspect all contributing opinions across layers |

## Tooling

| Feature | Status | Notes |
|---|---|---|
| usdcat (print/convert) | :construction: | |
| usdtree (hierarchy printing) | :thinking: | |
| usddiff (layer diffing) | :thinking: | |
| usdchecker (validation) | :thinking: | |
| usdzip (USDZ packaging) | :thinking: | |
| [usdGenSchema](https://openusd.org/release/tut_generating_new_schema.html) (schema codegen) | :construction: | |
