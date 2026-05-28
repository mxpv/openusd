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
| Algebraic types (opaque) | `6.4` | :white_check_mark: | `0.2.0` | `Value::Opaque` |
| Semantic aliases (color, normal, point, vector, texCoord, frame) | `6.5` | :thinking: | | Parsed as underlying types; semantic role not tracked separately |
| Arrays | `6.6.1` | :white_check_mark: | `0.1.2` | All scalar and dimensioned array variants |
| Dictionaries | `6.6.2` | :white_check_mark: | `0.1.2` | Including nested dictionaries |
| Dictionary combining | `6.6.2.1` | :white_check_mark: | `main` | Recursive merge of stronger/weaker dictionaries during value resolution |
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
| Spline specialized type | `7.4.2.4` | :construction: | | SplineKnot, interpolation modes, extrapolation, looping |
| Retiming specialized type ([layer offsets](https://openusd.org/release/glossary.html#usdglossary-layeroffset)) | `7.6.1.2.2` | :white_check_mark: | `0.1.2` | Parsed from subLayerOffsets; composed through arcs as of `main`. Runtime retiming during value resolution is tracked under Spec 12. |

## Paths (Spec 8)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Absolute/relative paths | `8.1` | :white_check_mark: | `0.1.1` | `sdf::Path` |
| Prim paths | `8.1` | :white_check_mark: | `0.1.1` | |
| Property paths | `8.1` | :white_check_mark: | `0.1.1` | |
| Variant selection paths | `8.1` | :white_check_mark: | `0.2.0` | `{set=selection}` syntax |
| Path grammar (PEG) | `8.5` | :white_check_mark: | `0.1.4` | Parsed from USDA and USDC |
| Element ordering | `8.2` | :construction: | | Normative ordering rules for property/prim names |
| Relative path resolution | `8.1` | :white_check_mark: | `0.2.0` | Anchoring via `make_absolute` |
| Legacy path compatibility | `8.7` | :thinking: | | Extended grammar with `[target]` and `.mapper` paths |

## Resource Interface (Spec 9)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Resource identifiers (URI) | `9.2` | :white_check_mark: | `0.1.1` | Asset paths as strings |
| Relative resource identifiers (anchored) | `9.4.1` | :white_check_mark: | `0.2.0` | `./` and `../` resolution relative to containing layer |
| Non-anchored identifiers (search paths) | `9.4.2` | :white_check_mark: | `0.2.0` | `DefaultResolver` with search paths |
| Resolving identifiers to locations | `9.5` | :white_check_mark: | `0.2.0` | `Resolver` trait |
| Resolving extensions | `9.6` | :white_check_mark: | `0.2.0` | `.usd`/`.usda`/`.usdc`/`.usdz` dispatch |
| Packaged resources | `9.7` | :white_check_mark: | `0.2.0` | `asset.usdz[sublayer.usd]` syntax |
| `file` URI scheme ([RFC 8089](https://datatracker.ietf.org/doc/html/rfc8089)) | `9.8` | :construction: | | Filesystem paths accepted but not as `file:///` URIs |
| `usd-anon` scheme (in-memory resources) | `9.8.1` | :thinking: | | For transient layers not backed by files |

## Composition (Spec 10)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [Sublayers](https://openusd.org/release/glossary.html#usdglossary-sublayers) | `10.3.1` | :white_check_mark: | `0.1.2` | Layer stack construction |
| Sublayer offset composition | `10.3.1.1` | :white_check_mark: | `main` | Effective sublayer offsets are composed through nested sublayers and carried on each `Node` via `MapFunction::time_offset`. Runtime retiming is tracked under Spec 12.3.2.1. |
| [References](https://openusd.org/release/api/class_usd_references.html) (internal + external) | `10.3.2.1` | :white_check_mark: | `0.1.2` | Including `defaultPrim` fallback |
| Reference [namespace mapping](https://openusd.org/release/api/class_pcp_map_function.html) | `10.3.2.1.1` | :white_check_mark: | `0.3.0` | `MapFunction` with source/target pairs |
| Reference offset composition | `10.3.2.1.2` | :white_check_mark: | `main` | Reference offsets are carried through reference arcs and composed with target layer-stack offsets. Runtime retiming is tracked under Spec 12.3.2.1. |
| [Payloads](https://openusd.org/release/api/class_usd_payloads.html) | `10.3.2.2` | :white_check_mark: | `0.1.2` | Treated identically to references |
| [Payload loading control](https://openusd.org/release/api/class_usd_stage_load_rules.html) | `10.3.2.2` | :white_check_mark: | `main` | `StageBuilder::initial_load_set` supports loading all payloads or leaving them unloaded |
| Payload offset composition | `10.3.2.2.2` | :white_check_mark: | `main` | Loaded payload offsets compose like references; unloaded payload offsets are ignored. Runtime retiming is tracked under Spec 12.3.2.1. |
| [Inherits](https://openusd.org/release/api/class_usd_inherits.html) | `10.3.2.3` | :white_check_mark: | `0.2.0` | Including implied inherit propagation |
| Inherit namespace mapping (with identity) | `10.3.2.3.1` | :white_check_mark: | `0.3.0` | `from_pair_identity` adds `(/, /)` catch-all |
| [Specializes](https://openusd.org/release/api/class_usd_specializes.html) | `10.3.2.4` | :white_check_mark: | `0.2.0` | |
| Specializes global weakness | `10.4.1` | :white_check_mark: | `0.3.0` | Stable-partition reorders specialize-introduced nodes after all others |
| [Variants](https://openusd.org/release/api/class_usd_variant_sets.html) | `10.3.2.5` | :white_check_mark: | `0.2.0` | Including deferred evaluation after R/P |
| Variant selection computation | `10.3.2.5.1` | :white_check_mark: | `0.2.0` | Strongest opinion wins, fallback to first variant |
| Variant fallback map | `10.3.2.5.1` | :white_check_mark: | `0.3.0` | `VariantFallbackMap` via `StageBuilder` |
| [Relocates](https://openusd.org/release/glossary.html#usdglossary-relocates) | `10.3.2.6` | :white_check_mark: | `0.3.0` | `layerRelocates`, source path resolution, child remapping |
| Relocates validation rules | `10.3.2.6` | :construction: | | 7 restriction checks not enforced |
| Relocates namespace mapping | `10.3.2.6.1` | :white_check_mark: | `0.3.0` | Composed with reference arc mappings |
| [LIVERPS strength ordering](https://openusd.org/release/glossary.html#livrps-strength-ordering) | `10.4` | :white_check_mark: | `0.3.0` | `ArcType` with `Ord` derived from discriminant |
| [Namespace mappings](https://openusd.org/release/api/class_pcp_map_function.html) (MapFunction) | `10.5` | :white_check_mark: | `0.3.0` | Compose, inverse, longest-prefix matching |
| Composition errors (non-fatal) | `10.6` | :white_check_mark: | `0.3.0` | `pcp::Error` with `StageBuilder::on_error` callback |
| List op arc computation | `10.3.2` | :white_check_mark: | `0.2.0` | Weakest-to-strongest list-op chaining |

## Stage Population (Spec 11)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Composed stage | `11.2` | :white_check_mark: | `0.2.0` | `Stage::open` with depth-first traversal |
| Populating the stage | `11.3` | :white_check_mark: | `0.2.0` | Lazy per-prim composition via `pcp::Cache` |
| [Population mask](https://openusd.org/release/api/class_usd_stage_population_mask.html) | `11.3` | :white_check_mark: | `main` | `StageBuilder::population_mask` limits stage queries, traversal, and root layer-stack dependency collection to a masked working set |
| Prim child discovery | `11.3.1` | :white_check_mark: | `0.2.0` | Merged `primChildren` with relocate adjustment. Full normative ordering is tracked in the `primOrder` row below. |
| Ordered prim children (`primOrder` reordering) | `11.3.1` | :construction: | `main` | Partial: strongest `primOrder` is applied after the final merge. Left for full spec coverage: merge weakest-to-strongest, apply relocates per layer stack, and reapply `primOrder` after every merge. |
| Ordered property children | `11.3.2` | :white_check_mark: | `0.2.0` | Merged `propertyChildren` |
| Ordered property children (`propertyOrder` reordering) | `11.3.2` | :white_check_mark: | `main` | Strongest opinion applied via `sdf::apply_ordering` |
| [Scene graph instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) | `11.3.3` | :construction: | | `instanceable` readable; shared representation not implemented |
| Model hierarchy (kind) | `11.4` | :white_check_mark: | `main` | `Stage::is_model`/`is_group`/`is_component`/`is_subcomponent` validate the contiguous kind hierarchy |
| [Stage queries](https://openusd.org/release/api/prim_flags_8h.html) (Active, Loaded, Defined, Abstract, Instance) | `11.5` | :white_check_mark: | `main` | `Stage::is_active`/`is_loaded`/`is_defined`/`is_abstract`/`is_instance`, `prim_status`, and `PrimPredicate` traversal filtering |
| [Session layer](https://openusd.org/release/glossary.html#usdglossary-sessionlayer) | `11.2` | :white_check_mark: | `0.3.0` | `StageBuilder::session_layer` |
| Stage authoring (`DefinePrim` / `OverridePrim` / `CreateAttribute` / `CreateRelationship` / `SetDefaultPrim`) | — | :construction: | `main` | Layer-tier authoring on `sdf::Layer` is in; Stage-tier wrappers route through `EditTarget` and `Cache::process_changes`. `StageBuilder::in_memory` creates an anonymous-root stage (C++ `CreateInMemory`). `EditTarget` is a minimal subset of `UsdEditTarget` — `layer_index` only, no `PcpMapFunction` for variant/reference routing yet. Composed handles `usd::Prim` / `usd::Attribute` / `usd::Relationship` (C++ `UsdPrim` / `UsdAttribute` / `UsdRelationship` analogs) are returned from the authoring methods with fluent `self → Self` setters for chaining. Surgical (`PcpChanges`-style) cache invalidation lands via `sdf::ChangeList` + `pcp::Changes` + `pcp::Dependencies`, with a three-tier classifier (significant / prim / spec) and per-layer reverse-dep map for fanout. |

## Value Resolution (Spec 12)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Metadata resolution (strongest opinion wins) | `12.2` | :white_check_mark: | `0.2.0` | `PrimIndex::resolve_field` with `ValueBlock` support for scalar fields. Special field classes are tracked separately below. |
| Specifier resolution | `12.2.1` | :white_check_mark: | `main` | `def`/`class`/`over` precedence with direct-inherit awareness in `PrimIndex::resolve_specifier` |
| typeName resolution (from prim definition) | `12.2.2` | :construction: | | Uses strongest opinion, not prim definition |
| variability resolution (weakest opinion) | `12.2.3` | :white_check_mark: | `main` | Weakest authored opinion via `PrimIndex::resolve_variability` |
| custom field resolution (any-true) | `12.2.4` | :white_check_mark: | `main` | Logical OR across opinions via `PrimIndex::resolve_custom` |
| Dictionary combining | `12.2.5` | :white_check_mark: | `main` | Recursive merge across dictionary-valued opinions |
| List op resolution | `12.2.6` | :construction: | `main` | Partial: composition-arc list ops and composed `apiSchemas` are resolved. Left for full metadata coverage: generic list-op field resolution for `targetPaths`, `connectionPaths`, `clipSets`, and any registered list-op metadata field. |
| Layer metadata (root layer only) | `12.2.7` | :white_check_mark: | `0.2.0` | `defaultPrim`, timing fields, etc. |
| Fallback values | `12.2.8` | :construction: | | Requires schema registry |
| Basic attribute resolution | `12.3` | :white_check_mark: | `0.2.0` | Resolves authored `default`, `timeSamples`, and `ValueBlock`. Layer-offset retiming, value clips, and splines are tracked separately. |
| Time-sample lookup and interpolation | `12.3, 12.5.1-2` | :white_check_mark: | `0.1.2` | `Stage::value_at` performs held/linear interpolation over composed samples. Per-node retiming and value clips are tracked separately. |
| Layer-offset retiming during value resolution | `12.3.2.1` | :construction: | | Offsets are composed and stored on PCP nodes. Left: sample each contributing node in its local time (`stage_time * scale + offset`), merge retimed samples/defaults correctly, and cover sublayer/reference/payload offset cases. |
| Spline evaluation | `12.5.3` | :construction: | | Bezier/Hermite curve interpolation |
| Interpolation (Held) | `12.5.1` | :white_check_mark: | `main` | `Stage::value_at(attr, time)` with `InterpolationType::Held`. |
| Interpolation (Linear) | `12.5.2` | :white_check_mark: | `main` | `Stage::value_at(attr, time)` with `InterpolationType::Linear` (default). All §12.5.2 types incl. `quath`/`f`/`d` via slerp; held-fallback for unsupported types and past-last-sample. |
| [Value clips](https://openusd.org/release/api/_usd__page__value_clips.html) | `12.3` | :construction: | | `clips`/`clipSets` for split time samples |
| Relationship targets (raw + forwarded) | `12.4` | :construction: | | `targetPaths` readable; forwarding not implemented |
| Attribute connections | `12.4` | :construction: | | `connectionPaths` readable; not resolved |

## Schemas (Spec 13)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [Schema registry](https://openusd.org/release/api/class_usd_schema_registry.html) | `13.3` | :construction: | | Type hierarchy, prim definitions |
| [Typed schemas](https://openusd.org/release/api/class_usd_typed.html) (IsA) | `13.3.1` | :construction: | | `typeName` readable; registry not implemented |
| [Applied schemas](https://openusd.org/release/api/class_usd_a_p_i_schema_base.html) (HasA) | `13.3.2` | :construction: | | `apiSchemas` list-ops compose across contributing layers; `Prim::add_applied_schema` authors registry-free applied schema tokens by merging into the local list op. Left for full spec coverage: schema registry, single/multiple application validation, built-in/auto-apply inclusions, composed prim definitions, and fallback property values. |
| Schema inclusions (built-ins, auto-applies) | `13.3.2.1` | :construction: | | |
| Prim definitions (property fallbacks) | `13.3` | :construction: | | |
| Core schema types | `13.4` | :construction: | | |
| [Value type names](https://openusd.org/release/api/class_sdf_value_type_name.html) | `13.3` | :construction: | | Attribute type validation |
| Extension metadata fields (fallbackPrimTypes, apiSchemas, clips, clipSets) | `13.2` | :construction: | | Fields readable; `apiSchemas` list-op composition applied. Left: composed-prim `fallbackPrimTypes`, value clip semantics for `clips`/`clipSets`, and any schema-domain behavior layered on these fields. |
| [Schema codegen](https://openusd.org/release/tut_generating_new_schema.html) | `13.3` | :construction: | | Generate typed APIs from schema definitions |

## Color (Spec 14)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Supported color spaces | `14.1` | :thinking: | | |
| Core metadata extensions (colorSpace) | `14.2` | :thinking: | | |
| ColorSpaceDefinitionAPI | `14.3` | :thinking: | | |

## Collections (Spec 15)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [CollectionAPI](https://openusd.org/release/api/class_usd_collection_a_p_i.html) | `15.1` | :construction: | | |
| Authoring and evaluating collections | `15.2` | :construction: | | |

## Core File Formats (Spec 16)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| USDA (text) reading | `16.2` | :white_check_mark: | `0.1.4` | Recursive descent parser with logos tokenizer |
| USDA (text) writing | `16.2` | :white_check_mark: | `main` | `usda::TextWriter`; round-trips the compliance suite opinion-for-opinion |
| USDC (binary) reading | `16.3` | :white_check_mark: | `0.1.1` | Crate format with LZ4/integer compression |
| USDC (binary) writing | `16.3` | :white_check_mark: | `main` | `usdc::CrateWriter`; streaming packer with integer compression, LZ4 blocks, DFS path encoder |
| USDZ (package) reading | `16.4` | :white_check_mark: | `0.2.0` | ZIP-based package reader |
| USDZ (package) writing | `16.4` | :white_check_mark: | `main` | `usdz::ArchiveWriter`; STORED-only, 64-byte aligned entries |
| Format auto-detection (`.usd`) | `16.1` | :white_check_mark: | `0.2.0` | Magic byte detection |

## Beyond Core Spec

Features from the C++ reference implementation not covered by the core specification.

| Feature | Status | Version | Notes |
|---|---|---|---|
| [Variable expressions](https://openusd.org/release/api/_sdf__page__variable_expressions.html) | :white_check_mark: | `0.2.0` | 13 built-in functions, string interpolation (`expr` module) |
| Parallelism (Rayon) | :construction: | | Composition graph is `&`-only, ready for parallel execution |
| [Incremental invalidation](https://openusd.org/release/api/class_pcp_changes.html) | :thinking: | | Dependency tracking and change processing |
| [UsdGeom](https://openusd.org/release/api/usd_geom_page_front.html) (geometry, transforms, cameras) | :white_check_mark: | `main` | Schema reader behind `geom` feature. Cross-cutting Imageable / Boundable (visibility / purpose / extent / kind); Xformable with full `xformOpOrder` evaluator (`!invert!`, `!resetXformStack!`, every rotation order); intrinsic shapes (Cube, Sphere, Cylinder, Capsule, Cone, Plane, Xform); Camera (full attribute set with FOV helpers); Mesh + GeomSubset + PrimvarsAPI (subdivision, creases, corners, holes, primvar interpolation); BasisCurves, NurbsCurves, NurbsPatch, HermiteCurves, Points, TetMesh; PointInstancer. No authoring helpers; ModelAPI / MotionAPI / VisibilityAPI / BBoxCache / XformCache deferred. |
| [UsdShade](https://openusd.org/release/api/usd_shade_page_front.html) (materials, shaders) | :construction: | | |
| [UsdLux](https://openusd.org/release/api/usd_lux_page_front.html) (lighting) | :white_check_mark: | `main` | Schema reader behind `lux` feature. Covers all 8 concrete light prims (`DistantLight`, `SphereLight`, `RectLight`, `DiskLight`, `CylinderLight`, `DomeLight` + `DomeLight_1`, `GeometryLight`, `PortalLight`) and the applied `LightAPI` / `ShapingAPI` / `ShadowAPI` / `LightListAPI`. Pixar-exact defaults (incl. `DistantLight.intensity = 50000` override). No authoring helpers. |
| [UsdSkel](https://openusd.org/release/api/usd_skel_page_front.html) (skeletons, skinning) | :white_check_mark: | `main` | Schema reader behind `skel` feature. Covers `SkelRoot`, `Skeleton`, `SkelAnimation`, `BlendShape` (incl. inbetween shapes), and `SkelBindingAPI` with namespace-inherited `skel:skeleton` / `skel:animationSource`. No authoring helpers; stage-level interpolation of SkelAnimation time samples is left to the consumer. |
| [UsdVol](https://openusd.org/release/api/usd_vol_page_front.html) (volumes) | :construction: | | |
| [UsdPhysics](https://openusd.org/release/api/usd_physics_page_front.html) schema reader | :white_check_mark: | `main` | Reader behind `physics` feature. Covers all 8 prim types, 7 single-apply APIs, `LimitAPI` + `DriveAPI` multi-apply. No authoring helpers; collection evaluation for `CollisionGroup` is tracked under Spec 15. |
| [UsdRender](https://openusd.org/release/api/usd_render_page_front.html) | :construction: | | |
| UsdMedia, UsdUI, UsdProc | :construction: | | |
| [Flatten / export](https://openusd.org/release/api/flatten_utils_8h.html) | :construction: | | |
| [Namespace editing](https://openusd.org/release/api/class_usd_namespace_editor.html) | :construction: | | |
| [Native instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) (shared representation) | :construction: | | |
| [Stage cache](https://openusd.org/release/api/class_usd_utils_stage_cache.html) | :thinking: | | Avoid redundant stage loading |
| [Kind registry](https://openusd.org/release/api/class_kind_registry.html) | :thinking: | | Model/group/assembly/component taxonomy |
| [Edit targets](https://openusd.org/release/api/class_usd_edit_target.html) | :construction: | | Minimal subset landed: `EditTarget { layer_index }` + `Stage::edit_target` / `set_edit_target` routes Stage-tier authoring writes. Missing: `PcpMapFunction`-based path mapping for variant / reference / specialize edit contexts, RAII `UsdEditContext` analog, and `LayerStackIdentifier`-keyed targets (currently a bare `usize`). |
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
