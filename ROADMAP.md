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
| Spline specialized type | `7.4.2.4` | :construction: | | SplineKnot, interpolation modes, extrapolation, looping |
| Retiming specialized type ([layer offsets](https://openusd.org/release/glossary.html#usdglossary-layeroffset)) | `7.6.1.2.2` | :white_check_mark: | `0.1.2` | `0.1.2` — parsed from `subLayerOffsets`<br>`0.4.0` — composed through arcs<br>`main` — applied during value resolution (§12.3.2.1) |

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
| Sublayer offset composition | `10.3.1.1` | :white_check_mark: | `0.4.0` | Effective sublayer offsets composed through nested sublayers<br>Carried on each `Node` via `MapFunction::time_offset`<br>Applied during value resolution (§12.3.2.1)<br>`scale <= 0` falls back to identity via `LayerOffset::sanitized()` |
| [References](https://openusd.org/release/api/class_usd_references.html) (internal + external) | `10.3.2.1` | :white_check_mark: | `0.1.2` | Including `defaultPrim` fallback |
| Reference [namespace mapping](https://openusd.org/release/api/class_pcp_map_function.html) | `10.3.2.1.1` | :white_check_mark: | `0.3.0` | `MapFunction` with source/target pairs |
| Reference offset composition | `10.3.2.1.2` | :white_check_mark: | `0.4.0` | Reference offsets carried through reference arcs and composed with target layer-stack offsets<br>Applied during value resolution (§12.3.2.1)<br>`scale <= 0` falls back to identity via `LayerOffset::sanitized()` |
| [Payloads](https://openusd.org/release/api/class_usd_payloads.html) | `10.3.2.2` | :white_check_mark: | `0.1.2` | Treated identically to references |
| [Payload loading control](https://openusd.org/release/api/class_usd_stage_load_rules.html) | `10.3.2.2` | :white_check_mark: | `0.4.0` | `StageBuilder::initial_load_set` supports loading all payloads or leaving them unloaded |
| Payload offset composition | `10.3.2.2.2` | :white_check_mark: | `0.4.0` | Loaded payload offsets compose like references; unloaded payload offsets ignored<br>Applied during value resolution (§12.3.2.1)<br>`scale <= 0` falls back to identity via `LayerOffset::sanitized()` |
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
| [Population mask](https://openusd.org/release/api/class_usd_stage_population_mask.html) | `11.3` | :white_check_mark: | `0.4.0` | `StageBuilder::population_mask` limits stage queries, traversal, and root layer-stack dependency collection to a masked working set |
| Prim child discovery | `11.3.1` | :white_check_mark: | `0.2.0` | Merged `primChildren` with relocate adjustment. Full normative ordering is tracked in the `primOrder` row below. |
| Ordered prim children (`primOrder` reordering) | `11.3.1` | :construction: | | `0.4.0` — strongest `primOrder` applied after the final merge<br>Remaining — merge weakest-to-strongest<br>Remaining — apply relocates per layer stack<br>Remaining — reapply `primOrder` after every merge |
| Ordered property children | `11.3.2` | :white_check_mark: | `0.2.0` | Merged `propertyChildren` |
| Ordered property children (`propertyOrder` reordering) | `11.3.2` | :white_check_mark: | `0.4.0` | Strongest opinion applied via `sdf::apply_ordering` |
| [Scene graph instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) | `11.3.3` | :white_check_mark: | `main` | Instances sharing a composition reuse one prototype, composed once (`Cache` instancing key + canonical registry)<br>Local opinions on an instance's subtree are discarded; children and values come only from the arcs<br>Queries: `Stage`/`Prim` `get_prototype` / `get_instances` / `is_prototype` / `is_in_prototype`, `PrimStatus::IN_PROTOTYPE`, and a `PrimPredicate::with_instance_proxies` traversal toggle (default stops at instances)<br>Connection targets inside an instance remap into the queried instance; nested instances supported; prototype registry invalidated on composition change<br>Remaining — materialized `/__Prototype_N` namespace (prototype-root attributes are alias-backed by the canonical instance), relationship-target remap (gated on relationship target forwarding, §12.4), and parallel prototype composition |
| Model hierarchy (kind) | `11.4` | :white_check_mark: | `0.4.0` | `Stage::is_model`/`is_group`/`is_component`/`is_subcomponent` validate the contiguous kind hierarchy |
| [Stage queries](https://openusd.org/release/api/prim_flags_8h.html) (Active, Loaded, Defined, Abstract, Instance, InPrototype) | `11.5` | :white_check_mark: | `0.4.0` | `Stage::is_active`/`is_loaded`/`is_defined`/`is_abstract`/`is_instance`, `prim_status`, and `PrimPredicate` traversal filtering<br>`main` — `PrimStatus::IN_PROTOTYPE` and the instance-proxy traversal toggle (see Scene graph instancing, §11.3.3) |
| [Session layer](https://openusd.org/release/glossary.html#usdglossary-sessionlayer) | `11.2` | :white_check_mark: | `0.3.0` | `StageBuilder::session_layer` |

## Value Resolution (Spec 12)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| Metadata resolution (strongest opinion wins) | `12.2` | :white_check_mark: | `0.2.0` | `PrimIndex::resolve_field` with `ValueBlock` support for scalar fields<br>Special field classes are tracked separately below |
| Specifier resolution | `12.2.1` | :white_check_mark: | `0.4.0` | `def`/`class`/`over` precedence with direct-inherit awareness in `PrimIndex::resolve_specifier` |
| typeName resolution (from prim definition) | `12.2.2` | :construction: | | Uses strongest opinion, not prim definition |
| variability resolution (weakest opinion) | `12.2.3` | :white_check_mark: | `0.4.0` | Weakest authored opinion via `PrimIndex::resolve_variability` |
| custom field resolution (any-true) | `12.2.4` | :white_check_mark: | `0.4.0` | Logical OR across opinions via `PrimIndex::resolve_custom` |
| Dictionary combining | `12.2.5` | :white_check_mark: | `0.4.0` | Recursive merge across dictionary-valued opinions |
| List op resolution | `12.2.6` | :construction: | | `0.2.0` — composition-arc list ops<br>`0.4.0` — composed `apiSchemas`<br>`main` — composed `connectionPaths` and `targetPaths` via `PrimIndex::resolve_path_list_op`; `clipSets` order folded across layers via `PrimIndex::clip_sets_order`<br>Remaining — schema-registry-driven generic list-op field resolution so any field declared list-op composes without a hand-wired call site |
| Layer metadata (root layer only) | `12.2.7` | :white_check_mark: | `0.2.0` | `defaultPrim`, timing fields, etc. |
| Fallback values | `12.2.8` | :construction: | | Requires schema registry |
| Basic attribute resolution | `12.3` | :white_check_mark: | `main` | `0.2.0` — resolves authored `default`, `timeSamples`, and `ValueBlock`<br>`main` — layer-offset retiming applied<br>Value clips and splines are tracked separately |
| Time-sample lookup and interpolation | `12.3, 12.5.1-2` | :white_check_mark: | `main` | `0.1.2` — time-sample parsing<br>`0.4.0` — `Stage::value_at` performs held/linear interpolation over composed samples<br>`main` — per-node retiming and value clips |
| Layer-offset retiming during value resolution | `12.3.2.1` | :white_check_mark: | `main` | `PrimIndex::resolve_time_samples` maps each contributing node's authored sample times to stage time through the node's composed `map_to_root` offset (`stage_t = scale * layer_t + offset`)<br>Covers sublayer/reference/payload offsets<br>Strongest opinion wins among `timeSamples` nodes; `ValueBlock` blocks weaker layers<br>Cross-layer `default` vs `timeSamples` strength ordering is tracked under basic attribute resolution |
| Spline evaluation | `12.5.3` | :construction: | | Bezier/Hermite curve interpolation |
| Interpolation (Held) | `12.5.1` | :white_check_mark: | `0.4.0` | `Stage::value_at(attr, time)` with `InterpolationType::Held`. |
| Interpolation (Linear) | `12.5.2` | :white_check_mark: | `0.4.0` | `Stage::value_at(attr, time)` with `InterpolationType::Linear` (default)<br>All §12.5.2 types incl. `quath`/`f`/`d` via slerp<br>Held-fallback for unsupported types and past-last-sample |
| [Value clips](https://openusd.org/release/api/_usd__page__value_clips.html) | `12.3.4` | :construction: | | `main` — explicit clips resolved during `Stage::value_at`: `clips`/`clipSets` parsing, manifest gating, active-clip selection, stage-to-clip time mapping (incl. jump discontinuities), and clip strength below local L (`Cache::value_at`); `Prim::has_clips`/`clip_sets` introspection<br>Remaining — template clips (§12.3.4), `interpolateMissingClipValues` / missing-value sentinels (§12.3.4), and `UsdClipsAPI` authoring |
| Relationship targets (raw + forwarded) | `12.4` | :white_check_mark: | `main` | Composed raw `targetPaths` via `Stage::relationship_targets` / `Relationship::get_targets`, folding list-op edits across every contributing layer and remapping through arcs (shares `Cache::property_targets` with connections); `has_authored_targets` introspection<br>Forwarded targets via `Stage::forwarded_relationship_targets` / `Relationship::get_forwarded_targets`, recursively chasing relationship-to-relationship chains to prim/attribute terminals with cycle breaking and dedup |
| Attribute connections | `12.4` | :white_check_mark: | `main` | `Stage::connection_paths` folds list-op edits across every contributing layer via `PrimIndex::resolve_path_list_op`<br>Authoring on `Attribute`: `set_connections`, `add_connection`, `add_connection_prepended`, `remove_connection`, `clear_connections`, `has_authored_connections`<br>Stage-wide `usd::ConnectionGraph` indexes every edge and resolves chains to terminal sources |

## Schemas (Spec 13)

| Feature | Spec | Status | Version | Notes |
|---|---|---|---|---|
| [Schema registry](https://openusd.org/release/api/class_usd_schema_registry.html) | `13.3` | :construction: | | Type hierarchy, prim definitions |
| [Typed schemas](https://openusd.org/release/api/class_usd_typed.html) (IsA) | `13.3.1` | :construction: | | `typeName` readable; registry not implemented |
| [Applied schemas](https://openusd.org/release/api/class_usd_a_p_i_schema_base.html) (HasA) | `13.3.2` | :construction: | | `main` — `apiSchemas` list-ops compose across contributing layers; `Prim::add_applied_schema` authors registry-free applied schema tokens by merging into the local list op<br>Remaining — schema registry (§13.3), single/multiple application validation (§13.3.2), built-in/auto-apply inclusions (§13.3.2.1), composed prim definitions (§13.3), and fallback property values (§12.2.8) |
| Schema inclusions (built-ins, auto-applies) | `13.3.2.1` | :construction: | | |
| Prim definitions (property fallbacks) | `13.3` | :construction: | | |
| Core schema types | `13.4` | :construction: | | |
| [Value type names](https://openusd.org/release/api/class_sdf_value_type_name.html) | `13.3` | :construction: | | Attribute type validation |
| Extension metadata fields (fallbackPrimTypes, apiSchemas, clips, clipSets) | `13.2` | :construction: | | Fields readable; `apiSchemas` list-op composition applied; explicit value-clip semantics for `clips`/`clipSets` resolved during value resolution (§12.3.4)<br>Remaining — composed-prim `fallbackPrimTypes` (§13.2), template/missing-value clip behavior (§12.3.4), and any schema-domain behavior layered on these fields |
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
| USDA (text) writing | `16.2` | :white_check_mark: | `0.4.0` | `usda::TextWriter`; round-trips the compliance suite opinion-for-opinion |
| USDC (binary) reading | `16.3` | :white_check_mark: | `0.1.1` | Crate format with LZ4/integer compression |
| USDC (binary) writing | `16.3` | :white_check_mark: | `0.4.0` | `usdc::CrateWriter`; streaming packer with integer compression, LZ4 blocks, DFS path encoder |
| USDZ (package) reading | `16.4` | :white_check_mark: | `0.2.0` | ZIP-based package reader |
| USDZ (package) writing | `16.4` | :white_check_mark: | `0.4.0` | `usdz::ArchiveWriter`; STORED-only, 64-byte aligned entries |
| Format auto-detection (`.usd`) | `16.1` | :white_check_mark: | `0.2.0` | Magic byte detection |

## Beyond Core Spec

Features from the C++ reference implementation not covered by the core specification.

| Feature | Status | Version | Notes |
|---|---|---|---|
| [Variable expressions](https://openusd.org/release/api/_sdf__page__variable_expressions.html) | :white_check_mark: | `0.2.0` | 13 built-in functions, string interpolation (`expr` module) |
| Parallelism (Rayon) | :construction: | | Composition graph is `&`-only, ready for parallel execution |
| [Incremental invalidation](https://openusd.org/release/api/class_pcp_changes.html) | :thinking: | | Dependency tracking and change processing |
| [UsdGeom](https://openusd.org/release/api/usd_geom_page_front.html) (geometry, transforms, cameras) | :white_check_mark: | `0.4.0` | Schema reader behind `geom` feature<br>Cross-cutting Imageable / Boundable (visibility / purpose / extent / kind)<br>Xformable with full `xformOpOrder` evaluator (`!invert!`, `!resetXformStack!`, every rotation order)<br>Intrinsic shapes: Cube, Sphere, Cylinder, Capsule, Cone, Plane, Xform<br>Camera (full attribute set with FOV helpers)<br>Mesh + GeomSubset + PrimvarsAPI (subdivision, creases, corners, holes, primvar interpolation)<br>BasisCurves, NurbsCurves, NurbsPatch, HermiteCurves, Points, TetMesh<br>PointInstancer<br>Remaining — authoring helpers, ModelAPI / MotionAPI / VisibilityAPI / BBoxCache / XformCache |
| [UsdShade](https://openusd.org/release/api/usd_shade_page_front.html) (materials, shaders) | :construction: | | |
| [UsdLux](https://openusd.org/release/api/usd_lux_page_front.html) (lighting) | :white_check_mark: | `0.4.0` | Schema reader behind `lux` feature<br>All 8 concrete light prims: `DistantLight`, `SphereLight`, `RectLight`, `DiskLight`, `CylinderLight`, `DomeLight` + `DomeLight_1`, `GeometryLight`, `PortalLight`<br>Applied `LightAPI` / `ShapingAPI` / `ShadowAPI` / `LightListAPI`<br>Pixar-exact defaults (incl. `DistantLight.intensity = 50000` override)<br>Remaining — authoring helpers |
| [UsdSkel](https://openusd.org/release/api/usd_skel_page_front.html) (skeletons, skinning) | :white_check_mark: | `0.4.0` | Schema reader behind `skel` feature<br>Covers `SkelRoot`, `Skeleton`, `SkelAnimation`, `BlendShape` (incl. inbetween shapes)<br>`SkelBindingAPI` with namespace-inherited `skel:skeleton` / `skel:animationSource`<br>Remaining — authoring helpers; stage-level interpolation of SkelAnimation time samples (left to the consumer) |
| [UsdVol](https://openusd.org/release/api/usd_vol_page_front.html) (volumes) | :construction: | | |
| [UsdPhysics](https://openusd.org/release/api/usd_physics_page_front.html) schema reader | :white_check_mark: | `0.4.0` | Reader behind `physics` feature<br>All 8 prim types, 7 single-apply APIs<br>`LimitAPI` + `DriveAPI` multi-apply<br>Remaining — authoring helpers; collection evaluation for `CollisionGroup` (tracked under Spec 15) |
| [UsdRender](https://openusd.org/release/api/usd_render_page_front.html) | :construction: | | |
| UsdMedia, UsdUI, UsdProc | :construction: | | |
| [Flatten / export](https://openusd.org/release/api/flatten_utils_8h.html) | :construction: | | |
| [Namespace editing](https://openusd.org/release/api/class_usd_namespace_editor.html) | :construction: | | |
| [Native instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) (shared representation) | :white_check_mark: | `main` | Scene-graph instancing (see §11.3.3) — instances share one composed prototype<br>The shared representation is alias-backed by the canonical instance; materializing `/__Prototype_N` as an independently composed namespace is the remaining C++-parity gap |
| [Stage cache](https://openusd.org/release/api/class_usd_utils_stage_cache.html) | :thinking: | | Avoid redundant stage loading |
| [Kind registry](https://openusd.org/release/api/class_kind_registry.html) | :thinking: | | Model/group/assembly/component taxonomy |
| [Edit targets](https://openusd.org/release/api/class_usd_edit_target.html) | :construction: | | `EditTarget` pairs a `layer_index` with a `pcp::MapFunction`; authoring routes through `with_target_layer_at` / `map_to_spec_path`<br>`EditTarget::for_local_direct_variant` maps writes into a variant's `{set=sel}` namespace; `EditContext` is the RAII `UsdEditContext` analog (`Stage::edit_context`)<br>Remaining — `sdf::Layer` variant-spec authoring so variant edit targets work end-to-end<br>Remaining — arc-based path mapping for reference / specialize edit contexts<br>Remaining — `LayerStackIdentifier`-keyed targets (currently a bare `usize`) |
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
