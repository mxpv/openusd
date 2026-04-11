# Roadmap and Feature Parity

Comparison with the C++ reference implementation ([OpenUSD](https://github.com/PixarAnimationStudios/OpenUSD)).

| Feature | Status | Version | Notes |
|---|---|---|---|
| **File Formats** | | | |
| USDA (text) reading | :white_check_mark: Supported | 0.1.4 | Recursive descent parser with logos tokenizer |
| USDC (binary) reading | :white_check_mark: Supported | 0.1.1 | Crate format with LZ4 and integer compression |
| USDZ (archive) reading | :white_check_mark: Supported | 0.2.0 | ZIP-based package reader |
| Format auto-detection (`.usd`) | :white_check_mark: Supported | 0.2.0 | Magic byte detection |
| USDA (text) writing | :construction: Planned | | |
| USDC (binary) writing | :construction: Planned | | |
| USDZ (archive) writing | :construction: Planned | | |
| **Composition** | | | |
| [Sublayers](https://openusd.org/release/glossary.html#usdglossary-sublayers) | :white_check_mark: Supported | 0.1.2 | |
| [Inherits](https://openusd.org/release/api/class_usd_inherits.html) | :white_check_mark: Supported | 0.2.0 | |
| [Variants](https://openusd.org/release/api/class_usd_variant_sets.html) | :white_check_mark: Supported | 0.2.0 | |
| [References](https://openusd.org/release/api/class_usd_references.html) | :white_check_mark: Supported | 0.1.2 | |
| [Payloads](https://openusd.org/release/api/class_usd_payloads.html) | :white_check_mark: Supported | 0.1.2 | |
| [Specializes](https://openusd.org/release/api/class_usd_specializes.html) | :white_check_mark: Supported | 0.2.0 | |
| LIVERPS strength ordering | :white_check_mark: Supported | 0.2.0 | [What is LIVERPS?](https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html) |
| [List editing](https://openusd.org/release/glossary.html#usdglossary-listediting) (prepend/append/add/delete/explicit) | :white_check_mark: Supported | 0.2.0 | |
| Composition error reporting | :white_check_mark: Supported | | `pcp::Error` with `StageBuilder::on_error` callback |
| Node graph (PrimIndex) | :white_check_mark: Supported | | Arena-based node graph with per-node namespace mapping |
| Variant fallbacks | :construction: Planned | | `PcpVariantFallbackMap` — application-level default selections |
| [Session layer](https://openusd.org/release/glossary.html#usdglossary-sessionlayer) | :construction: Planned | | Non-destructive override layer on top of root |
| [Layer offsets](https://openusd.org/release/glossary.html#usdglossary-layeroffset) | :construction: Planned | | Time scale/offset for sublayers and references (already parsed) |
| [Payload loading control](https://openusd.org/release/api/class_usd_stage_load_rules.html) | :construction: Planned | | Dynamic include/exclude set for deferred payloads |
| [Relocates](https://openusd.org/release/glossary.html#usdglossary-relocates) | :construction: Planned | | Non-destructive namespace reorganization |
| [Incremental invalidation](https://openusd.org/release/api/class_pcp_changes.html) | :thinking: Considering | | Dependency tracking and change processing (`PcpChanges`) |
| Composition graph visualization | :thinking: Considering | | `dot` format export for debugging composition |
| [Map functions](https://openusd.org/release/api/class_pcp_map_function.html) | :white_check_mark: Supported | | `map_to_parent`/`map_to_root` namespace translation on nodes via `MapFunction` |
| **Scene Graph (Usd)** | | | |
| Composed stage | :white_check_mark: Supported | 0.2.0 | `Stage::open`, traverse, field queries |
| Generic field access | :white_check_mark: Supported | 0.2.0 | `Stage::field<T>` with path and field key |
| Time samples | :white_check_mark: Supported | 0.1.2 | |
| Value resolution across layers | :white_check_mark: Supported | 0.2.0 | First-opinion-wins with ValueBlock support |
| Prim typed wrapper | :construction: Planned | | `UsdPrim` with children, properties, metadata |
| Property typed wrapper | :construction: Planned | | `UsdProperty` base for attributes and relationships |
| Attribute typed wrapper | :construction: Planned | | `UsdAttribute` with value type, connections, interpolation |
| Relationship typed wrapper | :construction: Planned | | `UsdRelationship` with targets |
| [Native instancing](https://openusd.org/release/glossary.html#usdglossary-instancing) | :construction: Planned | | `instanceable` field is readable; composition sharing requires Node DAG |
| [Value clips](https://openusd.org/release/api/_usd__page__value_clips.html) | :construction: Planned | | |
| [Flatten / export](https://openusd.org/release/api/flatten_utils_8h.html) | :construction: Planned | | |
| [Namespace editing](https://openusd.org/release/api/class_usd_namespace_editor.html) | :construction: Planned | | |
| [Collection API](https://openusd.org/release/api/class_usd_collection_a_p_i.html) | :construction: Planned | | |
| [Prim predicates / filtered traversal](https://openusd.org/release/api/prim_flags_8h.html) | :thinking: Considering | | Composable filters (IsActive, IsDefined, IsLoaded, etc.) |
| [Stage population mask](https://openusd.org/release/api/class_usd_stage_population_mask.html) | :thinking: Considering | | Load only a subset of prims |
| [Load rules](https://openusd.org/release/api/class_usd_stage_load_rules.html) | :thinking: Considering | | Fine-grained payload loading control |
| [Edit targets](https://openusd.org/release/api/class_usd_edit_target.html) | :thinking: Considering | | Direct opinions to a specific layer |
| [Change notification](https://openusd.org/release/api/class_usd_notice.html) | :thinking: Considering | | Listeners for live scene updates |
| [Property stack queries](https://openusd.org/release/api/class_usd_resolve_info.html) | :thinking: Considering | | Inspect all contributing opinions across layers |
| **Data Types (Sdf/Vt/Gf)** | | | |
| Scalars, vectors, matrices, quaternions | :white_check_mark: Supported | 0.1.2 | All standard USD numeric types |
| Strings, tokens, asset paths | :white_check_mark: Supported | 0.1.1 | |
| Dictionaries | :white_check_mark: Supported | 0.1.2 | |
| Path expressions | :white_check_mark: Supported | 0.2.0 | |
| List operations | :white_check_mark: Supported | 0.2.0 | Token, string, path, reference, payload, int types |
| **Asset Resolution (Ar)** | | | |
| Resolver trait | :white_check_mark: Supported | 0.2.0 | Pluggable interface |
| Default filesystem resolver | :white_check_mark: Supported | 0.2.0 | With search paths and resolver contexts |
| Package-relative paths | :white_check_mark: Supported | 0.2.0 | USDZ sub-asset resolution |
| **Variable Expressions** | | | |
| [Expression syntax and evaluation](https://openusd.org/release/api/_sdf__page__variable_expressions.html) | :white_check_mark: Supported | 0.2.0 | 13 built-in functions, string interpolation |
| **Schema System** | | | |
| [Schema registry](https://openusd.org/release/api/class_usd_schema_registry.html) | :construction: Planned | | Type hierarchy, prim definitions |
| [Typed schemas (IsA)](https://openusd.org/release/api/class_usd_typed.html) | :construction: Planned | | Concrete and abstract prim types |
| [Applied API schemas (HasA)](https://openusd.org/release/api/class_usd_a_p_i_schema_base.html) | :construction: Planned | | Multi-apply and single-apply APIs |
| [Value type names](https://openusd.org/release/api/class_sdf_value_type_name.html) | :construction: Planned | | Attribute type validation |
| [Schema codegen](https://openusd.org/release/tut_generating_new_schema.html) | :construction: Planned | | Generate typed APIs from schema definitions |
| **Schema Domains** | | | |
| [UsdGeom](https://openusd.org/release/api/usd_geom_page_front.html) (geometry, transforms, cameras) | :construction: Planned | | |
| [UsdShade](https://openusd.org/release/api/usd_shade_page_front.html) (materials, shaders) | :construction: Planned | | |
| [UsdLux](https://openusd.org/release/api/usd_lux_page_front.html) (lighting) | :construction: Planned | | |
| [UsdSkel](https://openusd.org/release/api/usd_skel_page_front.html) (skeletons, skinning) | :construction: Planned | | |
| [UsdVol](https://openusd.org/release/api/usd_vol_page_front.html) (volumes) | :construction: Planned | | |
| [UsdPhysics](https://openusd.org/release/api/usd_physics_page_front.html) | :construction: Planned | | |
| [UsdRender](https://openusd.org/release/api/usd_render_page_front.html) | :construction: Planned | | |
| UsdMedia, UsdUI, UsdProc | :construction: Planned | | |
| [XformCache](https://openusd.org/release/api/class_usd_geom_xform_cache.html) | :thinking: Considering | | Cached transform evaluation |
| [BBoxCache](https://openusd.org/release/api/class_usd_geom_b_box_cache.html) | :thinking: Considering | | Cached bounding box computation |
| [PointInstancer](https://openusd.org/release/api/class_usd_geom_point_instancer.html) | :thinking: Considering | | Efficient mass instancing |
| [Primvar API](https://openusd.org/release/api/class_usd_geom_primvars_a_p_i.html) | :thinking: Considering | | Interpolated primvars with inheritance |
| [GeomSubset](https://openusd.org/release/api/class_usd_geom_subset.html) | :thinking: Considering | | Per-face material assignment |
| [Material binding API](https://openusd.org/release/api/class_usd_shade_material_binding_a_p_i.html) | :thinking: Considering | | Purpose-based and collection-based bindings |
| [Shader connectivity](https://openusd.org/release/api/class_usd_shade_connectable_a_p_i.html) | :thinking: Considering | | Connect inputs/outputs between shader nodes |
| **Rendering** | | | |
| Hydra / render delegates | :no_entry_sign:&nbsp;Out&nbsp;of&nbsp;scope | | |
| **Tooling** | | | |
| usdcat (print/convert) | :construction: Planned | | |
| usddiff (layer diffing) | :thinking: Considering | | |
| usdchecker (validation) | :thinking: Considering | | |
| usdtree (hierarchy printing) | :thinking: Considering | | |
| usdresolve (asset resolution testing) | :no_entry_sign:&nbsp;Out&nbsp;of&nbsp;scope | | |
| usdzip (USDZ packaging) | :thinking: Considering | | |
| usdview (interactive viewer) | :thinking: Considering | | Vulkan-based preview app |
| usdrecord (headless rendering) | :no_entry_sign:&nbsp;Out&nbsp;of&nbsp;scope | | Requires Hydra |
| usdGenSchema (schema codegen) | :construction: Planned | | |
| **Utilities** | | | |
| [Stage cache](https://openusd.org/release/api/class_usd_utils_stage_cache.html) | :thinking: Considering | | Avoid redundant stage loading |
| [Dependency analysis](https://openusd.org/release/api/dependencies_8h.html) | :thinking: Considering | | Compute external asset dependencies |
| [Stage metrics](https://openusd.org/release/api/group___usd_geom_up_axis__group.html) | :thinking: Considering | | upAxis, metersPerUnit |
| [Kind registry](https://openusd.org/release/api/class_kind_registry.html) | :thinking: Considering | | Model/group/assembly/component taxonomy |
| **Other** | | | |
| Plugin system | :no_entry_sign:&nbsp;Out&nbsp;of&nbsp;scope | | Resolver trait covers the extension point |
| Python bindings | :no_entry_sign:&nbsp;Out&nbsp;of&nbsp;scope | | Requires native C/C++ bindings |
| Parallelism (Rayon) | :construction: Planned | | Optional feature flag |
| Alembic plugin | :no_entry_sign:&nbsp;Out&nbsp;of&nbsp;scope | | |
