//! Token constants for the [UsdShade](super) schema family.
//!
//! Centralised so consumers match against canonical strings instead of
//! retyping literals. Mirrors the grouping in Pixar's
//! `pxr/usd/usdShade/tokens.h`.

// ── Concrete prim type names ────────────────────────────────────────
pub const T_MATERIAL: &str = "Material";
pub const T_NODE_GRAPH: &str = "NodeGraph";
pub const T_SHADER: &str = "Shader";

// ── API schemas ─────────────────────────────────────────────────────
pub const API_NODE_DEF: &str = "NodeDefAPI";
pub const API_MATERIAL_BINDING: &str = "MaterialBindingAPI";

// ── Property namespace prefixes ─────────────────────────────────────
/// Input attributes are authored as `inputs:<base>`.
pub const NS_INPUTS: &str = "inputs:";
/// Output attributes are authored as `outputs:<base>`.
pub const NS_OUTPUTS: &str = "outputs:";

// ── NodeDefAPI (Shader) attribute names ─────────────────────────────
pub const A_INFO_ID: &str = "info:id";
pub const A_INFO_IMPLEMENTATION_SOURCE: &str = "info:implementationSource";
pub const A_INFO_SOURCE_ASSET: &str = "info:sourceAsset";
pub const A_INFO_SOURCE_CODE: &str = "info:sourceCode";
pub const A_INFO_SOURCE_ASSET_SUBIDENTIFIER: &str = "info:sourceAsset:subIdentifier";

// `info:implementationSource` token values.
pub const IMPL_SOURCE_ID: &str = "id";
pub const IMPL_SOURCE_SOURCE_ASSET: &str = "sourceAsset";
pub const IMPL_SOURCE_SOURCE_CODE: &str = "sourceCode";

// ── Material / NodeGraph terminal output base names ─────────────────
pub const TERMINAL_SURFACE: &str = "surface";
pub const TERMINAL_DISPLACEMENT: &str = "displacement";
pub const TERMINAL_VOLUME: &str = "volume";

/// Universal render context — authored with no context segment, i.e.
/// the bare `outputs:surface` rather than `outputs:<ctx>:surface`.
pub const UNIVERSAL_RENDER_CONTEXT: &str = "";

// `outputs:surface` etc. on the universal render context.
pub const A_OUTPUTS_SURFACE: &str = "outputs:surface";
pub const A_OUTPUTS_DISPLACEMENT: &str = "outputs:displacement";
pub const A_OUTPUTS_VOLUME: &str = "outputs:volume";

// ── Connectability metadata (UsdShadeInput) ─────────────────────────
pub const META_CONNECTABILITY: &str = "connectability";
pub const CONNECTABILITY_FULL: &str = "full";
pub const CONNECTABILITY_INTERFACE_ONLY: &str = "interfaceOnly";

// ── MaterialBindingAPI relationship names + binding metadata ────────
pub const REL_MATERIAL_BINDING: &str = "material:binding";
pub const REL_MATERIAL_BINDING_COLLECTION: &str = "material:binding:collection";
/// `bindMaterialAs` metadata on a binding relationship records the
/// binding strength.
pub const META_BIND_MATERIAL_AS: &str = "bindMaterialAs";

// Binding-strength token values (`bindMaterialAs`).
pub const STRENGTH_WEAKER_THAN_DESCENDANTS: &str = "weakerThanDescendants";
pub const STRENGTH_STRONGER_THAN_DESCENDANTS: &str = "strongerThanDescendants";

// Material-binding purpose token values. `allPurpose` is the empty
// token (the fallback binding `material:binding`).
pub const PURPOSE_ALL: &str = "";
pub const PURPOSE_FULL: &str = "full";
pub const PURPOSE_PREVIEW: &str = "preview";

// ── Canonical UsdPreviewSurface shader id + input/output names ──────
pub const SHADER_ID_PREVIEW_SURFACE: &str = "UsdPreviewSurface";
pub const SHADER_ID_UV_TEXTURE: &str = "UsdUVTexture";
pub const SHADER_ID_PRIMVAR_READER_FLOAT2: &str = "UsdPrimvarReader_float2";

// UsdPreviewSurface inputs (`inputs:<name>`).
pub const PS_DIFFUSE_COLOR: &str = "diffuseColor";
pub const PS_EMISSIVE_COLOR: &str = "emissiveColor";
pub const PS_METALLIC: &str = "metallic";
pub const PS_ROUGHNESS: &str = "roughness";
pub const PS_CLEARCOAT: &str = "clearcoat";
pub const PS_CLEARCOAT_ROUGHNESS: &str = "clearcoatRoughness";
pub const PS_OPACITY: &str = "opacity";
pub const PS_OPACITY_THRESHOLD: &str = "opacityThreshold";
pub const PS_IOR: &str = "ior";
pub const PS_NORMAL: &str = "normal";
pub const PS_DISPLACEMENT: &str = "displacement";
pub const PS_OCCLUSION: &str = "occlusion";
pub const PS_SPECULAR_COLOR: &str = "specularColor";
pub const PS_USE_SPECULAR_WORKFLOW: &str = "useSpecularWorkflow";

// UsdUVTexture inputs / outputs.
pub const TEX_FILE: &str = "file";
pub const TEX_ST: &str = "st";
pub const TEX_WRAP_S: &str = "wrapS";
pub const TEX_WRAP_T: &str = "wrapT";
pub const TEX_FALLBACK: &str = "fallback";
pub const TEX_SCALE: &str = "scale";
pub const TEX_BIAS: &str = "bias";
pub const TEX_SOURCE_COLOR_SPACE: &str = "sourceColorSpace";
pub const TEX_OUT_R: &str = "r";
pub const TEX_OUT_G: &str = "g";
pub const TEX_OUT_B: &str = "b";
pub const TEX_OUT_A: &str = "a";
pub const TEX_OUT_RGB: &str = "rgb";

// UsdPrimvarReader inputs / outputs.
pub const PVR_VARNAME: &str = "varname";
pub const PVR_OUT_RESULT: &str = "result";
