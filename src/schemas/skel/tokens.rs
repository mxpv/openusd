//! Token constants for the [UsdSkel](super) schema family.
//!
//! Centralised so consumers can match against canonical strings instead of
//! retyping literals. Mirrors the grouping in Pixar's
//! `pxr/usd/usdSkel/tokens.h`.

// Concrete prim type names.
pub const T_SKEL_ROOT: &str = "SkelRoot";
pub const T_SKELETON: &str = "Skeleton";
pub const T_SKEL_ANIMATION: &str = "SkelAnimation";
pub const T_BLEND_SHAPE: &str = "BlendShape";

// API schemas.
pub const API_SKEL_BINDING: &str = "SkelBindingAPI";

// Boundable attribute (shared with UsdGeom; mirrored here for the
// `SkelRoot` reader that decodes it).
pub const A_EXTENT: &str = "extent";

// Skeleton attribute names.
pub const A_JOINTS: &str = "joints";
pub const A_JOINT_NAMES: &str = "jointNames";
pub const A_BIND_TRANSFORMS: &str = "bindTransforms";
pub const A_REST_TRANSFORMS: &str = "restTransforms";

// SkelAnimation attribute names.
pub const A_TRANSLATIONS: &str = "translations";
pub const A_ROTATIONS: &str = "rotations";
pub const A_SCALES: &str = "scales";
pub const A_BLEND_SHAPES: &str = "blendShapes";
pub const A_BLEND_SHAPE_WEIGHTS: &str = "blendShapeWeights";

// BlendShape attribute names.
pub const A_OFFSETS: &str = "offsets";
pub const A_NORMAL_OFFSETS: &str = "normalOffsets";
pub const A_POINT_INDICES: &str = "pointIndices";

// Inbetween-shape namespace + weight metadata.
pub const NS_INBETWEENS: &str = "inbetweens:";
pub const META_WEIGHT: &str = "weight";

// SkelBindingAPI properties.
pub const A_SKEL_JOINTS: &str = "skel:joints";
pub const A_SKEL_BLEND_SHAPES: &str = "skel:blendShapes";
pub const REL_SKEL_BLEND_SHAPE_TARGETS: &str = "skel:blendShapeTargets";
pub const REL_SKEL_SKELETON: &str = "skel:skeleton";
pub const REL_SKEL_ANIMATION_SOURCE: &str = "skel:animationSource";
pub const A_JOINT_INDICES: &str = "primvars:skel:jointIndices";
pub const A_JOINT_WEIGHTS: &str = "primvars:skel:jointWeights";
pub const A_GEOM_BIND_TRANSFORM: &str = "primvars:skel:geomBindTransform";
pub const A_SKINNING_METHOD: &str = "primvars:skel:skinningMethod";

// Primvar metadata field names.
pub const META_INTERPOLATION: &str = "interpolation";
pub const META_ELEMENT_SIZE: &str = "elementSize";

// Skinning-method tokens (`primvars:skel:skinningMethod`).
pub const SKINNING_METHOD_CLASSIC_LINEAR: &str = "classicLinear";
pub const SKINNING_METHOD_DUAL_QUATERNION: &str = "dualQuaternion";

// Primvar interpolation tokens recognised on the joint-influences primvars.
pub const INTERP_CONSTANT: &str = "constant";
pub const INTERP_VERTEX: &str = "vertex";
