// The families this crate exposes, shared by the build script that generates
// them and the test that checks what it generated.
//
// Included by both rather than declared as a module: `build.rs` is its own
// crate, so a module of the library is not reachable from it. Whatever
// configures the generator has to be the same on both sides — a test
// comparing against a differently-configured generator would be comparing the
// wrong thing — and one copy is how that is guaranteed. Both includers carry
// `use std::path::Path`, which is what `configured` names its argument by.

/// Each family as the Cargo feature that enables it and the library its
/// definitions declare.
///
/// The Rust path a library's views live at is what a *later* library inherits
/// through: `usdLux`'s lights are `usdGeom` xformables, so generating the lux
/// views needs to know where the geom ones are. Every family is named for
/// that, whether or not a build generates it, since the feature graph is what
/// keeps a view from deriving from a module that is not there.
const FAMILIES: [(&str, &str); 10] = [
    ("geom", "usdGeom"),
    ("lux", "usdLux"),
    ("media", "usdMedia"),
    ("physics", "usdPhysics"),
    ("proc", "usdProc"),
    ("render", "usdRender"),
    ("shade", "usdShade"),
    ("skel", "usdSkel"),
    ("ui", "usdUI"),
    ("vol", "usdVol"),
];

/// A generator that resolves every family, whether or not this build generates
/// it, with `schemas` as the directory their sublayers resolve through.
///
/// The token enums are configured here too, each named and sourced from the one
/// property that defines it. A token set is not an identity: `visibility` and
/// `guideVisibility` admit different tokens under one obvious name, and
/// `guideVisibility` falls back to `invisible` where `proxyVisibility` and
/// `renderVisibility` admit the same tokens and fall back to `inherited`. So
/// nothing is shared automatically — an enum exists because it is named here,
/// and a property free to use one does so at the call site. An enum whose
/// library this build does not generate produces nothing, so the list does not
/// have to know which features are on.
///
/// A token set no single property declares gets no enum: `Interpolation` and
/// `Dof` are not `allowedTokens` at all, and `CurveBasis` names a `hermite`
/// basis its schema's property does not admit. Those stay hand-written.
fn configured(schemas: &Path) -> openusd_build::Builder {
    use openusd_build::TokenEnum;

    let mut builder = openusd_build::configure().search_path(schemas);
    for (family, library) in FAMILIES {
        builder = builder.extern_library(library, format!("crate::{family}"));
    }

    builder
        .token_enum(TokenEnum::new("Visibility", "usdGeom", "Imageable.visibility").with_default())
        .token_enum(TokenEnum::new("Purpose", "usdGeom", "Imageable.purpose").with_default())
        .token_enum(TokenEnum::new("Orientation", "usdGeom", "Gprim.orientation").with_default())
        .token_enum(TokenEnum::new("Axis", "usdGeom", "Cylinder.axis").with_default())
        .token_enum(TokenEnum::new("ElementType", "usdGeom", "GeomSubset.elementType").with_default())
        .token_enum(TokenEnum::new("SubdivisionScheme", "usdGeom", "Mesh.subdivisionScheme").with_default())
        .token_enum(TokenEnum::new("InterpolateBoundary", "usdGeom", "Mesh.interpolateBoundary").with_default())
        .token_enum(
            TokenEnum::new(
                "FaceVaryingLinearInterpolation",
                "usdGeom",
                "Mesh.faceVaryingLinearInterpolation",
            )
            .with_default(),
        )
        .token_enum(TokenEnum::new("TriangleSubdivisionRule", "usdGeom", "Mesh.triangleSubdivisionRule").with_default())
        .token_enum(TokenEnum::new("PatchForm", "usdGeom", "NurbsPatch.uForm").with_default())
        .token_enum(TokenEnum::new("CurveType", "usdGeom", "BasisCurves.type").with_default())
        .token_enum(TokenEnum::new("CurveWrap", "usdGeom", "BasisCurves.wrap").with_default())
        .token_enum(TokenEnum::new("Projection", "usdGeom", "Camera.projection").with_default())
        .token_enum(TokenEnum::new("StereoRole", "usdGeom", "Camera.stereoRole").with_default())
        // Its source documents a fallback in prose but declares none, so the
        // enum gets no `Default` here; `lux` writes the one it needs by hand.
        .token_enum(TokenEnum::new(
            "LightListCacheBehavior",
            "usdLux",
            "LightListAPI.lightList:cacheBehavior",
        ))
        .token_enum(TokenEnum::new("TextureFormat", "usdLux", "DomeLight.inputs:texture:format").with_default())
        // `scene` is the up axis the stage declares, which `SceneUp` says and
        // `Scene` would not.
        .token_enum(
            TokenEnum::new("PoleAxis", "usdLux", "DomeLight_1.poleAxis")
                .with_default()
                .variant("scene", "SceneUp"),
        )
        .token_enum(TokenEnum::new("AuralMode", "usdMedia", "SpatialAudio.auralMode").with_default())
        .token_enum(TokenEnum::new("PlaybackMode", "usdMedia", "SpatialAudio.playbackMode").with_default())
        .token_enum(TokenEnum::new("JointAxis", "usdPhysics", "PhysicsRevoluteJoint.physics:axis").with_default())
        .token_enum(TokenEnum::new("DriveType", "usdPhysics", "PhysicsDriveAPI.physics:type").with_default())
        .token_enum(
            TokenEnum::new(
                "CollisionApprox",
                "usdPhysics",
                "PhysicsMeshCollisionAPI.physics:approximation",
            )
            .with_default(),
        )
        .token_enum(
            TokenEnum::new(
                "AspectRatioConformPolicy",
                "usdRender",
                "RenderSettingsBase.aspectRatioConformPolicy",
            )
            .with_default(),
        )
        .token_enum(TokenEnum::new("ProductType", "usdRender", "RenderProduct.productType").with_default())
        .token_enum(TokenEnum::new("SourceType", "usdRender", "RenderVar.sourceType").with_default())
        .token_enum(
            TokenEnum::new("ImplementationSource", "usdShade", "NodeDefAPI.info:implementationSource").with_default(),
        )
        .token_enum(
            TokenEnum::new("SkinningMethod", "usdSkel", "SkelBindingAPI.primvars:skel:skinningMethod").with_default(),
        )
        // The only source that declares no fallback and needs none.
        .token_enum(TokenEnum::new(
            "ExpansionState",
            "usdUI",
            "NodeGraphNodeAPI.ui:nodegraph:node:expansionState",
        ))
        // `None` is a role the data can carry, not the absence of one.
        .token_enum(
            TokenEnum::new("VectorDataRoleHint", "usdVol", "VolumeFieldAsset.vectorDataRoleHint")
                .with_default()
                .variant("None", "NoRole"),
        )
}
