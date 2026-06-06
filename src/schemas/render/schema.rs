//! The UsdRender prim views: [`RenderSettings`], [`RenderProduct`],
//! [`RenderVar`], [`RenderPass`], and [`RenderDenoisePass`].

use anyhow::Result;

use crate::sdf::{self, Value, Variability};
use crate::usd::{Attribute, Prim, Relationship, Stage};

use super::impl_render_schema;
use super::tokens as tok;
use crate::schemas::common::get_typed;

/// The top-level render configuration (C++ `UsdRenderSettings`) — a
/// [`RenderSettingsBase`](super::RenderSettingsBase) that enumerates the
/// [`RenderProduct`]s to produce and the purposes / color space to render with.
#[derive(Clone, derive_more::Deref)]
pub struct RenderSettings(Prim);

impl RenderSettings {
    /// Author a `def RenderSettings` prim at `path`
    /// (C++ `UsdRenderSettings::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_RENDER_SETTINGS)?))
    }

    /// Wrap `path` as a `RenderSettings` if it is typed `RenderSettings`
    /// (C++ `UsdRenderSettings::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_RENDER_SETTINGS).map(|o| o.map(Self))
    }

    /// Resolve the stage's default `RenderSettings` from the
    /// `renderSettingsPrimPath` stage metadata (C++
    /// `UsdRenderSettings::GetStageRenderSettings`). Composes a session-layer
    /// opinion over the root layer; returns `None` when unauthored.
    ///
    /// Read-only: authoring this stage metadata needs a generic stage-metadata
    /// setter the core `Stage` API does not yet expose.
    pub fn stage_settings_path(stage: &Stage) -> Result<Option<sdf::Path>> {
        Ok(match stage.stage_metadata(tok::META_RENDER_SETTINGS_PRIM_PATH)? {
            Some(Value::String(s) | Value::Token(s) | Value::AssetPath(s)) => Some(sdf::Path::new(&s)?),
            _ => None,
        })
    }

    /// The `products` relationship — the `RenderProduct` prims to produce.
    /// C++ `UsdRenderSettings::GetProductsRel`.
    pub fn products_rel(&self) -> Relationship {
        self.relationship(tok::REL_PRODUCTS)
    }

    /// Author the `products` relationship (C++ `CreateProductsRel`).
    pub fn create_products_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::REL_PRODUCTS)?.set_custom(false)?)
    }

    /// The `UsdGeomImageable` purposes included in the render.
    /// C++ `UsdRenderSettings::GetIncludedPurposesAttr`.
    ///
    /// Type `uniform token[]`. Fetch with `get::<sdf::Value>()?` (a
    /// [`sdf::Value::TokenVec`]).
    pub fn included_purposes_attr(&self) -> Attribute {
        self.attribute(tok::A_INCLUDED_PURPOSES)
    }

    /// Author `includedPurposes` (`uniform token[]`)
    /// (C++ `CreateIncludedPurposesAttr`).
    pub fn create_included_purposes_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_INCLUDED_PURPOSES, "token[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// The ordered material-binding resolution priority.
    /// C++ `UsdRenderSettings::GetMaterialBindingPurposesAttr`.
    ///
    /// Type `uniform token[]`. Fetch with `get::<sdf::Value>()?` (a
    /// [`sdf::Value::TokenVec`]).
    pub fn material_binding_purposes_attr(&self) -> Attribute {
        self.attribute(tok::A_MATERIAL_BINDING_PURPOSES)
    }

    /// Author `materialBindingPurposes` (`uniform token[]`)
    /// (C++ `CreateMaterialBindingPurposesAttr`).
    pub fn create_material_binding_purposes_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_MATERIAL_BINDING_PURPOSES, "token[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// The renderer's linear working color space.
    /// C++ `UsdRenderSettings::GetRenderingColorSpaceAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<String>()?`.
    pub fn rendering_color_space_attr(&self) -> Attribute {
        self.attribute(tok::A_RENDERING_COLOR_SPACE)
    }

    /// Author `renderingColorSpace` (`uniform token`)
    /// (C++ `CreateRenderingColorSpaceAttr`).
    pub fn create_rendering_color_space_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_RENDERING_COLOR_SPACE, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }
}

impl_render_schema!(settings_base RenderSettings);

/// One output artifact of a render — an image or deep image (C++
/// `UsdRenderProduct`). A [`RenderSettingsBase`](super::RenderSettingsBase) that
/// inherits the framing attributes from its settings and may override any of
/// them, plus the product-specific type / name / composited vars.
#[derive(Clone, derive_more::Deref)]
pub struct RenderProduct(Prim);

impl RenderProduct {
    /// Author a `def RenderProduct` prim at `path`
    /// (C++ `UsdRenderProduct::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_RENDER_PRODUCT)?))
    }

    /// Wrap `path` as a `RenderProduct` if it is typed `RenderProduct`
    /// (C++ `UsdRenderProduct::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_RENDER_PRODUCT).map(|o| o.map(Self))
    }

    /// The kind of artifact this product emits (`raster` / `deepRaster`).
    /// C++ `UsdRenderProduct::GetProductTypeAttr`.
    ///
    /// Type `uniform token`. Fetch with
    /// `get::<`[`ProductType`](super::ProductType)`>()?`.
    pub fn product_type_attr(&self) -> Attribute {
        self.attribute(tok::A_PRODUCT_TYPE)
    }

    /// Author `productType` (`uniform token`) (C++ `CreateProductTypeAttr`).
    /// Pass a [`ProductType`](super::ProductType) to `set`.
    pub fn create_product_type_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_PRODUCT_TYPE, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// The output / display-driver name (e.g. a file name).
    /// C++ `UsdRenderProduct::GetProductNameAttr`. Authored varying `token`
    /// (not `uniform`), per the schema, so it can be time-sampled.
    ///
    /// Type `token`. Fetch with `get::<String>()?`.
    pub fn product_name_attr(&self) -> Attribute {
        self.attribute(tok::A_PRODUCT_NAME)
    }

    /// Author `productName` (`token`) (C++ `CreateProductNameAttr`).
    pub fn create_product_name_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_PRODUCT_NAME, "token")?.set_custom(false)?)
    }

    /// The `orderedVars` relationship — the `RenderVar` prims composited into
    /// this product, in order. C++ `UsdRenderProduct::GetOrderedVarsRel`.
    pub fn ordered_vars_rel(&self) -> Relationship {
        self.relationship(tok::REL_ORDERED_VARS)
    }

    /// Author the `orderedVars` relationship (C++ `CreateOrderedVarsRel`).
    pub fn create_ordered_vars_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::REL_ORDERED_VARS)?.set_custom(false)?)
    }
}

impl_render_schema!(settings_base RenderProduct);

/// One output channel of a render — an arbitrary output variable / AOV (C++
/// `UsdRenderVar`).
#[derive(Clone, derive_more::Deref)]
pub struct RenderVar(Prim);

impl RenderVar {
    /// Author a `def RenderVar` prim at `path` (C++ `UsdRenderVar::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_RENDER_VAR)?))
    }

    /// Wrap `path` as a `RenderVar` if it is typed `RenderVar`
    /// (C++ `UsdRenderVar::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_RENDER_VAR).map(|o| o.map(Self))
    }

    /// The channel's USD attribute type (e.g. `color3f`, `float`).
    /// C++ `UsdRenderVar::GetDataTypeAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<String>()?`.
    pub fn data_type_attr(&self) -> Attribute {
        self.attribute(tok::A_DATA_TYPE)
    }

    /// Author `dataType` (`uniform token`) (C++ `CreateDataTypeAttr`).
    pub fn create_data_type_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_DATA_TYPE, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// The name the renderer looks up to produce this channel.
    /// C++ `UsdRenderVar::GetSourceNameAttr`.
    ///
    /// Type `uniform string`. Fetch with `get::<String>()?`.
    pub fn source_name_attr(&self) -> Attribute {
        self.attribute(tok::A_SOURCE_NAME)
    }

    /// Author `sourceName` (`uniform string`) (C++ `CreateSourceNameAttr`).
    pub fn create_source_name_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SOURCE_NAME, "string")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// How `sourceName` is interpreted (`raw` / `primvar` / `lpe` /
    /// `intrinsic`). C++ `UsdRenderVar::GetSourceTypeAttr`.
    ///
    /// Type `uniform token`. Fetch with
    /// `get::<`[`SourceType`](super::SourceType)`>()?`.
    pub fn source_type_attr(&self) -> Attribute {
        self.attribute(tok::A_SOURCE_TYPE)
    }

    /// Author `sourceType` (`uniform token`) (C++ `CreateSourceTypeAttr`). Pass
    /// a [`SourceType`](super::SourceType) to `set`.
    pub fn create_source_type_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SOURCE_TYPE, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }
}

impl_render_schema!(typed RenderVar);

/// A node in a multi-pass render graph (C++ `UsdRenderPass`).
///
/// Covers the scalar attributes, the `renderSource` / `inputPasses`
/// relationships, and the two collection `includeRoot` flags. The
/// `renderVisibility` / `cameraVisibility` / `prune` / `matte`
/// collection-membership relationships (a multi-apply `CollectionAPI`) are not
/// modelled yet — they need collection-membership evaluation.
#[derive(Clone, derive_more::Deref)]
pub struct RenderPass(Prim);

impl RenderPass {
    /// Author a `def RenderPass` prim at `path` (C++ `UsdRenderPass::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_RENDER_PASS)?))
    }

    /// Wrap `path` as a `RenderPass` if it is typed `RenderPass`
    /// (C++ `UsdRenderPass::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_RENDER_PASS).map(|o| o.map(Self))
    }

    /// Categorises the pass within a custom pipeline (e.g. `prman`, `usdrender`).
    /// C++ `UsdRenderPass::GetPassTypeAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<String>()?`.
    pub fn pass_type_attr(&self) -> Attribute {
        self.attribute(tok::A_PASS_TYPE)
    }

    /// Author `passType` (`uniform token`) (C++ `CreatePassTypeAttr`).
    pub fn create_pass_type_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_PASS_TYPE, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// The command and arguments that generate the pass (`{var}` substituted by
    /// the consumer). C++ `UsdRenderPass::GetCommandAttr`.
    ///
    /// Type `uniform string[]`. Fetch with `get::<sdf::Value>()?` (a
    /// [`sdf::Value::StringVec`]).
    pub fn command_attr(&self) -> Attribute {
        self.attribute(tok::A_COMMAND)
    }

    /// Author `command` (`uniform string[]`) (C++ `CreateCommandAttr`).
    pub fn create_command_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_COMMAND, "string[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// An external asset holding the pass's prims / config.
    /// C++ `UsdRenderPass::GetFileNameAttr`.
    ///
    /// Type `uniform asset`. Fetch with `get::<sdf::Value>()?` (an
    /// [`sdf::Value::AssetPath`]).
    pub fn file_name_attr(&self) -> Attribute {
        self.attribute(tok::A_FILE_NAME)
    }

    /// Author `fileName` (`uniform asset`) (C++ `CreateFileNameAttr`).
    pub fn create_file_name_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_FILE_NAME, "asset")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// The `renderSource` relationship — the object to render (a settings prim
    /// or external source). C++ `UsdRenderPass::GetRenderSourceRel`.
    pub fn render_source_rel(&self) -> Relationship {
        self.relationship(tok::REL_RENDER_SOURCE)
    }

    /// Author the `renderSource` relationship (C++ `CreateRenderSourceRel`).
    pub fn create_render_source_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::REL_RENDER_SOURCE)?.set_custom(false)?)
    }

    /// The `inputPasses` relationship — the passes this one depends on.
    /// C++ `UsdRenderPass::GetInputPassesRel`.
    pub fn input_passes_rel(&self) -> Relationship {
        self.relationship(tok::REL_INPUT_PASSES)
    }

    /// Author the `inputPasses` relationship (C++ `CreateInputPassesRel`).
    pub fn create_input_passes_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::REL_INPUT_PASSES)?.set_custom(false)?)
    }

    /// Whether the `renderVisibility` collection includes the scene root by
    /// default. C++ exposes this through the multi-apply `CollectionAPI`
    /// instance `renderVisibility`.
    ///
    /// Type `uniform bool`. Fetch with `get::<bool>()?`.
    pub fn render_visibility_include_root_attr(&self) -> Attribute {
        self.attribute(tok::A_RENDER_VISIBILITY_INCLUDE_ROOT)
    }

    /// Author `collection:renderVisibility:includeRoot` (`uniform bool`).
    pub fn create_render_visibility_include_root_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_RENDER_VISIBILITY_INCLUDE_ROOT, "bool")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Whether the `cameraVisibility` collection includes the scene root by
    /// default. C++ exposes this through the multi-apply `CollectionAPI`
    /// instance `cameraVisibility`.
    ///
    /// Type `uniform bool`. Fetch with `get::<bool>()?`.
    pub fn camera_visibility_include_root_attr(&self) -> Attribute {
        self.attribute(tok::A_CAMERA_VISIBILITY_INCLUDE_ROOT)
    }

    /// Author `collection:cameraVisibility:includeRoot` (`uniform bool`).
    pub fn create_camera_visibility_include_root_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_CAMERA_VISIBILITY_INCLUDE_ROOT, "bool")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }
}

impl_render_schema!(typed RenderPass);

/// A denoise pass (C++ `UsdRenderDenoisePass`, a `dev`-era schema). A marker
/// prim referenced as the denoise source of a product or pass; it carries no
/// attributes of its own.
#[derive(Clone, derive_more::Deref)]
pub struct RenderDenoisePass(Prim);

impl RenderDenoisePass {
    /// Author a `def RenderDenoisePass` prim at `path`
    /// (C++ `UsdRenderDenoisePass::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.define_prim(path)?.set_type_name(tok::T_RENDER_DENOISE_PASS)?,
        ))
    }

    /// Wrap `path` as a `RenderDenoisePass` if it is typed `RenderDenoisePass`
    /// (C++ `UsdRenderDenoisePass::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_RENDER_DENOISE_PASS).map(|o| o.map(Self))
    }
}

impl_render_schema!(typed RenderDenoisePass);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf;
    use crate::schemas::render::{AspectRatioConformPolicy, ProductType, RenderSettingsBase, SourceType};

    #[test]
    fn render_settings_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let s = RenderSettings::define(&stage, "/Render/Settings")?;
        s.create_resolution_attr()?.set(gf::vec2i(1280, 720))?;
        s.create_aspect_ratio_conform_policy_attr()?
            .set(AspectRatioConformPolicy::AdjustApertureWidth)?;
        s.create_camera_rel()?.add_target(sdf::path("/World/Cam")?)?;
        s.create_products_rel()?
            .add_target(sdf::path("/Render/Products/beauty")?)?;
        s.create_included_purposes_attr()?
            .set(Value::TokenVec(vec!["default".into(), "render".into()]))?;
        s.create_rendering_color_space_attr()?.set("lin_rec709".to_string())?;

        let s = RenderSettings::get(&stage, "/Render/Settings")?.expect("RenderSettings");
        assert_eq!(
            s.resolution_attr().get::<Value>()?.and_then(|v| v.try_as_vec_2i()),
            Some(gf::vec2i(1280, 720))
        );
        assert_eq!(
            s.aspect_ratio_conform_policy_attr().get::<AspectRatioConformPolicy>()?,
            Some(AspectRatioConformPolicy::AdjustApertureWidth)
        );
        assert_eq!(s.camera_rel().targets()?, vec![sdf::path("/World/Cam")?]);
        assert_eq!(s.products_rel().targets()?, vec![sdf::path("/Render/Products/beauty")?]);
        assert_eq!(
            s.rendering_color_space_attr().get::<String>()?.as_deref(),
            Some("lin_rec709")
        );

        // A non-RenderSettings prim reads back as None.
        stage.define_prim(sdf::path("/NotSettings")?)?.set_type_name("Scope")?;
        assert!(RenderSettings::get(&stage, "/NotSettings")?.is_none());
        Ok(())
    }

    #[test]
    fn render_product_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let p = RenderProduct::define(&stage, "/Render/Products/beauty")?;
        p.create_product_type_attr()?.set(ProductType::Raster)?;
        p.create_product_name_attr()?.set("beauty.exr".to_string())?;
        // A product-level override of an inherited base attribute.
        p.create_resolution_attr()?.set(gf::vec2i(512, 512))?;
        p.create_ordered_vars_rel()?
            .add_target(sdf::path("/Render/Vars/color")?)?;

        let p = RenderProduct::get(&stage, "/Render/Products/beauty")?.expect("RenderProduct");
        assert_eq!(p.product_type_attr().get::<ProductType>()?, Some(ProductType::Raster));
        assert_eq!(p.product_name_attr().get::<String>()?.as_deref(), Some("beauty.exr"));
        assert_eq!(
            p.resolution_attr().get::<Value>()?.and_then(|v| v.try_as_vec_2i()),
            Some(gf::vec2i(512, 512))
        );
        assert_eq!(p.ordered_vars_rel().targets()?, vec![sdf::path("/Render/Vars/color")?]);
        Ok(())
    }

    #[test]
    fn render_var_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let v = RenderVar::define(&stage, "/Render/Vars/N")?;
        v.create_data_type_attr()?.set("normal3f".to_string())?;
        v.create_source_name_attr()?.set("Nworld".to_string())?;
        v.create_source_type_attr()?.set(SourceType::Primvar)?;

        let v = RenderVar::get(&stage, "/Render/Vars/N")?.expect("RenderVar");
        assert_eq!(v.data_type_attr().get::<String>()?.as_deref(), Some("normal3f"));
        assert_eq!(v.source_name_attr().get::<String>()?.as_deref(), Some("Nworld"));
        assert_eq!(v.source_type_attr().get::<SourceType>()?, Some(SourceType::Primvar));
        Ok(())
    }

    #[test]
    fn render_pass_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let p = RenderPass::define(&stage, "/Render/Passes/beauty")?;
        p.create_pass_type_attr()?.set("prman".to_string())?;
        p.create_command_attr()?.set(Value::StringVec(vec![
            "prman".into(),
            "-t:0".into(),
            "{fileName}".into(),
        ]))?;
        p.create_file_name_attr()?
            .set(Value::AssetPath("./beauty.rib".into()))?;
        p.create_render_source_rel()?
            .add_target(sdf::path("/Render/Settings")?)?;
        p.create_camera_visibility_include_root_attr()?.set(false)?;

        let p = RenderPass::get(&stage, "/Render/Passes/beauty")?.expect("RenderPass");
        assert_eq!(p.pass_type_attr().get::<String>()?.as_deref(), Some("prman"));
        assert_eq!(
            p.command_attr().get::<Value>()?.and_then(|v| v.try_as_string_vec()),
            Some(vec!["prman".to_string(), "-t:0".to_string(), "{fileName}".to_string()])
        );
        assert_eq!(p.render_source_rel().targets()?, vec![sdf::path("/Render/Settings")?]);
        assert_eq!(p.camera_visibility_include_root_attr().get::<bool>()?, Some(false));
        Ok(())
    }

    #[test]
    fn denoise_pass_type_gate() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        RenderDenoisePass::define(&stage, "/Render/Denoise")?;
        assert!(RenderDenoisePass::get(&stage, "/Render/Denoise")?.is_some());
        assert!(RenderDenoisePass::get(&stage, "/Render/Settings")?.is_none());
        Ok(())
    }
}
