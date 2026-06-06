//! The computed render spec (`UsdRenderComputeSpec`).
//!
//! Flattens a `RenderSettings` prim, its products, vars, and cameras into
//! a self-contained [`spec::RenderSpec`]: each product's base attributes
//! are resolved (settings, then authored product overrides), the
//! aspect-ratio conform policy is applied against the bound camera's
//! aperture, and the products' `orderedVars` are de-duplicated into one
//! global var list referenced by per-product indices. Render-delegate
//! `namespace:`-prefixed settings are gathered per level (settings,
//! product, var) into `namespacedSettings`.

use anyhow::Result;

use std::collections::HashMap;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::{Attribute, Relationship, Stage};

use super::conform::apply_aspect_ratio_policy;
use super::spec::{Product, RenderSpec, RenderVar as SpecVar};
use super::{
    AspectRatioConformPolicy, ProductType, RenderProduct, RenderSettings, RenderSettingsBase, RenderVar, SourceType,
};

/// Compute the [`RenderSpec`](super::spec::RenderSpec) for the `RenderSettings`
/// prim at `settings_prim`. Returns `None` when the prim is not a
/// `RenderSettings`.
///
/// Mirrors C++ `UsdRenderComputeSpec`: resolve the settings base, then per
/// product copy that base and override it with the product's authored
/// opinions, apply the conform policy against the bound camera, and gather
/// the global de-duplicated var list.
///
/// `namespaces` filters the gathered `namespacedSettings` (render-delegate
/// `namespace:`-prefixed opinions) by top-level namespace; an empty slice
/// gathers every namespace.
pub fn compute_render_spec(stage: &Stage, settings_prim: &Path, namespaces: &[&str]) -> Result<Option<RenderSpec>> {
    let Some(settings) = RenderSettings::get(stage, settings_prim.clone())? else {
        return Ok(None);
    };
    // Resolve the settings base against the spec defaults.
    let settings_base = ResolvedBase::resolve(&settings, &ResolvedBase::spec_default())?;

    let mut render_vars: Vec<SpecVar> = Vec::new();
    // var path → index into `render_vars`, so de-duplication is O(1) rather
    // than scanning the vector for each product's vars.
    let mut var_index: HashMap<String, usize> = HashMap::new();
    let mut products: Vec<Product> = Vec::new();

    for product_path in settings.products_rel().forwarded_targets()? {
        let Some(product) = RenderProduct::get(stage, product_path.clone())? else {
            continue; // a `products` target that isn't a RenderProduct is ignored
        };

        // Product attributes override the resolved settings base where authored.
        let base = ResolvedBase::resolve(&product, &settings_base)?;

        // Apply the conform policy against the bound camera's aperture. With
        // no camera bound there is no aperture to reconcile.
        let (aperture_size, pixel_aspect_ratio) = match &base.camera {
            Some(camera) => {
                let aperture = read_camera_aperture(stage, &Path::new(camera)?)?;
                let conformed = apply_aspect_ratio_policy(
                    base.aspect_ratio_conform_policy,
                    base.resolution,
                    base.pixel_aspect_ratio,
                    aperture,
                );
                (conformed.aperture_size, conformed.pixel_aspect_ratio)
            }
            None => ([0.0, 0.0], base.pixel_aspect_ratio),
        };

        let render_var_indices = collect_var_indices(
            stage,
            &product.ordered_vars_rel(),
            &mut render_vars,
            &mut var_index,
            namespaces,
        )?;

        products.push(Product {
            render_product_path: product_path.as_str().to_string(),
            product_type: product.product_type_attr().get::<ProductType>()?.unwrap_or_default(),
            name: product.product_name_attr().get::<String>()?.unwrap_or_default(),
            camera_path: base.camera,
            disable_motion_blur: base.disable_motion_blur,
            disable_depth_of_field: base.disable_depth_of_field,
            resolution: base.resolution,
            pixel_aspect_ratio,
            aspect_ratio_conform_policy: base.aspect_ratio_conform_policy,
            aperture_size,
            data_window_ndc: base.data_window_ndc,
            render_var_indices,
            namespaced_settings: compute_namespaced_settings(stage, &product_path, namespaces)?,
        });
    }

    Ok(Some(RenderSpec {
        products,
        render_vars,
        included_purposes: read_token_vec(&settings.included_purposes_attr())?
            .unwrap_or_else(|| vec!["default".to_string(), "render".to_string()]),
        material_binding_purposes: read_token_vec(&settings.material_binding_purposes_attr())?
            .unwrap_or_else(|| vec!["full".to_string(), String::new()]),
        namespaced_settings: compute_namespaced_settings(stage, settings_prim, namespaces)?,
    }))
}

/// The camera + framing attributes resolved from a [`RenderSettingsBase`] view,
/// with per-attribute fallback to a weaker base (the spec defaults for the
/// settings, the resolved settings for a product). The intermediate value the
/// render-spec computation flattens.
struct ResolvedBase {
    resolution: [i32; 2],
    pixel_aspect_ratio: f32,
    aspect_ratio_conform_policy: AspectRatioConformPolicy,
    data_window_ndc: [f32; 4],
    disable_motion_blur: bool,
    disable_depth_of_field: bool,
    camera: Option<String>,
}

impl ResolvedBase {
    /// The `usdRender/schema.usda` fallbacks for the base attributes.
    fn spec_default() -> Self {
        Self {
            resolution: [2048, 1080],
            pixel_aspect_ratio: 1.0,
            aspect_ratio_conform_policy: AspectRatioConformPolicy::ExpandAperture,
            data_window_ndc: [0.0, 0.0, 1.0, 1.0],
            disable_motion_blur: false,
            disable_depth_of_field: false,
            camera: None,
        }
    }

    /// Resolve each base attribute on `view`, falling back to the matching
    /// field of `fallback` for any unauthored attribute. With `fallback =
    /// spec_default()` this resolves the spec fallbacks; with `fallback =
    /// settings-base` it implements the product-overrides-settings rule: a
    /// product attribute overrides only where the product authors it, mirroring
    /// C++ `_Get(attr, val, getDefaultValue=false)`, which uses the value only
    /// when the attribute has an authored opinion.
    fn resolve(view: &impl RenderSettingsBase, fallback: &ResolvedBase) -> Result<Self> {
        Ok(Self {
            resolution: read_int2(&view.resolution_attr())?.unwrap_or(fallback.resolution),
            pixel_aspect_ratio: read_f32(&view.pixel_aspect_ratio_attr())?.unwrap_or(fallback.pixel_aspect_ratio),
            aspect_ratio_conform_policy: view
                .aspect_ratio_conform_policy_attr()
                .get::<AspectRatioConformPolicy>()?
                .unwrap_or(fallback.aspect_ratio_conform_policy),
            data_window_ndc: read_float4(&view.data_window_ndc_attr())?.unwrap_or(fallback.data_window_ndc),
            disable_motion_blur: view
                .disable_motion_blur_attr()
                .get::<bool>()?
                .unwrap_or(fallback.disable_motion_blur),
            disable_depth_of_field: view
                .disable_depth_of_field_attr()
                .get::<bool>()?
                .unwrap_or(fallback.disable_depth_of_field),
            camera: read_rel_first_target(&view.camera_rel())?.or_else(|| fallback.camera.clone()),
        })
    }
}

/// Gather the `namespace:`-prefixed render-delegate settings authored on
/// `prim` (spec — `_ReadNamespacedSettings`). `namespaces` filters by
/// top-level namespace; an empty slice gathers every namespace.
///
/// Unnamespaced attributes (the schema attrs like `resolution`) are
/// skipped. The settings-driven-by-a-node-graph case (`outputs:`-connected
/// values) is left as a TODO until UsdShade's value-producer resolution is
/// available; only plain authored namespaced attributes are gathered here.
pub fn compute_namespaced_settings(stage: &Stage, prim: &Path, namespaces: &[&str]) -> Result<Vec<(String, Value)>> {
    let mut out = Vec::new();
    for name in stage.prim_at(prim.clone()).property_names()? {
        // TODO(shade): `outputs:`-connected settings are driven by a node
        // graph; resolving their value producer needs UsdShade.
        if name.starts_with("outputs:") {
            continue;
        }
        let Some((namespace, _)) = name.split_once(':') else {
            continue; // unnamespaced — not a delegate setting
        };
        if !namespaces.is_empty() && !namespaces.contains(&namespace) {
            continue;
        }
        if let Some(value) = stage.field::<Value>(prim.append_property(&name)?, FieldKey::Default)? {
            out.push((name, value));
        }
    }
    // `prim_properties` order isn't guaranteed stable across backends/layers;
    // sort by setting name for deterministic output.
    out.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(out)
}

/// Resolve a product's `orderedVars` to indices into the shared
/// `render_vars` list, appending any var not seen before (de-duplication
/// by var path). Targets that aren't `RenderVar` prims are skipped.
fn collect_var_indices(
    stage: &Stage,
    ordered_vars_rel: &Relationship,
    render_vars: &mut Vec<SpecVar>,
    var_index: &mut HashMap<String, usize>,
    namespaces: &[&str],
) -> Result<Vec<usize>> {
    let mut indices = Vec::new();
    for var_path in ordered_vars_rel.forwarded_targets()? {
        let key = var_path.as_str().to_string();
        if let Some(&i) = var_index.get(&key) {
            indices.push(i);
            continue;
        }
        let Some(var) = RenderVar::get(stage, var_path.clone())? else {
            continue;
        };
        render_vars.push(SpecVar {
            render_var_path: key.clone(),
            data_type: var
                .data_type_attr()
                .get::<String>()?
                .unwrap_or_else(|| "color3f".to_string()),
            source_name: var.source_name_attr().get::<String>()?.unwrap_or_default(),
            source_type: var.source_type_attr().get::<SourceType>()?.unwrap_or_default(),
            namespaced_settings: compute_namespaced_settings(stage, &var_path, namespaces)?,
        });
        let i = render_vars.len() - 1;
        var_index.insert(key, i);
        indices.push(i);
    }
    Ok(indices)
}

/// Read a camera prim's `(horizontalAperture, verticalAperture)`, falling
/// back to `UsdGeomCamera`'s defaults `(20.955, 15.2908)` mm. Reads the
/// aperture attributes by name so it needs no dependency on the `geom`
/// feature — the conform policy only needs these two floats.
fn read_camera_aperture(stage: &Stage, camera: &Path) -> Result<[f32; 2]> {
    let prim = stage.prim_at(camera.clone());
    Ok([
        read_f32(&prim.attribute("horizontalAperture"))?.unwrap_or(20.955),
        read_f32(&prim.attribute("verticalAperture"))?.unwrap_or(15.2908),
    ])
}

/// Narrow a `f64` to `f32`, clamping to the finite `f32` range so a large
/// authored double can't silently become `inf`.
fn f64_to_f32(d: f64) -> f32 {
    d.clamp(f32::MIN as f64, f32::MAX as f64) as f32
}

fn read_f32(attr: &Attribute) -> Result<Option<f32>> {
    Ok(match attr.get::<Value>()? {
        Some(Value::Float(f)) => Some(f),
        Some(Value::Double(d)) => Some(f64_to_f32(d)),
        Some(Value::Half(h)) => Some(h.to_f32()),
        _ => None,
    })
}

fn read_int2(attr: &Attribute) -> Result<Option<[i32; 2]>> {
    Ok(attr.get::<Value>()?.and_then(|v| v.try_as_vec_2i()))
}

fn read_float4(attr: &Attribute) -> Result<Option<[f32; 4]>> {
    Ok(match attr.get::<Value>()? {
        Some(Value::Vec4f(v)) => Some(v),
        Some(Value::Vec4d(v)) => Some([f64_to_f32(v[0]), f64_to_f32(v[1]), f64_to_f32(v[2]), f64_to_f32(v[3])]),
        _ => None,
    })
}

fn read_token_vec(attr: &Attribute) -> Result<Option<Vec<String>>> {
    Ok(match attr.get::<Value>()? {
        Some(Value::TokenVec(v) | Value::StringVec(v)) => Some(v),
        _ => None,
    })
}

fn read_rel_first_target(rel: &Relationship) -> Result<Option<String>> {
    Ok(rel.targets()?.into_iter().next().map(|p| p.as_str().to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    /// Two products share one var: it appears once in the global list and is
    /// referenced by index from both products.
    #[test]
    fn products_and_dedup_vars() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;

        let color = RenderVar::define(&stage, "/Render/Vars/color")?;
        color.create_data_type_attr()?.set("color3f".to_string())?;
        color.create_source_type_attr()?.set(SourceType::Raw)?;
        let alpha = RenderVar::define(&stage, "/Render/Vars/alpha")?;
        alpha.create_data_type_attr()?.set("float".to_string())?;
        alpha.create_source_name_attr()?.set("a".to_string())?;

        let beauty = RenderProduct::define(&stage, "/Render/Products/beauty")?;
        beauty.create_product_type_attr()?.set(ProductType::Raster)?;
        beauty
            .create_ordered_vars_rel()?
            .set_targets([sdf::path("/Render/Vars/color")?, sdf::path("/Render/Vars/alpha")?])?;
        // matte re-uses `color`, so it must NOT add a second global entry.
        RenderProduct::define(&stage, "/Render/Products/matte")?
            .create_ordered_vars_rel()?
            .set_targets([sdf::path("/Render/Vars/color")?])?;

        let settings = RenderSettings::define(&stage, "/Render/Settings")?;
        settings.create_resolution_attr()?.set([1024, 512])?;
        settings.create_products_rel()?.set_targets([
            sdf::path("/Render/Products/beauty")?,
            sdf::path("/Render/Products/matte")?,
        ])?;

        let spec = compute_render_spec(&stage, &sdf::path("/Render/Settings")?, &[])?.expect("RenderSpec");
        assert_eq!(spec.products.len(), 2);
        // color + alpha → exactly two global vars (color shared, not duplicated).
        assert_eq!(spec.render_vars.len(), 2);
        assert_eq!(spec.render_vars[0].render_var_path, "/Render/Vars/color");
        assert_eq!(spec.render_vars[1].render_var_path, "/Render/Vars/alpha");

        // beauty references both; matte references the shared `color` (index 0).
        assert_eq!(spec.products[0].render_var_indices, vec![0, 1]);
        assert_eq!(spec.products[1].render_var_indices, vec![0]);
        // resolution inherited from the settings base.
        assert_eq!(spec.products[0].resolution, [1024, 512]);
        Ok(())
    }

    /// A product attribute overrides the settings value only where the product
    /// authors it; everything else inherits the resolved settings.
    #[test]
    fn product_overrides_only_authored() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let settings = RenderSettings::define(&stage, "/Render/Settings")?;
        settings.create_resolution_attr()?.set([1920, 1080])?;
        settings.create_pixel_aspect_ratio_attr()?.set(2.0_f32)?;
        settings
            .create_products_rel()?
            .set_targets([sdf::path("/Render/Products/p")?])?;
        // Product authors only `resolution`.
        RenderProduct::define(&stage, "/Render/Products/p")?
            .create_resolution_attr()?
            .set([512, 512])?;

        let spec = compute_render_spec(&stage, &sdf::path("/Render/Settings")?, &[])?.expect("RenderSpec");
        let p = &spec.products[0];
        assert_eq!(p.resolution, [512, 512]); // overridden by the product
        assert!((p.pixel_aspect_ratio - 2.0).abs() < 1e-6); // inherited from settings
        Ok(())
    }

    /// A bound camera drives the conform policy: a square aperture against a
    /// 2:1 image expands the aperture width (default `expandAperture`).
    #[test]
    fn conform_against_bound_camera() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let cam = stage.define_prim(sdf::path("/World/Cam")?)?.set_type_name("Camera")?;
        for (name, v) in [("horizontalAperture", 10.0f32), ("verticalAperture", 10.0)] {
            stage
                .create_attribute(cam.path().append_property(name)?, "float")?
                .set(sdf::Value::Float(v))?;
        }
        RenderProduct::define(&stage, "/Render/Products/p")?;
        let settings = RenderSettings::define(&stage, "/Render/Settings")?;
        settings.create_resolution_attr()?.set([200, 100])?;
        settings.create_camera_rel()?.add_target(sdf::path("/World/Cam")?)?;
        settings
            .create_products_rel()?
            .set_targets([sdf::path("/Render/Products/p")?])?;

        let spec = compute_render_spec(&stage, &sdf::path("/Render/Settings")?, &[])?.expect("RenderSpec");
        let p = &spec.products[0];
        assert_eq!(p.camera_path.as_deref(), Some("/World/Cam"));
        // expandAperture, square aperture vs 2:1 image → width grows to 20.
        assert!((p.aperture_size[0] - 20.0).abs() < 1e-3);
        assert!((p.aperture_size[1] - 10.0).abs() < 1e-3);
        Ok(())
    }

    #[test]
    fn non_settings_prim_is_none() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim(sdf::path("/Scope")?)?.set_type_name("Scope")?;
        assert!(compute_render_spec(&stage, &sdf::path("/Scope")?, &[])?.is_none());
        Ok(())
    }

    /// `namespace:`-prefixed delegate settings are gathered (filtered by the
    /// requested namespace); the unnamespaced schema attrs are not.
    #[test]
    fn namespaced_settings_filtered() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let settings = RenderSettings::define(&stage, "/Render/Settings")?;
        settings.create_resolution_attr()?.set([512, 512])?;
        // A render-delegate setting (gathered) and a foreign-namespace one (filtered out).
        stage
            .create_attribute(settings.path().append_property("ri:hider:maxsamples")?, "int")?
            .set(sdf::Value::Int(64))?;
        stage
            .create_attribute(settings.path().append_property("karma:foo")?, "int")?
            .set(sdf::Value::Int(1))?;

        let spec = compute_render_spec(&stage, &sdf::path("/Render/Settings")?, &["ri"])?.expect("RenderSpec");
        // Only the `ri:` setting is gathered; `karma:` filtered, `resolution` unnamespaced.
        assert_eq!(spec.namespaced_settings.len(), 1);
        assert_eq!(spec.namespaced_settings[0].0, "ri:hider:maxsamples");
        assert_eq!(spec.namespaced_settings[0].1, sdf::Value::Int(64));

        // An empty namespace filter gathers both delegate settings.
        let all = compute_render_spec(&stage, &sdf::path("/Render/Settings")?, &[])?.expect("RenderSpec");
        assert_eq!(all.namespaced_settings.len(), 2);
        Ok(())
    }
}
