//! The computed render spec (`UsdRenderComputeSpec`).
//!
//! Flattens a `RenderSettings` prim, its products, vars, and cameras into
//! a self-contained [`spec::RenderSpec`]: each product's base attributes
//! are resolved (settings, then authored product overrides), the
//! aspect-ratio conform policy is applied against the bound camera's
//! aperture, and the products' `orderedVars` are de-duplicated into one
//! global var list referenced by per-product indices.
//!
//! `namespacedSettings` gathering (render-delegate `namespace:`-prefixed
//! settings) is added in a following commit; the fields are left empty here.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::Stage;

use super::conform::apply_aspect_ratio_policy;
use super::read::{
    read_base_overriding, read_camera_aperture, read_render_product, read_render_settings, read_render_var,
};
use super::spec::{Product, RenderSpec, RenderVar};

/// Compute the [`RenderSpec`] for the `RenderSettings` prim at
/// `settings_prim`. Returns `None` when the prim is not a `RenderSettings`.
///
/// Mirrors C++ `UsdRenderComputeSpec`: resolve the settings base, then per
/// product copy that base and override it with the product's authored
/// opinions, apply the conform policy against the bound camera, and gather
/// the global de-duplicated var list.
pub fn compute_render_spec(stage: &Stage, settings_prim: &Path) -> Result<Option<RenderSpec>> {
    let Some(settings) = read_render_settings(stage, settings_prim)? else {
        return Ok(None);
    };
    let settings_base = settings.base;

    let mut render_vars: Vec<RenderVar> = Vec::new();
    let mut products: Vec<Product> = Vec::new();

    let products_rel = settings_prim.append_property(super::tokens::REL_PRODUCTS)?;
    for product_path in stage.forwarded_relationship_targets(&products_rel)? {
        let Some(product) = read_render_product(stage, &product_path)? else {
            continue; // a `products` target that isn't a RenderProduct is ignored
        };

        // Product attributes override the resolved settings base where authored.
        let base = read_base_overriding(stage, &product_path, &settings_base)?;

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

        let ordered_vars_rel = product_path.append_property(super::tokens::REL_ORDERED_VARS)?;
        let render_var_indices = collect_var_indices(stage, &ordered_vars_rel, &mut render_vars)?;

        products.push(Product {
            render_product_path: product_path.as_str().to_string(),
            product_type: product.product_type,
            name: product.product_name,
            camera_path: base.camera,
            disable_motion_blur: base.disable_motion_blur,
            disable_depth_of_field: base.disable_depth_of_field,
            resolution: base.resolution,
            pixel_aspect_ratio,
            aspect_ratio_conform_policy: base.aspect_ratio_conform_policy,
            aperture_size,
            data_window_ndc: base.data_window_ndc,
            render_var_indices,
            namespaced_settings: Vec::new(),
        });
    }

    Ok(Some(RenderSpec {
        products,
        render_vars,
        included_purposes: settings.included_purposes,
        material_binding_purposes: settings.material_binding_purposes,
        namespaced_settings: Vec::new(),
    }))
}

/// Resolve a product's `orderedVars` to indices into the shared
/// `render_vars` list, appending any var not seen before (de-duplication
/// by var path). Targets that aren't `RenderVar` prims are skipped.
fn collect_var_indices(stage: &Stage, ordered_vars_rel: &Path, render_vars: &mut Vec<RenderVar>) -> Result<Vec<usize>> {
    let mut indices = Vec::new();
    for var_path in stage.forwarded_relationship_targets(ordered_vars_rel)? {
        let key = var_path.as_str().to_string();
        if let Some(i) = render_vars.iter().position(|v| v.render_var_path == key) {
            indices.push(i);
            continue;
        }
        let Some(var) = read_render_var(stage, &var_path)? else {
            continue;
        };
        render_vars.push(RenderVar {
            render_var_path: key,
            data_type: var.data_type,
            source_name: var.source_name,
            source_type: var.source_type,
            namespaced_settings: Vec::new(),
        });
        indices.push(render_vars.len() - 1);
    }
    Ok(indices)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::render::types::{ProductType, SourceType};
    use crate::schemas::render::{
        define_render_product, define_render_settings, define_render_var, SettingsBaseSetters,
    };
    use crate::sdf;

    /// Two products share one var: it appears once in the global list and is
    /// referenced by index from both products.
    #[test]
    fn computes_products_and_dedups_vars() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;

        define_render_var(&stage, sdf::path("/Render/Vars/color")?)?
            .set_data_type("color3f")?
            .set_source_type(SourceType::Raw)?;
        define_render_var(&stage, sdf::path("/Render/Vars/alpha")?)?
            .set_data_type("float")?
            .set_source_name("a")?;

        define_render_product(&stage, sdf::path("/Render/Products/beauty")?)?
            .set_product_type(ProductType::Raster)?
            .set_ordered_vars([sdf::path("/Render/Vars/color")?, sdf::path("/Render/Vars/alpha")?])?;
        define_render_product(&stage, sdf::path("/Render/Products/matte")?)?
            // Re-uses `color`, so it must NOT add a second global entry.
            .set_ordered_vars([sdf::path("/Render/Vars/color")?])?;

        define_render_settings(&stage, sdf::path("/Render/Settings")?)?
            .set_resolution([1024, 512])?
            .set_products([
                sdf::path("/Render/Products/beauty")?,
                sdf::path("/Render/Products/matte")?,
            ])?;

        let spec = compute_render_spec(&stage, &sdf::path("/Render/Settings")?)?.expect("RenderSpec");
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

    /// A bound camera drives the conform policy: a square aperture against a
    /// 2:1 image expands the aperture width (default `expandAperture`).
    #[test]
    fn applies_conform_against_bound_camera() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let cam = stage.define_prim(sdf::path("/World/Cam")?)?.set_type_name("Camera")?;
        for (name, v) in [("horizontalAperture", 10.0f32), ("verticalAperture", 10.0)] {
            stage
                .create_attribute(cam.path().append_property(name)?, "float")?
                .set(sdf::Value::Float(v))?;
        }
        define_render_product(&stage, sdf::path("/Render/Products/p")?)?;
        define_render_settings(&stage, sdf::path("/Render/Settings")?)?
            .set_resolution([200, 100])?
            .set_camera(sdf::path("/World/Cam")?)?
            .set_products([sdf::path("/Render/Products/p")?])?;

        let spec = compute_render_spec(&stage, &sdf::path("/Render/Settings")?)?.expect("RenderSpec");
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
        assert!(compute_render_spec(&stage, &sdf::path("/Scope")?)?.is_none());
        Ok(())
    }
}
