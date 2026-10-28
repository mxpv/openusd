//! The computed render spec (`UsdRenderComputeSpec`).
//!
//! Flattens a `Settings` prim, its products, vars, and cameras into
//! a self-contained [`RenderSpec`]: each product's base attributes
//! are resolved (settings, then authored product overrides), the
//! aspect-ratio conform policy is applied against the bound camera's
//! aperture, and the products' `orderedVars` are de-duplicated into one
//! global var list referenced by per-product indices. Each level (settings,
//! product, var) carries the render-delegate settings
//! [`namespaced_settings`] gathers on its prim.

use std::collections::HashMap;

use openusd::sdf::Path;
use openusd::usd::{Attribute, Stage};
use openusd::vt::{self, Value};
use openusd::{Result, gf, tf};

use super::conform::conform_aperture;
use super::spec::{Product as SpecProduct, RenderSpec, SpecDiagnostic, Var as SpecVar};
use super::{
    AspectRatioConformPolicy, Product, ProductSchema, Settings, SettingsBaseSchema, SettingsSchema, Var, VarSchema,
};
use crate::SchemaError;
use crate::authored_at;
use crate::geom::{self, CameraSchema};
use crate::shade::{self, ConnectableContext, Output, ProducerFilter};

/// Compute the [`RenderSpec`] for the `Settings`
/// prim at `settings_prim`. Returns `None` when `settings_prim` names no
/// `Settings` prim.
///
/// Mirrors C++ `UsdRenderComputeSpec`: resolve the settings base, then per
/// product copy that base and override it with the product's authored
/// opinions, apply the conform policy against the bound camera, and gather
/// the global de-duplicated var list. A product whose camera is not a
/// `Camera`, and a var target that is not a `Var`, are left out and recorded
/// in [`RenderSpec::diagnostics`].
///
/// `namespaces` is passed to [`namespaced_settings`] at each level, which
/// follows connected outputs under the default [`ConnectableContext`];
/// [`render_spec_in`] follows them under another.
pub fn render_spec(
    stage: &Stage,
    settings_prim: &Path,
    namespaces: &[&str],
) -> Result<Option<RenderSpec>, SchemaError> {
    render_spec_in(&ConnectableContext::default(), stage, settings_prim, namespaces)
}

/// The [`RenderSpec`] for the `Settings` prim at `settings_prim`, as
/// [`render_spec`] computes it, with each connected output followed under
/// `context`'s behaviors.
pub fn render_spec_in(
    context: &ConnectableContext,
    stage: &Stage,
    settings_prim: &Path,
    namespaces: &[&str],
) -> Result<Option<RenderSpec>, SchemaError> {
    let Some(settings) = Settings::get(stage, settings_prim)? else {
        return Ok(None);
    };
    let settings_base = ResolvedBase::read(&settings, None)?;

    let mut spec = RenderSpec::default();
    // var path → index into `spec.render_vars`, for the de-duplication.
    let mut var_index: HashMap<Path, usize> = HashMap::new();

    for product_path in settings.products_rel().forwarded_targets()? {
        let Some(product) = Product::get(stage, &product_path)? else {
            continue; // a `products` target that isn't a Product is ignored
        };

        // Product attributes override the resolved settings base where authored.
        let base = ResolvedBase::read(&product, Some(&settings_base))?;

        let camera = match &base.camera {
            Some(path) => geom::Camera::get(stage, path)?,
            None => None,
        };
        let Some(camera) = camera else {
            spec.diagnostics.push(SpecDiagnostic::MissingCamera {
                product: product_path,
                camera: base.camera,
            });
            continue;
        };
        let resolution: [i32; 2] = base.resolution.into();
        // An aperture that does not read stays zero, as in the C++ spec's
        // product, and conforming then adjusts nothing.
        let conformed = conform_aperture(
            AspectRatioConformPolicy::from_token(&base.aspect_ratio_conform_policy),
            resolution,
            base.pixel_aspect_ratio,
            [
                camera.horizontal_aperture()?.unwrap_or_default(),
                camera.vertical_aperture()?.unwrap_or_default(),
            ],
        );

        let render_var_indices = collect_var_indices(
            context,
            stage,
            &product,
            &product_path,
            &mut spec,
            &mut var_index,
            namespaces,
        )?;

        spec.products.push(SpecProduct {
            product_type: product.product_type()?.unwrap_or_default(),
            name: product.product_name()?.map(String::from).unwrap_or_default(),
            camera_path: camera.path().clone(),
            disable_motion_blur: base.disable_motion_blur,
            disable_depth_of_field: base.disable_depth_of_field,
            resolution,
            pixel_aspect_ratio: conformed.pixel_aspect_ratio,
            aspect_ratio_conform_policy: base.aspect_ratio_conform_policy,
            aperture_size: conformed.aperture_size,
            data_window_ndc: base.data_window_ndc,
            render_var_indices,
            namespaced_settings: namespaced_settings_in(context, stage, &product_path, namespaces)?,
            render_product_path: product_path,
        });
    }

    spec.included_purposes = settings.included_purposes()?.unwrap_or_default();
    spec.material_binding_purposes = settings.material_binding_purposes()?.unwrap_or_default();
    spec.namespaced_settings = namespaced_settings_in(context, stage, settings_prim, namespaces)?;
    Ok(Some(spec))
}

/// The settings authored on `prim`, sorted by name (C++
/// `UsdRenderComputeNamespacedSettings`), with connected outputs followed
/// under the default [`ConnectableContext`]; [`namespaced_settings_in`]
/// follows them under another.
///
/// An authored attribute whose name has a namespace contributes under its
/// full name; an `outputs:` attribute's namespace is read past its
/// `outputs:` prefix. A non-empty `namespaces` admits only the attributes
/// whose outermost namespace it lists.
///
/// An output contributes the prim path of each attribute that produces its
/// value, as a [`Value::PathVec`] in producer order. An unconnected output
/// with an authored value is its own producer, as C++'s walk answers with
/// `shaderOutputsOnly` off. A connection chain longer than the producer walk
/// follows is [`SchemaError::ConnectionDepthExceeded`]. Any other attribute
/// contributes its value at the default time, and one that reads no value,
/// such as a blocked one with no schema fallback, is left out.
///
/// Every authored relationship contributes its targets as a
/// [`Value::PathVec`], whatever its namespace and `namespaces`, as C++
/// gathers them. The schema's own relationships, such as `camera`, are among
/// them.
pub fn namespaced_settings(
    stage: &Stage,
    prim: &Path,
    namespaces: &[&str],
) -> Result<Vec<(String, Value)>, SchemaError> {
    namespaced_settings_in(&ConnectableContext::default(), stage, prim, namespaces)
}

/// The settings authored on `prim`, as [`namespaced_settings`] gathers them,
/// with each connected output followed under `context`'s behaviors.
pub fn namespaced_settings_in(
    context: &ConnectableContext,
    stage: &Stage,
    prim: &Path,
    namespaces: &[&str],
) -> Result<Vec<(String, Value)>, SchemaError> {
    let (attributes, relationships) = stage.prim(prim)?.authored_properties()?;
    let mut out = Vec::new();
    for attr in attributes {
        let name = attr.name();
        let base_name = name.strip_prefix(shade::tokens::OUTPUTS);
        let Some((namespace, _)) = base_name.unwrap_or(name).split_once(':') else {
            continue;
        };
        if !namespaces.is_empty() && !namespaces.contains(&namespace) {
            continue;
        }
        let name = name.to_string();
        // A connection is stronger than a value authored on the output.
        if let Some(output) = base_name.and_then(|_| Output::from_attribute(attr.clone())) {
            let producers = context.value_producing_attributes(output, ProducerFilter::Any)?;
            if !producers.is_empty() {
                let paths = producers.iter().map(|producer| producer.path().prim_path()).collect();
                out.push((name, Value::PathVec(paths)));
                continue;
            }
        }
        if let Some(value) = attr.get::<Value>()? {
            out.push((name, value));
        }
    }
    for rel in relationships {
        out.push((rel.name().to_string(), Value::PathVec(rel.targets()?)));
    }
    // Sorted by name, the order of the C++ `VtDictionary`.
    out.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(out)
}

/// Resolve `product`'s `orderedVars` to indices into `spec.render_vars`,
/// appending any var not seen before (de-duplication by var path). A target
/// that isn't a `Var` prim is skipped with a
/// [`SpecDiagnostic::MissingVar`].
fn collect_var_indices(
    context: &ConnectableContext,
    stage: &Stage,
    product: &Product,
    product_path: &Path,
    spec: &mut RenderSpec,
    var_index: &mut HashMap<Path, usize>,
    namespaces: &[&str],
) -> Result<Vec<usize>, SchemaError> {
    let mut indices = Vec::new();
    for var_path in product.ordered_vars_rel().forwarded_targets()? {
        if let Some(&i) = var_index.get(&var_path) {
            indices.push(i);
            continue;
        }
        let Some(var) = Var::get(stage, &var_path)? else {
            spec.diagnostics.push(SpecDiagnostic::MissingVar {
                product: product_path.clone(),
                var: var_path,
            });
            continue;
        };
        let i = spec.render_vars.len();
        spec.render_vars.push(SpecVar {
            data_type: var.data_type()?.map(String::from).unwrap_or_default(),
            source_name: var.source_name()?.unwrap_or_default(),
            source_type: var.source_type()?.unwrap_or_default(),
            namespaced_settings: namespaced_settings_in(context, stage, &var_path, namespaces)?,
            render_var_path: var_path.clone(),
        });
        var_index.insert(var_path, i);
        indices.push(i);
    }
    Ok(indices)
}

/// The camera + framing attributes resolved from a [`SettingsBaseSchema`] view:
/// the intermediate value the render-spec computation flattens.
struct ResolvedBase {
    resolution: gf::Vec2i,
    pixel_aspect_ratio: f32,
    aspect_ratio_conform_policy: tf::Token,
    data_window_ndc: [f32; 4],
    disable_motion_blur: bool,
    disable_depth_of_field: bool,
    camera: Option<Path>,
}

impl ResolvedBase {
    /// Resolve each base attribute on `view`. With no `inherited` base (the
    /// settings) a value resolves its schema fallback; with one (a product)
    /// only an authored value overrides the inherited one, as C++
    /// `_ReadSettingsBase`'s `getDefault` selects.
    ///
    /// The camera is the first forwarded `camera` target, and an empty
    /// relationship keeps the inherited camera.
    ///
    /// The conform policy stays the authored token, as in C++. A token that
    /// names no [`AspectRatioConformPolicy`](super::AspectRatioConformPolicy)
    /// adjusts nothing.
    fn read(view: &impl SettingsBaseSchema, inherited: Option<&ResolvedBase>) -> Result<Self> {
        Ok(Self {
            resolution: read_attr(&view.resolution_attr(), inherited.map(|base| base.resolution))?,
            pixel_aspect_ratio: read_attr(
                &view.pixel_aspect_ratio_attr(),
                inherited.map(|base| base.pixel_aspect_ratio),
            )?,
            aspect_ratio_conform_policy: read_attr(
                &view.aspect_ratio_conform_policy_attr(),
                inherited.map(|base| base.aspect_ratio_conform_policy.clone()),
            )?,
            data_window_ndc: read_attr(&view.data_window_ndc_attr(), inherited.map(|base| base.data_window_ndc))?,
            disable_motion_blur: read_attr(
                &view.disable_motion_blur_attr(),
                inherited.map(|base| base.disable_motion_blur),
            )?,
            disable_depth_of_field: read_attr(
                &view.disable_depth_of_field_attr(),
                inherited.map(|base| base.disable_depth_of_field),
            )?,
            camera: (view.camera_rel().forwarded_targets()?.into_iter().next())
                .or_else(|| inherited.and_then(|base| base.camera.clone())),
        })
    }
}

/// `attr`'s value read as C++ `_Get(attr, val, getDefault)`: with no
/// `inherited` value the fallback-resolving read, else the authored value
/// over `inherited`. A value neither reads keeps the type's default, as the
/// C++ spec's zero-initialized field does.
fn read_attr<T>(attr: &Attribute, inherited: Option<T>) -> Result<T>
where
    T: vt::FromValue + Default,
    T::Error: Into<openusd::Error>,
{
    Ok(match inherited {
        None => attr.get::<T>()?.unwrap_or_default(),
        Some(inherited) => authored_at::<T>(attr, None)?.unwrap_or(inherited),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::render::{ProductType, SourceType};
    use crate::shade::Connectable;

    use openusd::gf;
    use openusd::sdf;

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// A `Camera` at `path`, with a 10×10 aperture.
    fn camera(stage: &Stage, path: &str) -> Result<geom::Camera> {
        let camera = geom::Camera::define(stage, path)?;
        camera.create_horizontal_aperture_attr()?.set(10.0_f32)?;
        camera.create_vertical_aperture_attr()?.set(10.0_f32)?;
        Ok(camera)
    }

    /// A settings prim at `/Render/Settings` binding `/World/Cam` and
    /// producing `products`.
    fn settings(stage: &Stage, products: &[&str]) -> Result<Settings> {
        camera(stage, "/World/Cam")?;
        let settings = Settings::define(stage, "/Render/Settings")?;
        settings.create_camera_rel()?.add_target("/World/Cam")?;
        settings.create_products_rel()?.set_targets(products.iter().copied())?;
        Ok(settings)
    }

    fn compute(stage: &Stage) -> Result<RenderSpec> {
        Ok(render_spec(stage, &sdf::path("/Render/Settings")?, &[])?.expect("RenderSpec"))
    }

    /// Two products share one var: it appears once in the global list and is
    /// referenced by index from both products.
    #[test]
    fn products_and_dedup_vars() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;

        let color = Var::define(&stage, "/Render/Vars/color")?;
        color.create_data_type_attr()?.set(vt::Value::token("color3f"))?;
        color.create_source_type_attr()?.set(SourceType::Raw)?;
        let alpha = Var::define(&stage, "/Render/Vars/alpha")?;
        alpha.create_data_type_attr()?.set(vt::Value::token("float"))?;
        alpha.create_source_name_attr()?.set("a".to_string())?;

        let beauty = Product::define(&stage, "/Render/Products/beauty")?;
        beauty.create_product_type_attr()?.set(ProductType::Raster)?;
        beauty
            .create_ordered_vars_rel()?
            .set_targets([sdf::path("/Render/Vars/color")?, sdf::path("/Render/Vars/alpha")?])?;
        // matte re-uses `color`, so it must NOT add a second global entry.
        Product::define(&stage, "/Render/Products/matte")?
            .create_ordered_vars_rel()?
            .set_targets(["/Render/Vars/color"])?;

        settings(&stage, &["/Render/Products/beauty", "/Render/Products/matte"])?
            .create_resolution_attr()?
            .set(gf::vec2i(1024, 512))?;

        let spec = compute(&stage)?;
        assert_eq!(spec.products.len(), 2);
        // color + alpha → exactly two global vars (color shared, not duplicated).
        assert_eq!(spec.render_vars.len(), 2);
        assert_eq!(spec.render_vars[0].render_var_path, sdf::path("/Render/Vars/color")?);
        assert_eq!(spec.render_vars[1].render_var_path, sdf::path("/Render/Vars/alpha")?);

        // beauty references both; matte references the shared `color` (index 0).
        assert_eq!(spec.products[0].render_var_indices, vec![0, 1]);
        assert_eq!(spec.products[1].render_var_indices, vec![0]);
        // resolution inherited from the settings base.
        assert_eq!(spec.products[0].resolution, [1024, 512]);
        assert!(spec.diagnostics.is_empty());
        Ok(())
    }

    /// A product attribute overrides the settings value only where the product
    /// authors it; everything else inherits the resolved settings.
    #[test]
    fn product_overrides_only_authored() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let settings = settings(&stage, &["/Render/Products/p"])?;
        settings.create_resolution_attr()?.set(gf::vec2i(1920, 1080))?;
        settings.create_pixel_aspect_ratio_attr()?.set(2.0_f32)?;
        // Product authors only `resolution`.
        Product::define(&stage, "/Render/Products/p")?
            .create_resolution_attr()?
            .set(gf::vec2i(512, 512))?;

        let spec = compute(&stage)?;
        let p = &spec.products[0];
        assert_eq!(p.resolution, [512, 512]); // overridden by the product
        assert!((p.pixel_aspect_ratio - 2.0).abs() < 1e-6); // inherited from settings
        Ok(())
    }

    /// A bound camera drives the conform policy: a square aperture against a
    /// 2:1 image expands the aperture width (default `expandAperture`).
    #[test]
    fn conform_against_bound_camera() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        Product::define(&stage, "/Render/Products/p")?;
        settings(&stage, &["/Render/Products/p"])?
            .create_resolution_attr()?
            .set(gf::vec2i(200, 100))?;

        let spec = compute(&stage)?;
        let p = &spec.products[0];
        assert_eq!(p.camera_path, sdf::path("/World/Cam")?);
        // expandAperture, square aperture vs 2:1 image → width grows to 20.
        assert!((p.aperture_size[0] - 20.0).abs() < 1e-3);
        assert!((p.aperture_size[1] - 10.0).abs() < 1e-3);
        Ok(())
    }

    /// A product with no camera is left out with its vars; the next product
    /// is kept.
    #[test]
    fn missing_camera_skips() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        Var::define(&stage, "/Render/Vars/X")?;
        Var::define(&stage, "/Render/Vars/Y")?;
        Product::define(&stage, "/Render/Products/a")?
            .create_ordered_vars_rel()?
            .set_targets(["/Render/Vars/X"])?;
        let b = Product::define(&stage, "/Render/Products/b")?;
        b.create_ordered_vars_rel()?.set_targets(["/Render/Vars/Y"])?;
        camera(&stage, "/World/Cam")?;
        b.create_camera_rel()?.add_target("/World/Cam")?;
        Settings::define(&stage, "/Render/Settings")?
            .create_products_rel()?
            .set_targets(["/Render/Products/a", "/Render/Products/b"])?;

        let spec = compute(&stage)?;
        assert_eq!(spec.products.len(), 1);
        assert_eq!(spec.products[0].render_product_path, sdf::path("/Render/Products/b")?);
        assert_eq!(spec.products[0].render_var_indices, vec![0]);
        assert_eq!(spec.render_vars.len(), 1);
        assert_eq!(spec.render_vars[0].render_var_path, sdf::path("/Render/Vars/Y")?);
        assert_eq!(
            spec.diagnostics,
            vec![SpecDiagnostic::MissingCamera {
                product: sdf::path("/Render/Products/a")?,
                camera: None,
            }]
        );
        Ok(())
    }

    #[test]
    fn non_camera_skips() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/World/Scope")?.set_type_name("Scope")?;
        Product::define(&stage, "/Render/Products/p")?;
        let settings = Settings::define(&stage, "/Render/Settings")?;
        settings.create_camera_rel()?.add_target("/World/Scope")?;
        settings.create_products_rel()?.set_targets(["/Render/Products/p"])?;

        let spec = compute(&stage)?;
        assert!(spec.products.is_empty());
        assert_eq!(
            spec.diagnostics,
            vec![SpecDiagnostic::MissingCamera {
                product: sdf::path("/Render/Products/p")?,
                camera: Some(sdf::path("/World/Scope")?),
            }]
        );
        Ok(())
    }

    /// A camera target naming a property of a `Camera` is no camera.
    #[test]
    fn camera_property_path() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        camera(&stage, "/World/Cam")?;
        Product::define(&stage, "/Render/Products/p")?
            .create_camera_rel()?
            .add_target("/World/Cam.focalLength")?;
        Settings::define(&stage, "/Render/Settings")?
            .create_products_rel()?
            .set_targets(["/Render/Products/p"])?;

        let spec = compute(&stage)?;
        assert!(spec.products.is_empty());
        assert_eq!(
            spec.diagnostics,
            vec![SpecDiagnostic::MissingCamera {
                product: sdf::path("/Render/Products/p")?,
                camera: Some(sdf::path("/World/Cam.focalLength")?),
            }]
        );
        Ok(())
    }

    /// A `products` target naming a property of a `Product` is ignored
    /// without a diagnostic, as a target that is no product is.
    #[test]
    fn product_property_path() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        Product::define(&stage, "/Render/Products/p")?;
        settings(&stage, &["/Render/Products/p.resolution", "/Render/Products/p"])?;

        let spec = compute(&stage)?;
        assert_eq!(spec.products.len(), 1);
        assert_eq!(spec.products[0].render_product_path, sdf::path("/Render/Products/p")?);
        assert!(spec.diagnostics.is_empty());
        Ok(())
    }

    #[test]
    fn var_property_path() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        Var::define(&stage, "/Render/Vars/v")?;
        Product::define(&stage, "/Render/Products/p")?
            .create_ordered_vars_rel()?
            .set_targets(["/Render/Vars/v.sourceName"])?;
        settings(&stage, &["/Render/Products/p"])?;

        let spec = compute(&stage)?;
        assert_eq!(spec.products.len(), 1);
        assert!(spec.products[0].render_var_indices.is_empty());
        assert!(spec.render_vars.is_empty());
        assert_eq!(
            spec.diagnostics,
            vec![SpecDiagnostic::MissingVar {
                product: sdf::path("/Render/Products/p")?,
                var: sdf::path("/Render/Vars/v.sourceName")?,
            }]
        );
        Ok(())
    }

    #[test]
    fn missing_var_diagnostic() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/Render/Vars/scope")?.set_type_name("Scope")?;
        Product::define(&stage, "/Render/Products/p")?
            .create_ordered_vars_rel()?
            .set_targets(["/Render/Vars/scope"])?;
        settings(&stage, &["/Render/Products/p"])?;

        let spec = compute(&stage)?;
        assert_eq!(spec.products.len(), 1);
        assert_eq!(
            spec.diagnostics,
            vec![SpecDiagnostic::MissingVar {
                product: sdf::path("/Render/Products/p")?,
                var: sdf::path("/Render/Vars/scope")?,
            }]
        );
        Ok(())
    }

    /// A property path of a `Settings` prim names no settings.
    #[test]
    fn settings_property_path() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        settings(&stage, &[])?;
        assert!(render_spec(&stage, &sdf::path("/Render/Settings.camera")?, &[])?.is_none());
        Ok(())
    }

    #[test]
    fn product_camera_overrides() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        camera(&stage, "/World/Other")?;
        Product::define(&stage, "/Render/Products/p")?
            .create_camera_rel()?
            .add_target("/World/Other")?;
        settings(&stage, &["/Render/Products/p"])?;

        let spec = compute(&stage)?;
        assert_eq!(spec.products[0].camera_path, sdf::path("/World/Other")?);
        Ok(())
    }

    /// The settings' `camera` targets a relationship that targets the camera.
    #[test]
    fn camera_forwarded() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        camera(&stage, "/World/Cam")?;
        let rig = stage.define_prim("/World/Rig")?;
        stage
            .create_relationship(rig.path().append_property("active")?)?
            .add_target("/World/Cam")?;
        Product::define(&stage, "/Render/Products/p")?;
        let settings = Settings::define(&stage, "/Render/Settings")?;
        settings.create_camera_rel()?.add_target("/World/Rig.active")?;
        settings.create_products_rel()?.set_targets(["/Render/Products/p"])?;

        let spec = compute(&stage)?;
        assert_eq!(spec.products[0].camera_path, sdf::path("/World/Cam")?);
        Ok(())
    }

    /// A conform policy outside the enum is kept and adjusts nothing.
    #[test]
    fn unknown_policy_kept() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        Product::define(&stage, "/Render/Products/p")?
            .create_aspect_ratio_conform_policy_attr()?
            .set(vt::Value::token("bogus"))?;
        settings(&stage, &["/Render/Products/p"])?
            .create_resolution_attr()?
            .set(gf::vec2i(200, 100))?;

        let spec = compute(&stage)?;
        let p = &spec.products[0];
        assert_eq!(p.aspect_ratio_conform_policy, "bogus");
        assert_eq!(p.aperture_size, [10.0, 10.0]);
        Ok(())
    }

    /// A blocked settings attribute reads its schema fallback.
    #[test]
    fn blocked_purposes_fallback() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        settings(&stage, &[])?.create_included_purposes_attr()?.block()?;
        assert_eq!(compute(&stage)?.included_purposes, vec!["default", "render"]);
        Ok(())
    }

    /// A block is not an authored value. A product that blocks an attribute
    /// inherits the settings' value, not the schema fallback.
    #[test]
    fn blocked_product_inherits() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        Product::define(&stage, "/Render/Products/p")?
            .create_resolution_attr()?
            .block()?;
        settings(&stage, &["/Render/Products/p"])?
            .create_resolution_attr()?
            .set(gf::vec2i(1024, 512))?;
        assert_eq!(compute(&stage)?.products[0].resolution, [1024, 512]);
        Ok(())
    }

    #[test]
    fn non_settings_prim_is_none() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/Scope")?.set_type_name("Scope")?;
        assert!(render_spec(&stage, &sdf::path("/Scope")?, &[])?.is_none());
        Ok(())
    }

    /// The names of the settings gathered on `/S` under `namespaces`.
    fn setting_names(stage: &Stage, namespaces: &[&str]) -> Result<Vec<String>> {
        Ok(namespaced_settings(stage, &sdf::path("/S")?, namespaces)?
            .into_iter()
            .map(|(name, _)| name)
            .collect())
    }

    /// An `int` attribute `name` on `/S`, set to 1.
    fn int_attr(stage: &Stage, name: &str) -> Result<Attribute> {
        Ok(stage
            .create_attribute(sdf::path("/S")?.append_property(name)?, "int")?
            .set(vt::Value::Int(1))?)
    }

    #[test]
    fn unnamespaced_skipped() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/S")?;
        int_attr(&stage, "plain")?;
        int_attr(&stage, "ri:a")?;
        assert_eq!(setting_names(&stage, &[])?, ["ri:a"]);
        Ok(())
    }

    /// A namespace is matched whole, and only the outermost one.
    #[test]
    fn namespace_exact_match() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/S")?;
        for name in ["ri:a", "rix:a", "other:ri:a"] {
            int_attr(&stage, name)?;
        }
        assert_eq!(setting_names(&stage, &["ri"])?, ["ri:a"]);
        Ok(())
    }

    /// A blocked attribute no schema declares reads no value, and is left out.
    #[test]
    fn blocked_setting_omitted() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/S")?;
        int_attr(&stage, "ri:x")?.block()?;
        int_attr(&stage, "ri:y")?;
        assert_eq!(setting_names(&stage, &[])?, ["ri:y"]);
        Ok(())
    }

    /// The output view of the attribute `name` on `prim`, of `type_name`.
    fn output(stage: &Stage, prim: &str, name: &str, type_name: &str) -> Result<Output> {
        let attr = stage.create_attribute(sdf::path(prim)?.append_property(name)?, type_name)?;
        Ok(Output::from_attribute(attr).expect("an outputs: attribute"))
    }

    /// The setting `name` gathered on `/S` under `context`.
    fn setting(context: &ConnectableContext, stage: &Stage, name: &str) -> Result<Option<Value>> {
        let settings = namespaced_settings_in(context, stage, &sdf::path("/S")?, &[])?;
        Ok(settings
            .into_iter()
            .find(|(setting, _)| setting == name)
            .map(|(_, value)| value))
    }

    /// A connected output gathers the prim of the shader output producing it.
    #[test]
    fn connected_output_paths() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/S")?;
        let filter = crate::shade::Shader::define(&stage, "/Shaders/Filter")?.create_output("out", "token")?;
        output(&stage, "/S", "outputs:ri:displayFilter", "token")?.connect_to(&filter)?;
        assert_eq!(
            setting(&ConnectableContext::default(), &stage, "outputs:ri:displayFilter")?,
            Some(Value::PathVec(vec![sdf::path("/Shaders/Filter")?]))
        );
        Ok(())
    }

    /// An unconnected output with an authored value is its own producer.
    #[test]
    fn authored_output_self() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/S")?;
        output(&stage, "/S", "outputs:ri:x", "int")?.set(Value::Int(1))?;
        assert_eq!(
            setting(&ConnectableContext::default(), &stage, "outputs:ri:x")?,
            Some(Value::PathVec(vec![sdf::path("/S")?]))
        );
        Ok(())
    }

    /// An output's namespace is read past `outputs:`. `outputs:x` has none.
    #[test]
    fn bare_output_skipped() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/S")?;
        output(&stage, "/S", "outputs:x", "int")?.set(Value::Int(1))?;
        output(&stage, "/S", "outputs:ri:y", "int")?.set(Value::Int(1))?;
        assert_eq!(setting_names(&stage, &[])?, ["outputs:ri:y"]);
        assert_eq!(setting_names(&stage, &["outputs"])?, Vec::<String>::new());
        Ok(())
    }

    /// The walk a context runs follows an output through the prims its
    /// registry makes containers, and stops at them under the default one.
    #[test]
    fn output_custom_context() -> Result {
        use crate::shade::behavior::tests::{FAMILY, custom_context};

        let stage = crate::geom::boundable::tests::stage_with(FAMILY)?;
        stage.define_prim("/S")?;
        stage.define_prim("/Box")?.set_type_name("TestTyped")?;
        let inner = crate::shade::Shader::define(&stage, "/Box/Inner")?.create_output("out", "float")?;
        let routed = output(&stage, "/Box", "outputs:out", "float")?.connect_to(&inner)?;
        output(&stage, "/S", "outputs:ri:f", "float")?.connect_to(&routed)?;

        let paths = |prims: &[&str]| -> Result<Option<Value>> {
            let mut paths = Vec::new();
            for prim in prims {
                paths.push(sdf::path(*prim)?);
            }
            Ok(Some(Value::PathVec(paths)))
        };
        assert_eq!(
            setting(&custom_context(false), &stage, "outputs:ri:f")?,
            paths(&["/Box/Inner"])?
        );
        assert_eq!(
            setting(&ConnectableContext::default(), &stage, "outputs:ri:f")?,
            paths(&["/Box"])?
        );
        Ok(())
    }
}
