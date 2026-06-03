//! The computed render spec (`UsdRenderSpec`).
//!
//! A flattened, fallback-resolved view of a `RenderSettings` prim, its
//! products, vars, and camera: product attributes have overridden the
//! settings they inherit, the aspect-ratio conform policy has been
//! applied to `aperture_size`, and vars are de-duplicated into one global
//! list referenced by per-product indices.
//!
//! These are pure value types; the computation that fills them is built
//! up across the following commits (`compute_render_spec`).

use crate::sdf::Value;

use super::{AspectRatioConformPolicy, ProductType, SourceType};

/// One render product, flattened: the inherited base attributes resolved
/// and the camera aperture conform-adjusted.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Product {
    /// Scene path of the source `RenderProduct` prim.
    pub render_product_path: String,
    /// `productType` (e.g. `raster`).
    pub product_type: ProductType,
    /// `productName` — output / display-driver name.
    pub name: String,
    /// Resolved `camera` path, if the product (or its settings) bound one.
    pub camera_path: Option<String>,
    /// Resolved `disableMotionBlur`.
    pub disable_motion_blur: bool,
    /// Resolved `disableDepthOfField`.
    pub disable_depth_of_field: bool,
    /// Resolved `resolution`.
    pub resolution: [i32; 2],
    /// Resolved `pixelAspectRatio` (may be recomputed by the conform policy).
    pub pixel_aspect_ratio: f32,
    /// Resolved `aspectRatioConformPolicy`.
    pub aspect_ratio_conform_policy: AspectRatioConformPolicy,
    /// Camera aperture `(width, height)` after the conform policy is applied.
    pub aperture_size: [f32; 2],
    /// Resolved `dataWindowNDC` — `(xmin, ymin, xmax, ymax)`.
    pub data_window_ndc: [f32; 4],
    /// Indices into [`RenderSpec::render_vars`] for this product's
    /// `orderedVars`.
    pub render_var_indices: Vec<usize>,
    /// `namespace:`-prefixed render-delegate settings gathered on the product.
    pub namespaced_settings: Vec<(String, Value)>,
}

/// One render var (AOV), flattened.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct RenderVar {
    /// Scene path of the source `RenderVar` prim.
    pub render_var_path: String,
    /// `dataType`.
    pub data_type: String,
    /// `sourceName`.
    pub source_name: String,
    /// `sourceType`.
    pub source_type: SourceType,
    /// `namespace:`-prefixed render-delegate settings gathered on the var.
    pub namespaced_settings: Vec<(String, Value)>,
}

/// The computed render spec for one `RenderSettings` prim.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct RenderSpec {
    /// The products to produce, in `products`-relationship order.
    pub products: Vec<Product>,
    /// The global, de-duplicated var list referenced by
    /// [`Product::render_var_indices`].
    pub render_vars: Vec<RenderVar>,
    /// `includedPurposes` from the settings.
    pub included_purposes: Vec<String>,
    /// `materialBindingPurposes` from the settings.
    pub material_binding_purposes: Vec<String>,
    /// `namespace:`-prefixed render-delegate settings gathered on the settings.
    pub namespaced_settings: Vec<(String, Value)>,
}
