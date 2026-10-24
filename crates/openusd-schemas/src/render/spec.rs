//! The computed render spec (`UsdRenderSpec`).
//!
//! A flattened, fallback-resolved view of a `Settings` prim, its
//! products, vars, and camera: product attributes have overridden the
//! settings they inherit, the aspect-ratio conform policy has been
//! applied to `aperture_size`, and vars are de-duplicated into one global
//! list referenced by per-product indices.
//!
//! These are pure value types; [`render_spec`](super::render_spec) fills
//! them.

use openusd::sdf::{Path, Value};
use openusd::tf;

use super::{ProductType, SourceType};

/// One render product, flattened: the inherited base attributes resolved
/// and the camera aperture conform-adjusted.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Product {
    /// Scene path of the source `Product` prim.
    pub render_product_path: Path,
    /// `productType` (e.g. `raster`).
    pub product_type: ProductType,
    /// `productName` — output / display-driver name.
    pub name: String,
    /// The `Camera` the product renders through: its own `camera` target,
    /// else the settings'.
    pub camera_path: Path,
    /// Resolved `disableMotionBlur`.
    pub disable_motion_blur: bool,
    /// Resolved `disableDepthOfField`.
    pub disable_depth_of_field: bool,
    /// Resolved `resolution`.
    pub resolution: [i32; 2],
    /// Resolved `pixelAspectRatio` (may be recomputed by the conform policy).
    pub pixel_aspect_ratio: f32,
    /// Resolved `aspectRatioConformPolicy`, kept as authored: a token that
    /// names no [`AspectRatioConformPolicy`](super::AspectRatioConformPolicy)
    /// leaves the aperture unadjusted.
    pub aspect_ratio_conform_policy: tf::Token,
    /// Camera aperture `(width, height)` after the conform policy is applied.
    pub aperture_size: [f32; 2],
    /// Resolved `dataWindowNDC` — `(xmin, ymin, xmax, ymax)`.
    pub data_window_ndc: [f32; 4],
    /// Indices into [`RenderSpec::render_vars`] for this product's
    /// `orderedVars`.
    pub render_var_indices: Vec<usize>,
    /// The settings
    /// [`namespaced_settings`](super::namespaced_settings) gathers on the
    /// product.
    pub namespaced_settings: Vec<(String, Value)>,
}

/// One render var (AOV), flattened.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Var {
    /// Scene path of the source `Var` prim.
    pub render_var_path: Path,
    /// `dataType`.
    pub data_type: String,
    /// `sourceName`.
    pub source_name: String,
    /// `sourceType`.
    pub source_type: SourceType,
    /// The settings
    /// [`namespaced_settings`](super::namespaced_settings) gathers on the var.
    pub namespaced_settings: Vec<(String, Value)>,
}

/// The computed render spec for one `Settings` prim.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct RenderSpec {
    /// The products to produce, in `products`-relationship order.
    pub products: Vec<Product>,
    /// The global, de-duplicated var list referenced by
    /// [`Product::render_var_indices`].
    pub render_vars: Vec<Var>,
    /// `includedPurposes` from the settings.
    pub included_purposes: Vec<tf::Token>,
    /// `materialBindingPurposes` from the settings.
    pub material_binding_purposes: Vec<tf::Token>,
    /// The settings
    /// [`namespaced_settings`](super::namespaced_settings) gathers on the
    /// settings.
    pub namespaced_settings: Vec<(String, Value)>,
    /// What the computation skipped, and why.
    pub diagnostics: Vec<SpecDiagnostic>,
}

/// A product or var the computation skipped, and why. C++ reports each as a
/// runtime error and goes on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecDiagnostic {
    /// A product whose camera is not a `Camera` prim, or that binds none;
    /// the product is left out with its vars.
    MissingCamera {
        /// The product.
        product: Path,
        /// The camera it binds, its own or the settings'.
        camera: Option<Path>,
    },
    /// An `orderedVars` target that is not a `Var` prim; the var is left
    /// out, and its product kept.
    MissingVar {
        /// The product whose `orderedVars` names it.
        product: Path,
        /// The target.
        var: Path,
    },
}
