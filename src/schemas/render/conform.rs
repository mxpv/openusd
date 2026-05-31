//! Aspect-ratio conform policy (spec) — reconciling the camera aperture
//! aspect ratio with the image aspect ratio.
//!
//! Mirrors C++ `UsdRenderComputeSpec`'s `_ApplyAspectRatioPolicy`. The
//! computation never writes back to the camera; it produces the adjusted
//! aperture (and possibly `pixelAspectRatio`) stored on the computed spec.

use super::types::AspectRatioConformPolicy;

/// The aperture (and `pixelAspectRatio`) after the conform policy is applied.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ConformedAperture {
    /// Camera aperture `(width, height)` after adjustment.
    pub aperture_size: [f32; 2],
    /// `pixelAspectRatio` — recomputed only by `adjustPixelAspectRatio`,
    /// otherwise the input value.
    pub pixel_aspect_ratio: f32,
}

/// Reconcile the camera `aperture` aspect with the image aspect
/// (`resolution` × `pixel_aspect_ratio`) per `policy` (spec
/// 12 / `_ApplyAspectRatioPolicy`).
///
/// `expandAperture` grows the aperture so nothing is cropped;
/// `cropAperture` shrinks it (the mirror branch); the two `adjustAperture*`
/// policies pin one dimension; `adjustPixelAspectRatio` leaves the aperture
/// alone and changes `pixelAspectRatio` instead. The adjusted dimension is
/// always set so `width / height == imageAspectRatio`.
pub fn apply_aspect_ratio_policy(
    policy: AspectRatioConformPolicy,
    resolution: [i32; 2],
    pixel_aspect_ratio: f32,
    aperture: [f32; 2],
) -> ConformedAperture {
    // Guard the divisors so malformed inputs can't yield inf/NaN — with a
    // zero resolution height or aperture height there is nothing to reconcile,
    // so return the aperture and pixel aspect unchanged.
    if resolution[1] == 0 || aperture[1] == 0.0 {
        return ConformedAperture {
            aperture_size: aperture,
            pixel_aspect_ratio,
        };
    }

    let res_aspect = resolution[0] as f32 / resolution[1] as f32;
    let image_aspect = pixel_aspect_ratio * res_aspect;
    let aperture_aspect = aperture[0] / aperture[1];

    let mut size = aperture;
    let mut par = pixel_aspect_ratio;

    enum Adjust {
        None,
        Width,
        Height,
    }
    // Branch selection mirrors C++ exactly: expand and crop differ only in
    // which dimension they pick under the same `aperture_aspect > image_aspect`
    // test, so getting the comparison backwards crops where it should expand.
    let adjust = match policy {
        AspectRatioConformPolicy::AdjustPixelAspectRatio => {
            par = aperture_aspect / res_aspect;
            Adjust::None
        }
        AspectRatioConformPolicy::AdjustApertureHeight => Adjust::Height,
        AspectRatioConformPolicy::AdjustApertureWidth => Adjust::Width,
        AspectRatioConformPolicy::ExpandAperture => {
            if aperture_aspect > image_aspect {
                Adjust::Height
            } else {
                Adjust::Width
            }
        }
        AspectRatioConformPolicy::CropAperture => {
            if aperture_aspect > image_aspect {
                Adjust::Width
            } else {
                Adjust::Height
            }
        }
    };

    match adjust {
        Adjust::Width => size[0] = size[1] * image_aspect,
        Adjust::Height => size[1] = size[0] / image_aspect,
        Adjust::None => {}
    }

    ConformedAperture {
        aperture_size: size,
        pixel_aspect_ratio: par,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // resolution 200×100 → res_aspect 2.0; pixelAspectRatio 1.0 →
    // image_aspect 2.0. Square aperture 10×10 → aperture_aspect 1.0
    // (taller, relative to the image).
    const RES: [i32; 2] = [200, 100];
    const PAR: f32 = 1.0;
    const APERTURE: [f32; 2] = [10.0, 10.0];

    fn run(policy: AspectRatioConformPolicy) -> ConformedAperture {
        apply_aspect_ratio_policy(policy, RES, PAR, APERTURE)
    }

    fn approx(a: [f32; 2], b: [f32; 2]) -> bool {
        (a[0] - b[0]).abs() < 1e-4 && (a[1] - b[1]).abs() < 1e-4
    }

    #[test]
    fn expand_grows_width_when_aperture_is_taller() {
        // aperture_aspect 1.0 < image 2.0 → grow Width to 10*2 = 20.
        let c = run(AspectRatioConformPolicy::ExpandAperture);
        assert!(approx(c.aperture_size, [20.0, 10.0]));
        assert_eq!(c.pixel_aspect_ratio, 1.0);
    }

    #[test]
    fn crop_shrinks_height_the_mirror_branch() {
        // Same test, opposite branch → shrink Height to 10/2 = 5.
        let c = run(AspectRatioConformPolicy::CropAperture);
        assert!(approx(c.aperture_size, [10.0, 5.0]));
    }

    #[test]
    fn adjust_aperture_width_pins_height() {
        let c = run(AspectRatioConformPolicy::AdjustApertureWidth);
        assert!(approx(c.aperture_size, [20.0, 10.0]));
    }

    #[test]
    fn adjust_aperture_height_pins_width() {
        let c = run(AspectRatioConformPolicy::AdjustApertureHeight);
        assert!(approx(c.aperture_size, [10.0, 5.0]));
    }

    #[test]
    fn zero_divisors_return_finite_unchanged() {
        // Malformed inputs must not yield inf/NaN.
        let c = apply_aspect_ratio_policy(AspectRatioConformPolicy::ExpandAperture, [200, 0], 1.0, [10.0, 10.0]);
        assert_eq!(c.aperture_size, [10.0, 10.0]);
        assert!(c.aperture_size.iter().all(|v| v.is_finite()));
        let c = apply_aspect_ratio_policy(AspectRatioConformPolicy::ExpandAperture, [200, 100], 1.0, [10.0, 0.0]);
        assert!(c.aperture_size.iter().all(|v| v.is_finite()));
    }

    #[test]
    fn adjust_pixel_aspect_ratio_leaves_aperture() {
        // par = aperture_aspect / res_aspect = 1.0 / 2.0 = 0.5; aperture intact.
        let c = run(AspectRatioConformPolicy::AdjustPixelAspectRatio);
        assert!(approx(c.aperture_size, [10.0, 10.0]));
        assert!((c.pixel_aspect_ratio - 0.5).abs() < 1e-6);
    }
}
