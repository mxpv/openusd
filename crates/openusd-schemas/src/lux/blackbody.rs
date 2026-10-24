//! The color of a blackbody at a temperature, which a light's
//! `enableColorTemperature` multiplies its color by.

use openusd::gf;

/// The Rec.709 linear RGB of a blackbody at `kelvin`, scaled to the
/// luminance of white, `(1, 1, 1)`, then clamped at zero (C++
/// `UsdLuxBlackbodyTemperatureAsRgb`).
///
/// The curve runs from 1000 K to 10000 K, and a temperature outside that
/// range takes its nearer end. `NaN` takes the 1000 K end, where C++ leaves
/// the result undefined. 6500 K is close to white, though not exactly: the
/// Rec.709 white point lies off the Planckian locus.
pub fn blackbody_rgb(kelvin: f32) -> gf::Vec3f {
    let u = if kelvin.is_nan() {
        0.0
    } else {
        ((kelvin - 1000.0) / 9000.0).clamp(0.0, 1.0)
    };
    // The last four knots are the segment starting at `u == 1`, which keeps
    // every segment index in bounds.
    let x = u * (KNOTS.len() - 4) as f32;
    let segment = x.floor() as usize;
    let t = x - segment as f32;
    let [k0, k1, k2, k3] = [0, 1, 2, 3].map(|knot| gf::Vec3f::from(KNOTS[segment + knot]));
    let [a, b, c, d] = BASIS.map(|[w0, w1, w2, w3]| k0 * w0 + k1 * w1 + k2 * w2 + k3 * w3);
    let rgb = ((a * t + b) * t + c) * t + d;
    let rgb = rgb / rgb.dot(REC709_LUMA);
    // The spline dips a little below zero between knots, as the blue channel
    // does near 1300 K.
    rgb.max(gf::Vec3f::from([0.0; 3]))
}

/// The weight of each Rec.709 channel in luminance.
const REC709_LUMA: gf::Vec3f = gf::Vec3f {
    x: 0.2126,
    y: 0.7152,
    z: 0.0722,
};

/// Rec.709 blackbody colors from 1000 K to 10000 K in 500 K steps (John
/// Walker, "Colour Rendering of Spectra"), the first knot repeated once and
/// the last twice to give the spline its ends.
const KNOTS: [[f32; 3]; 22] = [
    [1.000000, 0.027490, 0.000000], // 1000 K (approximation)
    [1.000000, 0.027490, 0.000000], // 1000 K (approximation)
    [1.000000, 0.149664, 0.000000], // 1500 K (approximation)
    [1.000000, 0.256644, 0.008095], // 2000 K
    [1.000000, 0.372033, 0.067450], // 2500 K
    [1.000000, 0.476725, 0.153601], // 3000 K
    [1.000000, 0.570376, 0.259196], // 3500 K
    [1.000000, 0.653480, 0.377155], // 4000 K
    [1.000000, 0.726878, 0.501606], // 4500 K
    [1.000000, 0.791543, 0.628050], // 5000 K
    [1.000000, 0.848462, 0.753228], // 5500 K
    [1.000000, 0.898581, 0.874905], // 6000 K
    [1.000000, 0.942771, 0.991642], // 6500 K
    [0.906947, 0.890456, 1.000000], // 7000 K
    [0.828247, 0.841838, 1.000000], // 7500 K
    [0.765791, 0.801896, 1.000000], // 8000 K
    [0.715255, 0.768579, 1.000000], // 8500 K
    [0.673683, 0.740423, 1.000000], // 9000 K
    [0.638992, 0.716359, 1.000000], // 9500 K
    [0.609681, 0.695588, 1.000000], // 10000 K
    [0.609681, 0.695588, 1.000000], // 10000 K
    [0.609681, 0.695588, 1.000000], // 10000 K
];

/// The Catmull-Rom basis, one row per cubic coefficient.
const BASIS: [[f32; 4]; 4] = [
    [-0.5, 1.5, -1.5, 0.5],
    [1.0, -2.5, 2.0, -0.5],
    [-0.5, 0.0, 0.5, 0.0],
    [0.0, 1.0, 0.0, 0.0],
];

#[cfg(test)]
mod tests {
    use super::*;

    /// `testUsdLuxLight.py:test_BlackbodySpectrum`: 6500 K is close to white,
    /// 1000 K is red and 10000 K blue.
    #[test]
    fn blackbody_rgb_curve() {
        let white = blackbody_rgb(6500.0);
        assert!((white - gf::vec3f(1.0, 1.0, 1.0)).length() < 0.1, "{white:?}");
        let warm = blackbody_rgb(1000.0);
        assert!(warm.x > warm.y && warm.x > warm.z, "{warm:?}");
        let cool = blackbody_rgb(10000.0);
        assert!(cool.z > cool.x && cool.z > cool.y, "{cool:?}");
    }

    /// At a knot the curve is the knot's color at the luminance of white,
    /// and a temperature past either end, or `NaN`, takes that end.
    #[test]
    fn blackbody_knot() {
        let at_luma = |knot: [f32; 3]| {
            let knot = gf::Vec3f::from(knot);
            knot / knot.dot(REC709_LUMA)
        };
        let close = |found: gf::Vec3f, expected: gf::Vec3f| (found - expected).length() < 1e-5;
        assert!(close(blackbody_rgb(10000.0), at_luma(KNOTS[19])));
        assert!(close(blackbody_rgb(1000.0), at_luma(KNOTS[1])));
        assert_eq!(blackbody_rgb(20000.0), blackbody_rgb(10000.0));
        assert_eq!(blackbody_rgb(0.0), blackbody_rgb(1000.0));
        assert_eq!(blackbody_rgb(f32::NAN), blackbody_rgb(1000.0));
    }
}
