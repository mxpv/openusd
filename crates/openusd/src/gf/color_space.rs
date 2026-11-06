//! Color spaces (C++ `GfColorSpace`), built on a port of the nanocolor
//! library that C++ OpenUSD bundles under `pxr/base/gf/nc`.
//!
//! A [`ColorSpace`] is a set of red, green and blue primaries, a white point,
//! and a transfer curve given by a gamma and a linear bias. AOUSD core spec
//! §14.1 lists the built-in spaces; [`color_space_names`] holds their tokens.

use std::array;
use std::sync::LazyLock;

use crate::{gf, tf};

/// A color space (C++ `GfColorSpace`): red, green and blue primaries and a
/// white point, which give the matrix taking linear RGB to CIE XYZ, and a
/// transfer curve, which encodes linear values.
///
/// The curve is linear below a knee and `(1 + bias) · t^(1 / gamma) − bias`
/// above it; [`transfer_params`](Self::transfer_params) gives the knee and the
/// slope of the linear segment. A gamma of 1 is a linear space.
///
/// Equality compares the name and every parameter exactly. C++ `operator==`
/// compares only the transform, within a tolerance;
/// [`is_equivalent`](Self::is_equivalent) is that comparison.
#[derive(Debug, Clone, PartialEq)]
pub struct ColorSpace {
    name: tf::Token,
    /// The red, green and blue primaries, then the white point.
    primaries: [gf::Vec2f; 4],
    gamma: f32,
    linear_bias: f32,
    /// The knee of the transfer curve, in encoded values.
    k0: f32,
    /// The slope of the transfer curve's linear segment.
    phi: f32,
    rgb_to_xyz: M33,
}

/// A 3×3 matrix in nanocolor's layout: row-major, applied to a column vector
/// (`xyz = M · rgb`). Its arithmetic below is nanocolor's, in `f32`, and its
/// results match C++ to the bit. [`gf::Mat3d`] is the public form.
type M33 = [f32; 9];

impl ColorSpace {
    /// The built-in color space named `name`, matched against either its token
    /// (`lin_rec709_scene`) or its descriptive name (`Linear Rec.709 (sRGB)`).
    ///
    /// A name that is not built in gives an identity transform with a linear
    /// curve under that name, as C++ does, for use as a sentinel to compare
    /// against. [`is_valid`](Self::is_valid) tells the two apart.
    pub fn new(name: impl Into<tf::Token>) -> Self {
        let name = name.into();
        match builtin(name.as_str()) {
            Some(index) => BUILTIN_SPACES[index].clone(),
            None => Self::from_nc_matrix(name, IDENTITY, 1.0, 0.0),
        }
    }

    /// Whether `name` is a built-in color space's token or descriptive name
    /// (C++ `GfColorSpace::IsValid`).
    pub fn is_valid(name: &str) -> bool {
        builtin(name).is_some()
    }

    /// A color space from its primaries, white point and curve.
    ///
    /// A white point whose x is 0 gives a zero matrix, as in C++.
    pub fn from_primaries(name: impl Into<tf::Token>, primaries: [gf::Vec2f; 4], gamma: f32, linear_bias: f32) -> Self {
        let (k0, phi) = transfer(gamma, linear_bias);
        Self {
            name: name.into(),
            primaries,
            gamma,
            linear_bias,
            k0,
            phi,
            rgb_to_xyz: primaries_matrix(primaries),
        }
    }

    /// A color space from its RGB-to-XYZ matrix and curve.
    ///
    /// `rgb_to_xyz` follows the [`gf`](crate::gf) row-vector convention,
    /// `xyz = rgb · M`, and [`rgb_to_xyz`](Self::rgb_to_xyz) returns it. C++
    /// takes the transpose, the matrix applied to a column vector. The
    /// primaries and white point are the chromaticities of unit red, green,
    /// blue and white under the matrix.
    pub fn from_matrix(name: impl Into<tf::Token>, rgb_to_xyz: gf::Mat3d, gamma: f32, linear_bias: f32) -> Self {
        // The narrowing to f32 matches the `GfMatrix3f` C++ takes.
        let m = rgb_to_xyz.transpose().0.map(|e| e as f32);
        Self::from_nc_matrix(name.into(), m, gamma, linear_bias)
    }

    /// The color space's token (C++ `GetName`). A built-in found by its
    /// descriptive name answers its token.
    pub fn name(&self) -> &tf::Token {
        &self.name
    }

    /// The matrix taking linear RGB to CIE XYZ, in the [`gf`](crate::gf)
    /// row-vector convention: `xyz = rgb · M`. C++ `GetRGBToXYZ` returns the
    /// transpose.
    pub fn rgb_to_xyz(&self) -> gf::Mat3d {
        to_mat3d(self.rgb_to_xyz)
    }

    /// The matrix taking linear RGB in `src` to linear RGB in this space, in
    /// the [`gf`](crate::gf) row-vector convention: `dst = rgb · M`. C++
    /// `GetRGBToRGB` returns the transpose.
    pub fn rgb_to_rgb(&self, src: &ColorSpace) -> gf::Mat3d {
        to_mat3d(rgb_to_rgb(src, self))
    }

    /// The gamma of the curve above its knee.
    pub fn gamma(&self) -> f32 {
        self.gamma
    }

    /// The linear bias of the curve above its knee.
    pub fn linear_bias(&self) -> f32 {
        self.linear_bias
    }

    /// The knee of the transfer curve, in encoded values, and the slope of its
    /// linear segment (C++ `GetTransferFunctionParams`, nanocolor's `K0` and
    /// `phi`).
    ///
    /// Every space computes these from its gamma and bias. C++ leaves both at
    /// 0 for a space built from a matrix, for the `data`, `identity`, `raw`
    /// and `unknown` spaces, and for the sentinel of a name that is not built
    /// in. In C++ that drops the linear segment from a matrix-built space's
    /// curve, makes the linear conversion of a negative value in an identity
    /// space `-inf`, and shifts the primaries derived for a matrix-built space
    /// with a bias above 0.
    pub fn transfer_params(&self) -> (f32, f32) {
        (self.k0, self.phi)
    }

    /// The red, green and blue primaries and the white point, in that order
    /// (C++ `GetPrimariesAndWhitePoint`). All four are zero when the white
    /// point's x is 0, as C++ reports for a space it cannot describe by
    /// primaries.
    pub fn primaries_and_white_point(&self) -> [gf::Vec2f; 4] {
        if self.primaries[3].x == 0.0 {
            return [gf::Vec2f::default(); 4];
        }
        self.primaries
    }

    /// Whether the two spaces transform colors alike (C++ `operator==`): the
    /// matrices agree within 1e-5 per element, and the gammas and biases
    /// within 1e-3. The names are not compared.
    ///
    /// The comparison is not transitive, which is why it is not
    /// [`PartialEq`].
    pub fn is_equivalent(&self, other: &ColorSpace) -> bool {
        self.rgb_to_xyz
            .iter()
            .zip(&other.rgb_to_xyz)
            .all(|(a, b)| (a - b).abs() <= 1e-5)
            && (self.gamma - other.gamma).abs() <= 1e-3
            && (self.linear_bias - other.linear_bias).abs() <= 1e-3
    }

    /// Convert `rgb` in place from this space to `to` (C++ `ConvertRGBSpan`):
    /// decode by this space's curve, transform, and encode by `to`'s curve.
    pub fn convert_rgb_to(&self, to: &ColorSpace, rgb: &mut [gf::Vec3f]) {
        // TODO(perf): C++ transforms with SSE2 or NEON. Each color is
        // independent, and the slice could split across threads. A linear space
        // (gamma 1, bias 0) could skip its curve, which leaves every value as
        // it is.
        let tx = rgb_to_rgb(self, to);
        for color in rgb {
            *color = self.convert_with(to, &tx, *color);
        }
    }

    /// Convert the color of each `rgba` in place from this space to `to`,
    /// leaving its alpha unchanged (C++ `ConvertRGBASpan`).
    pub fn convert_rgba_to(&self, to: &ColorSpace, rgba: &mut [gf::Vec4f]) {
        // TODO(perf): as in `convert_rgb_to`.
        let tx = rgb_to_rgb(self, to);
        for color in rgba {
            let rgb = self.convert_with(to, &tx, gf::vec3f(color.x, color.y, color.z));
            *color = gf::vec4f(rgb.x, rgb.y, rgb.z, color.w);
        }
    }

    /// Remove the transfer curve from encoded RGB in this space, giving
    /// linear RGB (nanocolor `_ToLinear`).
    pub fn to_linear(&self, rgb: gf::Vec3f) -> gf::Vec3f {
        let linear = |t: f32| {
            if t < self.k0 {
                return t / self.phi;
            }
            let a = self.linear_bias;
            ((t + a) / (1.0 + a)).powf(self.gamma)
        };
        gf::vec3f(linear(rgb.x), linear(rgb.y), linear(rgb.z))
    }

    /// Apply the transfer curve to linear RGB in this space, giving encoded
    /// RGB (nanocolor `_FromLinear`).
    pub fn from_linear(&self, rgb: gf::Vec3f) -> gf::Vec3f {
        let encoded = |t: f32| {
            if t < self.k0 / self.phi {
                return t * self.phi;
            }
            let a = self.linear_bias;
            (1.0 + a) * t.powf(1.0 / self.gamma) - a
        };
        gf::vec3f(encoded(rgb.x), encoded(rgb.y), encoded(rgb.z))
    }

    /// Encoded RGB in this space to CIE XYZ (nanocolor `NcRGBToXYZ`).
    pub fn to_xyz(&self, rgb: gf::Vec3f) -> gf::Vec3f {
        apply(&self.rgb_to_xyz, self.to_linear(rgb))
    }

    /// CIE XYZ to encoded RGB in this space (nanocolor `NcXYZToRGB`).
    pub fn from_xyz(&self, xyz: gf::Vec3f) -> gf::Vec3f {
        // TODO(perf): the inverse is the same for every call; a space could
        // hold it beside `rgb_to_xyz`.
        self.from_linear(apply(&invert(&self.rgb_to_xyz), xyz))
    }

    /// The encoded RGB in this space of a luminance and chromaticity, each
    /// component's magnitude divided by the largest (nanocolor `NcYxyToRGB`).
    ///
    /// Every component comes out non-negative, as in C++. The scaling runs
    /// after the curve. In a linear space the luminance cancels; in an encoded
    /// one it reaches the result only through the curve.
    pub fn from_yxy(&self, luminance: f32, xy: gf::Vec2f) -> gf::Vec3f {
        let rgb = self.from_xyz(yxy_to_xyz(luminance, xy));
        let max = rgb.x.abs().max(rgb.y.abs()).max(rgb.z.abs());
        gf::vec3f(rgb.x.abs() / max, rgb.y.abs() / max, rgb.z.abs() / max)
    }

    /// `rgb` in this space converted to `to`, through the matrix `tx` taking
    /// this space's linear RGB to `to`'s.
    fn convert_with(&self, to: &ColorSpace, tx: &M33, rgb: gf::Vec3f) -> gf::Vec3f {
        to.from_linear(apply(tx, self.to_linear(rgb)))
    }

    /// A space from a nanocolor-layout matrix (C++ `NcCreateColorSpaceM33`),
    /// with the primaries and white point the matrix implies.
    fn from_nc_matrix(name: tf::Token, rgb_to_xyz: M33, gamma: f32, linear_bias: f32) -> Self {
        let (k0, phi) = transfer(gamma, linear_bias);
        let space = Self {
            name,
            primaries: [gf::Vec2f::default(); 4],
            gamma,
            linear_bias,
            k0,
            phi,
            rgb_to_xyz,
        };
        let primaries = [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0], [1.0, 1.0, 1.0]]
            .map(|rgb| xyz_to_yxy(space.to_xyz(rgb.into())).1);
        Self { primaries, ..space }
    }
}

/// The luminance and chromaticity of CIE XYZ (nanocolor `NcXYZToYxy`). XYZ
/// summing to 0 gives a luminance of 0 and the chromaticity `(0, Y)`, as in
/// C++.
pub fn xyz_to_yxy(xyz: gf::Vec3f) -> (f32, gf::Vec2f) {
    let sum = xyz.x + xyz.y + xyz.z;
    if sum == 0.0 {
        return (0.0, gf::vec2f(0.0, xyz.y));
    }
    (xyz.y, gf::vec2f(xyz.x / sum, xyz.y / sum))
}

/// The CIE XYZ of a luminance and chromaticity (nanocolor `NcYxyToXYZ`).
pub fn yxy_to_xyz(luminance: f32, xy: gf::Vec2f) -> gf::Vec3f {
    gf::vec3f(
        luminance * xy.x / xy.y,
        luminance,
        luminance * (1.0 - xy.x - xy.y) / xy.y,
    )
}

/// The tokens of the built-in color spaces (C++ `GfColorSpaceNames`), as AOUSD
/// core spec §14.1.1 lists them.
pub mod color_space_names {
    /// ACEScg, the AP1 primaries with a linear curve.
    pub const LINEAR_AP1: &str = "lin_ap1_scene";
    /// ACES2065-1, the AP0 primaries with a linear curve.
    pub const LINEAR_AP0: &str = "lin_ap0_scene";
    /// Linear Rec.709 (sRGB), the default color space of AOUSD core spec
    /// §14.4.4.
    pub const LINEAR_REC709: &str = "lin_rec709_scene";
    /// Linear P3-D65.
    pub const LINEAR_P3_D65: &str = "lin_p3d65_scene";
    /// Linear Rec.2020.
    pub const LINEAR_REC2020: &str = "lin_rec2020_scene";
    /// Linear Adobe RGB.
    pub const LINEAR_ADOBE_RGB: &str = "lin_adobergb_scene";
    /// CIE XYZ, with values adapted to the D65 white point.
    pub const LINEAR_CIE_XYZ_D65: &str = "lin_ciexyzd65_scene";
    /// sRGB-encoded Rec.709 (sRGB).
    pub const SRGB_REC709: &str = "srgb_rec709_scene";
    /// Gamma 2.2-encoded Rec.709.
    pub const G22_REC709: &str = "g22_rec709_scene";
    /// Gamma 1.8-encoded Rec.709.
    pub const G18_REC709: &str = "g18_rec709_scene";
    /// sRGB-encoded AP1.
    pub const SRGB_AP1: &str = "srgb_ap1_scene";
    /// Gamma 2.2-encoded AP1.
    pub const G22_AP1: &str = "g22_ap1_scene";
    /// sRGB-encoded P3-D65.
    pub const SRGB_P3_D65: &str = "srgb_p3d65_scene";
    /// Gamma 2.2-encoded Adobe RGB.
    pub const G22_ADOBE_RGB: &str = "g22_adobergb_scene";
    /// An identity transform, for backwards compatibility with older assets.
    pub const IDENTITY: &str = "identity";
    /// Values that are not color data, which no conversion changes.
    pub const DATA: &str = "data";
    /// Raw values, the older spelling of [`DATA`].
    pub const RAW: &str = "raw";
    /// A color space that is not known.
    pub const UNKNOWN: &str = "unknown";
    /// The C++ `CIEXYZ` alias of [`LINEAR_CIE_XYZ_D65`].
    pub const CIE_XYZ: &str = LINEAR_CIE_XYZ_D65;
    /// The C++ `LinearDisplayP3` alias of [`LINEAR_P3_D65`].
    pub const LINEAR_DISPLAY_P3: &str = LINEAR_P3_D65;
}

const IDENTITY: M33 = [1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0];

/// One entry of nanocolor's built-in table.
struct Builtin {
    descriptive: &'static str,
    token: &'static str,
    /// Red, green and blue primaries, then the white point; `None` for a space
    /// whose matrix is the identity, as for those holding values no
    /// conversion changes.
    primaries: Option<[[f32; 2]; 4]>,
    /// The curve's gamma and linear bias.
    curve: (f32, f32),
}

const D65: [f32; 2] = [0.3127, 0.329];
/// AP1, pre-adapted to D65 with a Bradford transform.
const AP1: [[f32; 2]; 4] = [
    [0.713_195_86, 0.292_688_9],
    [0.159_508_56, 0.838_788_5],
    [0.128_673, 0.043_895_572],
    D65,
];
/// AP0, pre-adapted to D65.
const AP0: [[f32; 2]; 4] = [
    [0.734_855_23, 0.264_225_33],
    [-0.006_170_912_6, 1.011_315],
    [0.015_967_56, -0.064_235_5],
    D65,
];
const REC709: [[f32; 2]; 4] = [[0.64, 0.33], [0.3, 0.6], [0.15, 0.06], D65];
const P3_D65: [[f32; 2]; 4] = [[0.68, 0.32], [0.265, 0.69], [0.15, 0.06], D65];
const REC2020: [[f32; 2]; 4] = [[0.708, 0.292], [0.17, 0.797], [0.131, 0.046], D65];
const ADOBE_RGB: [[f32; 2]; 4] = [[0.64, 0.33], [0.21, 0.71], [0.15, 0.06], D65];
const CIE_XYZ: [[f32; 2]; 4] = [[1.0, 0.0], [0.0, 1.0], [0.0, 0.0], D65];

const LINEAR: (f32, f32) = (1.0, 0.0);
const SRGB: (f32, f32) = (2.4, 0.055);
const G22: (f32, f32) = (2.2, 0.0);
const G18: (f32, f32) = (1.8, 0.0);

/// Nanocolor's built-in color spaces, in its order.
const BUILTINS: [Builtin; 18] = {
    use color_space_names as names;
    const fn entry(
        descriptive: &'static str,
        token: &'static str,
        primaries: Option<[[f32; 2]; 4]>,
        curve: (f32, f32),
    ) -> Builtin {
        Builtin {
            descriptive,
            token,
            primaries,
            curve,
        }
    }
    [
        entry("ACEScg", names::LINEAR_AP1, Some(AP1), LINEAR),
        entry("ACES2065-1", names::LINEAR_AP0, Some(AP0), LINEAR),
        entry("Linear Rec.709 (sRGB)", names::LINEAR_REC709, Some(REC709), LINEAR),
        entry("Linear P3-D65", names::LINEAR_P3_D65, Some(P3_D65), LINEAR),
        entry("Linear Rec.2020", names::LINEAR_REC2020, Some(REC2020), LINEAR),
        entry("Linear AdobeRGB", names::LINEAR_ADOBE_RGB, Some(ADOBE_RGB), LINEAR),
        entry(
            "CIE XYZ-D65 - Scene-referred",
            names::LINEAR_CIE_XYZ_D65,
            Some(CIE_XYZ),
            LINEAR,
        ),
        entry("sRGB Encoded Rec.709 (sRGB)", names::SRGB_REC709, Some(REC709), SRGB),
        entry("Gamma 2.2 Encoded Rec.709", names::G22_REC709, Some(REC709), G22),
        entry("Gamma 1.8 Encoded Rec.709", names::G18_REC709, Some(REC709), G18),
        entry("sRGB Encoded AP1", names::SRGB_AP1, Some(AP1), SRGB),
        entry("Gamma 2.2 Encoded AP1", names::G22_AP1, Some(AP1), G22),
        entry("sRGB Encoded P3-D65", names::SRGB_P3_D65, Some(P3_D65), SRGB),
        entry("Gamma 2.2 Encoded AdobeRGB", names::G22_ADOBE_RGB, Some(ADOBE_RGB), G22),
        entry("Data", names::DATA, None, LINEAR),
        entry("Identity", names::IDENTITY, None, LINEAR),
        entry("Raw", names::RAW, None, LINEAR),
        entry("Unknown", names::UNKNOWN, None, LINEAR),
    ]
};

/// The spaces of [`BUILTINS`], built once, in the same order.
static BUILTIN_SPACES: LazyLock<[ColorSpace; 18]> = LazyLock::new(|| {
    BUILTINS.each_ref().map(|b| {
        let name = tf::Token::new(b.token);
        let (gamma, linear_bias) = b.curve;
        match b.primaries {
            Some(primaries) => ColorSpace::from_primaries(name, primaries.map(gf::Vec2f::from), gamma, linear_bias),
            None => ColorSpace::from_nc_matrix(name, IDENTITY, gamma, linear_bias),
        }
    })
});

/// The index in [`BUILTINS`] of the space whose token or descriptive name is
/// `name` (C++ `NcGetNamedColorSpace`).
fn builtin(name: &str) -> Option<usize> {
    BUILTINS.iter().position(|b| b.token == name || b.descriptive == name)
}

/// The knee and linear slope of the curve with `gamma` and `bias` (the first
/// half of C++ `_InitColorSpace`).
fn transfer(gamma: f32, bias: f32) -> (f32, f32) {
    if gamma == 1.0 {
        return (1.0e9, 1.0);
    }
    if bias <= 0.0 {
        return (0.0, 1.0);
    }
    let k0 = bias / (gamma - 1.0);
    let phi = (bias / ((gamma * bias / (gamma + gamma * bias - 1.0 - bias)).ln() * gamma).exp()) / (gamma - 1.0);
    (k0, phi)
}

/// The RGB-to-XYZ matrix of the red, green and blue primaries and the white
/// point, by SMPTE RP 177-1993 (the second half of C++ `_InitColorSpace`).
/// Zero when the white point's x is 0.
fn primaries_matrix([red, green, blue, white]: [gf::Vec2f; 4]) -> M33 {
    if white.x == 0.0 {
        return [0.0; 9];
    }
    let z = |c: gf::Vec2f| 1.0 - c.x - c.y;
    // The primaries' xyz, bound as columns.
    let p = [
        red.x,
        green.x,
        blue.x,
        red.y,
        green.y,
        blue.y,
        z(red),
        z(green),
        z(blue),
    ];
    // The white point at a luminance of 1.
    let w = gf::vec3f(white.x / white.y, 1.0, z(white) / white.y);
    // Scale each primary so the three sum to the white point.
    let c = apply(&invert(&p), w);
    let scale = [c.x, c.y, c.z];
    array::from_fn(|i| p[i] * scale[i % 3])
}

/// The matrix taking linear RGB in `src` to linear RGB in `dst` (C++
/// `NcGetRGBToRGBMatrix`).
fn rgb_to_rgb(src: &ColorSpace, dst: &ColorSpace) -> M33 {
    multiply(&invert(&dst.rgb_to_xyz), &src.rgb_to_xyz)
}

/// The inverse of `m` (C++ `_M3ffInvert`), with the reciprocal of the
/// determinant taken in double precision as C does.
fn invert(m: &M33) -> M33 {
    // C++ indexes the transpose; the result is the inverse either way.
    let [m0, m3, m6, m1, m4, m7, m2, m5, m8] = *m;
    let det = m0 * (m4 * m8 - m5 * m7) - m1 * (m3 * m8 - m5 * m6) + m2 * (m3 * m7 - m4 * m6);
    let inv_det = (1.0 / f64::from(det)) as f32;
    let t = [
        (m4 * m8 - m5 * m7) * inv_det,
        (m2 * m7 - m1 * m8) * inv_det,
        (m1 * m5 - m2 * m4) * inv_det,
        (m5 * m6 - m3 * m8) * inv_det,
        (m0 * m8 - m2 * m6) * inv_det,
        (m2 * m3 - m0 * m5) * inv_det,
        (m3 * m7 - m4 * m6) * inv_det,
        (m1 * m6 - m0 * m7) * inv_det,
        (m0 * m4 - m1 * m3) * inv_det,
    ];
    [t[0], t[3], t[6], t[1], t[4], t[7], t[2], t[5], t[8]]
}

/// The product `lh · rh` (C++ `_M33fMultiply`).
fn multiply(lh: &M33, rh: &M33) -> M33 {
    array::from_fn(|i| {
        let (row, col) = (i / 3, i % 3);
        lh[row * 3] * rh[col] + lh[row * 3 + 1] * rh[3 + col] + lh[row * 3 + 2] * rh[6 + col]
    })
}

/// `m · v`, with `v` a column vector.
fn apply(m: &M33, v: gf::Vec3f) -> gf::Vec3f {
    gf::vec3f(
        m[0] * v.x + m[1] * v.y + m[2] * v.z,
        m[3] * v.x + m[4] * v.y + m[5] * v.z,
        m[6] * v.x + m[7] * v.y + m[8] * v.z,
    )
}

/// A nanocolor-layout matrix in the [`gf`](crate::gf) row-vector convention.
fn to_mat3d(m: M33) -> gf::Mat3d {
    gf::Mat3d(m.map(f64::from)).transpose()
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL: [&str; 20] = [
        color_space_names::LINEAR_AP1,
        color_space_names::LINEAR_AP0,
        color_space_names::LINEAR_REC709,
        color_space_names::LINEAR_P3_D65,
        color_space_names::LINEAR_REC2020,
        color_space_names::LINEAR_ADOBE_RGB,
        color_space_names::LINEAR_CIE_XYZ_D65,
        color_space_names::SRGB_REC709,
        color_space_names::G22_REC709,
        color_space_names::G18_REC709,
        color_space_names::SRGB_AP1,
        color_space_names::G22_AP1,
        color_space_names::SRGB_P3_D65,
        color_space_names::G22_ADOBE_RGB,
        color_space_names::IDENTITY,
        color_space_names::DATA,
        color_space_names::RAW,
        color_space_names::UNKNOWN,
        color_space_names::CIE_XYZ,
        color_space_names::LINEAR_DISPLAY_P3,
    ];

    /// The Rec.709 RGB-to-XYZ matrix, in the row-vector convention.
    const REC709_RGB_TO_XYZ: [[f64; 3]; 3] = [
        [0.4124, 0.2126, 0.0193],
        [0.3576, 0.7152, 0.1192],
        [0.1805, 0.0722, 0.9505],
    ];

    /// `rgb` in `src`, converted to `dst`.
    fn convert(rgb: [f32; 3], src: &str, dst: &str) -> gf::Vec3f {
        let mut colors = [gf::Vec3f::from(rgb)];
        ColorSpace::new(src).convert_rgb_to(&ColorSpace::new(dst), &mut colors);
        colors[0]
    }

    /// `testGfColorCpp.cpp`: every name is valid, by token or description.
    #[test]
    fn names_valid() {
        for name in ALL {
            assert!(ColorSpace::is_valid(name), "{name}");
            assert_eq!(ColorSpace::new(name).name(), name);
        }
        assert!(!ColorSpace::is_valid("custom"));
        assert!(!ColorSpace::is_valid(""));
        assert!(!ColorSpace::is_valid("acescg"), "names compare exactly");
        assert!(!ColorSpace::is_valid("g24_rec709_scene"), "not in nanocolor's table");
        let by_description = ColorSpace::new("ACEScg");
        assert_eq!(by_description.name(), color_space_names::LINEAR_AP1);
        assert_eq!(by_description, ColorSpace::new(color_space_names::LINEAR_AP1));
    }

    /// A name that is not built in is an identity sentinel under that name.
    #[test]
    fn unknown_name_identity() {
        let sentinel = ColorSpace::new("custom");
        assert_eq!(sentinel.name(), "custom");
        assert_eq!(sentinel.rgb_to_xyz(), gf::Mat3d::IDENTITY);
        assert!(sentinel.is_equivalent(&ColorSpace::new(color_space_names::DATA)));
        assert!(!sentinel.is_equivalent(&ColorSpace::new(color_space_names::LINEAR_REC709)));
        assert_ne!(sentinel, ColorSpace::new(color_space_names::DATA));
        // The identity built-ins derive the unit primaries and an equal-energy
        // white from their matrix.
        let third = 1.0 / 3.0;
        assert_eq!(
            ColorSpace::new(color_space_names::DATA).primaries_and_white_point(),
            [
                gf::vec2f(1.0, 0.0),
                gf::vec2f(0.0, 1.0),
                gf::vec2f(0.0, 0.0),
                gf::vec2f(third, third)
            ]
        );
    }

    /// `testGfColorCpp.cpp:testColorSpace`.
    #[test]
    fn custom_getters() {
        let primaries = [
            gf::vec2f(0.64, 0.33),
            gf::vec2f(0.3, 0.6),
            gf::vec2f(0.15, 0.06),
            gf::vec2f(0.3127, 0.329),
        ];
        let custom = ColorSpace::from_primaries("custom_getter_test", primaries, 2.2, 0.05);
        assert_eq!(custom.name(), "custom_getter_test");
        assert_eq!(custom.primaries_and_white_point(), primaries);
        assert_eq!(custom.gamma(), 2.2);
        assert_eq!(custom.linear_bias(), 0.05);
        assert_ne!(custom.transfer_params(), (0.0, 0.0));

        // The Rec.709 matrix, in the row-vector convention.
        let m = gf::Mat3d::from(REC709_RGB_TO_XYZ);
        let matrix = ColorSpace::from_matrix("matrix_space", m, 2.2, 0.05);
        assert_eq!(matrix.name(), "matrix_space");
        assert!(matrix.rgb_to_xyz().is_close(m, 1e-5));
        assert!((matrix.gamma() - 2.2).abs() <= 1e-6);
        assert!((matrix.linear_bias() - 0.05).abs() <= 1e-6);
    }

    /// A matrix-built space with a curve has a linear segment, which C++ drops.
    #[test]
    fn matrix_transfer_params() {
        let srgb = ColorSpace::new(color_space_names::SRGB_REC709);
        let matrix = ColorSpace::from_matrix("srgb_by_matrix", srgb.rgb_to_xyz(), 2.4, 0.055);
        assert_eq!(matrix.transfer_params(), srgb.transfer_params());
        let (k0, phi) = srgb.transfer_params();
        assert!((k0 - 0.039_285_715).abs() <= 1e-6);
        assert!((phi - 12.92).abs() <= 1e-2);
        assert!(matrix.is_equivalent(&srgb));
        // The derived primaries are the matrix's, unshifted by the bias.
        let expected = srgb.primaries_and_white_point();
        for (got, want) in matrix.primaries_and_white_point().into_iter().zip(expected) {
            assert!(got.is_close(want, 1e-4), "{got:?} {want:?}");
        }
        // Below the knee, both decode along the linear segment.
        let rec709 = ColorSpace::new(color_space_names::LINEAR_REC709);
        let mut by_matrix = [gf::vec3f(0.01, 0.5, 1.0)];
        matrix.convert_rgb_to(&rec709, &mut by_matrix);
        let builtin = convert(
            [0.01, 0.5, 1.0],
            color_space_names::SRGB_REC709,
            color_space_names::LINEAR_REC709,
        );
        assert!(by_matrix[0].is_close(builtin, 1e-5), "{:?} {builtin:?}", by_matrix[0]);
        assert!((builtin.x - 0.01 / 12.92).abs() <= 1e-6);
    }

    /// A negative value in an identity space converts as itself, where C++
    /// divides by a zero slope.
    #[test]
    fn identity_negative_values() {
        let out = convert([-0.25, 0.5, 2.0], color_space_names::DATA, color_space_names::IDENTITY);
        assert_eq!(out, gf::vec3f(-0.25, 0.5, 2.0));
    }

    /// A nonsymmetric row-vector matrix round-trips, and converting to an
    /// identity destination multiplies by it.
    #[test]
    fn matrix_row_convention() {
        let m = gf::Mat3d::from(REC709_RGB_TO_XYZ);
        let space = ColorSpace::from_matrix("rec709_by_matrix", m, 1.0, 0.0);
        assert!(space.rgb_to_xyz().is_close(m, 1e-6));
        let identity = ColorSpace::from_matrix("xyz", gf::Mat3d::IDENTITY, 1.0, 0.0);
        let rgb = gf::vec3f(0.5, 0.25, 0.125);
        let mut colors = [rgb];
        space.convert_rgb_to(&identity, &mut colors);
        let row = [0.5, 0.25, 0.125];
        let expected: [f32; 3] = array::from_fn(|c| (0..3).map(|r| row[r] * m[(r, c)]).sum::<f64>() as f32);
        assert!(colors[0].is_close(expected.into(), 1e-6), "{:?}", colors[0]);
        // `lin_ciexyzd65_scene` is not the identity: its white is D65.
        let xyz = ColorSpace::new(color_space_names::LINEAR_CIE_XYZ_D65).rgb_to_xyz();
        assert!((xyz[(0, 0)] - 0.950_456).abs() <= 1e-4);
        assert!((xyz[(2, 2)] - 1.089_058).abs() <= 1e-4);
    }

    /// `testGfColorCpp.cpp:testSpanConversions`: the identity spaces and two
    /// regular ones round-trip a span, RGB and RGBA, keeping alpha.
    #[test]
    fn span_round_trip() {
        let special = [
            color_space_names::IDENTITY,
            color_space_names::DATA,
            color_space_names::RAW,
            color_space_names::UNKNOWN,
        ];
        let regular = [color_space_names::LINEAR_REC709, color_space_names::G22_AP1];
        let value = |i: usize| (i % 256) as f32 / 255.0;
        for special in special.map(ColorSpace::new) {
            for regular in regular.map(ColorSpace::new) {
                let original: Vec<gf::Vec3f> = (0..37)
                    .map(|i| gf::vec3f(value(3 * i), value(3 * i + 1), value(3 * i + 2)))
                    .collect();
                let mut rgb = original.clone();
                regular.convert_rgb_to(&special, &mut rgb);
                special.convert_rgb_to(&regular, &mut rgb);
                for (got, want) in rgb.iter().zip(&original) {
                    assert!(got.is_close(*want, 1e-5), "{got:?} {want:?}");
                }

                let original: Vec<gf::Vec4f> = (0..37)
                    .map(|i| gf::vec4f(value(4 * i), value(4 * i + 1), value(4 * i + 2), value(4 * i + 3)))
                    .collect();
                let mut rgba = original.clone();
                regular.convert_rgba_to(&special, &mut rgba);
                special.convert_rgba_to(&regular, &mut rgba);
                for (got, want) in rgba.iter().zip(&original) {
                    assert_eq!(got.w, want.w);
                    assert!(gf::vec3f(got.x, got.y, got.z).is_close(gf::vec3f(want.x, want.y, want.z), 1e-5));
                }
            }
        }
    }

    /// `testGfColorCpp.cpp:testKnownColorSpanConversion`.
    #[test]
    fn known_span_conversion() {
        let rec709 = ColorSpace::new(color_space_names::LINEAR_REC709);
        let ap0 = ColorSpace::new(color_space_names::LINEAR_AP0);
        let srgb_p3 = ColorSpace::new(color_space_names::SRGB_P3_D65);
        let linear = gf::vec3f(0.5, 0.25, 0.125);
        let mut colors = vec![linear; 47];
        rec709.convert_rgb_to(&ap0, &mut colors);
        assert!(
            colors
                .iter()
                .all(|c| c.is_close(gf::vec3f(0.337_736, 0.260_346, 0.145_521), 1e-5))
        );
        ap0.convert_rgb_to(&srgb_p3, &mut colors);
        assert!(
            colors
                .iter()
                .all(|c| c.is_close(gf::vec3f(0.705_302_9, 0.545_21, 0.410_651), 1e-4))
        );
        srgb_p3.convert_rgb_to(&rec709, &mut colors);
        assert!(colors.iter().all(|c| c.is_close(linear, 1e-5)));
    }

    /// `testGfColorCpp.cpp:testKnownColors`: one color in five spaces, each
    /// converted to linear Rec.709, sRGB and gamma 2.2 Rec.709.
    #[test]
    fn known_colors() {
        let linear = [0.5, 0.25, 0.125];
        let g22 = [0.729_74, 0.532_521, 0.388_602];
        let srgb = [0.735_357, 0.537_099, 0.388_573];
        let ap0 = [0.337_736, 0.260_346, 0.145_521];
        let srgb_p3 = [0.705_302_9, 0.545_21, 0.410_651];
        let to_ap0 = convert(linear, color_space_names::LINEAR_REC709, color_space_names::LINEAR_AP0);
        assert!(to_ap0.is_close(ap0.into(), 1e-5));
        let known = [
            (g22, color_space_names::G22_REC709, 1e-5),
            (srgb, color_space_names::SRGB_REC709, 1e-5),
            (ap0, color_space_names::LINEAR_AP0, 1e-5),
            (srgb_p3, color_space_names::SRGB_P3_D65, 1e-3),
        ];
        for (rgb, space, tolerance) in known {
            let as_linear = convert(rgb, space, color_space_names::LINEAR_REC709);
            assert!(as_linear.is_close(linear.into(), tolerance), "{space}: {as_linear:?}");
            let back = convert(
                as_linear.into(),
                color_space_names::LINEAR_REC709,
                color_space_names::G22_REC709,
            );
            assert!(back.is_close(g22.into(), tolerance), "{space}: {back:?}");
            let tolerance = if space == color_space_names::SRGB_P3_D65 {
                1e-4
            } else {
                1e-5
            };
            let as_srgb = convert(rgb, space, color_space_names::SRGB_REC709);
            assert!(as_srgb.is_close(srgb.into(), tolerance), "{space}: {as_srgb:?}");
            let back = convert(
                as_srgb.into(),
                color_space_names::SRGB_REC709,
                color_space_names::G22_REC709,
            );
            assert!(back.is_close(g22.into(), tolerance), "{space}: {back:?}");
        }
    }

    /// The curve, XYZ and Yxy helpers invert each other.
    #[test]
    fn helpers_round_trip() {
        let srgb = ColorSpace::new(color_space_names::SRGB_REC709);
        let rgb = gf::vec3f(0.02, 0.5, 0.9);
        assert!(srgb.from_linear(srgb.to_linear(rgb)).is_close(rgb, 1e-6));
        assert!((srgb.to_linear(rgb).x - 0.02 / 12.92).abs() <= 1e-6);
        let xyz = srgb.to_xyz(rgb);
        assert!(srgb.from_xyz(xyz).is_close(rgb, 1e-5));
        let (luminance, xy) = xyz_to_yxy(xyz);
        assert_eq!(luminance, xyz.y);
        assert!(yxy_to_xyz(luminance, xy).is_close(xyz, 1e-6));
        assert_eq!(xyz_to_yxy(gf::Vec3f::default()), (0.0, gf::vec2f(0.0, 0.0)));
    }

    /// `testGfColorCpp.cpp:testLinRec709ToAP0Matrix`, in the row-vector
    /// convention.
    #[test]
    fn rec709_to_ap0_matrix() {
        let rec709 = ColorSpace::new(color_space_names::LINEAR_REC709);
        let ap0 = ColorSpace::new(color_space_names::LINEAR_AP0);
        let expected = gf::Mat3d::from([
            [0.439_632_98, 0.382_988_7, 0.177_378_32],
            [0.089_776_44, 0.813_439_43, 0.096_784_13],
            [0.017_541_17, 0.111_546_55, 0.870_912_28],
        ])
        .transpose();
        assert!(ap0.rgb_to_rgb(&rec709).is_close(expected, 1e-5));
        let composed = rec709.rgb_to_xyz() * ap0.rgb_to_xyz().inverse_or_max();
        assert!(composed.is_close(expected, 1e-5));
    }
}
