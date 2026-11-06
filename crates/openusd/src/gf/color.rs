//! A color in a color space (C++ `GfColor`).

use std::{fmt, slice};

use crate::{gf, vt};

/// An RGB triple and the [`ColorSpace`](gf::ColorSpace) it is in (C++
/// `GfColor`).
///
/// The default is black in Linear Rec.709, the default color space of AOUSD
/// core spec §14.4.4.
///
/// Equality compares the triple and the color space exactly, the space's
/// name included. C++ `operator==` compares the spaces as
/// [`ColorSpace::is_equivalent`](gf::ColorSpace::is_equivalent) does.
#[derive(Debug, Clone, PartialEq)]
pub struct Color {
    rgb: gf::Vec3f,
    space: gf::ColorSpace,
}

impl Default for Color {
    fn default() -> Self {
        Self::black(gf::ColorSpace::new(gf::color_space_names::LINEAR_REC709))
    }
}

impl Color {
    /// `rgb`, in `space`.
    pub fn new(rgb: impl Into<gf::Vec3f>, space: gf::ColorSpace) -> Self {
        Self { rgb: rgb.into(), space }
    }

    /// Black, in `space`.
    pub fn black(space: gf::ColorSpace) -> Self {
        Self::new(gf::Vec3f::default(), space)
    }

    /// The color converted to `space` (the C++ `GfColor` constructor from a
    /// color and a color space).
    pub fn to_space(&self, space: gf::ColorSpace) -> Self {
        let mut rgb = self.rgb;
        self.space.convert_rgb_to(&space, slice::from_mut(&mut rgb));
        Self { rgb, space }
    }

    /// Set the color to that of a blackbody at `kelvin`, in the color's space
    /// (C++ `SetFromPlanckianLocus`).
    ///
    /// The chromaticity is Krystek's 1985 rational approximation of the
    /// Planckian locus, defined from 1000 K to 15000 K; a temperature outside
    /// that range is clamped to it. Rec.709 cannot represent a temperature
    /// below about 1900 K.
    ///
    /// As in C++, the result is scaled so its largest component's magnitude is
    /// 1, and every component comes out non-negative, including those of a
    /// temperature outside the space's gamut. The scaling follows the
    /// transfer curve. In a linear space `luminance` has no effect; in an
    /// encoded one it changes the result only through the curve.
    pub fn set_from_planckian_locus(&mut self, kelvin: f32, luminance: f32) {
        self.rgb = self.space.from_yxy(luminance, planckian_xy(kelvin));
    }

    /// The CIE xy chromaticity of the color.
    pub fn chromaticity(&self) -> gf::Vec2f {
        gf::xyz_to_yxy(self.space.to_xyz(self.rgb)).1
    }

    /// Set the color to the chromaticity `xy` at a luminance of 1, scaled as
    /// [`ColorSpace::from_yxy`](gf::ColorSpace::from_yxy) scales it.
    pub fn set_from_chromaticity(&mut self, xy: gf::Vec2f) {
        self.rgb = self.space.from_yxy(1.0, xy);
    }

    /// The RGB triple, in [`color_space`](Self::color_space).
    pub fn rgb(&self) -> gf::Vec3f {
        self.rgb
    }

    /// The color space the RGB triple is in.
    pub fn color_space(&self) -> &gf::ColorSpace {
        &self.space
    }

    /// Whether the RGB triples lie within `tolerance` of each other, by the
    /// length of their difference (C++ `GfIsClose`). The color spaces are not
    /// compared.
    pub fn is_close(&self, other: &Color, tolerance: f32) -> bool {
        self.rgb.is_close(other.rgb, tolerance)
    }
}

/// `(r, g, b, name)`, as C++ prints a `GfColor`.
impl fmt::Display for Color {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = String::new();
        let rgb = [self.rgb.x, self.rgb.y, self.rgb.z];
        vt::stream_out::separated(&mut text, ["(", ", "], &rgb, vt::stream_out::float);
        write!(f, "{text}{})", self.space.name())
    }
}

/// The CIE xy chromaticity of a blackbody at `kelvin`, clamped to
/// 1000–15000 K (nanocolor `NcKelvinToYxy`, after M. Krystek, "An algorithm
/// to calculate correlated colour temperature", 1985). The rational
/// polynomials evaluate in double precision, as C does.
pub fn planckian_xy(kelvin: f32) -> gf::Vec2f {
    let t = f64::from(kelvin.clamp(1000.0, 15000.0));
    let u = ((0.860_117_757 + 1.541_182_54e-4 * t + 1.286_412_1e-7 * t * t)
        / (1.0 + 8.424_202_35e-4 * t + 7.081_451_63e-7 * t * t)) as f32;
    let v = ((0.317_398_726 + 4.228_062_45e-5 * t + 4.204_816_91e-8 * t * t)
        / (1.0 - 2.897_418_16e-5 * t + 1.614_560_53e-7 * t * t)) as f32;
    // From CIE 1960 (u, v) through (u', v'), where v' = 1.5 v.
    let v_prime = 3.0 * v / 2.0;
    let d = 6.0 * u - 16.0 * v_prime + 12.0;
    gf::vec2f(9.0 * u / d, 4.0 * v_prime / d)
}

#[cfg(test)]
mod tests {
    use super::*;
    use gf::{ColorSpace, color_space_names as names};

    /// Unit red, green and blue.
    const UNITS: [[f32; 3]; 3] = [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]];

    fn mauve_linear() -> Color {
        Color::new([0.5, 0.25, 0.125], ColorSpace::new(names::LINEAR_REC709))
    }

    /// Whether `p` lies in the triangle `v0`, `v1`, `v2`, by barycentric
    /// coordinates.
    fn in_triangle(p: gf::Vec2f, [v0, v1, v2]: [gf::Vec2f; 3]) -> bool {
        let (e1, e2, ep) = (v1 - v0, v2 - v0, p - v0);
        let (d00, d01, d02, d11, d12) = (e1.dot(e1), e1.dot(e2), e1.dot(ep), e2.dot(e2), e2.dot(ep));
        let inv = 1.0 / (d00 * d11 - d01 * d01);
        let u = (d11 * d02 - d01 * d12) * inv;
        let v = (d00 * d12 - d01 * d02) * inv;
        u >= 0.0 && v >= 0.0 && u + v <= 1.0
    }

    /// `testGfColorCpp.cpp` and `testGfColorPy.py`: construction.
    #[test]
    fn construction() {
        let c = Color::default();
        assert_eq!(c.color_space(), &ColorSpace::new(names::LINEAR_REC709));
        assert_eq!(c.rgb(), gf::Vec3f::default());
        let c = Color::black(ColorSpace::new(names::SRGB_REC709));
        assert_eq!(c.color_space(), &ColorSpace::new(names::SRGB_REC709));
        assert_eq!(c.rgb(), gf::Vec3f::default());
        let c = Color::new([0.5, 0.5, 0.5], ColorSpace::new(names::SRGB_REC709));
        assert_eq!(c.rgb(), gf::vec3f(0.5, 0.5, 0.5));
        assert_eq!(c.clone(), c);
        assert_eq!(c.to_string(), "(0.5, 0.5, 0.5, srgb_rec709_scene)");
        assert_eq!(Color::default().to_string(), "(0, 0, 0, lin_rec709_scene)");
        let extreme = Color::new([1e-7, 1e20, 0.5], ColorSpace::new(names::RAW));
        assert_eq!(extreme.to_string(), "(1e-7, 1e20, 0.5, raw)");
    }

    /// `testGfColorCpp.cpp`: the sRGB curve and Rec.2020 round-trip.
    #[test]
    fn round_trips() {
        let mauve = mauve_linear();
        let srgb = mauve.to_space(ColorSpace::new(names::SRGB_REC709));
        let linear = srgb.to_space(ColorSpace::new(names::LINEAR_REC709));
        assert!(mauve.is_close(&linear, 1e-6));
        assert!(srgb.is_close(&linear.to_space(ColorSpace::new(names::SRGB_REC709)), 1e-7));
        let rec2020 = mauve.to_space(ColorSpace::new(names::LINEAR_REC2020));
        assert!(mauve.is_close(&rec2020.to_space(ColorSpace::new(names::LINEAR_REC709)), 1e-5));
    }

    /// `testGfColorCpp.cpp`: chromaticity is kept by a curve, and nearly kept
    /// through a white point change.
    #[test]
    fn chromaticity_kept() {
        let mauve = mauve_linear();
        let gamma = mauve.to_space(ColorSpace::new(names::G22_REC709));
        let baseline = mauve.chromaticity();
        assert!(baseline.is_close(gamma.chromaticity(), 1e-5));
        let srgb = mauve.to_space(ColorSpace::new(names::SRGB_REC709));
        let ap0 = srgb.to_space(ColorSpace::new(names::LINEAR_AP0));
        let srgb_p3 = ap0.to_space(ColorSpace::new(names::SRGB_P3_D65));
        let srgb_2 = ap0.to_space(ColorSpace::new(names::SRGB_REC709));
        let srgb_3 = srgb_p3.to_space(ColorSpace::new(names::SRGB_REC709));
        assert!(baseline.is_close(srgb.chromaticity(), 1e-5));
        assert!(srgb_2.chromaticity().is_close(srgb_3.chromaticity(), 2e-2));
        assert!(baseline.is_close(srgb_2.chromaticity(), 5e-2));
        assert!(baseline.is_close(srgb_3.chromaticity(), 2e-2));
    }

    /// `testGfColorCpp.cpp`: conversion through several spaces and back, with
    /// each step keeping its space.
    #[test]
    fn conversion_chain() {
        let mauve = mauve_linear();
        let g22 = mauve.to_space(ColorSpace::new(names::G22_REC709));
        assert_eq!(g22.color_space(), &ColorSpace::new(names::G22_REC709));
        let linear = g22.to_space(ColorSpace::new(names::LINEAR_REC709));
        assert!(linear.is_close(&mauve, 1e-5));
        let srgb = linear.to_space(ColorSpace::new(names::SRGB_REC709));
        assert!(g22.chromaticity().is_close(srgb.chromaticity(), 1e-5));
        let back = srgb
            .to_space(ColorSpace::new(names::LINEAR_AP0))
            .to_space(ColorSpace::new(names::SRGB_REC709))
            .to_space(ColorSpace::new(names::SRGB_P3_D65))
            .to_space(ColorSpace::new(names::LINEAR_REC709));
        assert!(back.is_close(&linear, 1e-5));
    }

    /// `testGfColorCpp.cpp`: distinct spaces differ.
    #[test]
    fn spaces_differ() {
        let srgb = ColorSpace::new(names::SRGB_REC709);
        for other in [
            names::LINEAR_REC709,
            names::G22_REC709,
            names::LINEAR_AP0,
            names::SRGB_P3_D65,
            names::LINEAR_REC2020,
        ] {
            assert_ne!(srgb, ColorSpace::new(other));
            assert!(!srgb.is_equivalent(&ColorSpace::new(other)), "{other}");
        }
    }

    /// `testGfColorCpp.cpp`: 6504 K is near D65.
    #[test]
    fn kelvin_near_d65() {
        let white = Color::new([1.0, 1.0, 1.0], ColorSpace::new(names::LINEAR_REC709));
        let mut c = Color::default();
        c.set_from_planckian_locus(6504.0, 1.0);
        assert!(c.chromaticity().is_close(white.chromaticity(), 1e-2));
    }

    /// `testGfColorCpp.cpp`: a space's primaries are its unit vectors.
    #[test]
    fn primaries_unit_vectors() {
        let rec2020 = [[0.708, 0.292], [0.17, 0.797], [0.131, 0.046]];
        let rec709 = [[0.64, 0.33], [0.3, 0.6], [0.15, 0.06]];
        for (name, primaries) in [(names::LINEAR_REC2020, rec2020), (names::LINEAR_REC709, rec709)] {
            for (xy, unit) in primaries.into_iter().zip(UNITS) {
                let mut c = Color::black(ColorSpace::new(name));
                c.set_from_chromaticity(xy.into());
                assert!(
                    c.is_close(&Color::new(unit, ColorSpace::new(name)), 1e-5),
                    "{name}: {c}"
                );
            }
        }
    }

    /// `testGfColorCpp.cpp`: the Rec.709 primaries lie in the Rec.2020 and AP0
    /// gamuts.
    #[test]
    fn rec709_in_gamut() {
        let gamut = |name: &str| UNITS.map(|unit| Color::new(unit, ColorSpace::new(name)).chromaticity());
        for wider in [names::LINEAR_REC2020, names::LINEAR_AP0] {
            for primary in gamut(names::LINEAR_REC709) {
                assert!(in_triangle(primary, gamut(wider)), "{wider}: {primary:?}");
            }
        }
    }

    /// `testGfColorCpp.cpp:testPlanckianLocus`: the locus against known
    /// chromaticities from 1000 K to 15000 K, and clamping outside it.
    #[test]
    fn planckian_locus() {
        let known = [
            [0.653_087_7, 0.344_681_1],
            [0.526_649_3, 0.413_311_7],
            [0.437_049_3, 0.404_375_3],
            [0.380_411_1, 0.376_599_3],
            [0.345_040_7, 0.351_299_2],
            [0.322_066_2, 0.331_556_1],
            [0.306_403_1, 0.316_500_2],
            [0.295_240_5, 0.304_904_3],
            [0.286_979_2, 0.295_808_2],
            [0.280_669_4, 0.288_533_5],
            [0.275_721_4, 0.282_609_3],
            [0.271_754_5, 0.277_706],
            [0.268_513_8, 0.273_589_2],
            [0.265_823_6, 0.270_088_8],
            [0.263_559_1, 0.267_079_3],
        ];
        for (i, xy) in known.into_iter().enumerate() {
            let mut c = Color::black(ColorSpace::new(names::DATA));
            c.set_from_planckian_locus(1000.0 * (i + 1) as f32, 1.0);
            assert!(
                c.chromaticity().is_close(xy.into(), 1e-3),
                "{} K: {:?}",
                1000 * (i + 1),
                c.chromaticity()
            );
        }
        for kelvin in [999.0, 15001.0] {
            let mut c = Color::default();
            c.set_from_planckian_locus(kelvin, 1.0);
            let gf::Vec3f { x, y, z } = c.rgb();
            assert!(x.is_finite() && y.is_finite() && z.is_finite(), "{kelvin} K: {c}");
        }
        let (mut low, mut floor) = (Color::default(), Color::default());
        low.set_from_planckian_locus(500.0, 1.0);
        floor.set_from_planckian_locus(1000.0, 1.0);
        assert_eq!(low, floor);
    }

    /// The luminance cancels in a linear space, and the components of an
    /// out-of-gamut temperature come out non-negative, as in C++.
    #[test]
    fn planckian_scaling() {
        let (mut dim, mut bright) = (Color::default(), Color::default());
        dim.set_from_planckian_locus(1200.0, 0.25);
        bright.set_from_planckian_locus(1200.0, 4.0);
        assert!(dim.is_close(&bright, 1e-6));
        let gf::Vec3f { x, y, z } = dim.rgb();
        assert!(x >= 0.0 && y >= 0.0 && z >= 0.0, "{dim}");
        assert_eq!(x.max(y).max(z), 1.0);
    }
}
