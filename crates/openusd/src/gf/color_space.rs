//! The color spaces C++ `GfColorSpace` knows by name.

/// The color spaces C++ `GfColorSpace` constructs by name, each as its
/// short name (C++ `GfColorSpaceNames`) and its descriptive name: the
/// table of Nanocolor, the library `GfColorSpace` wraps.
// TODO: `GfColorSpace` itself — each space's primaries, white point and
// transfer function, and conversion between spaces — with a color space
// a `ColorSpaceDefinitionAPI` defines built from its attributes.
const NAMED: [(&str, &str); 19] = [
    ("lin_ap1_scene", "ACEScg"),
    ("lin_ap0_scene", "ACES2065-1"),
    ("lin_rec709_scene", "Linear Rec.709 (sRGB)"),
    ("lin_p3d65_scene", "Linear P3-D65"),
    ("lin_rec2020_scene", "Linear Rec.2020"),
    ("lin_adobergb_scene", "Linear AdobeRGB"),
    ("lin_ciexyzd65_scene", "CIE XYZ-D65 - Scene-referred"),
    ("srgb_rec709_scene", "sRGB Encoded Rec.709 (sRGB)"),
    ("g24_rec709_scene", "Gamma 2.4 Encoded Rec.709"),
    ("g22_rec709_scene", "Gamma 2.2 Encoded Rec.709"),
    ("g18_rec709_scene", "Gamma 1.8 Encoded Rec.709"),
    ("srgb_ap1_scene", "sRGB Encoded AP1"),
    ("g22_ap1_scene", "Gamma 2.2 Encoded AP1"),
    ("srgb_p3d65_scene", "sRGB Encoded P3-D65"),
    ("g22_adobergb_scene", "Gamma 2.2 Encoded AdobeRGB"),
    ("data", "Data"),
    ("identity", "Identity"),
    ("raw", "Raw"),
    ("unknown", "Unknown"),
];

/// Whether `name` is a color space C++ `GfColorSpace` knows, by its short
/// or its descriptive name (C++ `GfColorSpace::IsValid`).
pub fn is_valid_color_space(name: &str) -> bool {
    NAMED
        .iter()
        .any(|(short, descriptive)| name == *short || name == *descriptive)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn named_spaces() {
        assert!(is_valid_color_space("lin_rec709_scene"));
        assert!(is_valid_color_space("ACEScg"));
        assert!(is_valid_color_space("raw"));
        assert!(!is_valid_color_space("custom"));
        assert!(!is_valid_color_space(""));
        assert!(!is_valid_color_space("acescg"), "names compare exactly");
    }
}
