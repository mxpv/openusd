//! Units of measurement (C++ `SdfLengthUnit`, `SdfAngularUnit`,
//! `SdfDimensionlessUnit`).
//!
//! C++ splits the categories across three C enums reached through `TfEnum`.
//! The thirteen names are unique, so one enum carries them all here and
//! [`Unit::category`] says which quantity a unit measures.
//!
//! An authored `displayUnit` is stored as the token naming the unit rather
//! than as a [`Unit`], which is a difference visible through the public `sdf`
//! API: reading the field back gives `Value::Token("mm")` where C++ gives a
//! `TfEnum`. The token is what both file formats carry — the crate format has
//! no entry for an enum at all — so it is what a layer holds, and
//! [`AttributeSpec::display_unit`](super::AttributeSpec::display_unit) is
//! where it becomes a `Unit`.

use std::fmt;

use strum::VariantArray;

/// A unit a value can be expressed in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, VariantArray)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum Unit {
    Millimeter,
    Centimeter,
    Decimeter,
    Meter,
    Kilometer,
    Inch,
    Foot,
    Yard,
    Mile,
    Degrees,
    Radians,
    Percent,
    /// The dimensionless unit of a quantity that is just a number, and the
    /// unit of every type that measures nothing.
    Default,
}

/// The quantity a [`Unit`] measures. Two units convert into one another only
/// within a category.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum UnitCategory {
    Length,
    Angular,
    Dimensionless,
}

impl Unit {
    /// The name this unit is written as: `mm`, `deg`, `%`, `default`.
    pub const fn name(self) -> &'static str {
        self.row().1
    }

    /// The quantity this unit measures.
    pub const fn category(self) -> UnitCategory {
        self.row().0
    }

    /// This unit's size measured in its category's default unit, so a
    /// centimetre is `0.01` and a mile is `1609.344`. Converting between two
    /// units of one category is the ratio of their scales.
    pub const fn scale(self) -> f64 {
        self.row().2
    }

    /// The unit `name` writes, or `None` for a name no category uses
    /// (C++ `SdfGetUnitFromName`).
    pub fn from_name(name: &str) -> Option<Self> {
        Unit::VARIANTS.iter().copied().find(|unit| unit.name() == name)
    }

    /// The category, name and scale of one unit, which is how C++ tabulates
    /// them too (`_SDF_UNITS`).
    const fn row(self) -> (UnitCategory, &'static str, f64) {
        match self {
            Unit::Millimeter => (UnitCategory::Length, "mm", 0.001),
            Unit::Centimeter => (UnitCategory::Length, "cm", 0.01),
            Unit::Decimeter => (UnitCategory::Length, "dm", 0.1),
            Unit::Meter => (UnitCategory::Length, "m", 1.0),
            Unit::Kilometer => (UnitCategory::Length, "km", 1000.0),
            Unit::Inch => (UnitCategory::Length, "in", 0.0254),
            Unit::Foot => (UnitCategory::Length, "ft", 0.3048),
            Unit::Yard => (UnitCategory::Length, "yd", 0.9144),
            Unit::Mile => (UnitCategory::Length, "mi", 1609.344),
            Unit::Degrees => (UnitCategory::Angular, "deg", 1.0),
            Unit::Radians => (UnitCategory::Angular, "rad", 57.295_779_513_082_32),
            Unit::Percent => (UnitCategory::Dimensionless, "%", 0.01),
            Unit::Default => (UnitCategory::Dimensionless, "default", 1.0),
        }
    }
}

impl UnitCategory {
    /// The unit this category measures in, the one whose
    /// [`scale`](Unit::scale) is `1.0` (C++ `SdfDefaultUnit`).
    pub const fn default_unit(self) -> Unit {
        match self {
            UnitCategory::Length => Unit::Meter,
            UnitCategory::Angular => Unit::Degrees,
            UnitCategory::Dimensionless => Unit::Default,
        }
    }
}

impl fmt::Display for Unit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_round_trip() {
        for unit in Unit::VARIANTS {
            assert_eq!(Unit::from_name(unit.name()), Some(*unit), "{unit}");
        }
        assert_eq!(Unit::from_name("furlong"), None);
    }

    /// A category measures in the one unit whose scale is 1.0, which is how
    /// C++ picks its default rather than by naming it.
    #[test]
    fn default_unit_scales_one() {
        for category in [UnitCategory::Length, UnitCategory::Angular, UnitCategory::Dimensionless] {
            let default = category.default_unit();
            assert_eq!(default.category(), category);
            assert_eq!(default.scale(), 1.0);
            let ones = Unit::VARIANTS
                .iter()
                .filter(|unit| unit.category() == category && unit.scale() == 1.0)
                .count();
            assert_eq!(ones, 1, "{category:?}");
        }
    }

    #[test]
    fn scales_convert() {
        assert_eq!(Unit::Centimeter.scale() / Unit::Millimeter.scale(), 10.0);
        assert_eq!(Unit::Percent.scale(), 0.01);
    }
}
