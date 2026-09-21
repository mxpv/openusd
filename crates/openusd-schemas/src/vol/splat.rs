//! Choosing between a Gaussian splat's paired attributes (C++
//! `UsdVolParticleField3DGaussianSplat::UsesFloat*`).
//!
//! A splat stores its bulk data twice over in the schema: once at float
//! precision and once at half, as `positions` beside `positionsh`. Only one of
//! each pair carries the data, and which one is not recorded anywhere — it is
//! read off the data itself.

use openusd::Result;
use openusd::sdf::Value;
use openusd::usd::{Attribute, TimeCode};

use super::{ParticleField3DGaussianSplat, ParticleField3DGaussianSplatSchema};

/// One of a Gaussian splat's paired attributes, named without the precision
/// it is stored at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SplatData {
    /// `positions` / `positionsh` — where each particle is.
    Positions,
    /// `orientations` / `orientationsh` — how each particle is turned.
    Orientations,
    /// `scales` / `scalesh` — how far each particle reaches.
    Scales,
    /// `opacities` / `opacitiesh` — how much each particle occludes.
    Opacities,
    /// `radiance:sphericalHarmonicsCoefficients` and its half counterpart —
    /// the radiance each particle emits, as spherical harmonics.
    RadianceCoefficients,
}

impl ParticleField3DGaussianSplat {
    /// The attribute of the pair `data` names that carries the splat's data:
    /// the float one where it holds anything, and the half one otherwise. A
    /// splat that authors neither answers with the half attribute.
    pub fn attribute_in_use(&self, data: SplatData) -> Result<Attribute> {
        let float = self.float_attr(data);
        Ok(match holds_elements(&float)? {
            true => float,
            false => self.half_attr(data),
        })
    }

    /// Whether `data` is carried at float precision rather than half, which is
    /// what [`attribute_in_use`](Self::attribute_in_use) answers by handing
    /// back the attribute itself.
    pub fn uses_float(&self, data: SplatData) -> Result<bool> {
        holds_elements(&self.float_attr(data))
    }

    /// The float attribute `data` names.
    fn float_attr(&self, data: SplatData) -> Attribute {
        match data {
            SplatData::Positions => self.positions_attr(),
            SplatData::Orientations => self.orientations_attr(),
            SplatData::Scales => self.scales_attr(),
            SplatData::Opacities => self.opacities_attr(),
            SplatData::RadianceCoefficients => self.radiance_spherical_harmonics_coefficients_attr(),
        }
    }

    /// The half attribute `data` names.
    fn half_attr(&self, data: SplatData) -> Attribute {
        match data {
            SplatData::Positions => self.positionsh_attr(),
            SplatData::Orientations => self.orientationsh_attr(),
            SplatData::Scales => self.scalesh_attr(),
            SplatData::Opacities => self.opacitiesh_attr(),
            SplatData::RadianceCoefficients => self.radiance_spherical_harmonics_coefficientsh_attr(),
        }
    }
}

/// Whether `attr` holds an array with anything in it at the earliest time it
/// has a value.
///
/// Reading at [`TimeCode::EARLIEST`] answers with the first time sample where
/// the attribute is animated, and with the default value where it is not.
// TODO(perf): this composes and copies the whole array — millions of elements
// on a real splat — to ask whether it has any. `usd::Attribute` offers only a
// typed `get_at`, so the seam is an array-size read there that borrows the
// composed value rather than handing back an owned one.
fn holds_elements(attr: &Attribute) -> Result<bool> {
    let value = attr.get_at::<Value>(TimeCode::EARLIEST)?;
    Ok(value.and_then(|value| value.array_len()).is_some_and(|len| len > 0))
}
