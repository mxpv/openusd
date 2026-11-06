//! Color-space resolution (AOUSD core spec §14.4.3, C++ `UsdColorSpaceAPI`'s
//! and `UsdColorSpaceDefinitionAPI`'s computations).
//!
//! An attribute's color space is its own `colorSpace` metadata where it has
//! one. Otherwise it is the `colorSpace:name` of the nearest prim, from the
//! attribute's own up through its ancestors, that has [`ColorSpaceAPI`]
//! applied. A name is valid when it is a built-in
//! [`gf::ColorSpace`](crate::gf::ColorSpace) or a [`ColorSpaceDefinitionAPI`]
//! instance on the prim or an ancestor defines it.
//!
//! [`ColorSpaceAPI`] and [`ColorSpaceDefinitionAPI`] are generated from the
//! schema's own definition; this module adds the computations a property
//! declaration cannot express, and the [`ColorSpaceCache`] they share.

use std::collections::HashMap;

use crate::{Result, gf, sdf, tf, vt};

use super::{Attribute, ColorSpaceAPI, ColorSpaceDefinitionAPI, Prim, Stage};

/// The computed color-space name of each prim a resolution has visited, kept
/// per stage (C++ `UsdColorSpaceAPI::ColorSpaceHashCache`).
///
/// Resolutions over a subtree walk the same ancestors; one cache handed to
/// each computes every prim's name once, for any stage resolved. An empty
/// token records that no color space applies to the prim.
///
/// Nothing evicts an entry: start a new cache after any edit to a stage the
/// cache covers. The edits that make an entry stale are a `colorSpace:name`
/// value; applying or removing [`ColorSpaceAPI`] or a
/// [`ColorSpaceDefinitionAPI`] instance; a definition's `name`; and any
/// composition change that alters those opinions or the prim hierarchy, such
/// as a reference, a payload load, a variant selection or a prim's
/// activation. An attribute's own `colorSpace` metadata is never cached, so
/// editing it leaves the cache current.
///
/// The cache holds a handle to each stage it has resolved on, which keeps
/// that stage open while the cache lives.
// TODO(rayon): each prim's walk is independent of every other's. A cache
// shared across threads would need its own locking.
#[derive(Debug, Default)]
pub struct ColorSpaceCache {
    /// Each stage's own path map, since a path names a prim on every stage.
    stages: HashMap<Stage, sdf::PathMap<tf::Token>>,
}

impl ColorSpaceCache {
    /// The computed color-space name of the prim at `path` on `stage`, empty
    /// where none applies, or `None` where it has not been computed (C++
    /// `ColorSpaceCache::Find`).
    pub fn get(&self, stage: &Stage, path: &sdf::Path) -> Option<&tf::Token> {
        self.stages.get(stage)?.get(path)
    }

    /// Record `name` as the computed color-space name of the prim at `path`
    /// on `stage` (C++ `ColorSpaceCache::Insert`).
    pub fn insert(&mut self, stage: &Stage, path: sdf::Path, name: tf::Token) {
        self.names_mut(stage).insert(path, name);
    }

    /// The names computed on `stage`, created empty where there are none.
    fn names_mut(&mut self, stage: &Stage) -> &mut sdf::PathMap<tf::Token> {
        self.stages.entry(stage.clone()).or_default()
    }
}

impl ColorSpaceAPI {
    /// The name of the color space that applies to `attribute` (C++
    /// `UsdColorSpaceAPI::ComputeColorSpaceName` of an attribute): its own
    /// `colorSpace`, authored or declared by its schema
    /// ([`Attribute::color_space`]), else the one
    /// [`compute_name`](Self::compute_name) gives its prim.
    ///
    /// The attribute's own `colorSpace` is returned as it is, without checking
    /// that it names a known color space;
    /// [`is_valid_name`](Self::is_valid_name) checks it. An empty one, or one
    /// that is not a token, is `None`, and the prim's is not consulted.
    ///
    /// `None` means no color space is assigned, and the spec's default, Linear
    /// Rec.709 ([`gf::color_space_names::LINEAR_REC709`]), applies. This
    /// function does not substitute the default.
    pub fn compute_attribute_name(
        attribute: &Attribute,
        cache: Option<&mut ColorSpaceCache>,
    ) -> Result<Option<tf::Token>> {
        match attribute.metadata::<vt::Value>(sdf::FieldKey::ColorSpace.as_str())? {
            Some(own) => Ok(own.try_as_token().filter(|own| !own.is_empty())),
            None => Self::compute_name(&attribute.prim(), cache),
        }
    }

    /// The name of the color space that applies to `prim` (C++
    /// `UsdColorSpaceAPI::ComputeColorSpaceName` of a prim): the
    /// `colorSpace:name` of the nearest prim, `prim` itself or an ancestor,
    /// that has [`ColorSpaceAPI`] applied and authors a non-empty name. A prim
    /// that authors the property without the schema applied is passed over.
    ///
    /// `None` where no prim assigns a name, for a prim the stage does not
    /// hold, and where the nearest name is not
    /// [valid](Self::is_valid_name) at the prim that assigns it. `None` means
    /// the spec's default, Linear Rec.709
    /// ([`gf::color_space_names::LINEAR_REC709`]), applies; this function does
    /// not substitute it.
    // TODO: report an unknown name. C++ warns through `TF_WARN` ("Unknown
    // color space"); this crate has no diagnostic channel for a query to carry
    // the report out through.
    pub fn compute_name(prim: &Prim, cache: Option<&mut ColorSpaceCache>) -> Result<Option<tf::Token>> {
        // A prim the stage does not hold has no color space, as in C++.
        if !prim.is_valid()? {
            return Ok(None);
        }
        let stage = prim.stage();
        let known = cache.as_deref().and_then(|cache| cache.stages.get(stage));
        // Every prim the walk passes before its answer has that answer too,
        // which a cache records.
        let mut walked = Vec::new();
        let name = 'walk: {
            for current in prim.ancestors() {
                if let Some(cached) = known.and_then(|names| names.get(current.path())) {
                    break 'walk cached.clone();
                }
                if cache.is_some() {
                    walked.push(current.path().clone());
                }
                let Some(api) = Self::from_prim(current.clone())? else {
                    continue;
                };
                let Some(assigned) = api.color_space_name()?.filter(|n| !n.is_empty()) else {
                    continue;
                };
                // An unknown name ends the walk unanswered, and C++ leaves it
                // out of the cache.
                if !Self::is_valid_name(&current, &assigned)? {
                    return Ok(None);
                }
                break 'walk assigned;
            }
            tf::Token::default()
        };
        if let Some(cache) = cache {
            let names = cache.names_mut(stage);
            for path in walked {
                names.insert(path, name.clone());
            }
        }
        Ok((!name.is_empty()).then_some(name))
    }

    /// Whether `name` is a built-in color space, or one a
    /// [`ColorSpaceDefinitionAPI`] instance's `name` defines on `prim` or an
    /// ancestor (C++ `UsdColorSpaceAPI::IsValidColorSpaceName`). An empty
    /// name is not valid.
    ///
    /// A definition that reuses a built-in's name is passed over.
    pub fn is_valid_name(prim: &Prim, name: &str) -> Result<bool> {
        if name.is_empty() {
            return Ok(false);
        }
        if gf::ColorSpace::is_valid(name) {
            return Ok(true);
        }
        Ok(definition(prim, name)?.is_some())
    }

    /// The color space that applies to `attribute` (C++
    /// `UsdColorSpaceAPI::ComputeColorSpace` of an attribute): the one named by
    /// [`compute_attribute_name`](Self::compute_attribute_name), as
    /// [`compute_named`](Self::compute_named) builds it at the attribute's
    /// prim.
    ///
    /// Where no color space is assigned, this is the empty-name identity
    /// sentinel, not the spec's default. A caller applies the default from
    /// the name:
    ///
    /// ```
    /// # use openusd::{gf, usd};
    /// # fn example(attr: &usd::Attribute) -> openusd::Result<gf::ColorSpace> {
    /// let space = match usd::ColorSpaceAPI::compute_attribute_name(attr, None)? {
    ///     Some(name) => usd::ColorSpaceAPI::compute_named(&attr.prim(), &name)?,
    ///     None => gf::ColorSpace::new(gf::color_space_names::LINEAR_REC709),
    /// };
    /// # Ok(space)
    /// # }
    /// ```
    pub fn compute_attribute(attribute: &Attribute, cache: Option<&mut ColorSpaceCache>) -> Result<gf::ColorSpace> {
        let name = Self::compute_attribute_name(attribute, cache)?.unwrap_or_default();
        Self::compute_named(&attribute.prim(), &name)
    }

    /// The color space that applies to `prim` (C++
    /// `UsdColorSpaceAPI::ComputeColorSpace` of a prim): the one named by
    /// [`compute_name`](Self::compute_name), as
    /// [`compute_named`](Self::compute_named) builds it.
    ///
    /// Where no color space is assigned, this is the empty-name identity
    /// sentinel, not the spec's default;
    /// [`compute_attribute`](Self::compute_attribute) shows how a caller
    /// applies it.
    pub fn compute(prim: &Prim, cache: Option<&mut ColorSpaceCache>) -> Result<gf::ColorSpace> {
        let name = Self::compute_name(prim, cache)?.unwrap_or_default();
        Self::compute_named(prim, &name)
    }

    /// The color space `name` names at `prim` (C++
    /// `UsdColorSpaceAPI::ComputeColorSpace` given a name): a built-in, or the
    /// one the nearest [`ColorSpaceDefinitionAPI`] defining `name` describes,
    /// on `prim` or an ancestor.
    ///
    /// An empty name, or one nothing defines, gives the empty-name identity
    /// sentinel [`gf::ColorSpace::new`] builds for a name that is not built
    /// in, as in C++.
    pub fn compute_named(prim: &Prim, name: &str) -> Result<gf::ColorSpace> {
        if name.is_empty() || gf::ColorSpace::is_valid(name) {
            return Ok(gf::ColorSpace::new(name));
        }
        match definition(prim, name)? {
            Some(definition) => definition.color_space(),
            None => Ok(gf::ColorSpace::new("")),
        }
    }
}

impl ColorSpaceDefinitionAPI {
    /// The color space the instance's attributes describe, named by the
    /// instance name (C++ `ComputeColorSpaceFromDefinitionAttributes`).
    ///
    /// The instance name and the `name` attribute differ unless an author
    /// keeps them equal.
    ///
    /// Where the prim does not carry the instance, its attributes have no
    /// values, and this is the built-in `raw` space, as in C++.
    pub fn color_space(&self) -> Result<gf::ColorSpace> {
        let values = (
            self.red_chroma()?,
            self.green_chroma()?,
            self.blue_chroma()?,
            self.white_point()?,
            self.gamma()?,
            self.linear_bias()?,
        );
        let (Some(red), Some(green), Some(blue), Some(white), Some(gamma), Some(linear_bias)) = values else {
            return Ok(gf::ColorSpace::new(gf::color_space_names::RAW));
        };
        Ok(gf::ColorSpace::from_primaries(
            self.name().clone(),
            [red, green, blue, white],
            gamma,
            linear_bias,
        ))
    }

    /// Author the instance's red, green and blue primaries, white point,
    /// gamma and linear bias, in one edit (C++
    /// `CreateColorSpaceAttrsWithChroma`).
    pub fn create_attrs_with_chroma(
        &self,
        [red, green, blue, white]: [gf::Vec2f; 4],
        gamma: f32,
        linear_bias: f32,
    ) -> Result<()> {
        self.stage().edit(|edit| {
            let attributes = [
                self.red_chroma_attr_builder().set(red),
                self.green_chroma_attr_builder().set(green),
                self.blue_chroma_attr_builder().set(blue),
                self.white_point_attr_builder().set(white),
                self.gamma_attr_builder().set(gamma),
                self.linear_bias_attr_builder().set(linear_bias),
            ];
            for attribute in attributes {
                attribute.in_edit(edit).build()?;
            }
            Ok(())
        })
    }

    /// Author the instance's attributes from an RGB-to-XYZ matrix, in one
    /// edit (C++ `CreateColorSpaceAttrsWithMatrix`): the primaries and white
    /// point are those [`gf::ColorSpace::from_matrix`] derives.
    ///
    /// `rgb_to_xyz` follows the [`gf`](crate::gf) row-vector convention,
    /// `xyz = rgb · M`; C++ takes the transpose. With a linear bias above 0,
    /// C++ derives other primaries, from a curve without its linear segment
    /// (see [`gf::ColorSpace::transfer_params`]).
    pub fn create_attrs_with_matrix(&self, rgb_to_xyz: gf::Mat3d, gamma: f32, linear_bias: f32) -> Result<()> {
        let space = gf::ColorSpace::from_matrix(self.name().clone(), rgb_to_xyz, gamma, linear_bias);
        self.create_attrs_with_chroma(space.primaries_and_white_point(), gamma, linear_bias)
    }
}

/// The nearest [`ColorSpaceDefinitionAPI`] instance whose `name` is `name`,
/// on `prim` or an ancestor, in each prim's `apiSchemas` order. `name` is not
/// a built-in's, and a definition reusing a built-in's name never matches.
// TODO: report a definition that reuses a built-in's name. C++ warns through
// `TF_WARN` ("illegal redefinition of standard color space"); this crate has
// no diagnostic channel for a query to carry the report out through.
// TODO(perf): `ColorSpaceAPI::compute` and `compute_attribute` walk the
// definitions twice for a name that is not built in, once to validate it and
// once to build it. One walk, remembering whether the match sits at or above
// the assigning prim, would serve both. `ColorSpaceCache` holds names only, so
// each attribute under a shared cache still walks the definitions again;
// caching the definition found for each assigning prim would remove that.
fn definition(prim: &Prim, name: &str) -> Result<Option<ColorSpaceDefinitionAPI>> {
    if !prim.is_valid()? {
        return Ok(None);
    }
    for current in prim.ancestors() {
        for definition in ColorSpaceDefinitionAPI::all(&current)? {
            if definition
                .name_attr()
                .get::<tf::Token>()?
                .is_some_and(|defined| defined == name)
            {
                return Ok(Some(definition));
            }
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `/World` applies `ColorSpaceAPI` naming a built-in space and defines
    /// `studio`, `/World/Set` names `studio`, and `/World/Odd` names a space
    /// nothing defines.
    fn stage() -> Result<Stage> {
        let stage = Stage::builder().in_memory("color.usda")?;
        let world = stage.define_prim("/World")?;
        ColorSpaceAPI::apply(&world)?
            .create_color_space_name_attr()?
            .set(tf::Token::new("ACEScg"))?;
        ColorSpaceDefinitionAPI::apply(&world, "studio")?
            .create_name_attr()?
            .set(tf::Token::new("studio"))?;
        let set = stage.define_prim("/World/Set")?;
        ColorSpaceAPI::apply(&set)?
            .create_color_space_name_attr()?
            .set(tf::Token::new("studio"))?;
        stage.define_prim("/World/Set/Chair")?;
        let odd = stage.define_prim("/World/Odd")?;
        ColorSpaceAPI::apply(&odd)?
            .create_color_space_name_attr()?
            .set(tf::Token::new("nowhere"))?;
        Ok(stage)
    }

    #[test]
    fn valid_names() -> Result<()> {
        let stage = stage()?;
        let chair = stage.prim("/World/Set/Chair")?;
        assert!(ColorSpaceAPI::is_valid_name(&chair, "lin_rec709_scene")?);
        assert!(ColorSpaceAPI::is_valid_name(&chair, "studio")?, "defined above");
        assert!(!ColorSpaceAPI::is_valid_name(&chair, "nowhere")?);
        assert!(!ColorSpaceAPI::is_valid_name(&chair, "")?);
        let other = stage.define_prim("/Other")?;
        assert!(!ColorSpaceAPI::is_valid_name(&other, "studio")?, "defined elsewhere");
        Ok(())
    }

    #[test]
    fn prim_names_inherit() -> Result<()> {
        let stage = stage()?;
        let name = |path: &str| -> Result<Option<String>> {
            Ok(ColorSpaceAPI::compute_name(&stage.prim(path)?, None)?.map(|t| t.to_string()))
        };
        assert_eq!(name("/World")?.as_deref(), Some("ACEScg"));
        assert_eq!(name("/World/Set/Chair")?.as_deref(), Some("studio"));
        assert_eq!(name("/World/Odd")?, None, "an unknown name ends the search");
        stage.define_prim("/Other")?;
        assert_eq!(name("/Other")?, None);
        Ok(())
    }

    #[test]
    fn attribute_names() -> Result<()> {
        let stage = stage()?;
        let chair = stage.prim("/World/Set/Chair")?;
        let inherited = chair.create_attribute("tint", "color3f")?;
        assert_eq!(
            ColorSpaceAPI::compute_attribute_name(&inherited, None)?,
            Some(tf::Token::new("studio"))
        );
        let own = chair.create_attribute("albedo", "color3f")?.set_color_space("raw")?;
        assert_eq!(own.color_space()?, Some(tf::Token::new("raw")));
        assert_eq!(
            ColorSpaceAPI::compute_attribute_name(&own, None)?,
            Some(tf::Token::new("raw"))
        );
        Ok(())
    }
}
