//! The color space that applies to a prim or an attribute, by name (C++
//! `UsdColorSpaceAPI::ComputeColorSpaceName` and
//! `IsValidColorSpaceName`).

use crate::Result;
use crate::gf;
use crate::tf;

use super::{Attribute, ColorSpaceAPI, ColorSpaceDefinitionAPI, Prim, tokens};

/// The color space names that apply down the namespace: a prim's own
/// `colorSpace:name` where it applies [`ColorSpaceAPI`], else its nearest
/// ancestor's, and an attribute's own `colorSpace` ahead of either.
// TODO(perf): C++ takes an optional `ColorSpaceCache` keyed by prim path,
// which a caller asking for many prims under one ancestor would want.
// TODO: report a name that names no color space, and a definition that
// redefines a built-in one; C++ warns through `TF_WARN`, and this crate has
// no diagnostic channel for a query to carry the report out through.
impl ColorSpaceAPI {
    /// Whether `name` names a color space at `prim`: one C++ `GfColorSpace`
    /// knows ([`gf::is_valid_color_space`]), or one a
    /// [`ColorSpaceDefinitionAPI`] instance on `prim` or an ancestor defines
    /// (C++ `UsdColorSpaceAPI::IsValidColorSpaceName`). A definition that
    /// names a built-in color space defines nothing.
    pub fn is_valid_name(prim: &Prim, name: &str) -> Result<bool> {
        if name.is_empty() {
            return Ok(false);
        }
        if gf::is_valid_color_space(name) {
            return Ok(true);
        }
        for prim in prim.ancestors() {
            for definition in ColorSpaceDefinitionAPI::all(&prim)? {
                let defined = definition.name_attr().get::<tf::Token>()?;
                if defined.is_some_and(|defined| defined == name && !gf::is_valid_color_space(&defined)) {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    /// The color space that applies to `prim` (C++
    /// `UsdColorSpaceAPI::ComputeColorSpaceName` of a prim): the
    /// `colorSpace:name` of `prim` or its nearest ancestor applying
    /// [`ColorSpaceAPI`] with a non-empty one, `None` where that names no
    /// color space at that prim ([`is_valid_name`](Self::is_valid_name)) or
    /// no prim has one.
    pub fn compute_name(prim: &Prim) -> Result<Option<tf::Token>> {
        for prim in prim.ancestors() {
            if !prim.has_api_schema(tokens::COLOR_SPACE_API)? {
                continue;
            }
            let Some(name) = ColorSpaceAPI::from_prim_unchecked(prim.clone()).color_space_name()? else {
                continue;
            };
            if name.is_empty() {
                continue;
            }
            return Ok(Self::is_valid_name(&prim, &name)?.then_some(name));
        }
        Ok(None)
    }

    /// The color space that applies to `attribute` (C++
    /// `UsdColorSpaceAPI::ComputeColorSpaceName` of an attribute): its own
    /// `colorSpace`, authored or declared by its schema
    /// ([`Attribute::color_space`]), else the one that applies to its prim
    /// ([`compute_name`](Self::compute_name)).
    pub fn compute_attribute_name(attribute: &Attribute) -> Result<Option<tf::Token>> {
        match attribute.color_space()? {
            Some(own) => Ok(Some(own)),
            None => Self::compute_name(&attribute.prim()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::usd::Stage;

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
            Ok(ColorSpaceAPI::compute_name(&stage.prim(path)?)?.map(|t| t.to_string()))
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
            ColorSpaceAPI::compute_attribute_name(&inherited)?,
            Some(tf::Token::new("studio"))
        );
        let own = chair.create_attribute("albedo", "color3f")?.set_color_space("raw")?;
        assert_eq!(own.color_space()?, Some(tf::Token::new("raw")));
        assert_eq!(
            ColorSpaceAPI::compute_attribute_name(&own)?,
            Some(tf::Token::new("raw"))
        );
        Ok(())
    }
}
