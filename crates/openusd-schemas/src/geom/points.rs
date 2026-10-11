//! What `UsdGeomPointBased` and `UsdGeomPoints` answer beyond their own
//! properties: how many points a `Points` prim holds, and how `normals` and
//! `widths` lie on the geometry.

use openusd::Result;
use openusd::usd;

use super::{Interpolation, PointBasedSchema, Points, PointsSchema, array_len, tokens};

/// What every `UsdGeomPointBased` answers about its `normals`.
///
/// Every [`PointBasedSchema`] answers it, so a `Mesh` or a `BasisCurves` view
/// has these wherever the generated accessors are.
pub trait PointBasedExt: PointBasedSchema {
    /// How `normals` lie on the geometry (C++ `GetNormalsInterpolation`),
    /// [`Interpolation::Vertex`] where none is authored.
    ///
    /// An authored token that names no interpolation is an error.
    fn normals_interpolation(&self) -> Result<Interpolation> {
        interpolation(&self.normals_attr())
    }

    /// Author the `interpolation` of `normals` (C++
    /// `SetNormalsInterpolation`), declaring the attribute where no layer has
    /// yet.
    fn set_normals_interpolation(&self, interpolation: Interpolation) -> Result<()> {
        set_interpolation(self.normals_attr_builder(), interpolation)
    }
}

impl<T: PointBasedSchema> PointBasedExt for T {}

impl Points {
    /// How many points the prim holds at `time`, where `None` is the default
    /// time (C++ `GetPointCount`): the length of `points`, and zero where it
    /// reads no value.
    pub fn point_count(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<usize> {
        Ok(array_len(self.points_at(time)?))
    }

    /// How `widths` lie on the points (C++ `GetWidthsInterpolation`),
    /// [`Interpolation::Vertex`] where none is authored.
    ///
    /// An authored token that names no interpolation is an error.
    pub fn widths_interpolation(&self) -> Result<Interpolation> {
        interpolation(&self.widths_attr())
    }

    /// Author the `interpolation` of `widths` (C++ `SetWidthsInterpolation`),
    /// declaring the attribute where no layer has yet.
    pub fn set_widths_interpolation(&self, interpolation: Interpolation) -> Result<()> {
        set_interpolation(self.widths_attr_builder(), interpolation)
    }
}

/// The `interpolation` authored on `attr`, or [`Interpolation::Vertex`], the
/// one `normals` and `widths` have where none is.
pub(super) fn interpolation(attr: &usd::Attribute) -> Result<Interpolation> {
    Ok(attr
        .get_metadata::<Interpolation>(tokens::INTERPOLATION)?
        .unwrap_or(Interpolation::Vertex))
}

/// Author `interpolation` on the attribute `builder` declares, as one edit
/// with the declaration.
pub(super) fn set_interpolation(builder: usd::AttributeBuilder<'_>, interpolation: Interpolation) -> Result<()> {
    builder.metadata(tokens::INTERPOLATION, interpolation).build()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, tf};

    use super::PointBasedExt;
    use crate::SchemaError;
    use crate::geom::{Interpolation, PointBasedSchema, Points, PointsSchema, tokens};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// The point-count cases of C++ `testUsdGeomPoints`
    /// `test_ComputePointCount`.
    #[test]
    fn point_count() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let points = |n: usize| vec![gf::vec3f(1.0, 2.0, 3.0); n];
        let unset = Points::define(&stage, "/Unset")?;
        let blocked = Points::define(&stage, "/Blocked")?;
        blocked.create_points_attr()?.block()?;
        let empty = Points::define(&stage, "/Empty")?;
        empty.create_points_attr()?.set(points(0))?;
        let sampled = Points::define(&stage, "/Sampled")?;
        sampled
            .create_points_attr()?
            .set_at(points(3), usd::TimeCode::new(1.0))?;
        let both = Points::define(&stage, "/Both")?;
        both.create_points_attr()?
            .set(points(4))?
            .set_at(points(5), usd::TimeCode::new(1.0))?;

        for (schema, earliest, default) in [
            (&unset, 0, 0),
            (&blocked, 0, 0),
            (&empty, 0, 0),
            (&sampled, 3, 0),
            (&both, 5, 4),
        ] {
            assert_eq!(
                schema.point_count(usd::TimeCode::EARLIEST)?,
                earliest,
                "{}",
                schema.path()
            );
            assert_eq!(schema.point_count(None)?, default, "{}", schema.path());
        }
        Ok(())
    }

    /// A `Points` prim's widths carry their own interpolation, and a token
    /// that names none is an error.
    #[test]
    fn points_widths_interpolation() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let points = Points::define(&stage, "/Points")?;
        assert_eq!(points.widths_interpolation()?, Interpolation::Vertex);
        assert_eq!(points.normals_interpolation()?, Interpolation::Vertex);

        points.set_widths_interpolation(Interpolation::Constant)?;
        assert_eq!(points.widths_interpolation()?, Interpolation::Constant);

        points
            .widths_attr()
            .set_metadata(tokens::INTERPOLATION, tf::Token::from("frobosity"))?;
        assert!(points.widths_interpolation().is_err());
        Ok(())
    }
}
