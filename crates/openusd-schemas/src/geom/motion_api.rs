//! What `UsdGeomMotionAPI` answers beyond its own properties.

use openusd::sdf;
use openusd::usd::{self, SchemaBase};
use openusd::{Error, Result};

use super::{MotionAPI, nearest, tokens};
use crate::authored_at;

impl MotionAPI {
    /// The motion-blur scale in effect at `time` (C++
    /// `UsdGeomMotionAPI::ComputeMotionBlurScale`), where `None` is the
    /// default time, or 1.0 when nothing supplies one.
    ///
    /// Each of these computations reads its attribute from the nearest prim,
    /// this one or an ancestor of any type, that applies `MotionAPI` and
    /// authors a value there that reads at `time`. A schema fallback is no
    /// authored value, so it never hides an ancestor's.
    ///
    /// # Example
    ///
    /// ```
    /// use openusd::usd::{self, SchemaBase};
    /// use openusd_schemas::geom;
    ///
    /// let stage = usd::Stage::builder()
    ///     .schema_registry(openusd_schemas::schema_registry())
    ///     .in_memory("scene.usda")?;
    /// let shot = geom::MotionAPI::apply(geom::Xform::define(&stage, "/Shot")?.prim())?;
    /// shot.create_motion_blur_scale_attr()?.set(0.5_f32)?;
    ///
    /// // The mesh does not apply `MotionAPI`. Viewed through it, the mesh
    /// // reads the shot's setting.
    /// let mesh = geom::Mesh::define(&stage, "/Shot/Mesh")?;
    /// let motion = geom::MotionAPI::from_prim_unchecked(mesh.prim().clone());
    /// assert_eq!(motion.compute_motion_blur_scale(None)?, 0.5);
    ///
    /// // Nothing authors a sample count: the default answers.
    /// assert_eq!(motion.compute_nonlinear_sample_count(None)?, 3);
    /// # Ok::<(), openusd_schemas::SchemaError>(())
    /// ```
    pub fn compute_motion_blur_scale(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<f32> {
        self.inherited(tokens::MOTION_BLUR_SCALE, time.into(), 1.0)
    }

    /// The number of samples a nonlinear interpolation of this prim's motion
    /// takes at `time` (C++ `ComputeNonlinearSampleCount`), where `None` is the
    /// default time, or 3 when nothing supplies one. Inherited as
    /// [`compute_motion_blur_scale`](Self::compute_motion_blur_scale) is.
    pub fn compute_nonlinear_sample_count(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<i32> {
        self.inherited(tokens::MOTION_NONLINEAR_SAMPLE_COUNT, time.into(), 3)
    }

    /// The velocity scale in effect at `time` (C++ `ComputeVelocityScale`),
    /// where `None` is the default time, or 1.0 when nothing supplies one.
    /// Inherited as [`compute_motion_blur_scale`](Self::compute_motion_blur_scale)
    /// is. Upstream deprecates the attribute in favor of authoring velocities
    /// directly.
    pub fn compute_velocity_scale(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<f32> {
        self.inherited(tokens::MOTION_VELOCITY_SCALE, time.into(), 1.0)
    }

    /// The value of `name` at `time` from the nearest prim that supplies one,
    /// or `fallback` (C++ `_ComputeInheritedMotionAttr`).
    ///
    /// A prim whose authored value reads as nothing at `time`, such as a
    /// blocked sample, is passed over. An authored value of another type does
    /// not read as nothing at the default time: the typed read then answers
    /// with the prim's own fallback, as it does in C++.
    fn inherited<T>(&self, name: &str, time: Option<usd::TimeCode>, fallback: T) -> Result<T>
    where
        T: sdf::FromValue,
        T::Error: Into<Error>,
    {
        let supplied = nearest(self.stage(), self.path(), MotionAPI::from_prim, |api| {
            authored_at(&api.attribute(name), time)
        })?;
        Ok(supplied.unwrap_or(fallback))
    }
}

#[cfg(test)]
mod tests {
    use openusd::Result;
    use openusd::sdf;
    use openusd::usd::{SchemaBase, Stage, TimeCode};

    use crate::geom::{Mesh, MotionAPI, Xform};

    /// `prim` viewed as [`MotionAPI`], whether or not it applies it.
    fn motion(prim: &impl SchemaBase) -> MotionAPI {
        MotionAPI::from_prim_unchecked(prim.prim().clone())
    }

    fn stage() -> Result<Stage> {
        crate::tests::stage("anon.usda")
    }

    /// An ancestor's authored settings reach a child that does not author its
    /// own, whether or not the child applies the API: the child's schema
    /// fallback does not hide them (C++ `testUsdGeomMotionAPI`).
    #[test]
    fn motion_inherits() -> Result<()> {
        let stage = stage()?;
        let root = MotionAPI::apply(Xform::define(&stage, "/root1")?.prim())?;
        root.create_motion_blur_scale_attr()?.set(0.5_f32)?;
        root.create_nonlinear_sample_count_attr()?.set(5)?;
        let mesh = Mesh::define(&stage, "/root1/mesh1")?;
        let check = |mesh: &Mesh| -> Result<()> {
            assert_eq!(motion(mesh).compute_motion_blur_scale(None)?, 0.5);
            assert_eq!(motion(mesh).compute_nonlinear_sample_count(None)?, 5);
            Ok(())
        };

        check(&mesh)?;
        MotionAPI::apply(mesh.prim())?;
        check(&mesh)?;
        Ok(())
    }

    /// A value authored on a prim that does not apply the API counts for
    /// nothing, and counts once the API is applied.
    #[test]
    fn unapplied_ignored() -> Result<()> {
        let stage = stage()?;
        let root = MotionAPI::apply(Xform::define(&stage, "/root1")?.prim())?;
        root.create_motion_blur_scale_attr()?.set(0.5_f32)?;
        root.create_nonlinear_sample_count_attr()?.set(5)?;
        let mesh = Mesh::define(&stage, "/root1/mesh2")?;
        motion(&mesh).create_motion_blur_scale_attr()?.set(2.0_f32)?;
        motion(&mesh).create_nonlinear_sample_count_attr()?.set(10)?;

        assert_eq!(motion(&mesh).compute_motion_blur_scale(None)?, 0.5);
        assert_eq!(motion(&mesh).compute_nonlinear_sample_count(None)?, 5);
        MotionAPI::apply(mesh.prim())?;
        assert_eq!(motion(&mesh).compute_motion_blur_scale(None)?, 2.0);
        assert_eq!(motion(&mesh).compute_nonlinear_sample_count(None)?, 10);
        Ok(())
    }

    /// With nothing authored anywhere, the fallbacks C++ hard-codes answer.
    #[test]
    fn motion_fallbacks() -> Result<()> {
        let stage = stage()?;
        Xform::define(&stage, "/root2")?;
        let mesh = motion(&Mesh::define(&stage, "/root2/mesh")?);
        assert_eq!(mesh.compute_motion_blur_scale(None)?, 1.0);
        assert_eq!(mesh.compute_nonlinear_sample_count(None)?, 3);
        assert_eq!(mesh.compute_velocity_scale(None)?, 1.0);
        Ok(())
    }

    /// An ancestor's samples are read at the time asked for.
    #[test]
    fn motion_animated() -> Result<()> {
        let stage = stage()?;
        MotionAPI::apply(Xform::define(&stage, "/root")?.prim())?
            .create_motion_blur_scale_attr()?
            .set_at(0.25_f32, TimeCode::new(1.0))?
            .set_at(0.75_f32, TimeCode::new(2.0))?;
        let mesh = motion(&Mesh::define(&stage, "/root/mesh")?);
        assert_eq!(mesh.compute_motion_blur_scale(TimeCode::new(1.0))?, 0.25);
        assert_eq!(mesh.compute_motion_blur_scale(TimeCode::new(2.0))?, 0.75);
        Ok(())
    }

    /// A child that blocks its `default` authors no value, so the parent's
    /// setting answers.
    #[test]
    fn blocked_inherits() -> Result<()> {
        let stage = stage()?;
        MotionAPI::apply(Xform::define(&stage, "/root")?.prim())?
            .create_motion_blur_scale_attr()?
            .set(0.5_f32)?;
        let mesh = MotionAPI::apply(Mesh::define(&stage, "/root/mesh")?.prim())?;
        mesh.create_motion_blur_scale_attr()?.block()?;
        assert_eq!(mesh.compute_motion_blur_scale(None)?, 0.5);
        Ok(())
    }

    /// A child's blocked sample reads no value at its time, so the parent's
    /// setting answers there, while the child's other samples answer theirs.
    #[test]
    fn blocked_sample_inherits() -> Result<()> {
        let stage = stage()?;
        MotionAPI::apply(Xform::define(&stage, "/root")?.prim())?
            .create_motion_blur_scale_attr()?
            .set(0.5_f32)?;
        let mesh = MotionAPI::apply(Mesh::define(&stage, "/root/mesh")?.prim())?;
        mesh.create_motion_blur_scale_attr()?
            .set_at(2.0_f32, TimeCode::new(1.0))?
            .set_at(sdf::Value::ValueBlock, TimeCode::new(2.0))?
            .set_at(4.0_f32, TimeCode::new(3.0))?;

        assert_eq!(mesh.compute_motion_blur_scale(TimeCode::new(1.0))?, 2.0);
        assert_eq!(mesh.compute_motion_blur_scale(TimeCode::new(2.0))?, 0.5);
        assert_eq!(mesh.compute_motion_blur_scale(TimeCode::new(3.0))?, 4.0);
        Ok(())
    }

    /// The walk reaches ancestors of any type, not only geometry.
    #[test]
    fn untyped_ancestor() -> Result<()> {
        let stage = stage()?;
        let group = MotionAPI::apply(&stage.define_prim("/group")?)?;
        group.create_nonlinear_sample_count_attr()?.set(7)?;
        let mesh = motion(&Mesh::define(&stage, "/group/mesh")?);
        assert_eq!(mesh.compute_nonlinear_sample_count(None)?, 7);
        Ok(())
    }

    /// An authored `double` where the schema declares a `float` does not read
    /// as a float, so at the default time the child's typed read answers with
    /// its own fallback. OpenUSD 26.08 returns 1.0 here, not the parent's 0.5.
    #[test]
    fn mismatch_fallback() -> Result<()> {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0
def Xform "root" (
    prepend apiSchemas = ["MotionAPI"]
)
{
    float motion:blurScale = 0.5

    def Mesh "mesh" (
        prepend apiSchemas = ["MotionAPI"]
    )
    {
        double motion:blurScale = 2
    }
}
"#,
        )?;
        let mesh = MotionAPI::get(&stage, "/root/mesh")?.expect("MotionAPI is applied");
        assert_eq!(mesh.compute_motion_blur_scale(None)?, 1.0);
        Ok(())
    }

    /// The deprecated velocity scale is inherited like the others.
    #[test]
    fn velocity_scale() -> Result<()> {
        let stage = stage()?;
        MotionAPI::apply(Xform::define(&stage, "/root")?.prim())?
            .create_velocity_scale_attr()?
            .set(3.0_f32)?;
        let mesh = motion(&Mesh::define(&stage, "/root/mesh")?);
        assert_eq!(mesh.compute_velocity_scale(None)?, 3.0);
        Ok(())
    }
}
