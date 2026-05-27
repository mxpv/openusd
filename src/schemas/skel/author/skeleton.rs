//! `Skeleton` prim authoring.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::skel::tokens::{A_BIND_TRANSFORMS, A_JOINTS, A_JOINT_NAMES, A_REST_TRANSFORMS, T_SKELETON};

use super::common::{author_uniform_matrix4d_array, author_uniform_token_array};

/// Author a `def Skeleton` prim at `path` and return a chainable
/// [`SkeletonAuthor`] for setting the spec-defined uniform attributes:
/// `joints`, `jointNames`, `bindTransforms`, `restTransforms`.
///
/// Per Pixar's `usdSkel/schema.usda`, all four are `uniform` arrays —
/// the authoring helpers default to that variability without the caller
/// having to thread it through.
pub fn define_skeleton<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<SkeletonAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_SKELETON)?;
    Ok(SkeletonAuthor { prim })
}

/// Chainable Skeleton authoring handle. Each setter writes one of the
/// 4 spec'd uniform arrays.
pub struct SkeletonAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> SkeletonAuthor<'s> {
    /// The underlying Skeleton prim handle, ready for further
    /// `apply_*` API authoring or to extract the path.
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `joints` — array of path tokens defining the skeleton's
    /// joint topology and ordering.
    pub fn set_joints<I, S>(self, joints: I) -> Result<Self>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let tokens: Vec<String> = joints.into_iter().map(Into::into).collect();
        author_uniform_token_array(self.prim.stage(), self.prim.path(), A_JOINTS, tokens)?;
        Ok(self)
    }

    /// Set `jointNames` — optional human-readable names per joint, in
    /// the same order as [`Self::set_joints`]. Useful for DCC apps
    /// that require unique joint names (USD itself allows non-unique
    /// leaf names because the joint paths are full SdfPath tokens).
    pub fn set_joint_names<I, S>(self, names: I) -> Result<Self>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let tokens: Vec<String> = names.into_iter().map(Into::into).collect();
        author_uniform_token_array(self.prim.stage(), self.prim.path(), A_JOINT_NAMES, tokens)?;
        Ok(self)
    }

    /// Set `bindTransforms` — bind-pose transforms in **world space**,
    /// in joint order. Each matrix is row-major flat `[f64; 16]`.
    pub fn set_bind_transforms(self, transforms: impl Into<Vec<[f64; 16]>>) -> Result<Self> {
        author_uniform_matrix4d_array(
            self.prim.stage(),
            self.prim.path(),
            A_BIND_TRANSFORMS,
            transforms.into(),
        )?;
        Ok(self)
    }

    /// Set `restTransforms` — rest-pose transforms in **local space**
    /// (parent-relative), in joint order. Used as a fallback for any
    /// joint missing from the bound SkelAnimation's joint set.
    pub fn set_rest_transforms(self, transforms: impl Into<Vec<[f64; 16]>>) -> Result<Self> {
        author_uniform_matrix4d_array(
            self.prim.stage(),
            self.prim.path(),
            A_REST_TRANSFORMS,
            transforms.into(),
        )?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    fn identity() -> [f64; 16] {
        let mut m = [0.0; 16];
        m[0] = 1.0;
        m[5] = 1.0;
        m[10] = 1.0;
        m[15] = 1.0;
        m
    }

    fn translated(y: f64) -> [f64; 16] {
        let mut m = identity();
        m[13] = y;
        m
    }

    #[test]
    fn define_skeleton_writes_all_spec_arrays() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_skeleton(&stage, sdf::path("/Rig")?)?
            .set_joints(["Root", "Root/Hip", "Root/Hip/Knee"])?
            .set_joint_names(["root", "hip", "knee"])?
            .set_bind_transforms(vec![identity(), translated(1.0), translated(2.0)])?
            .set_rest_transforms(vec![identity(), translated(1.0), translated(1.0)])?;

        let rig = sdf::path("/Rig")?;
        assert_eq!(stage.type_name(&rig)?.as_deref(), Some(T_SKELETON));

        // Joints as uniform token[] default value.
        let joints = stage.field::<sdf::Value>("/Rig.joints", sdf::FieldKey::Default)?;
        assert_eq!(
            joints,
            Some(sdf::Value::TokenVec(vec![
                "Root".into(),
                "Root/Hip".into(),
                "Root/Hip/Knee".into(),
            ])),
        );
        assert_eq!(
            stage.field::<sdf::Value>("/Rig.joints", sdf::FieldKey::Variability)?,
            Some(sdf::Value::Variability(sdf::Variability::Uniform)),
        );

        // jointNames carried per spec.
        let names = stage.field::<sdf::Value>("/Rig.jointNames", sdf::FieldKey::Default)?;
        assert_eq!(
            names,
            Some(sdf::Value::TokenVec(vec!["root".into(), "hip".into(), "knee".into()])),
        );

        // bindTransforms / restTransforms hold matrix4d[].
        let bind = stage.field::<sdf::Value>("/Rig.bindTransforms", sdf::FieldKey::Default)?;
        let rest = stage.field::<sdf::Value>("/Rig.restTransforms", sdf::FieldKey::Default)?;
        match bind {
            Some(sdf::Value::Matrix4dVec(v)) => {
                assert_eq!(v.len(), 3);
                assert_eq!(v[1][13], 1.0);
            }
            other => panic!("expected matrix4d[] for bindTransforms, got {other:?}"),
        }
        match rest {
            Some(sdf::Value::Matrix4dVec(v)) => assert_eq!(v.len(), 3),
            other => panic!("expected matrix4d[] for restTransforms, got {other:?}"),
        }
        Ok(())
    }

    #[test]
    fn jointnames_are_optional() -> Result<()> {
        // The schema marks jointNames as optional — author a Skeleton
        // without it and confirm it doesn't appear.
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_skeleton(&stage, sdf::path("/Rig")?)?
            .set_joints(["A", "B"])?
            .set_bind_transforms(vec![identity(), identity()])?;

        assert!(stage
            .field::<sdf::Value>("/Rig.jointNames", sdf::FieldKey::Default)?
            .is_none());
        Ok(())
    }
}
