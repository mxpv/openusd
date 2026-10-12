//! `UsdGeomXformCommonAPI`: a prim's transform as one translate, one
//! rotate, one scale and a pivot.
//!
//! The API fits a stack whose `xformOpOrder` is a subsequence of
//! `[xformOp:translate, xformOp:translate:pivot, xformOp:rotateXYZ,
//! xformOp:scale, !invert!xformOp:translate:pivot]`, where the rotation may
//! be any three-axis order and the pivot comes with its inverse or not at
//! all.

use openusd::Result;
use openusd::usd::{self, SchemaBase};
use openusd::{gf, sdf, tf};

use super::xform_op::TOKEN_RESET_XFORM_STACK;
use super::xformable::{OpWrite, StackEdit};
use super::{XformCommonAPI, XformOp, XformOpKind, XformOpPrecision, Xformable, XformableExt, tokens};
use crate::SchemaError;

/// The order a three-axis rotation applies its angles in (C++
/// `UsdGeomXformCommonAPI::RotationOrder`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum RotationOrder {
    /// X, then Y, then Z.
    #[default]
    XYZ,
    /// X, then Z, then Y.
    XZY,
    /// Y, then X, then Z.
    YXZ,
    /// Y, then Z, then X.
    YZX,
    /// Z, then X, then Y.
    ZXY,
    /// Z, then Y, then X.
    ZYX,
}

impl RotationOrder {
    /// The kind of op that rotates in this order (C++
    /// `ConvertRotationOrderToOpType`).
    pub fn op_kind(self) -> XformOpKind {
        match self {
            Self::XYZ => XformOpKind::RotateXYZ,
            Self::XZY => XformOpKind::RotateXZY,
            Self::YXZ => XformOpKind::RotateYXZ,
            Self::YZX => XformOpKind::RotateYZX,
            Self::ZXY => XformOpKind::RotateZXY,
            Self::ZYX => XformOpKind::RotateZYX,
        }
    }

    /// The order a three-axis rotate op of `kind` applies its angles in, or
    /// `None` for any other kind (C++ `ConvertOpTypeToRotationOrder`, with
    /// `CanConvertOpTypeToRotationOrder` as the `None`).
    pub fn from_op_kind(kind: XformOpKind) -> Option<Self> {
        Some(match kind {
            XformOpKind::RotateXYZ => Self::XYZ,
            XformOpKind::RotateXZY => Self::XZY,
            XformOpKind::RotateYXZ => Self::YXZ,
            XformOpKind::RotateYZX => Self::YZX,
            XformOpKind::RotateZXY => Self::ZXY,
            XformOpKind::RotateZYX => Self::ZYX,
            _ => return None,
        })
    }

    /// The X, Y and Z angles, in degrees, that make `rotation` when applied
    /// in this order.
    fn angles(self, rotation: gf::Rotation) -> gf::Vec3f {
        const AXES: [gf::Vec3d; 3] = [gf::Vec3d::X_AXIS, gf::Vec3d::Y_AXIS, gf::Vec3d::Z_AXIS];
        // The axes turned about, first to last.
        let [first, second, third] = match self {
            Self::XYZ => [0, 1, 2],
            Self::XZY => [0, 2, 1],
            Self::YXZ => [1, 0, 2],
            Self::YZX => [1, 2, 0],
            Self::ZXY => [2, 0, 1],
            Self::ZYX => [2, 1, 0],
        };
        let turns = rotation.decompose(AXES[third], AXES[second], AXES[first]);
        let mut angles = [0.0; 3];
        angles[third] = turns.x as f32;
        angles[second] = turns.y as f32;
        angles[first] = turns.z as f32;
        angles.into()
    }

    /// The matrix that rotates by `rotation`, in degrees, in this order (C++
    /// `GetRotationTransform`).
    pub fn rotation_transform(self, rotation: gf::Vec3f) -> gf::Mat4d {
        self.op_kind()
            .matrix(sdf::Value::Vec3f(rotation), false)
            .unwrap_or(gf::Mat4d::IDENTITY)
    }
}

/// One of the ops [`XformCommonAPI`] reads a transform as (C++
/// `UsdGeomXformCommonAPI::OpFlags`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CommonXformOp {
    /// `xformOp:translate`.
    Translate,
    /// The three-axis rotate op.
    Rotate,
    /// `xformOp:scale`.
    Scale,
    /// `xformOp:translate:pivot`, together with its inverse.
    Pivot,
}

/// The ops of a stack [`XformCommonAPI`] fits (C++
/// `UsdGeomXformCommonAPI::Ops`), each `None` where the stack does not list
/// it.
#[derive(Clone, Default)]
pub struct CommonXformOps {
    /// `xformOp:translate`.
    pub translate: Option<XformOp>,
    /// `xformOp:translate:pivot`.
    pub pivot: Option<XformOp>,
    /// The three-axis rotate op.
    pub rotate: Option<XformOp>,
    /// `xformOp:scale`.
    pub scale: Option<XformOp>,
    /// `!invert!xformOp:translate:pivot`.
    pub inverse_pivot: Option<XformOp>,
}

/// A transform as the vectors [`XformCommonAPI`] reads and authors (C++
/// `GetXformVectors` / `SetXformVectors`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct XformVectors {
    /// The translation.
    pub translation: gf::Vec3d,
    /// The rotation angles about X, Y and Z, in degrees.
    pub rotation: gf::Vec3f,
    /// The scale along each axis.
    pub scale: gf::Vec3f,
    /// The point the rotation and the scale are about.
    pub pivot: gf::Vec3f,
    /// The order the rotation applies its angles in.
    pub rotation_order: RotationOrder,
}

impl Default for XformVectors {
    /// The identity transform.
    fn default() -> Self {
        XformVectors {
            translation: gf::vec3d(0.0, 0.0, 0.0),
            rotation: gf::vec3f(0.0, 0.0, 0.0),
            scale: gf::vec3f(1.0, 1.0, 1.0),
            pivot: gf::vec3f(0.0, 0.0, 0.0),
            rotation_order: RotationOrder::XYZ,
        }
    }
}

impl CommonXformOps {
    /// The order the rotate op applies its angles in, or `None` without one.
    fn rotation_order(&self) -> Option<RotationOrder> {
        self.rotate
            .as_ref()
            .and_then(XformOp::kind)
            .and_then(RotationOrder::from_op_kind)
    }
}

impl XformCommonAPI {
    /// `true` when the prim is `Xformable` and its stack fits this API (C++
    /// the schema's validity, `_IsCompatible`).
    pub fn is_compatible(&self) -> Result<bool> {
        match Xformable::from_prim(self.prim().clone())? {
            Some(xformable) => Ok(common_ops(xformable.ordered_xform_ops()?.0).is_some()),
            None => Ok(false),
        }
    }

    /// The ops this API reads, creating each of `ops` the stack does not
    /// list yet (C++ `CreateXformOps`).
    ///
    /// A new translate is `double3`, and a new pivot, rotate or scale
    /// `float3`. A new rotate op takes `rotation_order`, or XYZ where none
    /// is given. `xformOpOrder` is rewritten in this API's order, keeping a
    /// reset, and the declarations and the order are one edit. Nothing is
    /// authored when every op asked for is already there.
    ///
    /// A prim that is not `Xformable`, or whose stack does not fit this API,
    /// is [`SchemaError::IncompatibleXformable`]. Asking for a rotate op in
    /// an order other than the one the stack already rotates in is
    /// [`SchemaError::RotationOrderMismatch`].
    pub fn create_xform_ops(
        &self,
        rotation_order: Option<RotationOrder>,
        ops: &[CommonXformOp],
    ) -> Result<CommonXformOps, SchemaError> {
        let ops: Vec<_> = ops.iter().map(|op| (*op, None)).collect();
        self.author(rotation_order, ops, None)
    }

    /// Author the whole transform at `time`, where `None` is the default
    /// time, creating the ops the stack lacks (C++ `SetXformVectors`). The
    /// ops, their order and the four values are one edit.
    pub fn set_xform_vectors(
        &self,
        vectors: &XformVectors,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<(), SchemaError> {
        let values = vec![
            (CommonXformOp::Translate, Some(vectors.translation.into())),
            (CommonXformOp::Rotate, Some(vectors.rotation.into())),
            (CommonXformOp::Scale, Some(vectors.scale.into())),
            (CommonXformOp::Pivot, Some(vectors.pivot.into())),
        ];
        self.author(Some(vectors.rotation_order), values, time.into())?;
        Ok(())
    }

    /// Author the translation at `time`, where `None` is the default time,
    /// creating its op where the stack lacks it (C++ `SetTranslate`).
    pub fn set_translate(
        &self,
        translation: gf::Vec3d,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<(), SchemaError> {
        let values = vec![(CommonXformOp::Translate, Some(translation.into()))];
        self.author(None, values, time.into())?;
        Ok(())
    }

    /// Author the pivot at `time`, where `None` is the default time,
    /// creating its op and the inverse where the stack lacks them (C++
    /// `SetPivot`).
    pub fn set_pivot(&self, pivot: gf::Vec3f, time: impl Into<Option<usd::TimeCode>>) -> Result<(), SchemaError> {
        let values = vec![(CommonXformOp::Pivot, Some(pivot.into()))];
        self.author(None, values, time.into())?;
        Ok(())
    }

    /// Author the rotation angles, in degrees, at `time`, where `None` is
    /// the default time, creating a rotate op of `rotation_order` where the
    /// stack lacks one (C++ `SetRotate`).
    pub fn set_rotate(
        &self,
        rotation: gf::Vec3f,
        rotation_order: RotationOrder,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<(), SchemaError> {
        let values = vec![(CommonXformOp::Rotate, Some(rotation.into()))];
        self.author(Some(rotation_order), values, time.into())?;
        Ok(())
    }

    /// Author the scale at `time`, where `None` is the default time,
    /// creating its op where the stack lacks it (C++ `SetScale`).
    pub fn set_scale(&self, scale: gf::Vec3f, time: impl Into<Option<usd::TimeCode>>) -> Result<(), SchemaError> {
        let values = vec![(CommonXformOp::Scale, Some(scale.into()))];
        self.author(None, values, time.into())?;
        Ok(())
    }

    /// The transform at `time`, where `None` is the default time (C++
    /// `GetXformVectors`).
    ///
    /// A stack that fits this API answers its ops' values, with the identity
    /// for an op it does not list. Any other stack is composed into its local
    /// matrix, which is factored into a translation, an XYZ rotation and a
    /// scale about a zero pivot; shear in the matrix is lost.
    pub fn xform_vectors(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<XformVectors, SchemaError> {
        let time = time.into();
        let xformable = self.xformable();
        match common_ops(xformable.ordered_xform_ops()?.0) {
            Some(ops) => Ok(common_vectors(&ops, time)?),
            None => Ok(matrix_vectors(xformable.local_transform(time)?)),
        }
    }

    /// The transform at `time`, where `None` is the default time, read by
    /// folding runs of like ops together (C++
    /// `GetXformVectorsByAccumulation`).
    ///
    /// A stack that does not fit this API can still reduce to its shape:
    /// several translates in a row are one translation, several rotates one
    /// rotation. When the stack reduces, the vectors come from the folded
    /// matrices, keeping the pivot, and the rotation is read back as the
    /// angles that make it in the order of the stack's first rotate op.
    /// C++ reads back the angles of the ZYX order whatever order it answers,
    /// which are another rotation under any other. When the stack does not
    /// reduce, the answer is the one [`xform_vectors`](Self::xform_vectors)
    /// gives.
    pub fn xform_vectors_by_accumulation(
        &self,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<XformVectors, SchemaError> {
        let time = time.into();
        let typed = Xformable::from_prim(self.prim().clone())?.is_some();
        let xformable = self.xformable();
        let (ops, _) = xformable.ordered_xform_ops()?;
        if typed && let Some(common) = common_ops(ops.clone()) {
            return Ok(common_vectors(&common, time)?);
        }
        match accumulate(&ops, time)? {
            Some(vectors) => Ok(vectors),
            None => Ok(matrix_vectors(xformable.local_transform(time)?)),
        }
    }

    /// `true` when the stack resets its parent's transform (C++
    /// `GetResetXformStack`).
    pub fn resets_xform_stack(&self) -> Result<bool> {
        self.xformable().resets_xform_stack()
    }

    /// Author whether the stack resets its parent's transform (C++
    /// `SetResetXformStack`), on the terms
    /// [`XformableExt::set_reset_xform_stack`] states.
    pub fn set_reset_xform_stack(&self, reset: bool) -> Result<()> {
        self.xformable().set_reset_xform_stack(reset)?;
        Ok(())
    }

    /// This prim viewed as an [`Xformable`], whose op stack the API reads
    /// and authors whatever the prim's type.
    fn xformable(&self) -> Xformable {
        Xformable::from_prim_unchecked(self.prim().clone())
    }

    /// Create each op of `ops` the stack lacks and author the value paired
    /// with it at `time`, all as one edit, on the terms
    /// [`create_xform_ops`](Self::create_xform_ops) states.
    fn author(
        &self,
        rotation_order: Option<RotationOrder>,
        ops: Vec<(CommonXformOp, Option<sdf::Value>)>,
        time: Option<usd::TimeCode>,
    ) -> Result<CommonXformOps, SchemaError> {
        let prim = self.prim();
        let incompatible = || SchemaError::IncompatibleXformable {
            prim: prim.path().clone(),
        };
        let xformable = Xformable::from_prim(prim.clone())?.ok_or_else(incompatible)?;
        let (ordered, resets) = xformable.ordered_xform_ops()?;
        let mut common = common_ops(ordered).ok_or_else(incompatible)?;

        let existing = common.rotation_order();
        if ops.iter().any(|(op, _)| *op == CommonXformOp::Rotate)
            && let (Some(requested), Some(existing)) = (rotation_order, existing)
            && requested != existing
        {
            return Err(SchemaError::RotationOrderMismatch {
                prim: prim.path().clone(),
                requested: requested.op_kind().as_token(),
                existing: existing.op_kind().as_token(),
            });
        }

        let rotate_kind = existing.or(rotation_order).unwrap_or_default().op_kind();
        let (double, float) = (XformOpPrecision::Double, XformOpPrecision::Float);
        let mut writes: Vec<OpWrite> = Vec::new();
        let mut added = false;
        for (op, value) in ops {
            let (slot, kind, precision, suffix) = match op {
                CommonXformOp::Translate => (&mut common.translate, XformOpKind::Translate, double, None),
                CommonXformOp::Pivot => (&mut common.pivot, XformOpKind::Translate, float, Some(tokens::PIVOT)),
                CommonXformOp::Rotate => (&mut common.rotate, rotate_kind, float, None),
                CommonXformOp::Scale => (&mut common.scale, XformOpKind::Scale, float, None),
            };
            // An op the stack lists keeps its own name: a rotate op fits
            // under any suffix.
            let name = match slot.as_ref() {
                Some(op) => tf::Token::from(op.name()),
                None => kind.op_name(suffix, false),
            };
            if writes.iter().any(|write| write.name == name) {
                continue;
            }
            if slot.is_none() {
                let attr = prim.attribute(name.as_str());
                *slot = Some(XformOp::new(&attr, false));
                if op == CommonXformOp::Pivot {
                    common.inverse_pivot = Some(XformOp::new(&attr, true));
                }
                added = true;
            }
            writes.push(OpWrite {
                name,
                new_type: kind.value_type(precision),
                value,
            });
        }

        let order = added.then(|| {
            let listed = [
                &common.translate,
                &common.pivot,
                &common.rotate,
                &common.scale,
                &common.inverse_pivot,
            ];
            resets
                .then(|| tf::Token::from(TOKEN_RESET_XFORM_STACK))
                .into_iter()
                .chain(listed.into_iter().flatten().map(XformOp::op_name))
                .collect()
        });
        StackEdit::prepare(prim, writes, order, time)?.commit(prim)?;
        Ok(common)
    }
}

/// The ops of a stack as [`XformCommonAPI`] reads them, or `None` for a
/// stack that does not fit (C++ `_GetCommonXformOps`).
fn common_ops(ops: Vec<XformOp>) -> Option<CommonXformOps> {
    if ops.len() > 5 {
        return None;
    }
    let translate = XformOpKind::Translate.op_name(None, false);
    let pivot = XformOpKind::Translate.op_name(Some(tokens::PIVOT), false);
    let scale = XformOpKind::Scale.op_name(None, false);
    let is_op =
        |op: &XformOp, name: &tf::Token, inverse: bool| op.name() == name.as_str() && op.is_inverse() == inverse;
    let is_rotate = |op: &XformOp| !op.is_inverse() && op.kind().and_then(RotationOrder::from_op_kind).is_some();

    let mut rest = ops.into_iter().peekable();
    let common = CommonXformOps {
        translate: rest.next_if(|op| is_op(op, &translate, false)),
        pivot: rest.next_if(|op| is_op(op, &pivot, false)),
        rotate: rest.next_if(is_rotate),
        scale: rest.next_if(|op| is_op(op, &scale, false)),
        inverse_pivot: rest.next_if(|op| is_op(op, &pivot, true)),
    };
    let fits = rest.next().is_none() && common.pivot.is_some() == common.inverse_pivot.is_some();
    fits.then_some(common)
}

/// The vectors the ops of a fitting stack hold at `time`, with the identity
/// for an op the stack does not list or that has no value.
fn common_vectors(ops: &CommonXformOps, time: Option<usd::TimeCode>) -> Result<XformVectors> {
    let read = |op: &Option<XformOp>| -> Result<Option<sdf::Value>> {
        match op {
            Some(op) => op.attribute().get_at::<sdf::Value>(time),
            None => Ok(None),
        }
    };
    let float3 = |value: Option<sdf::Value>| value.and_then(|value| value.cast::<gf::Vec3f>().ok());
    let identity = XformVectors::default();
    Ok(XformVectors {
        translation: read(&ops.translate)?
            .and_then(|value| value.cast::<[f64; 3]>().ok())
            .map_or(identity.translation, gf::Vec3d::from),
        rotation: float3(read(&ops.rotate)?).unwrap_or(identity.rotation),
        scale: float3(read(&ops.scale)?).unwrap_or(identity.scale),
        pivot: float3(read(&ops.pivot)?).unwrap_or(identity.pivot),
        rotation_order: ops.rotation_order().unwrap_or_default(),
    })
}

/// The vectors a local matrix factors into: its translation, its rotation as
/// XYZ angles, and its scale, about a zero pivot (C++
/// `_ConvertMatrixToComponents`).
fn matrix_vectors(matrix: gf::Mat4d) -> XformVectors {
    let factors = matrix.factor(gf::Mat4d::FACTOR_EPSILON);
    let mut rotation = factors.rotation;
    rotation.orthonormalize();
    let angles = rotation
        .extract_rotation()
        .decompose(gf::Vec3d::Z_AXIS, gf::Vec3d::Y_AXIS, gf::Vec3d::X_AXIS);
    XformVectors {
        translation: factors.translation,
        rotation: gf::vec3f(angles.z as f32, angles.y as f32, angles.x as f32),
        scale: factors.scale.to_f32(),
        ..XformVectors::default()
    }
}

/// Fold `ops` into the translate, pivot, rotate, scale and inverse-pivot
/// slots of [`XformCommonAPI`]'s order and read the vectors off the folded
/// matrices, or `None` when the stack does not reduce to that order (the
/// body of C++ `GetXformVectorsByAccumulation`).
fn accumulate(ops: &[XformOp], time: Option<usd::TimeCode>) -> Result<Option<XformVectors>, SchemaError> {
    let is_rotate = |kind: Option<XformOpKind>| {
        matches!(
            kind,
            Some(XformOpKind::RotateX | XformOpKind::RotateY | XformOpKind::RotateZ)
        ) || kind.and_then(RotationOrder::from_op_kind).is_some()
    };
    let is_translate = |kind: Option<XformOpKind>| kind == Some(XformOpKind::Translate);

    // The kind the fold advances past, and the one a rotate slot takes: the
    // stack's first rotate op and its last.
    let rotate_kind = ops.iter().map(XformOp::kind).find(|kind| is_rotate(*kind)).flatten();
    let slot_rotate_kind = ops.iter().map(XformOp::kind).rfind(|kind| is_rotate(*kind)).flatten();
    let has_scale = ops.iter().any(|op| op.kind() == Some(XformOpKind::Scale));
    let inverse_translates = ops
        .iter()
        .filter(|op| is_translate(op.kind()) && op.is_inverse())
        .count();

    // The slots, in order: translate, pivot, then a rotate, an identity
    // translate and a scale where the stack has them, then the inverse pivot.
    const TRANSLATE: usize = 0;
    const PIVOT: usize = 1;
    let mut slots = vec![Some(XformOpKind::Translate), Some(XformOpKind::Translate)];
    let mut slot = |present: bool, kind: Option<XformOpKind>| {
        present.then(|| {
            slots.push(kind);
            slots.len() - 1
        })
    };
    let rotate_slot = slot(slot_rotate_kind.is_some(), slot_rotate_kind);
    let identity_slot = slot(inverse_translates > 1, Some(XformOpKind::Translate));
    let scale_slot = slot(has_scale, Some(XformOpKind::Scale));
    slots.push(Some(XformOpKind::Translate));
    let inverse_pivot_slot = slots.len() - 1;

    let mut matrices = vec![gf::Mat4d::IDENTITY; slots.len()];
    let mut remaining = ops.len();
    // One past the slot being folded into, so zero means the slots ran out.
    let mut current = slots.len();
    while remaining > 0 && current > 0 {
        let op = &ops[remaining - 1];
        let index = current - 1;
        if op.kind() != slots[index] || op.kind().is_none() {
            current -= 1;
            continue;
        }
        matrices[index] = matrices[index] * op.transform(time)?;
        remaining -= 1;

        // A rotate slot takes one op of the stack's rotate kind. A translate
        // slot closes on an inverse op, and the pivot slot once it undoes
        // the inverse pivot folded so far.
        let closes_translate = is_translate(slots[index])
            && (op.is_inverse() || (index == PIVOT && are_inverses(matrices[PIVOT], matrices[inverse_pivot_slot])));
        if slots[index] == rotate_kind || closes_translate {
            current -= 1;
        }
    }

    let mut reducible = remaining == 0;
    if identity_slot.is_some_and(|index| !is_identity(matrices[index])) {
        reducible = false;
    }
    // A stack that ran out while still in the inverse-pivot slot had only
    // plain translates there, which are the translation.
    if current == inverse_pivot_slot + 1 {
        matrices[TRANSLATE] = matrices[inverse_pivot_slot];
        matrices[inverse_pivot_slot] = gf::Mat4d::IDENTITY;
    }
    if !reducible || !are_inverses(matrices[PIVOT], matrices[inverse_pivot_slot]) {
        return Ok(None);
    }

    let identity = XformVectors::default();
    let rotation_order = rotate_kind.and_then(RotationOrder::from_op_kind).unwrap_or_default();
    Ok(Some(XformVectors {
        translation: matrices[TRANSLATE].extract_translation(),
        pivot: matrices[PIVOT].extract_translation().to_f32(),
        rotation: rotate_slot.map_or(identity.rotation, |index| {
            rotation_order.angles(matrices[index].extract_rotation())
        }),
        scale: scale_slot.map_or(identity.scale, |index| {
            let m = matrices[index];
            gf::vec3f(m[(0, 0)] as f32, m[(1, 1)] as f32, m[(2, 2)] as f32)
        }),
        rotation_order,
    }))
}

/// `true` when every row of `matrix` is within `1e-6` of the identity's.
fn is_identity(matrix: gf::Mat4d) -> bool {
    const TOLERANCE: f64 = 1e-6;
    (0..4).all(|r| {
        let distance_sq: f64 = (0..4)
            .map(|c| matrix[(r, c)] - gf::Mat4d::IDENTITY[(r, c)])
            .map(|d| d * d)
            .sum();
        distance_sq.sqrt() < TOLERANCE
    })
}

/// `true` when `a · b` is the identity.
fn are_inverses(a: gf::Mat4d, b: gf::Mat4d) -> bool {
    is_identity(a * b)
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, sdf};

    use super::{CommonXformOp, RotationOrder, XformVectors};
    use crate::SchemaError;
    use crate::geom::{Xform, XformCommonAPI, XformOpKind, XformOpPrecision, XformableExt, XformableSchema};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// An `Xform` at `path`, with the API over it.
    fn xform(stage: &usd::Stage, path: &str) -> Result<(Xform, XformCommonAPI)> {
        let xform = Xform::define(stage, path)?;
        let api = XformCommonAPI::from_prim_unchecked(xform.prim().clone());
        Ok((xform, api))
    }

    fn order(xform: &Xform) -> Result<Vec<String>> {
        let order = xform.xform_op_order()?.unwrap_or_default();
        Ok(order.iter().map(ToString::to_string).collect())
    }

    /// Adds an op of `kind` under `suffix`, holding `value`.
    fn add(xform: &Xform, kind: XformOpKind, suffix: Option<&str>, value: impl Into<sdf::Value>) -> Result {
        xform
            .add_xform_op(kind, XformOpPrecision::Float, suffix, false)?
            .set(value)
    }

    fn vectors(
        translation: [f64; 3],
        rotation: [f32; 3],
        scale: [f32; 3],
        pivot: [f32; 3],
        rotation_order: RotationOrder,
    ) -> XformVectors {
        XformVectors {
            translation: translation.into(),
            rotation: rotation.into(),
            scale: scale.into(),
            pivot: pivot.into(),
            rotation_order,
        }
    }

    fn assert_close(got: XformVectors, want: XformVectors) {
        let close = |a: f64, b: f64| (a - b).abs() < 1e-4;
        let all = [0, 1, 2]
            .iter()
            .all(|&i| close(got.translation[i], want.translation[i]));
        let floats = [
            (got.rotation, want.rotation),
            (got.scale, want.scale),
            (got.pivot, want.pivot),
        ];
        let rest = floats
            .iter()
            .all(|(a, b)| [0, 1, 2].iter().all(|&i| close(a[i] as f64, b[i] as f64)));
        assert!(
            all && rest && got.rotation_order == want.rotation_order,
            "{got:?} != {want:?}"
        );
    }

    /// A stack with no ops reads as the identity, and setting every vector
    /// builds the whole stack in the API's order.
    #[test]
    fn set_all_vectors() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let (x, api) = xform(&stage, "/X")?;
        assert!(api.is_compatible()?);
        assert_eq!(api.xform_vectors(None)?, XformVectors::default());

        let authored = vectors(
            [10.0, 20.0, 30.0],
            [30.0, 45.0, 60.0],
            [1.0, 2.0, 3.0],
            [0.0, 10.0, 0.0],
            RotationOrder::YXZ,
        );
        let commits = crate::tests::commits(&stage);
        api.set_xform_vectors(&authored, None)?;
        assert_eq!(commits.get(), 1, "the ops, their order and the values are one edit");
        assert_eq!(
            order(&x)?,
            [
                "xformOp:translate",
                "xformOp:translate:pivot",
                "xformOp:rotateYXZ",
                "xformOp:scale",
                "!invert!xformOp:translate:pivot"
            ]
        );
        assert_eq!(api.xform_vectors(None)?, authored);

        // Another rotation order is refused, at any time.
        let other = XformVectors {
            rotation_order: RotationOrder::ZYX,
            ..authored
        };
        assert!(matches!(
            api.set_xform_vectors(&other, usd::TimeCode::new(10.0)),
            Err(SchemaError::RotationOrderMismatch { .. })
        ));
        assert_eq!(api.xform_vectors(usd::TimeCode::new(10.0))?, authored);
        Ok(())
    }

    /// Each setter adds only its own op, in the API's order whatever order
    /// the setters run in.
    #[test]
    fn set_individual_ops() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let (x, api) = xform(&stage, "/X")?;

        api.set_translate(gf::vec3d(2.0, 3.0, 4.0), None)?;
        assert_eq!(order(&x)?, ["xformOp:translate"]);

        api.set_rotate(gf::vec3f(30.0, 45.0, 60.0), RotationOrder::XYZ, None)?;
        assert!(matches!(
            api.set_rotate(gf::vec3f(30.0, 45.0, 60.0), RotationOrder::ZYX, None),
            Err(SchemaError::RotationOrderMismatch { .. })
        ));
        assert_eq!(order(&x)?, ["xformOp:translate", "xformOp:rotateXYZ"]);

        api.set_pivot(gf::vec3f(100.0, 200.0, 300.0), usd::TimeCode::new(1.0))?;
        api.set_scale(gf::vec3f(1.5, 2.0, 4.5), usd::TimeCode::new(2.0))?;
        assert_eq!(
            order(&x)?,
            [
                "xformOp:translate",
                "xformOp:translate:pivot",
                "xformOp:rotateXYZ",
                "xformOp:scale",
                "!invert!xformOp:translate:pivot"
            ]
        );
        assert_eq!(
            api.xform_vectors(usd::TimeCode::new(1.0))?,
            vectors(
                [2.0, 3.0, 4.0],
                [30.0, 45.0, 60.0],
                [1.5, 2.0, 4.5],
                [100.0, 200.0, 300.0],
                RotationOrder::XYZ
            )
        );

        // Setting a vector again authors only its value.
        let commits = crate::tests::commits(&stage);
        api.set_translate(gf::vec3d(5.0, 6.0, 7.0), None)?;
        assert_eq!(commits.get(), 1);
        assert_eq!(api.xform_vectors(None)?.translation, gf::vec3d(5.0, 6.0, 7.0));
        Ok(())
    }

    /// A rotate op under a suffix still fits, and takes the rotation itself.
    #[test]
    fn rotate_op_with_suffix() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let (x, api) = xform(&stage, "/X")?;
        add(&x, XformOpKind::RotateXYZ, Some("spin"), gf::vec3f(1.0, 2.0, 3.0))?;
        assert!(api.is_compatible()?);

        let commits = crate::tests::commits(&stage);
        api.create_xform_ops(None, &[CommonXformOp::Rotate])?;
        assert_eq!(commits.get(), 0);

        api.set_rotate(gf::vec3f(10.0, 20.0, 30.0), RotationOrder::XYZ, None)?;
        assert_eq!(order(&x)?, ["xformOp:rotateXYZ:spin"]);
        assert!(!stage.attribute("/X.xformOp:rotateXYZ")?.is_defined()?);
        assert_eq!(api.xform_vectors(None)?.rotation, gf::vec3f(10.0, 20.0, 30.0));
        Ok(())
    }

    /// Creating ops declares them and orders them as one edit, and asks for
    /// nothing twice.
    #[test]
    fn create_ops_once() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let (x, api) = xform(&stage, "/X")?;
        let commits = crate::tests::commits(&stage);

        let ops = api.create_xform_ops(None, &[CommonXformOp::Pivot, CommonXformOp::Scale])?;
        assert_eq!(commits.get(), 1);
        assert!(ops.translate.is_none() && ops.rotate.is_none());
        assert!(ops.pivot.is_some() && ops.inverse_pivot.is_some() && ops.scale.is_some());
        assert_eq!(
            order(&x)?,
            [
                "xformOp:translate:pivot",
                "xformOp:scale",
                "!invert!xformOp:translate:pivot"
            ]
        );

        api.create_xform_ops(None, &[CommonXformOp::Pivot, CommonXformOp::Scale])?;
        assert_eq!(commits.get(), 1);
        Ok(())
    }

    /// The stacks the C++ tests list as incompatible: a kind the API has no
    /// slot for, or the right kinds out of order.
    #[test]
    fn incompatible_stacks() -> Result {
        use XformOpKind::{Orient, RotateX, RotateXZY, RotateYZX, RotateZXY, Scale, Transform, Translate};

        let stage = crate::tests::stage("anon.usda")?;
        let stacks: [&[XformOpKind]; 6] = [
            &[Orient],
            &[RotateX],
            &[Transform],
            &[Scale, RotateZXY],
            &[RotateYZX, Translate],
            &[Scale, Translate],
        ];
        for (index, kinds) in stacks.into_iter().enumerate() {
            let (x, api) = xform(&stage, &format!("/Bad{index}"))?;
            for &kind in kinds {
                x.add_xform_op(kind, XformOpPrecision::Double, None, false)?;
            }
            assert!(!api.is_compatible()?, "{kinds:?}");
            assert!(matches!(
                api.set_translate(gf::vec3d(1.0, 2.0, 3.0), None),
                Err(SchemaError::IncompatibleXformable { .. })
            ));
        }

        // An op after the inverse pivot is outside the pair.
        for (index, kind) in [Scale, RotateXZY, Translate].into_iter().enumerate() {
            let (x, api) = xform(&stage, &format!("/Outside{index}"))?;
            api.set_pivot(gf::vec3f(10.0, 20.0, 30.0), None)?;
            x.add_xform_op(kind, XformOpPrecision::Float, None, false)?;
            assert!(!api.is_compatible()?, "{kind:?}");
        }

        let untyped = XformCommonAPI::from_prim_unchecked(stage.define_prim("/Untyped")?);
        assert!(!untyped.is_compatible()?);
        Ok(())
    }

    /// A reset survives every op the API adds.
    #[test]
    fn reset_preserved() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let (x, api) = xform(&stage, "/World")?;
        api.set_reset_xform_stack(true)?;
        api.set_translate(gf::vec3d(10.0, 20.0, 30.0), None)?;
        assert_eq!(order(&x)?, ["!resetXformStack!", "xformOp:translate"]);

        api.set_rotate(gf::vec3f(10.0, 20.0, 30.0), RotationOrder::XYZ, None)?;
        api.set_scale(gf::vec3f(10.0, 20.0, 30.0), None)?;
        api.set_pivot(gf::vec3f(10.0, 20.0, 30.0), None)?;
        assert!(api.resets_xform_stack()?);
        assert_eq!(
            order(&x)?,
            [
                "!resetXformStack!",
                "xformOp:translate",
                "xformOp:translate:pivot",
                "xformOp:rotateXYZ",
                "xformOp:scale",
                "!invert!xformOp:translate:pivot"
            ]
        );
        Ok(())
    }

    /// A matrix stack factors into vectors that compose back to the matrix.
    #[test]
    fn matrix_decomposition() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let (x, x_api) = xform(&stage, "/X")?;
        x_api.set_xform_vectors(
            &vectors(
                [10.0, 20.0, 30.0],
                [30.0, 45.0, 60.0],
                [1.0, 2.0, 3.0],
                [0.0, 0.0, 0.0],
                RotationOrder::YXZ,
            ),
            None,
        )?;
        let matrix = x.local_transform(None)?;

        let (y, y_api) = xform(&stage, "/Y")?;
        y.make_matrix_xform()?.set(matrix)?;
        assert!(!y_api.is_compatible()?);
        let factored = y_api.xform_vectors(None)?;
        assert_eq!(factored.rotation_order, RotationOrder::XYZ);

        let (z, z_api) = xform(&stage, "/Z")?;
        z_api.set_xform_vectors(&factored, None)?;
        let composed = z.local_transform(None)?;
        for (got, want) in composed.0.iter().zip(matrix.0) {
            assert!((got - want).abs() < 1e-5, "{composed:?} != {matrix:?}");
        }
        Ok(())
    }

    /// The angles read back are those of the order answered, so authoring
    /// the vectors again makes the same transform.
    #[test]
    fn accumulation_keeps_order() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        for (index, order) in [
            RotationOrder::XYZ,
            RotationOrder::XZY,
            RotationOrder::YXZ,
            RotationOrder::YZX,
            RotationOrder::ZXY,
            RotationOrder::ZYX,
        ]
        .into_iter()
        .enumerate()
        {
            let (x, api) = xform(&stage, &format!("/Order{index}"))?;
            add(&x, XformOpKind::Translate, Some("myPivot"), gf::vec3f(1.0, 2.0, 3.0))?;
            add(&x, order.op_kind(), None, gf::vec3f(10.0, 20.0, 30.0))?;
            x.add_xform_op(XformOpKind::Translate, XformOpPrecision::Float, Some("myPivot"), true)?;
            assert!(!api.is_compatible()?);
            let want = vectors([0.0; 3], [10.0, 20.0, 30.0], [1.0; 3], [1.0, 2.0, 3.0], order);
            assert_close(api.xform_vectors_by_accumulation(None)?, want);
        }
        Ok(())
    }

    /// Stacks that do not fit the API but fold into its shape, as the C++
    /// tests list them.
    #[test]
    fn accumulation() -> Result {
        use XformOpKind::{RotateX, RotateXYZ, RotateY, RotateZ, RotateZYX, Scale, Translate};

        let stage = crate::tests::stage("anon.usda")?;
        let identity = XformVectors::default();
        let check = |x: &Xform, api: &XformCommonAPI, want: XformVectors| -> Result {
            assert!(!api.is_compatible()?, "{}", x.path());
            assert_close(api.xform_vectors_by_accumulation(None)?, want);
            Ok(())
        };

        for (name, kind, rotation) in [
            ("/RotX", RotateX, [45.0, 0.0, 0.0]),
            ("/RotY", RotateY, [0.0, 60.0, 0.0]),
            ("/RotZ", RotateZ, [0.0, 0.0, 115.0]),
        ] {
            let (x, api) = xform(&stage, name)?;
            add(&x, kind, None, rotation.iter().sum::<f32>())?;
            let want = XformVectors {
                rotation: rotation.into(),
                ..identity
            };
            check(&x, &api, want)?;
        }

        // A three-axis rotation in another order, about a pivot whose name
        // the API does not know.
        let (x, api) = xform(&stage, "/RotZYX")?;
        add(&x, Translate, Some("myRotatePivot"), gf::vec3f(-3.0, -2.0, -1.0))?;
        add(&x, RotateZYX, None, gf::vec3f(90.0, 60.0, 30.0))?;
        x.add_xform_op(Translate, XformOpPrecision::Float, Some("myRotatePivot"), true)?;
        let want = vectors(
            [0.0; 3],
            [90.0, 60.0, 30.0],
            [1.0; 3],
            [-3.0, -2.0, -1.0],
            RotationOrder::ZYX,
        );
        check(&x, &api, want)?;

        let (x, api) = xform(&stage, "/TranslationsOnly")?;
        for (suffix, value) in [
            ("transOne", [1.0, 2.0, 3.0]),
            ("transTwo", [9.0, 8.0, 7.0]),
            ("transThree", [10.0, 20.0, 30.0]),
            ("transFour", [90.0, 80.0, 70.0]),
        ] {
            add(&x, Translate, Some(suffix), gf::Vec3d::from(value))?;
        }
        let want = XformVectors {
            translation: gf::vec3d(110.0, 110.0, 110.0),
            ..identity
        };
        check(&x, &api, want)?;

        let (x, api) = xform(&stage, "/RotateWithPivot")?;
        add(&x, Translate, Some("rotatePivot"), gf::vec3f(3.0, 6.0, 9.0))?;
        add(&x, RotateXYZ, None, gf::vec3f(0.0, 45.0, 0.0))?;
        x.add_xform_op(Translate, XformOpPrecision::Float, Some("rotatePivot"), true)?;
        let want = XformVectors {
            rotation: gf::vec3f(0.0, 45.0, 0.0),
            pivot: gf::vec3f(3.0, 6.0, 9.0),
            ..identity
        };
        check(&x, &api, want)?;

        let (x, api) = xform(&stage, "/ScalesOnly")?;
        for (suffix, value) in [
            ("scaleOne", [1.0, 2.0, 3.0]),
            ("scaleTwo", [2.0, 4.0, 6.0]),
            ("scaleThree", [10.0, 20.0, 30.0]),
        ] {
            add(&x, Scale, Some(suffix), gf::Vec3f::from(value))?;
        }
        let want = XformVectors {
            scale: gf::vec3f(20.0, 160.0, 540.0),
            ..identity
        };
        check(&x, &api, want)?;

        let (x, api) = xform(&stage, "/ScalesWithPivot")?;
        add(&x, Translate, Some("scalePivot"), gf::vec3f(15.0, 25.0, 35.0))?;
        add(&x, Scale, Some("scaleOne"), gf::vec3f(10.0, 20.0, 30.0))?;
        add(&x, Scale, Some("scaleTwo"), gf::vec3f(0.5, 0.5, 0.5))?;
        x.add_xform_op(Translate, XformOpPrecision::Float, Some("scalePivot"), true)?;
        let want = XformVectors {
            scale: gf::vec3f(5.0, 10.0, 15.0),
            pivot: gf::vec3f(15.0, 25.0, 35.0),
            ..identity
        };
        check(&x, &api, want)
    }

    /// A stack that does not fold falls back to factoring its matrix: a
    /// scale listed outside the translate scales the translation too.
    #[test]
    fn accumulation_falls_back() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let (x, api) = xform(&stage, "/X")?;
        add(&x, XformOpKind::Scale, None, gf::vec3f(2.0, 2.0, 2.0))?;
        x.add_xform_op(XformOpKind::Translate, XformOpPrecision::Double, None, false)?
            .set(gf::vec3d(1.0, 2.0, 3.0))?;

        let by_accumulation = api.xform_vectors_by_accumulation(None)?;
        assert_eq!(by_accumulation, api.xform_vectors(None)?);
        assert_close(
            by_accumulation,
            vectors([2.0, 4.0, 6.0], [0.0; 3], [2.0; 3], [0.0; 3], RotationOrder::XYZ),
        );
        Ok(())
    }

    /// An order's rotation matrix is the one its rotate op applies.
    #[test]
    fn rotation_transform() {
        let angles = gf::vec3f(10.0, 20.0, 30.0);
        let radians = |degrees: f32| f64::from(degrees).to_radians();
        let (rx, ry, rz) = (
            gf::Mat4d::rotation_x(radians(angles.x)),
            gf::Mat4d::rotation_y(radians(angles.y)),
            gf::Mat4d::rotation_z(radians(angles.z)),
        );
        for (order, want) in [(RotationOrder::XYZ, rx * ry * rz), (RotationOrder::ZYX, rz * ry * rx)] {
            let got = order.rotation_transform(angles);
            for (g, w) in got.0.iter().zip(want.0) {
                assert!((g - w).abs() < 1e-12, "{order:?}: {got:?} != {want:?}");
            }
            assert_eq!(RotationOrder::from_op_kind(order.op_kind()), Some(order));
        }
        assert_eq!(RotationOrder::from_op_kind(XformOpKind::RotateX), None);
    }
}
