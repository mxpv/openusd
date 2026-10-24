//! What a dome light adds to its generated view: turning its texture to the
//! stage's up axis.

use openusd::usd::SchemaBase;

use super::{DomeLight, tokens};
use crate::SchemaError;
use crate::geom::{self, XformOpKind, XformOpPrecision, XformableExt, XformableSchema};

impl DomeLight {
    /// Turn the dome so its texture's up, `+Y`, is the stage's up axis (C++
    /// `UsdLuxDomeLight::OrientToStageUpAxis`).
    ///
    /// On a `Z`-up stage, a float `xformOp:rotateX:orientToStageUpAxis` of
    /// 90 degrees joins the op order, unless the stack already holds an op
    /// of that name, inverted or not. The declaration, the value and the
    /// order are one edit, and an op a layer already declares at another
    /// precision takes 90 at its own. A `Y`-up stage needs nothing.
    ///
    /// An `upAxis` token that names neither axis is the error
    /// [`geom::stage_up_axis`] gives. An entry the order lists but the stack
    /// skips, one before a `!resetXformStack!` or one no attribute declares,
    /// is [`SchemaError::XformOpExists`].
    pub fn orient_to_stage_up_axis(&self) -> Result<(), SchemaError> {
        if geom::stage_up_axis(self.prim().stage())? != geom::UpAxis::Z {
            return Ok(());
        }
        let name = XformOpKind::RotateX.op_name(Some(tokens::ORIENT_TO_STAGE_UP_AXIS), false);
        let (ops, _) = self.ordered_xform_ops()?;
        if ops.iter().any(|op| op.name() == name.as_str()) {
            return Ok(());
        }
        let order = self.xform_op_order()?.unwrap_or_default();
        if order.contains(&name) {
            return Err(SchemaError::XformOpExists { op: name.to_string() });
        }
        self.clone().set_xform_op(&name, XformOpPrecision::Float, 90.0f32)?;
        Ok(())
    }
}
