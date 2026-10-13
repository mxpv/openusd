//! `UsdGeomXformable` — transformable prims and the `xformOpOrder` stack.
//!
//! An `Xformable` prim carries its local transform as an ordered stack of
//! `xformOp:*` attributes named by `xformOpOrder`: the first entry is the
//! most local (innermost in the matrix product), the last outermost. Two
//! sentinels are honored — `!invert!<op>` inverts an op's value, and
//! `!resetXformStack!` opts the prim out of inheriting its parent transform
//! and discards the ops listed before it (surfaced via
//! [`XformableExt::resets_xform_stack`]). Per-op values flow through
//! [`openusd::usd::AttributeQuery::get_at`]. Time-sampled ops interpolate per
//! AOUSD §12.5.

use openusd::Result;

use crate::SchemaError;

use openusd::gf;
use openusd::sdf;
use openusd::tf;
use openusd::usd;

use super::xform_op::{NS_XFORM_OP, TOKEN_INVERT_PREFIX, TOKEN_RESET_XFORM_STACK};
use super::{XformOp, XformOpKind, Xformable, XformableSchema, tokens};

/// The precision an xform op's value is authored at (C++
/// `UsdGeomXformOp::Precision`).
///
/// Together with the op's kind it fixes the op attribute's value type: a
/// `translate` is `double3`, `float3` or `half3`, a single-axis `rotateX` is
/// `double`, `float` or `half`, and an `orient` is `quatd`, `quatf` or
/// `quath`. A `transform` is always `matrix4d`, since Sdf has no
/// single-precision matrix type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum XformOpPrecision {
    /// `double`, `double3`, `quatd` — and the only precision a `transform`
    /// has, since its `matrix4d` is the one matrix type Sdf carries.
    Double,
    /// `float`, `float3`, `quatf`.
    Float,
    /// `half`, `half3`, `quath`.
    Half,
}

impl XformOpPrecision {
    /// The precision an op declared as `type_name` holds its value at (C++
    /// `UsdGeomXformOp::GetPrecisionFromValueTypeName`), or `None` for a type
    /// no op is declared as.
    pub fn from_value_type(type_name: &sdf::ValueTypeName) -> Option<Self> {
        [Self::Double, Self::Float, Self::Half].into_iter().find(|precision| {
            XformOpKind::ALL
                .iter()
                .any(|kind| kind.value_type(*precision) == *type_name)
        })
    }
}

/// A prim that carries a transform stack (C++ `UsdGeomXformable`). Inherits
/// [`XformableSchema`].
///
/// Reader methods compose the `xformOp:*` stack `xformOpOrder` names; the
/// `set_*` setters author one op and append it to `xformOpOrder`, so
/// successive calls build the canonical T·R·S ordering. Setters consume
/// `self` and return it, so they chain
/// (`xform.set_translate(t)?.set_rotate_y(d)?`).
///
/// # Example
///
/// ```
/// use openusd::{gf, usd};
/// use openusd_schemas::geom::{self, XformableExt};
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let prop = geom::Xform::define(&stage, "/Prop")?
///     .set_translate(gf::vec3d(1.0, 2.0, 3.0))?
///     .set_scale(gf::vec3f(2.0, 2.0, 2.0))?;
///
/// // Each setter appended its op to `xformOpOrder`.
/// let (ops, resets) = prop.ordered_xform_ops()?;
/// let names: Vec<&str> = ops.iter().map(geom::XformOp::name).collect();
/// assert_eq!(names, ["xformOp:translate", "xformOp:scale"]);
/// assert!(!resets);
///
/// // The last op listed applies to a point first: scale, then translate.
/// assert_eq!(
///     prop.local_transform(None)?,
///     gf::Mat4d::scale([2.0, 2.0, 2.0]) * gf::Mat4d::translation([1.0, 2.0, 3.0])
/// );
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
pub trait XformableExt: XformableSchema {
    /// The ops that make up the local transform, outermost first, and whether
    /// the stack resets its parent's transform (C++ `GetOrderedXformOps`).
    ///
    /// A `!resetXformStack!` entry sets the flag and discards every op listed
    /// before it. An entry naming no attribute on the prim is skipped.
    fn ordered_xform_ops(&self) -> Result<(Vec<XformOp>, bool)> {
        let prim = self.prim();
        let mut ops = Vec::new();
        let mut resets = false;
        for entry in self.xform_op_order()?.unwrap_or_default() {
            if entry == TOKEN_RESET_XFORM_STACK {
                resets = true;
                ops.clear();
                continue;
            }
            let (inverse, name) = match entry.strip_prefix(TOKEN_INVERT_PREFIX) {
                Some(name) => (true, name),
                None => (false, entry.as_str()),
            };
            let attr = prim.attribute(name);
            if attr.is_defined()? {
                ops.push(XformOp::new(&attr, inverse));
            }
        }
        Ok((ops, resets))
    }

    /// `true` when `xformOpOrder` lists `!resetXformStack!`, opting the prim
    /// out of inheriting its parent transform (C++ `GetResetXformStack`).
    fn resets_xform_stack(&self) -> Result<bool> {
        Ok(self
            .xform_op_order()?
            .is_some_and(|order| order.iter().any(|entry| entry == TOKEN_RESET_XFORM_STACK)))
    }

    /// Compose the stack into a single local-to-parent 4×4 matrix at `time`,
    /// where `None` is the default time (C++ `GetLocalTransformation`).
    /// [`gf::Mat4d::IDENTITY`] when no stack is authored. An op directly
    /// beside its own inverse is skipped along with it.
    fn local_transform(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<gf::Mat4d, SchemaError> {
        XformQuery::new(self)?.local_transform(time)
    }

    /// `true` when an op of the stack might have a different value at another
    /// time (C++ `UsdGeomXformable::TransformMightBeTimeVarying`). Unlike
    /// [`XformQuery::transform_might_be_time_varying`], it does not first ask
    /// whether the ops have an effect, as the two C++ methods differ.
    fn transform_might_be_time_varying(&self) -> Result<bool> {
        XformQuery::new(self)?.ops_might_be_time_varying()
    }

    /// Every time at which an op of the stack authors a sample, ascending
    /// (C++ `GetTimeSamples`).
    fn time_samples(&self) -> Result<Vec<f64>> {
        self.time_samples_in(..)
    }

    /// The times within `interval` at which an op of the stack authors a
    /// sample, ascending (C++ `GetTimeSamplesInInterval`).
    fn time_samples_in(&self, interval: impl Into<gf::Interval>) -> Result<Vec<f64>> {
        XformQuery::new(self)?.time_samples_in(interval)
    }

    /// Replace `xformOpOrder` with `order` verbatim (C++
    /// `SetXformOpOrderAttr`-style), rather than the per-op append the
    /// `set_*` helpers do.
    fn set_xform_op_order<I, S>(self, order: I) -> Result<Self>
    where
        Self: Sized,
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let order: Vec<String> = order.into_iter().map(Into::into).collect();
        self.create_xform_op_order_attr()?.set(sdf::Value::token_vec(order))?;
        Ok(self)
    }

    /// Empty `xformOpOrder`, so the prim has no local transform and inherits
    /// its parent's (C++ `ClearXformOpOrder`). The op attributes stay.
    fn clear_xform_op_order(self) -> Result<Self>
    where
        Self: Sized,
    {
        self.set_xform_op_order([""; 0])
    }

    /// Author whether the stack resets its parent's transform (C++
    /// `SetResetXformStack`).
    ///
    /// Setting it puts `!resetXformStack!` ahead of the ops `xformOpOrder`
    /// lists. Unsetting it drops the last `!resetXformStack!` together with
    /// every entry before it, which are the ones it was discarding. Either
    /// authors nothing when the stack is already as asked.
    fn set_reset_xform_stack(self, reset: bool) -> Result<Self>
    where
        Self: Sized,
    {
        let order = self.xform_op_order()?.unwrap_or_default();
        let last_reset = order.iter().rposition(|entry| entry == TOKEN_RESET_XFORM_STACK);
        let order = match (reset, last_reset) {
            (true, Some(_)) | (false, None) => return Ok(self),
            (true, None) => [tf::Token::from(TOKEN_RESET_XFORM_STACK)]
                .into_iter()
                .chain(order)
                .collect(),
            (false, Some(last)) => order[last + 1..].to_vec(),
        };
        self.xform_op_order_attr_builder()
            .set(sdf::Value::TokenVec(order))
            .build()?;
        Ok(self)
    }

    /// Declare an op of `kind` at `precision` and append it to the stack,
    /// without a value (C++ `AddXformOp`, which `AddTranslateOp` and the
    /// other per-kind methods call).
    ///
    /// `suffix` names one instance of the kind, as `pivot` does in
    /// `xformOp:translate:pivot`. With `inverse` set the stack lists the op
    /// behind `!invert!`: the entry applies the inverse of the value the op
    /// attribute holds, which the op listed without it authors.
    ///
    /// An op the stage already declares keeps the precision it was declared
    /// at. An entry `xformOpOrder` already lists is
    /// [`SchemaError::XformOpExists`]. The declaration and the new order are
    /// one edit.
    fn add_xform_op(
        &self,
        kind: XformOpKind,
        precision: XformOpPrecision,
        suffix: Option<&str>,
        inverse: bool,
    ) -> Result<XformOp, SchemaError> {
        let order = self.xform_op_order()?.unwrap_or_default();
        add_op(self.prim(), order, kind, precision, suffix, inverse)
    }

    /// The op of `kind` that `xformOpOrder` lists with this `suffix` and this
    /// `inverse` flag (C++ `GetXformOp`, which `GetTranslateOp` and the other
    /// per-kind methods call), or `None` when it lists no such entry or the
    /// prim has no attribute for it.
    fn xform_op(&self, kind: XformOpKind, suffix: Option<&str>, inverse: bool) -> Result<Option<XformOp>> {
        let entry = kind.op_name(suffix, inverse);
        if !self.xform_op_order()?.unwrap_or_default().contains(&entry) {
            return Ok(None);
        }
        let attr = self.prim().attribute(kind.op_name(suffix, false).as_str());
        Ok(attr.is_defined()?.then(|| XformOp::new(&attr, inverse)))
    }

    /// Reduce the stack to a single `xformOp:transform` and return that op
    /// (C++ `MakeMatrixXform`).
    ///
    /// `xformOpOrder` lists the one op and nothing else, so a reset goes with
    /// the other entries. The op keeps whatever value it already holds.
    ///
    /// The order is authored at the stage's edit target, and where a
    /// stronger site holds a default for `xformOpOrder` that order would not
    /// be the one read. That is [`SchemaError::XformOpOrderShadowed`], and
    /// nothing is authored. C++ refuses only where the stack still composes
    /// ops after it has emptied the order at the edit target. A stronger
    /// empty order lets it through, and it leaves the emptied order behind
    /// when it refuses.
    fn make_matrix_xform(&self) -> Result<XformOp, SchemaError> {
        let prim = self.prim();
        StackEdit::matrix(prim, None, None)?.commit(prim)?;
        let name = XformOpKind::Transform.op_name(None, false);
        Ok(XformOp::new(&prim.attribute(name.as_str()), false))
    }

    /// Author `xformOp:<op>` at `precision` and append it to the stack (C++
    /// `UsdGeomXformable::AddXformOp`). `op` is the op token, with or without
    /// the `xformOp:` prefix that [`xform_op_order`](XformableSchema::xform_op_order)
    /// hands back, and may carry a `:suffix` naming one instance of it
    /// (`"translate:pivot"`), which the per-op setters below have no
    /// spelling for. The declaration, the value and the order are one edit.
    ///
    /// An op the stage already declares keeps the precision it was declared
    /// at, as C++ does when the two disagree; only an op nothing declares is
    /// created at `precision`. `value` is then converted to whichever type
    /// the op holds, so a `float3` scale authors into an asset's `double3`
    /// op and that asset's precision survives the round trip.
    ///
    /// Two divergences from C++, which reports both as coding errors and
    /// this crate performs silently: converting the value at all, where
    /// `UsdGeomXformOp::Set` refuses one of another type outright; and
    /// re-authoring an op already in `xformOpOrder`, where `AddXformOp`
    /// authors nothing. A `transform` is `matrix4d` whatever `precision`
    /// asks for, which C++ also reports. An op token naming no kind is
    /// [`SchemaError::UnknownXformOp`], since it would contribute nothing to
    /// the stack.
    fn set_xform_op(
        self,
        op: &str,
        precision: XformOpPrecision,
        value: impl Into<sdf::Value>,
    ) -> Result<Self, SchemaError>
    where
        Self: Sized,
    {
        let name = tf::Token::from(op_attr_name(op));
        let token = name.split(':').nth(1).unwrap_or_default();
        let kind =
            XformOpKind::from_token(token).ok_or_else(|| SchemaError::UnknownXformOp { op: token.to_string() })?;
        let write = OpWrite {
            name: name.clone(),
            new_type: kind.value_type(precision),
            value: Some(value.into()),
        };
        let mut order = self.xform_op_order()?.unwrap_or_default();
        let order = (!order.contains(&name)).then(|| {
            order.push(name);
            order
        });
        StackEdit::prepare(self.prim(), vec![write], order, None)?.commit(self.prim())?;
        Ok(self)
    }

    /// Author `xformOp:translate` (`double3` when new) and append it to the
    /// stack.
    fn set_translate(self, value: gf::Vec3d) -> Result<Self, SchemaError>
    where
        Self: Sized,
    {
        self.set_xform_op("translate", XformOpPrecision::Double, value)
    }

    /// Author `xformOp:scale` (`float3` when new) and append it to the stack.
    fn set_scale(self, value: gf::Vec3f) -> Result<Self, SchemaError>
    where
        Self: Sized,
    {
        self.set_xform_op("scale", XformOpPrecision::Float, value)
    }

    /// Author `xformOp:rotateX` in degrees and append it to the stack.
    fn set_rotate_x(self, degrees: f32) -> Result<Self, SchemaError>
    where
        Self: Sized,
    {
        self.set_xform_op("rotateX", XformOpPrecision::Float, degrees)
    }

    /// Author `xformOp:rotateY` in degrees and append it to the stack.
    fn set_rotate_y(self, degrees: f32) -> Result<Self, SchemaError>
    where
        Self: Sized,
    {
        self.set_xform_op("rotateY", XformOpPrecision::Float, degrees)
    }

    /// Author `xformOp:rotateZ` in degrees and append it to the stack.
    fn set_rotate_z(self, degrees: f32) -> Result<Self, SchemaError>
    where
        Self: Sized,
    {
        self.set_xform_op("rotateZ", XformOpPrecision::Float, degrees)
    }

    /// Author `xformOp:rotateXYZ` (Euler degrees, applied X → Y → Z,
    /// `float3` when new) and append it to the stack.
    fn set_rotate_xyz(self, degrees: gf::Vec3f) -> Result<Self, SchemaError>
    where
        Self: Sized,
    {
        self.set_xform_op("rotateXYZ", XformOpPrecision::Float, degrees)
    }

    /// Author `xformOp:orient` (`quatf` when new, `(w, x, y, z)`) and append
    /// it.
    fn set_orient(self, q: gf::Quatf) -> Result<Self, SchemaError>
    where
        Self: Sized,
    {
        self.set_xform_op("orient", XformOpPrecision::Float, q)
    }

    /// Author `xformOp:transform` (`matrix4d`, row-major flattened) and
    /// append it — for an exact 4×4 that does not decompose into T·R·S.
    fn set_transform(self, matrix: gf::Mat4d) -> Result<Self, SchemaError>
    where
        Self: Sized,
    {
        self.set_xform_op("transform", XformOpPrecision::Double, matrix)
    }
}

/// Every [`XformableSchema`] carries the transform stack, so a view has these
/// wherever the generated accessors are.
impl<T: XformableSchema> XformableExt for T {}

impl Xformable {
    /// Whether an attribute named `name` can change a prim's local
    /// transform: `xformOpOrder`, or one in the namespace of the ops (C++
    /// `IsTransformationAffectedByAttrNamed`).
    pub fn affects_transform(name: &str) -> bool {
        name == tokens::XFORM_OP_ORDER || XformOp::is_xform_op(name)
    }
}

/// One prim's ordered ops, read once so the local transform can be evaluated
/// at many times without re-reading `xformOpOrder` (C++
/// `UsdGeomXformable::XformQuery`).
///
/// Each op reads its value through a [`usd::AttributeQuery`], which resolves
/// the value source once and revalidates it against later edits.
/// The op list and reset flag are fixed when the query is built: after an
/// edit to `xformOpOrder`, or to which op attributes exist, build a new one.
///
/// The [`Default`] query has no ops and does not reset the stack, which is
/// what a prim that is not `Xformable` contributes.
///
/// # Example
///
/// ```
/// use openusd::{gf, usd};
/// use openusd_schemas::geom::{self, XformableExt};
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let prop = geom::Xform::define(&stage, "/Prop")?.set_translate(gf::vec3d(0.0, 0.0, 0.0))?;
///
/// // Two time samples animate the op.
/// stage
///     .attribute("/Prop.xformOp:translate")?
///     .set_at(gf::vec3d(0.0, 0.0, 0.0), usd::TimeCode::new(1.0))?
///     .set_at(gf::vec3d(10.0, 0.0, 0.0), usd::TimeCode::new(11.0))?;
///
/// // One query reads `xformOpOrder` once and answers at every time.
/// let query = geom::XformQuery::new(&prop)?;
/// assert!(query.transform_might_be_time_varying()?);
/// assert_eq!(query.time_samples()?, [1.0, 11.0]);
/// for (time, x) in [(1.0, 0.0), (6.0, 5.0), (11.0, 10.0)] {
///     assert_eq!(
///         query.local_transform(usd::TimeCode::new(time))?,
///         gf::Mat4d::translation([x, 0.0, 0.0])
///     );
/// }
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
#[derive(Clone, Default)]
pub struct XformQuery {
    ops: Vec<XformOp>,
    resets_xform_stack: bool,
}

impl XformQuery {
    /// The query over `xformable`'s ordered ops.
    pub fn new(xformable: &(impl XformableExt + ?Sized)) -> Result<Self> {
        let (ops, resets_xform_stack) = xformable.ordered_xform_ops()?;
        Ok(Self {
            ops,
            resets_xform_stack,
        })
    }

    /// The query over `prim` when it is `Xformable`, and the empty
    /// [`Default`] query when it is not.
    pub fn for_prim(prim: &usd::Prim) -> Result<Self> {
        match Xformable::from_prim(prim.clone())? {
            Some(xformable) => Self::new(&xformable),
            None => Ok(Self::default()),
        }
    }

    /// The local transform at `time`, where `None` is the default time (C++
    /// `GetLocalTransformation`). Identity for an empty stack.
    ///
    /// An op directly beside its own inverse is skipped along with it. A
    /// singular `transform` paired with its inverse therefore still evaluates.
    pub fn local_transform(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<gf::Mat4d, SchemaError> {
        let time = time.into();
        let mut m = gf::Mat4d::IDENTITY;
        // Row-vector convention: the last listed op is most local and applies
        // first to a point. The walk runs from the back and grows the product
        // on the right.
        let mut rev = self.ops.iter().rev().peekable();
        while let Some(op) = rev.next() {
            if rev.peek().is_some_and(|next| op.cancels(next)) {
                rev.next();
                continue;
            }
            m = m * op.transform(time)?;
        }
        Ok(m)
    }

    /// `true` when the stack resets its parent's transform (C++
    /// `GetResetXformStack`).
    pub fn resets_xform_stack(&self) -> bool {
        self.resets_xform_stack
    }

    /// `true` when the ops might affect the transform: false for an empty
    /// stack or a lone op beside its own inverse, true for a stack that
    /// resets (C++ `TransformMightHaveEffect`). It recognizes only those
    /// forms and does not inspect the matrices.
    pub fn transform_might_have_effect(&self) -> bool {
        if self.resets_xform_stack {
            return true;
        }
        match self.ops.as_slice() {
            [] => false,
            [first, second] => !first.cancels(second),
            _ => true,
        }
    }

    /// `true` when the stack lists at least one op (C++
    /// `HasNonEmptyXformOpOrder`).
    pub fn has_ops(&self) -> bool {
        !self.ops.is_empty()
    }

    /// `true` when the transform might differ between times: the ops have
    /// an effect and one of them might vary (C++
    /// `TransformMightBeTimeVarying`).
    pub fn transform_might_be_time_varying(&self) -> Result<bool> {
        Ok(self.transform_might_have_effect() && self.ops_might_be_time_varying()?)
    }

    /// Every time at which an op authors a sample, ascending (C++
    /// `GetTimeSamples`).
    pub fn time_samples(&self) -> Result<Vec<f64>> {
        self.time_samples_in(..)
    }

    /// The times within `interval` at which an op authors a sample, ascending
    /// (C++ `GetTimeSamplesInInterval`).
    pub fn time_samples_in(&self, interval: impl Into<gf::Interval>) -> Result<Vec<f64>> {
        let attrs: Vec<usd::Attribute> = self.ops.iter().map(|op| op.attribute().clone()).collect();
        usd::Attribute::unioned_time_samples_in(&attrs, interval)
    }

    /// `true` when the attribute named `name` is one of the ops (C++
    /// `IsAttributeIncludedInLocalTransform`).
    pub fn affects_transform(&self, name: &str) -> bool {
        self.ops.iter().any(|op| op.name() == name)
    }

    /// `true` when any op might vary over time.
    fn ops_might_be_time_varying(&self) -> Result<bool> {
        for op in &self.ops {
            if op.might_be_time_varying()? {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

/// One op attribute a stack edit touches.
pub(super) struct OpWrite {
    /// The op attribute's name.
    pub name: tf::Token,
    /// The type the op is declared as where nothing declares it yet.
    pub new_type: sdf::ValueTypeName,
    /// The value to author on it, if any.
    pub value: Option<sdf::Value>,
}

/// Op attributes and an `xformOpOrder` to author on a prim as one edit,
/// checked against the stage and ready to queue.
///
/// An op the stage already declares keeps that declaration, and every value
/// has been converted to the type its op holds, so a value an op cannot hold
/// is refused before anything is queued.
///
/// One is prepared and applied inside a single call and never kept: what it
/// was checked against is the stage as it stood then.
pub(super) struct StackEdit {
    /// Each op to author: its name, the type it is declared as, and the
    /// value to give it, if any.
    ops: Vec<(tf::Token, sdf::ValueTypeName, Option<sdf::Value>)>,
    /// What replaces `xformOpOrder`, where the edit changes it.
    order: Option<Vec<tf::Token>>,
    /// The time the values are authored at.
    time: Option<usd::TimeCode>,
}

impl StackEdit {
    /// The edit that declares each of `writes` where nothing declares it and
    /// authors its value at `time`, and replaces `xformOpOrder` with `order`
    /// where one is given.
    ///
    /// A declaration is read as the raw spelling it was authored with, so one
    /// the type table does not know is refused by the conversion.
    pub(super) fn prepare(
        prim: &usd::Prim,
        writes: Vec<OpWrite>,
        order: Option<Vec<tf::Token>>,
        time: Option<usd::TimeCode>,
    ) -> Result<Self, SchemaError> {
        let mut ops = Vec::new();
        for write in writes {
            let declared = super::declared_type(&prim.attribute(write.name.as_str()))?;
            if declared.is_some() && write.value.is_none() {
                continue;
            }
            let type_name = declared.unwrap_or(write.new_type);
            let value = write.value.map(|value| type_name.coerce(value)).transpose()?;
            ops.push((write.name, type_name, value));
        }
        Ok(StackEdit { ops, order, time })
    }

    /// The edit that replaces the whole stack with one `xformOp:transform`,
    /// holding `matrix` at `time` where one is given and the value it
    /// already has otherwise.
    ///
    /// Refused with [`SchemaError::XformOpOrderShadowed`] where a stronger
    /// site holds a value for `xformOpOrder`, since the replacement would
    /// not be the order read.
    pub(super) fn matrix(
        prim: &usd::Prim,
        matrix: Option<gf::Mat4d>,
        time: Option<usd::TimeCode>,
    ) -> Result<Self, SchemaError> {
        if let Some(site) = prim.attribute(super::tokens::XFORM_OP_ORDER).shadowing_opinion()? {
            return Err(SchemaError::XformOpOrderShadowed {
                prim: prim.path().clone(),
                layer: site.layer,
            });
        }
        let name = XformOpKind::Transform.op_name(None, false);
        let write = OpWrite {
            name: name.clone(),
            new_type: XformOpKind::Transform.value_type(XformOpPrecision::Double),
            value: matrix.map(sdf::Value::from),
        };
        Self::prepare(prim, vec![write], Some(vec![name]), time)
    }

    /// Queue the edit of `prim` on `edit`'s transaction.
    pub(super) fn apply(self, edit: &usd::StageEdit, prim: &usd::Prim) -> Result<(), SchemaError> {
        for (name, type_name, value) in self.ops {
            let builder = prim.attribute_builder(name, type_name).custom(false);
            match value {
                Some(value) => builder.set_at(value, self.time),
                None => builder,
            }
            .in_edit(edit)
            .build()?;
        }
        if let Some(order) = self.order {
            Xformable::from_prim_unchecked(prim.clone())
                .xform_op_order_attr_builder()
                .set(sdf::Value::TokenVec(order))
                .in_edit(edit)
                .build()?;
        }
        Ok(())
    }

    /// Author the edit on `prim` as a transaction of its own. An edit with
    /// neither an op to author nor an order commits nothing.
    pub(super) fn commit(self, prim: &usd::Prim) -> Result<(), SchemaError> {
        if self.ops.is_empty() && self.order.is_none() {
            return Ok(());
        }
        prim.stage()
            .edit(|edit| -> Result<(), SchemaError> { self.apply(edit, prim) })
    }
}

/// Declare the op of `kind` on `prim` where nothing declares it and author
/// `order` with the op's entry appended as `xformOpOrder`, on the terms
/// [`XformableExt::add_xform_op`] states.
fn add_op(
    prim: &usd::Prim,
    mut order: Vec<tf::Token>,
    kind: XformOpKind,
    precision: XformOpPrecision,
    suffix: Option<&str>,
    inverse: bool,
) -> Result<XformOp, SchemaError> {
    let entry = kind.op_name(suffix, inverse);
    if order.contains(&entry) {
        return Err(SchemaError::XformOpExists { op: entry.to_string() });
    }
    order.push(entry);

    let name = kind.op_name(suffix, false);
    let op = XformOp::new(&prim.attribute(name.as_str()), inverse);
    let write = OpWrite {
        name,
        new_type: kind.value_type(precision),
        value: None,
    };
    StackEdit::prepare(prim, vec![write], Some(order), None)?.commit(prim)?;
    Ok(op)
}

/// The attribute name of `op`, which may already carry the `xformOp:`
/// prefix — `xform_op_order` hands back prefixed names, so one fed straight
/// back in must not be prefixed twice (C++ `_MakeNamespaced`).
fn op_attr_name(op: &str) -> String {
    match XformOp::is_xform_op(op) {
        true => op.to_string(),
        false => format!("{NS_XFORM_OP}{op}"),
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::{XformOpPrecision, XformQuery, XformableExt};
    use crate::SchemaError;
    use crate::geom::XformableSchema;
    use crate::geom::{Xform, XformOp, XformOpKind, Xformable};
    use openusd::Result;
    use openusd::gf;
    use openusd::sdf;
    use openusd::usd;

    /// An asset that declares an op at another precision keeps it: the
    /// setter converts the value rather than failing on the mismatch.
    #[test]
    fn scale_into_double_op() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?;
        stage.create_attribute("/X.xformOp:scale", sdf::ValueTypeName::DOUBLE3)?;

        x.set_scale(gf::vec3f(2.0, 2.0, 2.0))?;

        assert_eq!(
            stage.attribute("/X.xformOp:scale")?.type_name()?,
            Some(sdf::ValueTypeName::DOUBLE3),
            "the declared precision survives"
        );
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:scale", sdf::FieldKey::Default)?,
            Some(sdf::Value::Vec3d(gf::vec3d(2.0, 2.0, 2.0)))
        );
        Ok(())
    }

    /// The precision picks a new op's value type, as C++ `AddXformOp` does;
    /// a `transform` has only the one matrix spelling whatever is asked for.
    #[test]
    fn op_precision_selects_type() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        Xform::define(&stage, "/X")?
            .set_xform_op("scale", XformOpPrecision::Double, gf::vec3f(2.0, 2.0, 2.0))?
            .set_xform_op("rotateX", XformOpPrecision::Half, 90.0_f32)?
            .set_xform_op("orient", XformOpPrecision::Double, gf::Quatf::IDENTITY)?
            .set_xform_op("transform", XformOpPrecision::Half, gf::Mat4d::IDENTITY)?;

        let declared = |path: &str| stage.attribute(path)?.type_name();
        assert_eq!(declared("/X.xformOp:scale")?, Some(sdf::ValueTypeName::DOUBLE3));
        assert_eq!(declared("/X.xformOp:rotateX")?, Some(sdf::ValueTypeName::HALF));
        assert_eq!(declared("/X.xformOp:orient")?, Some(sdf::ValueTypeName::QUATD));
        assert_eq!(declared("/X.xformOp:transform")?, Some(sdf::ValueTypeName::MATRIX4D));

        // Each value converted to the precision its op was created at.
        let default = |path: &str| stage.field::<sdf::Value>(path, sdf::FieldKey::Default);
        assert_eq!(
            default("/X.xformOp:scale")?,
            Some(sdf::Value::Vec3d(gf::vec3d(2.0, 2.0, 2.0)))
        );
        assert_eq!(
            default("/X.xformOp:rotateX")?,
            Some(sdf::Value::Half(gf::f16::from_f32(90.0)))
        );
        assert_eq!(
            default("/X.xformOp:orient")?,
            Some(sdf::Value::Quatd(gf::Quatd::IDENTITY)),
            "a quaternion converts component-wise in (w, x, y, z) order"
        );
        Ok(())
    }

    /// A suffix names one instance of an op, not a different kind, so the op
    /// takes its kind's value type.
    #[test]
    fn suffix_keeps_kind() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?.set_xform_op(
            "translate:pivot",
            XformOpPrecision::Float,
            gf::vec3f(1.0, 2.0, 3.0),
        )?;

        assert_eq!(
            stage.attribute("/X.xformOp:translate:pivot")?.type_name()?,
            Some(sdf::ValueTypeName::FLOAT3)
        );
        assert_eq!(x.xform_op_order()?.expect("authored"), vec!["xformOp:translate:pivot"]);
        Ok(())
    }

    /// A token naming no op kind has no value type, so it is refused rather
    /// than authored into a stack that would evaluate it as identity. The
    /// `!invert!` sentinel has no authoring spelling and lands here too.
    #[test]
    fn unknown_op_rejected() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?;
        for op in ["bogusOp", "!invert!translate"] {
            let error = x
                .clone()
                .set_xform_op(op, XformOpPrecision::Float, gf::vec3f(1.0, 2.0, 3.0))
                .err()
                .unwrap_or_else(|| panic!("{op} was accepted"));
            assert!(matches!(error, SchemaError::UnknownXformOp { .. }), "{op}: {error:?}");
        }
        assert_eq!(x.xform_op_order()?, None, "nothing was appended to the stack");
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:bogusOp", sdf::FieldKey::Default)?,
            None,
            "and nothing was authored for it"
        );

        // A layer already declaring an attribute for the token does not make
        // the token an op kind, so the answer is the same.
        stage.create_attribute("/X.xformOp:bogusOp", sdf::ValueTypeName::FLOAT3)?;
        let error = x
            .set_xform_op("bogusOp", XformOpPrecision::Float, gf::vec3f(1.0, 2.0, 3.0))
            .err()
            .unwrap_or_else(|| panic!("a declared bogus op was accepted"));
        assert!(matches!(error, SchemaError::UnknownXformOp { .. }), "{error:?}");
        Ok(())
    }

    /// An op declared with a spelling the type table does not know has no
    /// kind to convert to, so the write is refused rather than treated as an
    /// op nothing declares.
    #[test]
    fn unregistered_op_type_rejected() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?;
        stage.create_attribute("/X.xformOp:scale", "double3d[]")?;

        let error = x
            .clone()
            .set_xform_op("scale", XformOpPrecision::Float, gf::vec3f(2.0, 2.0, 2.0))
            .err()
            .unwrap_or_else(|| panic!("the unregistered declaration was accepted"));
        assert!(matches!(error, SchemaError::Core(_)), "{error:?}");
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:scale", sdf::FieldKey::Default)?,
            None,
            "no value was authored"
        );
        assert_eq!(x.xform_op_order()?, None);
        Ok(())
    }

    /// A value the op cannot hold is refused before anything is authored, so
    /// no declaration is left for a later write at another precision to find
    /// and keep.
    #[test]
    fn failed_conversion_authors_nothing() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?;

        // 70000 is past the half range, so the conversion to `half3` fails.
        let error = x
            .clone()
            .set_xform_op("scale", XformOpPrecision::Half, gf::vec3f(70000.0, 1.0, 1.0))
            .err()
            .unwrap_or_else(|| panic!("the out-of-range value was accepted"));
        assert!(matches!(error, SchemaError::Core(_)), "{error:?}");
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:scale", sdf::FieldKey::TypeName)?,
            None,
            "no declaration was left behind"
        );
        assert_eq!(x.xform_op_order()?, None);

        // So the op takes the precision the next write asks for.
        x.set_xform_op("scale", XformOpPrecision::Double, gf::vec3f(2.0, 2.0, 2.0))?;
        assert_eq!(
            stage.attribute("/X.xformOp:scale")?.type_name()?,
            Some(sdf::ValueTypeName::DOUBLE3)
        );
        Ok(())
    }

    /// `xform_op_order` hands back prefixed names, so one fed straight back
    /// in names the same op rather than a doubly-prefixed one.
    #[test]
    fn prefixed_op_not_doubled() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?.set_xform_op(
            "xformOp:translate",
            XformOpPrecision::Double,
            gf::vec3d(1.0, 2.0, 3.0),
        )?;
        assert_eq!(x.xform_op_order()?.expect("authored"), vec!["xformOp:translate"]);
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:translate", sdf::FieldKey::Default)?,
            Some(sdf::Value::Vec3d(gf::vec3d(1.0, 2.0, 3.0)))
        );
        Ok(())
    }

    #[test]
    fn transform_attr_names() {
        for name in ["xformOpOrder", "xformOp:translate", "xformOp:rotateXYZ:pivot"] {
            assert!(Xformable::affects_transform(name), "{name}");
        }
        for name in ["points", "!invert!xformOp:translate", "xformOpOrders"] {
            assert!(!Xformable::affects_transform(name), "{name}");
        }
    }

    #[test]
    fn translate_appears_in_order() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?.set_translate(gf::vec3d(1.0, 2.0, 3.0))?;
        assert_eq!(x.xform_op_order()?.expect("authored"), vec!["xformOp:translate"]);
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:translate", sdf::FieldKey::Default)?,
            Some(sdf::Value::Vec3d(gf::vec3d(1.0, 2.0, 3.0)))
        );
        Ok(())
    }

    #[test]
    fn trs_preserves_insertion_order() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(1.0, 2.0, 3.0))?
            .set_rotate_y(90.0)?
            .set_scale(gf::vec3f(2.0, 2.0, 2.0))?;
        assert_eq!(
            x.xform_op_order()?.expect("authored"),
            vec!["xformOp:translate", "xformOp:rotateY", "xformOp:scale"]
        );
        Ok(())
    }

    #[test]
    fn local_to_parent_translate_unrotated() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(3.0, 5.0, 7.0))?
            .set_rotate_z(90.0)?;
        let m = x.local_transform(None)?;
        assert_eq!([m.0[12], m.0[13], m.0[14]], [3.0, 5.0, 7.0]);
        Ok(())
    }

    #[test]
    fn re_authoring_op_does_not_duplicate() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(1.0, 0.0, 0.0))?
            .set_translate(gf::vec3d(2.0, 0.0, 0.0))?;
        assert_eq!(x.xform_op_order()?.expect("authored"), vec!["xformOp:translate"]);
        Ok(())
    }

    #[test]
    fn rotate_xyz_authors_float3() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        Xform::define(&stage, "/X")?.set_rotate_xyz(gf::vec3f(30.0, 45.0, 60.0))?;
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:rotateXYZ", sdf::FieldKey::Default)?,
            Some(sdf::Value::Vec3f(gf::vec3f(30.0, 45.0, 60.0)))
        );
        Ok(())
    }

    #[test]
    fn orient_writes_quatf() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        Xform::define(&stage, "/X")?.set_orient(gf::quatf(1.0, 0.0, 0.0, 0.0))?;
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:orient", sdf::FieldKey::Default)?,
            Some(sdf::Value::quatf(1.0, 0.0, 0.0, 0.0))
        );
        Ok(())
    }

    #[test]
    fn transform_writes_matrix4d() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let m = gf::Mat4d([
            1.0, 0.0, 0.0, 0.0, //
            0.0, 1.0, 0.0, 0.0, //
            0.0, 0.0, 1.0, 0.0, //
            5.0, 0.0, 0.0, 1.0,
        ]);
        Xform::define(&stage, "/X")?.set_transform(m)?;
        match stage.field::<sdf::Value>("/X.xformOp:transform", sdf::FieldKey::Default)? {
            Some(sdf::Value::Matrix4d(v)) => assert_eq!(v[12], 5.0),
            other => panic!("expected gf::Mat4d, got {other:?}"),
        }
        Ok(())
    }

    /// Every entry of `got` is within rounding of `want`.
    pub(crate) fn assert_close(got: gf::Mat4d, want: gf::Mat4d) {
        for (g, w) in got.0.iter().zip(want.0) {
            assert!((g - w).abs() < 1e-9, "{got:?} != {want:?}");
        }
    }

    /// Each op directly beside its own inverse cancels out (C++
    /// `test_InverseOps`), suffixed ops included.
    #[test]
    fn inverse_ops_cancel() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(20.0, 30.0, 40.0))?
            .set_scale(gf::vec3f(2.0, 3.0, 4.0))?
            .set_rotate_x(30.0)?
            .set_xform_op("rotateXYZ:first", XformOpPrecision::Float, gf::vec3f(10.0, 20.0, 30.0))?
            .set_xform_op("rotateZYX:last", XformOpPrecision::Float, gf::vec3f(30.0, 60.0, 45.0))?;
        let mut order = Vec::new();
        for op in x.xform_op_order()?.unwrap_or_default() {
            order.push(op.to_string());
            order.push(format!("!invert!{op}"));
        }
        let x = x.set_xform_op_order(order)?;
        assert_close(x.local_transform(None)?, gf::Mat4d::IDENTITY);
        Ok(())
    }

    /// A singular `transform` beside its own inverse is skipped with it, but
    /// with an op between them the inverse has to be taken, and fails (C++
    /// `test_SingularTransformOp`).
    #[test]
    fn singular_pair_skipped() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let singular = gf::Mat4d([
            32.0, 8.0, 11.0, 17.0, //
            8.0, 20.0, 17.0, 23.0, //
            11.0, 17.0, 14.0, 26.0, //
            17.0, 23.0, 26.0, 2.0,
        ]);
        let x = Xform::define(&stage, "/X")?
            .set_transform(singular)?
            .set_translate(gf::vec3d(1.0, 1.0, 1.0))?
            .set_xform_op_order(["xformOp:transform", "xformOp:translate", "!invert!xformOp:transform"])?;
        let error = x.local_transform(None).expect_err("the lone inverse is singular");
        assert!(matches!(error, SchemaError::SingularTransform { .. }), "{error:?}");

        let x = x.set_xform_op_order(["xformOp:transform", "!invert!xformOp:transform"])?;
        assert_eq!(x.local_transform(None)?, gf::Mat4d::IDENTITY);
        Ok(())
    }

    /// An entry naming no attribute is skipped, and the rest of the stack
    /// still evaluates (C++ `test_Bug109853`).
    #[test]
    fn missing_op_skipped() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(1.0, 2.0, 3.0))?
            .set_xform_op_order(["xformOp:transform", "xformOp:translate"])?;
        let (ops, resets) = x.ordered_xform_ops()?;
        let names: Vec<_> = ops.iter().map(XformOp::op_name).collect();
        assert_eq!(names, vec!["xformOp:translate"]);
        assert!(!resets);
        assert_eq!(x.local_transform(None)?, gf::Mat4d::translation([1.0, 2.0, 3.0]));
        Ok(())
    }

    /// A reset past the front of the stack discards the ops listed before
    /// it, and still resets the parent transform.
    #[test]
    fn mid_stack_reset() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(1.0, 0.0, 0.0))?
            .set_xform_op("translate:after", XformOpPrecision::Double, gf::vec3d(0.0, 2.0, 0.0))?
            .set_xform_op_order(["xformOp:translate", "!resetXformStack!", "xformOp:translate:after"])?;
        assert!(x.resets_xform_stack()?);
        let (ops, resets) = x.ordered_xform_ops()?;
        assert!(resets);
        assert_eq!(ops.len(), 1);
        assert_eq!(x.local_transform(None)?, gf::Mat4d::translation([0.0, 2.0, 0.0]));
        Ok(())
    }

    /// Only the ops after the last reset count toward time variation (C++
    /// `test_MightBeTimeVarying`).
    #[test]
    fn might_be_time_varying() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?;
        assert!(!x.transform_might_be_time_varying()?);

        let x = x.set_translate(gf::vec3d(10.0, 20.0, 30.0))?;
        let op = stage.attribute("/X.xformOp:translate")?;
        assert!(!x.transform_might_be_time_varying()?);

        let op = op.set_at(gf::vec3d(20.0, 40.0, 60.0), usd::TimeCode::new(1.0))?;
        assert!(!x.transform_might_be_time_varying()?, "one sample does not vary");
        assert_eq!(x.time_samples()?, vec![1.0]);

        op.set_at(gf::vec3d(30.0, 60.0, 90.0), usd::TimeCode::new(2.0))?;
        assert!(x.transform_might_be_time_varying()?);
        assert!(XformQuery::new(&x)?.transform_might_be_time_varying()?);
        assert_eq!(x.time_samples()?, vec![1.0, 2.0]);

        let x = x.set_xform_op_order(["xformOp:translate", "!resetXformStack!"])?;
        assert!(!x.transform_might_be_time_varying()?);
        assert!(x.time_samples()?.is_empty());

        let x = x.set_xform_op_order(["!resetXformStack!", "xformOp:translate"])?;
        assert!(x.transform_might_be_time_varying()?);
        assert_eq!(x.time_samples()?, vec![1.0, 2.0]);
        Ok(())
    }

    /// The stack's samples are the union of its ops' (C++
    /// `test_GetTimeSamples`).
    #[test]
    fn time_samples_union() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(0.0, 0.0, 0.0))?
            .set_scale(gf::vec3f(1.0, 1.0, 1.0))?;
        assert!(x.time_samples()?.is_empty());

        stage
            .attribute("/X.xformOp:translate")?
            .set_at(gf::vec3d(10.0, 20.0, 30.0), usd::TimeCode::new(1.0))?
            .set_at(gf::vec3d(10.0, 20.0, 30.0), usd::TimeCode::new(3.0))?;
        stage
            .attribute("/X.xformOp:scale")?
            .set_at(gf::vec3f(1.0, 2.0, 3.0), usd::TimeCode::new(2.0))?
            .set_at(gf::vec3f(1.0, 2.0, 3.0), usd::TimeCode::new(4.0))?;

        assert_eq!(x.time_samples()?, vec![1.0, 2.0, 3.0, 4.0]);
        assert_eq!(x.time_samples_in(1.5..=3.2)?, vec![2.0, 3.0]);
        let query = XformQuery::new(&x)?;
        assert_eq!(query.time_samples()?, vec![1.0, 2.0, 3.0, 4.0]);
        assert_eq!(query.time_samples_in(1.5..=3.2)?, vec![2.0, 3.0]);
        Ok(())
    }

    /// A query answers what the prim does, and names the attributes it reads.
    #[test]
    fn query_matches_prim() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(1.0, 2.0, 3.0))?
            .set_rotate_z(90.0)?;
        let query = XformQuery::new(&x)?;
        assert_eq!(query.local_transform(None)?, x.local_transform(None)?);
        assert!(!query.resets_xform_stack());
        assert!(query.has_ops());
        assert!(query.transform_might_have_effect());
        assert!(query.affects_transform("xformOp:rotateZ"));
        assert!(!query.affects_transform("xformOp:scale"));

        // An op beside its own inverse has no effect; an empty stack neither.
        let x = x.set_xform_op_order(["xformOp:translate", "!invert!xformOp:translate"])?;
        assert!(!XformQuery::new(&x)?.transform_might_have_effect());
        let empty = XformQuery::for_prim(&stage.define_prim("/Untyped")?)?;
        assert!(!empty.has_ops());
        assert!(!empty.transform_might_have_effect());
        assert_eq!(empty.local_transform(None)?, gf::Mat4d::IDENTITY);
        Ok(())
    }

    /// A schema's fallback `xformOpOrder` is the stack when no layer authors
    /// one.
    #[test]
    fn fallback_op_order() -> Result<(), SchemaError> {
        let layer = |text: &str| sdf::Layer::from_bytes("pivot", text.as_bytes().to_vec()).expect("the layer parses");
        let manifest = layer(
            r#"#usda 1.0

def "PivotXform"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["Xform"]
}
"#,
        );
        let schematics = layer(
            r#"#usda 1.0

class PivotXform "PivotXform"
{
    uniform token[] xformOpOrder = ["!resetXformStack!", "xformOp:translate"]
}
"#,
        );
        let registry = crate::ALL
            .iter()
            .fold(usd::SchemaRegistry::builder(), |builder, family| {
                builder.register(family)
            })
            .family(usd::FamilySource {
                name: "pivot",
                manifest: &manifest,
                schematics: &schematics,
            })
            .build()
            .expect("registry builds");
        let stage = usd::Stage::builder().schema_registry(registry).in_memory("anon.usda")?;
        stage.define_prim("/P")?.set_type_name("PivotXform")?;
        stage
            .create_attribute("/P.xformOp:translate", sdf::ValueTypeName::DOUBLE3)?
            .set(gf::vec3d(1.0, 2.0, 3.0))?;

        let x = crate::geom::Xformable::get(&stage, "/P")?.expect("a PivotXform is Xformable");
        assert_eq!(
            x.xform_op_order()?.expect("authored"),
            vec!["!resetXformStack!", "xformOp:translate"]
        );
        assert!(x.resets_xform_stack()?);
        assert_eq!(x.ordered_xform_ops()?.0.len(), 1);
        assert_eq!(x.local_transform(None)?, gf::Mat4d::translation([1.0, 2.0, 3.0]));
        Ok(())
    }

    /// Adding an op declares it at the precision asked for, lists it, and
    /// authors no value, all as one edit.
    #[test]
    fn add_op_declares() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?;
        let commits = crate::tests::commits(&stage);

        let op = x.add_xform_op(XformOpKind::Translate, XformOpPrecision::Double, None, false)?;
        assert_eq!(commits.get(), 1);
        assert_eq!(op.name(), "xformOp:translate");
        assert_eq!(op.precision()?, Some(XformOpPrecision::Double));
        assert!(!op.attribute().has_authored_value()?);
        assert_eq!(x.xform_op_order()?.expect("authored"), vec!["xformOp:translate"]);
        assert_eq!(x.local_transform(None)?, gf::Mat4d::IDENTITY);
        Ok(())
    }

    /// An entry the stack already lists is refused, and nothing is authored.
    #[test]
    fn add_op_twice_errors() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?;
        x.add_xform_op(XformOpKind::Scale, XformOpPrecision::Float, None, false)?;

        let commits = crate::tests::commits(&stage);
        let again = x.add_xform_op(XformOpKind::Scale, XformOpPrecision::Float, None, false);
        assert!(matches!(again, Err(SchemaError::XformOpExists { op }) if op == "xformOp:scale"));
        assert_eq!(commits.get(), 0);

        // The same kind under a suffix is another op.
        x.add_xform_op(XformOpKind::Scale, XformOpPrecision::Float, Some("tip"), false)?;
        assert_eq!(
            x.xform_op_order()?.expect("authored"),
            vec!["xformOp:scale", "xformOp:scale:tip"]
        );
        Ok(())
    }

    /// An op the stage already declares keeps its precision.
    #[test]
    fn add_op_keeps_declared() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?;
        stage.create_attribute("/X.xformOp:translate", sdf::ValueTypeName::FLOAT3)?;

        let op = x.add_xform_op(XformOpKind::Translate, XformOpPrecision::Double, None, false)?;
        assert_eq!(op.precision()?, Some(XformOpPrecision::Float));
        // The value converts to the declared precision.
        op.set(gf::vec3d(1.0, 2.0, 3.0))?;
        assert_eq!(
            op.attribute().get::<sdf::Value>()?,
            Some(sdf::Value::Vec3f(gf::vec3f(1.0, 2.0, 3.0)))
        );
        Ok(())
    }

    /// A pivot listed on both sides of a scale, once inverted, scales about
    /// the pivot, and only the forward op takes a value.
    #[test]
    fn add_inverse_op() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?;
        let pivot = x.add_xform_op(XformOpKind::Translate, XformOpPrecision::Double, Some("pivot"), false)?;
        let scale = x.add_xform_op(XformOpKind::Scale, XformOpPrecision::Float, None, false)?;
        let unpivot = x.add_xform_op(XformOpKind::Translate, XformOpPrecision::Double, Some("pivot"), true)?;

        assert_eq!(
            x.xform_op_order()?.expect("authored"),
            vec![
                "xformOp:translate:pivot",
                "xformOp:scale",
                "!invert!xformOp:translate:pivot"
            ]
        );
        assert!(unpivot.is_inverse() && unpivot.has_suffix("pivot"));
        assert!(matches!(
            unpivot.set(gf::vec3d(1.0, 0.0, 0.0)),
            Err(SchemaError::InverseXformOp { .. })
        ));

        pivot.set(gf::vec3d(1.0, 0.0, 0.0))?;
        scale.set(gf::vec3f(2.0, 2.0, 2.0))?;
        assert_eq!(
            x.local_transform(None)?,
            gf::Mat4d::translation([-1.0, 0.0, 0.0])
                * gf::Mat4d::scale([2.0, 2.0, 2.0])
                * gf::Mat4d::translation([1.0, 0.0, 0.0])
        );
        Ok(())
    }

    /// An op is found by its kind, suffix and direction, and only while the
    /// stack lists that entry.
    #[test]
    fn xform_op_lookup() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?;
        x.add_xform_op(XformOpKind::Translate, XformOpPrecision::Double, Some("pivot"), false)?;
        x.add_xform_op(XformOpKind::RotateZ, XformOpPrecision::Float, None, true)?;

        let found = |kind, suffix, inverse| Ok::<_, SchemaError>(x.xform_op(kind, suffix, inverse)?.is_some());
        assert!(found(XformOpKind::Translate, Some("pivot"), false)?);
        assert!(!found(XformOpKind::Translate, None, false)?);
        assert!(!found(XformOpKind::Translate, Some("pivot"), true)?);
        assert!(found(XformOpKind::RotateZ, None, true)?);
        assert!(!found(XformOpKind::RotateZ, None, false)?);

        let x = x.clear_xform_op_order()?;
        assert!(x.xform_op(XformOpKind::RotateZ, None, true)?.is_none());
        assert!(stage.attribute("/X.xformOp:rotateZ")?.is_defined()?);
        Ok(())
    }

    /// Setting the reset puts it first, and unsetting it drops it along with
    /// the entries it was discarding.
    #[test]
    fn set_reset_stack() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(1.0, 2.0, 3.0))?
            .set_reset_xform_stack(true)?;
        assert_eq!(
            x.xform_op_order()?.expect("authored"),
            vec!["!resetXformStack!", "xformOp:translate"]
        );

        let commits = crate::tests::commits(&stage);
        let x = x.set_reset_xform_stack(true)?;
        assert_eq!(commits.get(), 0);

        let x = x.set_reset_xform_stack(false)?;
        assert_eq!(x.xform_op_order()?.expect("authored"), vec!["xformOp:translate"]);
        assert_eq!(commits.get(), 1);
        let x = x.set_reset_xform_stack(false)?;
        assert_eq!(commits.get(), 1);

        let x = x
            .set_xform_op_order(["xformOp:scale", "!resetXformStack!", "xformOp:translate"])?
            .set_reset_xform_stack(false)?;
        assert_eq!(x.xform_op_order()?.expect("authored"), vec!["xformOp:translate"]);
        Ok(())
    }

    /// A stack reduced to one matrix lists only the `transform` op.
    #[test]
    fn make_matrix_xform() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(1.0, 2.0, 3.0))?
            .set_scale(gf::vec3f(2.0, 2.0, 2.0))?
            .set_reset_xform_stack(true)?;

        let op = x.make_matrix_xform()?;
        assert_eq!(x.xform_op_order()?.expect("authored"), vec!["xformOp:transform"]);
        assert_eq!(op.precision()?, Some(XformOpPrecision::Double));
        assert!(!x.resets_xform_stack()?);

        let matrix = gf::Mat4d::translation([4.0, 5.0, 6.0]);
        op.set(matrix)?;
        assert_eq!(x.local_transform(None)?, matrix);
        // Reducing it again keeps the value the op holds.
        x.make_matrix_xform()?;
        assert_eq!(x.local_transform(None)?, matrix);
        Ok(())
    }

    const ORDERED: &str = "over \"X\"\n{\n    uniform token[] xformOpOrder = [\"xformOp:translate\"]\n}";
    const DEFINED: &str = "def Xform \"X\"\n{\n    double3 xformOp:translate = (1, 2, 3)\n}";

    /// A stronger layer's order would shadow the one a reduction authors, so
    /// the reduction is refused and the edit target is left as it was.
    #[test]
    fn matrix_xform_shadowed() -> Result<(), SchemaError> {
        let (_dir, stage) = crate::tests::layered(&[("strong.usda", ORDERED), ("weak.usda", DEFINED)])?;
        let weak = crate::tests::target_layer(&stage, "weak.usda")?;
        let before = crate::tests::layer_text(&stage, &weak);
        let commits = crate::tests::commits(&stage);

        let x = Xform::get(&stage, "/X")?.expect("Xform");
        let Err(SchemaError::XformOpOrderShadowed { prim, layer }) = x.make_matrix_xform() else {
            panic!("the order is shadowed");
        };
        assert_eq!(prim.as_str(), "/X");
        assert!(layer.ends_with("strong.usda"), "{layer}");
        assert_eq!(crate::tests::layer_text(&stage, &weak), before);
        assert_eq!(commits.get(), 0);
        Ok(())
    }

    /// The order is a default, read at the default time, so a stronger
    /// layer that holds only samples for it shadows nothing.
    #[test]
    fn matrix_xform_under_samples() -> Result<(), SchemaError> {
        let sampled = "over \"X\"\n{\n    uniform token[] xformOpOrder.timeSamples = { 1: [\"xformOp:translate\"] }\n}";
        let (_dir, stage) = crate::tests::layered(&[("strong.usda", sampled), ("weak.usda", DEFINED)])?;
        crate::tests::target_layer(&stage, "weak.usda")?;

        let x = Xform::get(&stage, "/X")?.expect("Xform");
        x.make_matrix_xform()?;
        assert_eq!(x.xform_op_order()?.expect("authored"), vec!["xformOp:transform"]);
        Ok(())
    }

    /// A weaker layer's order is replaced by the one authored above it.
    #[test]
    fn matrix_xform_over_weaker() -> Result<(), SchemaError> {
        let ordered = "def Xform \"X\"\n{\n    double3 xformOp:translate = (1, 2, 3)\n    \
                       uniform token[] xformOpOrder = [\"xformOp:translate\"]\n}";
        let (_dir, stage) = crate::tests::layered(&[("strong.usda", "over \"X\"\n{\n}"), ("weak.usda", ordered)])?;
        crate::tests::target_layer(&stage, "strong.usda")?;

        let x = Xform::get(&stage, "/X")?.expect("Xform");
        x.make_matrix_xform()?.set(gf::Mat4d::translation([4.0, 5.0, 6.0]))?;
        assert_eq!(x.xform_op_order()?.expect("authored"), vec!["xformOp:transform"]);
        assert_eq!(x.local_transform(None)?, gf::Mat4d::translation([4.0, 5.0, 6.0]));
        Ok(())
    }

    /// Only the types an op is declared as name a precision.
    #[test]
    fn precision_from_type() {
        use sdf::ValueTypeName as T;

        for (type_name, precision) in [
            (T::MATRIX4D, Some(XformOpPrecision::Double)),
            (T::QUATF, Some(XformOpPrecision::Float)),
            (T::HALF3, Some(XformOpPrecision::Half)),
            (T::TOKEN, None),
        ] {
            assert_eq!(
                XformOpPrecision::from_value_type(&type_name),
                precision,
                "{type_name:?}"
            );
        }
    }
}
