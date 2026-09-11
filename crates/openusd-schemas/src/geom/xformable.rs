//! `UsdGeomXformable` — transformable prims and the `xformOpOrder` stack.
//!
//! An `Xformable` prim carries its local transform as an ordered stack of
//! `xformOp:*` attributes named by `xformOpOrder`: the first entry is the
//! most local (innermost in the matrix product), the last outermost. Two
//! sentinels are honored — `!invert!<op>` inverts an op's value, and a
//! leading `!resetXformStack!` opts the prim out of inheriting its parent
//! transform (surfaced via [`XformableExt::resets_xform_stack`]). Per-op values
//! flow through [`openusd::usd::Attribute::get`], so time-sampled ops
//! interpolate per AOUSD §12.5.

use openusd::Result;

use crate::SchemaError;

use openusd::gf;
use openusd::sdf;
use openusd::tf;
use openusd::usd::{Prim, TimeCode};

use super::XformableSchema;
use super::tokens;

const TOKEN_INVERT_PREFIX: &str = "!invert!";
const TOKEN_RESET_XFORM_STACK: &str = "!resetXformStack!";
const NS_XFORM_OP: &str = "xformOp:";

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

/// A prim that carries a transform stack (C++ `UsdGeomXformable`). Inherits
/// [`XformableSchema`].
///
/// Reader methods compose the authored `xformOp:*` stack; the `set_*` setters
/// author one op and append it to `xformOpOrder`, so successive calls build
/// the canonical T·R·S ordering. Setters consume `self` and return it, so
/// they chain (`xform.set_translate(t)?.set_rotate_y(d)?`).
pub trait XformableExt: XformableSchema {
    /// The authored `xformOpOrder` token list, flattening any list-op
    /// authoring. `None` when unauthored (C++ `GetXformOpOrderAttr().Get`).
    fn xform_op_order(&self) -> Result<Option<Vec<String>>> {
        let attr = self.prim().path().append_property(tokens::XFORM_OP_ORDER)?;
        Ok(match self.prim().stage().field::<sdf::Value>(attr, "default")? {
            Some(sdf::Value::TokenVec(v)) => Some(v.into_iter().map(Into::into).collect()),
            Some(sdf::Value::StringVec(v)) => Some(v),
            Some(sdf::Value::TokenListOp(op)) => Some(op.flatten().into_iter().map(Into::into).collect()),
            Some(sdf::Value::StringListOp(op)) => Some(op.flatten()),
            _ => None,
        })
    }

    /// `true` when the prim lists `!resetXformStack!` as the first entry of
    /// `xformOpOrder`, opting out of inheriting its parent transform
    /// (C++ `GetResetXformStack`).
    fn resets_xform_stack(&self) -> Result<bool> {
        Ok(matches!(
            self.xform_op_order()?.as_deref().and_then(|s| s.first()),
            Some(s) if s == TOKEN_RESET_XFORM_STACK
        ))
    }

    /// Compose `xformOpOrder` into a single local-to-parent 4×4 matrix at
    /// `time`. [`gf::Matrix4d::IDENTITY`] when no stack is authored. Mirrors C++
    /// `ComputeLocalToParentTransform`.
    fn local_to_parent_transform(&self, time: impl Into<TimeCode>) -> Result<gf::Matrix4d, SchemaError> {
        let time = time.into();
        let Some(order) = self.xform_op_order()? else {
            return Ok(gf::Matrix4d::IDENTITY);
        };
        let mut m = gf::Matrix4d::IDENTITY;
        for (i, op_name) in order.iter().enumerate() {
            if op_name == TOKEN_RESET_XFORM_STACK {
                if i == 0 {
                    continue;
                }
                return Err(SchemaError::InvalidOpOrder {
                    prim: self.prim().path().clone(),
                    index: i,
                });
            }
            // Row-vector convention: the last listed op is most local
            // (applied first to a point), so each new op is prepended,
            // growing the cumulative matrix on the left.
            m = build_op_matrix(self.prim(), op_name, time)? * m;
        }
        Ok(m)
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

    /// Author `xformOp:<op>` at `precision` and append it to the stack (C++
    /// `UsdGeomXformable::AddXformOp`). `op` is the op token, with or without
    /// the `xformOp:` prefix that [`xform_op_order`](Self::xform_op_order)
    /// hands back, and may carry a `:suffix` naming one instance of it
    /// (`"translate:pivot"`), which the per-op setters below have no
    /// spelling for.
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
        author_xform_op(self.prim(), op, precision, value.into())?;
        append_op(self.prim(), op)?;
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
    fn set_transform(self, matrix: gf::Matrix4d) -> Result<Self, SchemaError>
    where
        Self: Sized,
    {
        self.set_xform_op("transform", XformOpPrecision::Double, matrix)
    }
}

/// Build the 4×4 contribution of a single xformOp (possibly `!invert!`-ed).
fn build_op_matrix(prim: &Prim, op_name: &str, time: TimeCode) -> Result<gf::Matrix4d, SchemaError> {
    let (inverted, base) = match op_name.strip_prefix(TOKEN_INVERT_PREFIX) {
        Some(stripped) => (true, stripped),
        None => (false, op_name),
    };

    let attr = prim.path().append_property(base)?;
    let Some(raw) = prim.stage().attribute(attr)?.get_at::<sdf::Value>(time)? else {
        return Ok(gf::Matrix4d::IDENTITY);
    };

    let kind = op_kind(base);

    let m = match kind {
        "translate" => gf::Matrix4d::translation(value_to_vec3_f64(&raw).unwrap_or([0.0, 0.0, 0.0])),
        "translateX" => gf::Matrix4d::translation([value_to_scalar_f64(&raw).unwrap_or(0.0), 0.0, 0.0]),
        "translateY" => gf::Matrix4d::translation([0.0, value_to_scalar_f64(&raw).unwrap_or(0.0), 0.0]),
        "translateZ" => gf::Matrix4d::translation([0.0, 0.0, value_to_scalar_f64(&raw).unwrap_or(0.0)]),
        "scale" => gf::Matrix4d::scale(value_to_vec3_f64(&raw).unwrap_or([1.0, 1.0, 1.0])),
        "scaleX" => gf::Matrix4d::scale([value_to_scalar_f64(&raw).unwrap_or(1.0), 1.0, 1.0]),
        "scaleY" => gf::Matrix4d::scale([1.0, value_to_scalar_f64(&raw).unwrap_or(1.0), 1.0]),
        "scaleZ" => gf::Matrix4d::scale([1.0, 1.0, value_to_scalar_f64(&raw).unwrap_or(1.0)]),
        "orient" => gf::Matrix4d::from_quat(value_to_quat_wxyz(&raw).unwrap_or([1.0, 0.0, 0.0, 0.0])),
        // Rotation ops stay in f64 end-to-end; xformOp:rotate* may be authored
        // as `float` or `double` per the precision system, and reading via f32
        // would truncate the double-authored case before the trig math runs.
        "rotateX" => gf::Matrix4d::rotation_x(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateY" => gf::Matrix4d::rotation_y(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateZ" => gf::Matrix4d::rotation_z(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateXYZ" | "rotateYXZ" | "rotateZXY" | "rotateXZY" | "rotateYZX" | "rotateZYX" => {
            let v = value_to_vec3_f64(&raw).unwrap_or([0.0, 0.0, 0.0]);
            let rx = gf::Matrix4d::rotation_x(v[0].to_radians());
            let ry = gf::Matrix4d::rotation_y(v[1].to_radians());
            let rz = gf::Matrix4d::rotation_z(v[2].to_radians());
            // Apply axes in the order spelled by `kind` (row-vector product).
            match kind {
                "rotateXYZ" => rx * ry * rz,
                "rotateYXZ" => ry * rx * rz,
                "rotateZXY" => rz * rx * ry,
                "rotateXZY" => rx * rz * ry,
                "rotateYZX" => ry * rz * rx,
                "rotateZYX" => rz * ry * rx,
                _ => unreachable!("kind guard above"),
            }
        }
        "transform" => match raw {
            sdf::Value::Matrix4d(m) => m,
            _ => gf::Matrix4d::IDENTITY,
        },
        _ => gf::Matrix4d::IDENTITY,
    };

    if inverted {
        m.inverse().ok_or_else(|| SchemaError::SingularTransform {
            op: op_name.to_string(),
        })
    } else {
        Ok(m)
    }
}

/// Author a single `xformOp:<kind>` attribute (does not touch
/// `xformOpOrder`), on the terms [`XformableExt::set_xform_op`] states.
///
/// An op the stage already declares keeps that declaration; one nothing
/// declares takes `precision`. The value is converted to whichever of the two
/// applies before the attribute is authored, so a value the op cannot hold
/// leaves the stage untouched rather than a declaration that a later write at
/// another precision would find and keep.
///
/// The op's kind is resolved whatever the stage declares, so a token naming
/// no kind is refused even where a layer already declares an attribute for
/// it. The declaration is read as the raw spelling it was authored with, so
/// one the type table does not know is refused by the conversion rather than
/// mistaken for an op nothing declares.
fn author_xform_op(prim: &Prim, op: &str, precision: XformOpPrecision, value: sdf::Value) -> Result<(), SchemaError> {
    let fallback = op_value_type(op, precision)?;
    let name = op_attr_name(op);
    let declared = match prim
        .attribute(name.as_str())
        .get_metadata::<tf::Token>(sdf::FieldKey::TypeName.as_str())?
    {
        Some(token) => sdf::ValueTypeName::from(token),
        None => fallback,
    };
    let value = declared.coerce(value)?;
    prim.create_attribute(name, declared)?.set_custom(false)?.set(value)?;
    Ok(())
}

/// The attribute name of `op`, which may already carry the `xformOp:`
/// prefix — `xform_op_order` hands back prefixed names, so one fed straight
/// back in must not be prefixed twice (C++ `_MakeNamespaced`).
fn op_attr_name(op: &str) -> String {
    match op.starts_with(NS_XFORM_OP) {
        true => op.to_string(),
        false => format!("{NS_XFORM_OP}{op}"),
    }
}

/// The op token of `name`, without the `xformOp:` prefix and without the
/// `:suffix` that names one instance of the op rather than a kind of its own.
fn op_kind(name: &str) -> &str {
    let after_ns = name.strip_prefix(NS_XFORM_OP).unwrap_or(name);
    after_ns.split(':').next().unwrap_or(after_ns)
}

/// The value type `op` holds at `precision` (C++
/// `UsdGeomXformOp::GetValueTypeName`); a token naming no op kind has none.
// TODO: the op vocabulary is spelled here and again in `build_op_matrix`.
// C++ parses the token into one `XformOp::Type` that every switch keys off;
// an `XformOpKind` enum parsed once — taking the `!invert!` and
// `!resetXformStack!` sentinels with it, which have no authoring spelling
// today — would replace both string matches.
fn op_value_type(op: &str, precision: XformOpPrecision) -> Result<sdf::ValueTypeName, SchemaError> {
    use XformOpPrecision as P;

    Ok(match op_kind(op) {
        // A matrix has only the one precision in Sdf, which C++ reports when
        // another is asked for and this crate accepts silently.
        "transform" => sdf::ValueTypeName::MATRIX4D,
        "orient" => match precision {
            P::Double => sdf::ValueTypeName::QUATD,
            P::Float => sdf::ValueTypeName::QUATF,
            P::Half => sdf::ValueTypeName::QUATH,
        },
        "translateX" | "translateY" | "translateZ" | "scaleX" | "scaleY" | "scaleZ" | "rotateX" | "rotateY"
        | "rotateZ" => match precision {
            P::Double => sdf::ValueTypeName::DOUBLE,
            P::Float => sdf::ValueTypeName::FLOAT,
            P::Half => sdf::ValueTypeName::HALF,
        },
        "translate" | "scale" | "rotateXYZ" | "rotateXZY" | "rotateYXZ" | "rotateYZX" | "rotateZXY" | "rotateZYX" => {
            match precision {
                P::Double => sdf::ValueTypeName::DOUBLE3,
                P::Float => sdf::ValueTypeName::FLOAT3,
                P::Half => sdf::ValueTypeName::HALF3,
            }
        }
        other => {
            return Err(SchemaError::UnknownXformOp { op: other.to_string() });
        }
    })
}

/// Append `op` to `xformOpOrder`, de-duplicating re-authored ops.
fn append_op(prim: &Prim, op: &str) -> Result<()> {
    prim.append_to_uniform_token_array(tokens::XFORM_OP_ORDER, op_attr_name(op))?;
    Ok(())
}

fn value_to_scalar_f64(v: &sdf::Value) -> Option<f64> {
    match v {
        sdf::Value::Double(d) => Some(*d),
        sdf::Value::Float(f) => Some(*f as f64),
        sdf::Value::Half(h) => Some(h.to_f32() as f64),
        sdf::Value::Int(i) => Some(*i as f64),
        sdf::Value::Int64(i) => Some(*i as f64),
        _ => None,
    }
}

fn value_to_vec3_f64(v: &sdf::Value) -> Option<[f64; 3]> {
    match v {
        sdf::Value::Vec3d(a) => Some(<[f64; 3]>::from(*a)),
        sdf::Value::Vec3f(a) => Some([a.x as f64, a.y as f64, a.z as f64]),
        sdf::Value::Vec3h(a) => Some([a.x.to_f32() as f64, a.y.to_f32() as f64, a.z.to_f32() as f64]),
        _ => None,
    }
}

fn value_to_quat_wxyz(v: &sdf::Value) -> Option<[f64; 4]> {
    match v {
        sdf::Value::Quatd(q) => Some(<[f64; 4]>::from(*q)),
        sdf::Value::Quatf(q) => Some([q.w as f64, q.x as f64, q.y as f64, q.z as f64]),
        sdf::Value::Quath(q) => Some([
            q.w.to_f32() as f64,
            q.x.to_f32() as f64,
            q.y.to_f32() as f64,
            q.z.to_f32() as f64,
        ]),
        _ => None,
    }
}

/// Every [`XformableSchema`] carries the transform stack, so a view has these
/// wherever the generated accessors are.
impl<T: XformableSchema> XformableExt for T {}

#[cfg(test)]
mod tests {
    use super::{XformOpPrecision, XformableExt};
    use crate::SchemaError;
    use crate::geom::Xform;
    use openusd::Result;
    use openusd::gf;
    use openusd::sdf;

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
            .set_xform_op("transform", XformOpPrecision::Half, gf::Matrix4d::IDENTITY)?;

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
        assert_eq!(x.xform_op_order()?, Some(vec!["xformOp:translate:pivot".to_string()]));
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
        assert_eq!(x.xform_op_order()?, Some(vec!["xformOp:translate".to_string()]));
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:translate", sdf::FieldKey::Default)?,
            Some(sdf::Value::Vec3d(gf::vec3d(1.0, 2.0, 3.0)))
        );
        Ok(())
    }

    #[test]
    fn translate_appears_in_order() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?.set_translate(gf::vec3d(1.0, 2.0, 3.0))?;
        assert_eq!(x.xform_op_order()?, Some(vec!["xformOp:translate".to_string()]));
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
            x.xform_op_order()?,
            Some(vec![
                "xformOp:translate".to_string(),
                "xformOp:rotateY".to_string(),
                "xformOp:scale".to_string(),
            ])
        );
        Ok(())
    }

    #[test]
    fn local_to_parent_translate_unrotated() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(3.0, 5.0, 7.0))?
            .set_rotate_z(90.0)?;
        let m = x.local_to_parent_transform(0.0)?;
        assert_eq!([m.0[12], m.0[13], m.0[14]], [3.0, 5.0, 7.0]);
        Ok(())
    }

    #[test]
    fn re_authoring_op_does_not_duplicate() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate(gf::vec3d(1.0, 0.0, 0.0))?
            .set_translate(gf::vec3d(2.0, 0.0, 0.0))?;
        assert_eq!(x.xform_op_order()?, Some(vec!["xformOp:translate".to_string()]));
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
        let m = gf::Matrix4d([
            1.0, 0.0, 0.0, 0.0, //
            0.0, 1.0, 0.0, 0.0, //
            0.0, 0.0, 1.0, 0.0, //
            5.0, 0.0, 0.0, 1.0,
        ]);
        Xform::define(&stage, "/X")?.set_transform(m)?;
        match stage.field::<sdf::Value>("/X.xformOp:transform", sdf::FieldKey::Default)? {
            Some(sdf::Value::Matrix4d(v)) => assert_eq!(v[12], 5.0),
            other => panic!("expected gf::Matrix4d, got {other:?}"),
        }
        Ok(())
    }
}
