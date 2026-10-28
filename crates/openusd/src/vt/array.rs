//! The scalar/array pairing of the attribute value kinds (C++ `VtIsArray`,
//! `VtArray::ElementType`), and what it answers about a [`Value`].

use super::{Value, ValueKind};

/// The scalar/array pairing of the attribute kinds, written once.
macro_rules! array_pairs {
    ($($scalar:ident => $array:ident),* $(,)?) => {
        impl ValueKind {
            /// The kind of an array of this scalar kind; `None` for `Opaque`,
            /// for an array kind, and for every kind no attribute holds.
            pub const fn array_kind(self) -> Option<ValueKind> {
                match self {
                    $(ValueKind::$scalar => Some(ValueKind::$array),)*
                    _ => None,
                }
            }

            /// The element kind of this array kind; `None` for a scalar and for
            /// every kind that is not an attribute array (`PathVec`, `ValueVec`
            /// and `LayerOffsetVec` hold metadata, not attribute values).
            pub const fn element_kind(self) -> Option<ValueKind> {
                match self {
                    $(ValueKind::$array => Some(ValueKind::$scalar),)*
                    _ => None,
                }
            }

            /// The empty array of an array kind.
            pub(crate) fn empty_array(self) -> Option<Value> {
                match self {
                    $(ValueKind::$array => Some(Value::$array(Vec::new())),)*
                    _ => None,
                }
            }
        }

        impl Value {
            /// How many elements an attribute array holds, which
            /// [`array_len`](Value::array_len) answers for every array.
            pub(super) fn attribute_array_len(&self) -> Option<usize> {
                match self {
                    $(Value::$array(items) => Some(items.len()),)*
                    _ => None,
                }
            }

            /// The attribute array made of this one's elements at `positions`,
            /// in the order given, a position repeated as often as it is
            /// named.
            ///
            /// `None` when this value is not an attribute array, or when a
            /// position lies past its end.
            ///
            // TODO(perf): collecting through `Option` hides the iterator's
            // length, so the output grows by doubling. A caller that knows
            // every position is in range could gather into a vector sized
            // up front.
            pub fn gather(&self, positions: impl IntoIterator<Item = usize>) -> Option<Value> {
                match self {
                    $(Value::$array(items) => positions
                        .into_iter()
                        .map(|at| items.get(at).cloned())
                        .collect::<Option<Vec<_>>>()
                        .map(Value::$array),)*
                    _ => None,
                }
            }
        }
    };
}

array_pairs! {
    Bool => BoolVec,
    Uchar => UcharVec,
    Int => IntVec,
    Uint => UintVec,
    Int64 => Int64Vec,
    Uint64 => Uint64Vec,
    Half => HalfVec,
    Float => FloatVec,
    Double => DoubleVec,
    TimeCode => TimeCodeVec,
    String => StringVec,
    Token => TokenVec,
    AssetPath => AssetPathVec,
    PathExpression => PathExpressionVec,
    Vec2i => Vec2iVec,
    Vec2h => Vec2hVec,
    Vec2f => Vec2fVec,
    Vec2d => Vec2dVec,
    Vec3i => Vec3iVec,
    Vec3h => Vec3hVec,
    Vec3f => Vec3fVec,
    Vec3d => Vec3dVec,
    Vec4i => Vec4iVec,
    Vec4h => Vec4hVec,
    Vec4f => Vec4fVec,
    Vec4d => Vec4dVec,
    Quath => QuathVec,
    Quatf => QuatfVec,
    Quatd => QuatdVec,
    Matrix2d => Matrix2dVec,
    Matrix3d => Matrix3dVec,
    Matrix4d => Matrix4dVec,
}
