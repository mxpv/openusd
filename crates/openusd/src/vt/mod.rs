//! Value types (C++ `Vt`): [`Value`], the value an attribute or metadata field
//! holds (C++ `VtValue`), and [`Dictionary`] (C++ `VtDictionary`), with the
//! casts out of a value and the text C++ streams for one (`VtStreamOut`).
//!
//! C++ `VtValue` is type-erased, and `Sdf` registers its own value types into
//! it at runtime, so `Vt` sits below `Sdf`. [`Value`] is a closed enum, so it
//! names the `sdf` types it can hold, such as [`sdf::AssetPath`] and
//! [`sdf::ListOp`], directly.
//!
//! <https://openusd.org/dev/api/vt_page_front.html>

#[cfg(doc)]
use crate::sdf;

mod array;
mod coerce;
pub(crate) mod stream_out;
mod token_value;
mod value;

#[doc(inline)]
pub use crate::impl_token_value;
pub use value::{CastError, Dictionary, FromValue, FromValueCast, Value, ValueKind};
