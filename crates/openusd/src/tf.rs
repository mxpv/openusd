//! Tools Foundation (C++ `Tf`): foundational utility types shared across the
//! crate. [`Token`], the interned-identifier string (C++ `TfToken`),
//! [`is_valid_identifier`], the rule a declared name is checked against, and
//! the crate's own file-replacing writer (C++ `TfSafeOutputFile`).

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::convert::Infallible;
use std::error;
use std::fmt::{self, Write as _};
use std::fs;
use std::hash::{Hash, Hasher};
use std::io;
use std::iter;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::process;
use std::str::FromStr;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

/// An immutable identifier string.
///
/// Tokens name prims, properties, and variants, and carry the values of
/// `token`-typed attributes and metadata such as `typeName` and `kind`.
/// Mirrors C++ [`TfToken`](https://openusd.org/dev/api/class_tf_token.html):
/// the text is immutable, and tokens holding equal text compare and hash equal.
///
/// A compile-time token built with [`new`](Token::new) borrows a `&'static str`
/// and allocates nothing — the analog of `TfToken`'s immortal tokens, usable in
/// `const` (`const KIND: Token = Token::new("Xform")`). A runtime token built
/// from owned text (`from`) holds a shared `Arc<str>`, so cloning bumps a
/// refcount rather than copying. A `Token` is a distinct type, not a string:
/// read its text with [`as_str`](Token::as_str) and convert back with
/// `String::from`.
#[derive(Clone)]
pub struct Token(Repr);

/// The two token storages — a static literal or refcounted runtime text. Equal
/// text compares and hashes equal regardless of which storage holds it (see the
/// manual [`PartialEq`] / [`Hash`] on [`Token`]).
#[derive(Clone)]
enum Repr {
    Static(&'static str),
    Shared(Arc<str>), // TODO(perf): intern shared tokens in a global table for O(1) equality, like TfToken.
}

impl Token {
    /// Creates a compile-time token from a string literal — no allocation, and
    /// usable in `const` context.
    pub const fn new(text: &'static str) -> Self {
        Token(Repr::Static(text))
    }

    /// Borrows the token's text.
    pub fn as_str(&self) -> &str {
        match &self.0 {
            Repr::Static(s) => s,
            Repr::Shared(s) => s,
        }
    }
}

impl Default for Token {
    fn default() -> Self {
        Token(Repr::Static(""))
    }
}

/// Tokens read as their text, like `String` derefs to `str`: `str` methods
/// (`starts_with`, `strip_prefix`, …) apply directly, and a `&Token` coerces to
/// `&str` where a name is expected.
impl Deref for Token {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<str> for Token {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

/// A token borrows as its text. It hashes and compares by that text, so a
/// set or map keyed by tokens can be searched with a `&str`.
impl Borrow<str> for Token {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl From<&str> for Token {
    fn from(text: &str) -> Self {
        Token(Repr::Shared(Arc::from(text)))
    }
}

impl From<String> for Token {
    fn from(text: String) -> Self {
        Token(Repr::Shared(Arc::from(text)))
    }
}

impl From<&String> for Token {
    fn from(text: &String) -> Self {
        Token(Repr::Shared(Arc::from(text.as_str())))
    }
}

impl From<&Token> for Token {
    fn from(token: &Token) -> Self {
        token.clone()
    }
}

impl From<Token> for String {
    fn from(token: Token) -> Self {
        token.as_str().to_owned()
    }
}

/// Parsing a token is infallible: any string is a valid token. Lets callers
/// that decode text generically (e.g. the USDA parser's `parse_token::<T>`)
/// produce a `Token` without an intermediate `String`.
impl FromStr for Token {
    type Err = Infallible;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        Ok(Token::from(text))
    }
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for Token {}

impl PartialEq<str> for Token {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&str> for Token {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl PartialEq<Token> for str {
    fn eq(&self, other: &Token) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<Token> for &str {
    fn eq(&self, other: &Token) -> bool {
        *self == other.as_str()
    }
}

impl Hash for Token {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl PartialOrd for Token {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Token {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Token {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

/// A file written beside its destination and renamed over it once complete
/// (C++ `TfSafeOutputFile`). The destination is therefore never a
/// half-written file, and a file a reader holds a view of is never written
/// into. A destination that is a symbolic link is resolved first, so the
/// file the link reaches is what gets replaced. Dropped without
/// [`persist`](Self::persist), the file is removed.
pub(crate) struct SafeOutputFile {
    destination: PathBuf,
    path: PathBuf,
    /// Taken by [`persist`](Self::persist), which closes the handle before
    /// the rename.
    file: Option<fs::File>,
    persisted: bool,
}

impl SafeOutputFile {
    /// Creates the file beside `destination`.
    ///
    /// The replacement keeps the destination's permissions, and nothing
    /// reads the file under wider access than the destination allows in the
    /// meantime. On Unix a destination that exists lends its mode at
    /// [`persist`](Self::persist), and until then the file is readable by its
    /// owner alone. On Windows the file takes the destination's access
    /// control list, inheritance state included, before anything is written
    /// into it; a list that cannot be read or applied is an error. A
    /// destination that does not exist leaves the file with the process's
    /// default mode or the directory's defaults.
    pub(crate) fn create(destination: &Path) -> io::Result<Self> {
        let destination = real_path(destination);
        let name = destination
            .file_name()
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "no file name"))?;
        // Distinguishes the temporary files one process writes beside the
        // same destination at once.
        let seq = crate::next_id();
        let path = destination.with_file_name(format!(".{}.{}-{seq}.tmp", name.to_string_lossy(), process::id()));
        let mut options = fs::OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        if destination.exists() {
            use std::os::unix::fs::OpenOptionsExt;
            options.mode(0o600);
        }
        let file = options.open(&path)?;
        let temp = SafeOutputFile {
            destination,
            path,
            file: Some(file),
            persisted: false,
        };
        #[cfg(windows)]
        if temp.destination.exists() {
            copy_access_control(&temp.destination, &temp.path)?;
        }
        Ok(temp)
    }

    /// The file, to write to.
    pub(crate) fn file(&mut self) -> &mut fs::File {
        self.file.as_mut().expect("the file is open until persisted")
    }

    /// Flushes what was written to storage and renames the file over the
    /// destination, the one step that replaces it. A failure leaves the
    /// destination as it was and removes the file.
    pub(crate) fn persist(mut self) -> io::Result<()> {
        #[cfg(unix)]
        if let Ok(existing) = fs::metadata(&self.destination) {
            self.file().set_permissions(existing.permissions())?;
        }
        self.file().sync_all()?;
        self.file = None;
        fs::rename(&self.path, &self.destination)?;
        self.persisted = true;
        Ok(())
    }
}

impl Drop for SafeOutputFile {
    fn drop(&mut self) {
        if !self.persisted {
            self.file = None;
            let _ = fs::remove_file(&self.path);
        }
    }
}

/// Gives `to` the discretionary access control list of `from`, with the
/// same inheritance state: what a file replacing `from` needs to keep its
/// access control. A list that cannot be read or applied is an error.
#[cfg(windows)]
// The Win32 security API is reachable only through FFI. The crate denies
// `unsafe_code` everywhere else; the exemption stops at this function.
#[allow(unsafe_code)]
fn copy_access_control(from: &Path, to: &Path) -> io::Result<()> {
    use std::os::windows::ffi::OsStrExt;
    use std::ptr;
    use windows_sys::Win32::Foundation::{ERROR_SUCCESS, LocalFree};
    use windows_sys::Win32::Security::Authorization::{GetNamedSecurityInfoW, SE_FILE_OBJECT, SetNamedSecurityInfoW};
    use windows_sys::Win32::Security::{
        ACL, DACL_SECURITY_INFORMATION, GetSecurityDescriptorControl, PROTECTED_DACL_SECURITY_INFORMATION,
        SE_DACL_PROTECTED, UNPROTECTED_DACL_SECURITY_INFORMATION,
    };

    let wide = |path: &Path| path.as_os_str().encode_wide().chain([0]).collect::<Vec<u16>>();
    let (from, to) = (wide(from), wide(to));
    let mut dacl: *mut ACL = ptr::null_mut();
    let mut descriptor = ptr::null_mut();
    // SAFETY: `from` is a NUL-terminated wide string that outlives the call,
    // and each out-pointer is a live local the call writes once. The
    // descriptor the call allocates is released below.
    let status = unsafe {
        GetNamedSecurityInfoW(
            from.as_ptr(),
            SE_FILE_OBJECT,
            DACL_SECURITY_INFORMATION,
            ptr::null_mut(),
            ptr::null_mut(),
            &mut dacl,
            ptr::null_mut(),
            &mut descriptor,
        )
    };
    if status != ERROR_SUCCESS {
        return Err(io::Error::from_raw_os_error(status as i32));
    }
    let mut control = 0;
    let mut revision = 0;
    // SAFETY: `descriptor` is the descriptor the call above returned, still
    // allocated, and the out-pointers are live locals.
    let known = unsafe { GetSecurityDescriptorControl(descriptor, &mut control, &mut revision) } != 0;
    let applied = if known {
        // A list that stops inheriting from the directory stays that way.
        let inheritance = if (control & SE_DACL_PROTECTED) != 0 {
            PROTECTED_DACL_SECURITY_INFORMATION
        } else {
            UNPROTECTED_DACL_SECURITY_INFORMATION
        };
        // SAFETY: `to` is a NUL-terminated wide string that outlives the
        // call, and `dacl` points into `descriptor`, still allocated.
        let status = unsafe {
            SetNamedSecurityInfoW(
                to.as_ptr(),
                SE_FILE_OBJECT,
                DACL_SECURITY_INFORMATION | inheritance,
                ptr::null_mut(),
                ptr::null_mut(),
                dacl,
                ptr::null_mut(),
            )
        };
        if status == ERROR_SUCCESS {
            Ok(())
        } else {
            Err(io::Error::from_raw_os_error(status as i32))
        }
    } else {
        Err(io::Error::last_os_error())
    };
    // SAFETY: `descriptor` came from `GetNamedSecurityInfoW`, which names
    // `LocalFree` as its release, and nothing reads it after this.
    unsafe { LocalFree(descriptor) };
    applied
}

/// `path` with every symbolic link resolved (C++ `TfRealPath`): the
/// filesystem's canonical form when the path exists, otherwise the chain of
/// links followed as far as it goes, so a link to a file not yet written
/// still names the file. A path that is no link is returned as it is.
fn real_path(path: &Path) -> PathBuf {
    if let Ok(real) = fs::canonicalize(path) {
        return real;
    }
    let mut current = path.to_owned();
    // A chain longer than this is a loop.
    for _ in 0..32 {
        let Ok(target) = fs::read_link(&current) else {
            break;
        };
        current = current.parent().map_or(target.clone(), |dir| dir.join(target));
    }
    current
}

/// Whether `name` is an identifier (C++ `TfIsValidIdentifier`): ASCII letters,
/// digits and underscores, at least one of them, the first not a digit.
pub fn is_valid_identifier(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|first| first == b'_' || first.is_ascii_alphabetic())
        && bytes.all(|byte| byte == b'_' || byte.is_ascii_alphanumeric())
}

/// Writes `v`, a float or double, as C++ `TfStringify` writes one: the
/// shortest digits that read back to it at its own precision
/// (double-conversion's `ToShortest`, `ToShortestSingle`), the nearest of
/// those, an exact tie rounded to even, so a float `0.65` writes as `0.65`;
/// zmij picks the same digits. They are
/// laid out as double-conversion lays them out with `decimal_in_shortest_low`
/// -6 and `decimal_in_shortest_high` 15: decimal for exponents from -6 up to
/// 14, exponent form outside, no `+` on an exponent and no trailing `.0`.
pub(crate) fn stringify_float<F: zmij::Float + Into<f64>>(s: &mut String, v: F) {
    let wide: f64 = v.into();
    if wide.is_nan() {
        s.push_str("nan");
        return;
    }
    if wide.is_infinite() {
        s.push_str(if wide > 0.0 { "inf" } else { "-inf" });
        return;
    }
    let mut buffer = zmij::Buffer::new();
    let printed = buffer.format_finite(v);
    // zmij writes decimal form for most of the exponents double-conversion
    // does, and in the same layout but for the `.0` ending a whole number.
    // Its text is double-conversion's where the exponent is from -6 to 14:
    // an integer part of 15 digits or fewer, or a fraction whose first
    // significant digit is among its first six.
    if !printed.contains('e') {
        let unsigned = printed.strip_prefix('-').unwrap_or(printed);
        let in_decimal_range = match unsigned.strip_prefix("0.") {
            Some(fraction) => fraction.bytes().take_while(|&d| d == b'0').count() < 6,
            None => unsigned.find('.').unwrap_or(unsigned.len()) <= 15,
        };
        if in_decimal_range {
            s.push_str(printed.strip_suffix(".0").unwrap_or(printed));
            return;
        }
    }
    let (sign, printed) = printed.strip_prefix('-').map_or(("", printed), |p| ("-", p));
    s.push_str(sign);
    let (mantissa, scale) = printed.split_once('e').unwrap_or((printed, "0"));
    let scale: i32 = scale.parse().expect("zmij writes an integer exponent");
    let whole = mantissa.split_once('.').map_or(mantissa, |(whole, _)| whole);
    // The digits zmij printed, read in place. Here they start with a nonzero
    // one, either the single digit before an exponent's point or a whole
    // part of 16 digits or more, so the significant ones run to the last
    // nonzero digit.
    let printed_digits = || mantissa.bytes().filter(u8::is_ascii_digit);
    let n = printed_digits().count() - printed_digits().rev().take_while(|&d| d == b'0').count();
    let digits = || printed_digits().take(n).map(char::from);
    // Where the decimal point falls after the first significant digit.
    let decimal_point = whole.len() as i32 + scale;
    let exponent = decimal_point - 1;
    if (-6..15).contains(&exponent) {
        if decimal_point <= 0 {
            s.push_str("0.");
            s.extend(iter::repeat_n('0', decimal_point.unsigned_abs() as usize));
            s.extend(digits());
        } else if decimal_point as usize >= n {
            s.extend(digits());
            s.extend(iter::repeat_n('0', decimal_point as usize - n));
        } else {
            push_digits(s, digits(), decimal_point as usize);
        }
        return;
    }
    push_digits(s, digits(), 1);
    write!(s, "e{exponent}").expect("writing to a String cannot fail");
}

/// Writes `digits` with a decimal point before the one at `point`, where any
/// digit follows it.
pub(crate) fn push_digits(s: &mut String, digits: impl Iterator<Item = char>, point: usize) {
    for (i, digit) in digits.enumerate() {
        if i == point {
            s.push('.');
        }
        s.push(digit);
    }
}

/// Locks `mutex`, reading through a poisoned lock, for a lock whose state
/// is whole after every statement that changes it.
pub(crate) fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Renders `error` followed by its `source` chain as one `: `-separated line,
/// for flattening a typed error into a plain-text diagnostic field.
pub(crate) fn error_chain(error: &dyn error::Error) -> String {
    let mut text = error.to_string();
    let mut source = error.source();
    while let Some(cause) = source {
        let rendered = cause.to_string();
        // A wrapper often embeds its source's rendering (a transparent error,
        // or a located error quoting its cause); skip what the text already
        // contains so the chain reads each failure once.
        if !rendered.is_empty() && !text.contains(&rendered) {
            text.push_str(": ");
            text.push_str(&rendered);
        }
        source = cause.source();
    }
    text
}

#[cfg(test)]
mod tests {
    use super::*;

    const KIND: Token = Token::new("Xform");

    #[test]
    fn const_static_equals_runtime() {
        // A `const` static token and a runtime (`Arc`-backed) token with the
        // same text are equal and hash equal, so either storage works as a map
        // key or in a comparison.
        let runtime = Token::from("Xform".to_string());
        assert_eq!(KIND, runtime);
        assert_eq!(KIND.as_str(), "Xform");

        let mut set = std::collections::HashSet::new();
        set.insert(runtime);
        assert!(set.contains(&KIND));
    }

    #[test]
    fn identifier_rule() {
        for name in ["a", "_", "_9", "chargroup", "Kind_2"] {
            assert!(is_valid_identifier(name), "{name}");
        }
        for name in ["", "9lives", "my:kind", "my-kind", "my kind", "caf\u{e9}"] {
            assert!(!is_valid_identifier(name), "{name}");
        }
    }

    #[test]
    fn compares_with_str() {
        assert_eq!(KIND, "Xform");
        assert_eq!("Xform", KIND);
        assert_ne!(KIND, "Mesh");
        let name: &str = "Xform";
        assert!(KIND == name);
        assert!(name == KIND);
    }

    /// `v` as [`stringify_float`] writes it.
    fn shortest<F: zmij::Float + Into<f64>>(v: F) -> String {
        let mut text = String::new();
        stringify_float(&mut text, v);
        text
    }

    /// Values exactly halfway between two shortest spellings, as OpenUSD
    /// 26.11 wrote them: the tie goes to the even digit.
    #[test]
    fn shortest_ties_to_even() {
        for (bits, written) in [
            (0x3f83210000000000, "0.009340286254882812"),
            (0x3fea93d000000000, "0.8305435180664062"),
            (0x3ff98c0800000000, "1.5966873168945312"),
            (0x4002bc5400000000, "2.3419570922851562"),
            (0x4008d22400000000, "3.1026077270507812"),
            (0x400ee7f400000000, "3.8632583618164062"),
            (0x4022785200000000, "9.235000610351562"),
            (0x4025833a00000000, "10.756301879882812"),
            (0x40288e2200000000, "12.277603149414062"),
            (0x402b990a00000000, "13.798904418945312"),
            (0x402ea3f200000000, "15.320205688476562"),
            (0x4030d0dd00000000, "16.815872192382812"),
        ] {
            assert_eq!(shortest(f64::from_bits(bits)), written);
        }
        for (bits, written) in [
            (0x3d340000, "0.043945312"),
            (0x40a9a000, "5.3007812"),
            (0x41a65000, "20.789062"),
            (0x41f79000, "30.945312"),
            (0x4224a800, "41.164062"),
            (0x424d4800, "51.320312"),
            (0x4275e800, "61.476562"),
            (0x430f4400, "143.26562"),
            (0x43239400, "163.57812"),
            (0x4337e400, "183.89062"),
            (0x434c3400, "204.20312"),
            (0x43608400, "224.51562"),
        ] {
            assert_eq!(shortest(f32::from_bits(bits)), written);
        }
    }

    /// Where a number switches between decimal and exponent form, as OpenUSD
    /// 26.11 writes it.
    #[test]
    fn shortest_layout() {
        for (v, written) in [
            (0.0, "0"),
            (-0.0, "-0"),
            (24.0, "24"),
            (0.65, "0.65"),
            (1e14, "100000000000000"),
            (1e15, "1e15"),
            (1234567890123456.5, "1.2345678901234565e15"),
            (123456789012345.0, "123456789012345"),
            (1e-7, "1e-7"),
            (1e-6, "0.000001"),
            (1.5e300, "1.5e300"),
            (2.5e-300, "2.5e-300"),
        ] {
            assert_eq!(shortest(v), written, "{v}");
        }
        for (v, written) in [(0.65f32, "0.65"), (1e13f32, "10000000000000"), (1e15f32, "1e15")] {
            assert_eq!(shortest(v), written, "{v}");
        }
    }
}
