//! Tools Foundation (C++ `Tf`): foundational utility types shared across the
//! crate. [`Token`], the interned-identifier string (C++ `TfToken`), and the
//! crate's own file-replacing writer (C++ `TfSafeOutputFile`).

use std::cmp::Ordering;
use std::convert::Infallible;
use std::error;
use std::fmt;
use std::fs;
use std::hash::{Hash, Hasher};
use std::io;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::process;
use std::str::FromStr;
use std::sync::atomic::{self, AtomicU64};
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

/// Distinguishes the temporary files one process writes beside the same
/// destination at once.
static TEMP_SEQ: AtomicU64 = AtomicU64::new(0);

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
        let seq = TEMP_SEQ.fetch_add(1, atomic::Ordering::Relaxed);
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
    fn compares_with_str() {
        assert_eq!(KIND, "Xform");
        assert_eq!("Xform", KIND);
        assert_ne!(KIND, "Mesh");
        let name: &str = "Xform";
        assert!(KIND == name);
        assert!(name == KIND);
    }
}
