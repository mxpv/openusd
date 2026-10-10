//! Time and heap profile of opening a stage, one phase at a time.
//!
//! Opens the root layer, walks the composed namespace reading each prim's
//! type name, then decodes every array-valued attribute once, printing for
//! each phase its wall time, the heap it leaves behind (net retained bytes)
//! and the most heap it held at any moment above what it started with (the
//! phase peak), so a transient copy a phase makes and frees shows up where a
//! net figure would hide it. The array phase also reports the bytes the
//! decoded arrays hold, beside what the stage keeps once they are dropped.
//!
//! The heap is tracked by a wrapping global allocator, so file bytes a layer
//! holds count while mapped pages, which belong to the OS, do not. The
//! tracking costs an atomic update per allocation, which the phase times
//! include.
//!
//! Each phase also reports the working set it ends with and the page faults
//! it took, read from the process's own counters: on Windows a single fault
//! count with no hard / soft split, on Linux the minor and major counts, and
//! nothing elsewhere. The working set printed per phase is the current one.
//! The peak is a high-water mark of the whole process, printed once at the
//! end. A phase's own peak is read by comparing runs cut off with `--until`.
//!
//! The run ends with the package work the resolver did (package file opens,
//! central-directory parses and requests its cache answered).
//!
//! # Usage
//! ```bash
//! cargo run --release -p openusd --example open_bench -- [--time <t>] [--save] <root.usd[a|c|z]>
//! ```
//!
//! `--time <t>` reads arrays at time code `t`, resolving time samples;
//! without it the default value is read and no sample is touched. `--save`
//! adds a phase that authors one attribute and saves the root layer; it runs
//! on a copy of a single-file root in the temporary directory, so the file
//! named on the command line is never written. `--no-arrays` skips the
//! array phase, for measuring what a stage that never reads its arrays
//! holds. `--proxies` walks instance subtrees as instance proxies and
//! `--all` walks every composed prim whatever its status, where the default
//! traversal stops at instances and skips inactive, unloaded, undefined and
//! abstract prims. `--mmap` opens the scene through a resolver that maps
//! files (the `mmap` feature), which asks that nothing write the scene's
//! files while the benchmark runs. `--until <phase>` ends the run after the
//! phase named (`open`, `metadata`, `arrays` or `save`).

use std::alloc::{GlobalAlloc, Layout, System};
#[cfg(not(feature = "mmap"))]
use std::io;
use std::mem;
use std::path::{Path, PathBuf};
use std::process;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;
use std::{env, fs};

use openusd::usd::{PrimPredicate, Stage, TimeCode};
use openusd::{Error, Result, ar, sdf};

fn main() -> Result<()> {
    let Some(args) = Args::parse() else {
        eprintln!(
            "usage: open_bench [--time <t>] [--save] [--no-arrays] [--proxies | --all] [--mmap] \
             [--until <phase>] <root.usd[a|c|z]>"
        );
        process::exit(2);
    };
    let copy = if args.save {
        Some(copy_to_temp(&args.root)?)
    } else {
        None
    };
    let root = copy.as_deref().unwrap_or(&args.root).to_str().expect("a UTF-8 path");

    let resolver = Rc::new(resolver(args.mmap)?);
    let phase = Phase::start("open");
    let stage = Stage::builder().resolver(Rc::clone(&resolver)).open(root)?;
    phase.end("");

    let mut prims = Vec::new();
    if args.runs("metadata") {
        let phase = Phase::start("metadata");
        // One cache scope over the traversal, as over the array reads below.
        let _scope = stage.cache_scope();
        stage.traverse(args.predicate, |path| prims.push(path.clone()))?;
        for path in &prims {
            stage.prim(path.clone())?.type_name()?;
        }
        phase.end(&format!("prims: {}", prims.len()));
    }

    if !args.no_arrays && args.runs("arrays") {
        let phase = Phase::start("arrays");
        // One cache scope over the reads: resolving the asset paths of a
        // packaged scene opens each package once.
        let _scope = stage.cache_scope();
        let time = args.time.map(TimeCode::new);
        let (mut arrays, mut decoded) = (0usize, 0usize);
        for path in &prims {
            for attribute in stage.prim(path.clone())?.attributes()? {
                if let Some(value) = attribute.get_at::<sdf::Value>(time)?
                    && let Some(bytes) = array_bytes(&value)
                {
                    arrays += 1;
                    decoded += bytes;
                }
            }
        }
        phase.end(&format!("arrays: {arrays}  decoded: {}", mib(decoded)));
    }

    if args.save && args.runs("save") {
        let phase = Phase::start("save");
        let prim = prims.first().cloned().unwrap_or_else(sdf::Path::abs_root);
        stage.edit(|edit| -> Result<()> {
            let path = prim.append_property("openBench").map_err(Error::from)?;
            edit.attribute_builder(path, "int").set(1).build()?;
            Ok(())
        })?;
        let identifier = stage.root_layer().identifier().to_owned();
        stage.layer_mut(&identifier).expect("the root layer is live").save()?;
        phase.end("");
    }

    eprintln!("heap peak: {}", mib(PEAK.load(Ordering::Relaxed)));
    if let Some(memory) = Memory::read() {
        eprintln!("working set peak: {}", mib(memory.peak_working_set));
    }
    let packages = resolver.package_stats();
    eprintln!(
        "packages: opens {}  directory parses {}  cache hits {}",
        packages.opens, packages.directory_parses, packages.cache_hits,
    );
    drop(stage);
    if let Some(copy) = copy {
        fs::remove_file(copy)?;
    }
    Ok(())
}

/// The command line: the root layer to open and the optional switches.
struct Args {
    root: PathBuf,
    time: Option<f64>,
    save: bool,
    no_arrays: bool,
    predicate: PrimPredicate,
    mmap: bool,
    /// The last phase to run, every phase when `None`.
    until: Option<String>,
}

impl Args {
    /// Parses the process arguments, `None` when they do not name a root.
    fn parse() -> Option<Self> {
        let mut args = env::args().skip(1);
        let mut parsed = Args {
            root: PathBuf::new(),
            time: None,
            save: false,
            no_arrays: false,
            predicate: PrimPredicate::DEFAULT,
            mmap: false,
            until: None,
        };
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--time" => parsed.time = Some(args.next()?.parse().ok()?),
                "--save" => parsed.save = true,
                "--no-arrays" => parsed.no_arrays = true,
                "--proxies" => parsed.predicate = PrimPredicate::DEFAULT_PROXIES,
                "--all" => parsed.predicate = PrimPredicate::ALL,
                "--mmap" => parsed.mmap = true,
                "--until" => parsed.until = Some(args.next().filter(|phase| PHASES.contains(&phase.as_str()))?),
                _ => parsed.root = PathBuf::from(arg),
            }
        }
        (!parsed.root.as_os_str().is_empty()).then_some(parsed)
    }

    /// Whether `phase` is at or before the one `--until` names.
    fn runs(&self, phase: &str) -> bool {
        let position = |name: &str| PHASES.iter().position(|known| *known == name);
        match &self.until {
            Some(until) => position(phase) <= position(until),
            None => true,
        }
    }
}

/// The phases, in the order they run.
const PHASES: [&str; 4] = ["open", "metadata", "arrays", "save"];

/// The resolver the stage opens through, mapping files when `mmap` is set.
#[cfg(feature = "mmap")]
// The mapping opt-in is `unsafe` by contract; `--mmap` passes the promise on
// to whoever runs the benchmark, as the usage text says.
#[allow(unsafe_code)]
fn resolver(mmap: bool) -> Result<ar::DefaultResolver> {
    if !mmap {
        return Ok(ar::DefaultResolver::new());
    }
    // SAFETY: the benchmark only reads the scene, and `--mmap` asks its user
    // to keep every other writer away from the scene's files while it runs.
    Ok(unsafe { ar::DefaultResolver::new().map_files() })
}

/// The resolver the stage opens through; `--mmap` needs the feature that
/// provides it.
#[cfg(not(feature = "mmap"))]
fn resolver(mmap: bool) -> Result<ar::DefaultResolver> {
    if mmap {
        return Err(io::Error::other("--mmap needs the mmap feature").into());
    }
    Ok(ar::DefaultResolver::new())
}

/// Copies the single-file root at `root` into the temporary directory, where
/// the save phase may overwrite it.
fn copy_to_temp(root: &Path) -> Result<PathBuf> {
    let name = root.file_name().expect("a root with a file name");
    let copy = env::temp_dir().join(format!("open_bench-{}-{}", process::id(), name.to_string_lossy()));
    fs::copy(root, &copy)?;
    // The copy is saved over, which a read-only attribute copied from the
    // source would refuse. Windows permissions are that one attribute, so
    // clearing it widens nothing else.
    #[cfg(windows)]
    #[allow(clippy::permissions_set_readonly_false)]
    {
        let mut permissions = fs::metadata(&copy)?.permissions();
        permissions.set_readonly(false);
        fs::set_permissions(&copy, permissions)?;
    }
    Ok(copy)
}

/// One timed phase: the instant it began, and the heap and the process
/// counters it began with.
struct Phase {
    name: &'static str,
    start: Instant,
    live: usize,
    memory: Option<Memory>,
}

impl Phase {
    /// Starts timing `name` and resets the phase peak to the current heap.
    fn start(name: &'static str) -> Self {
        let live = LIVE.load(Ordering::Relaxed);
        PHASE_PEAK.store(live, Ordering::Relaxed);
        Phase {
            name,
            memory: Memory::read(),
            start: Instant::now(),
            live,
        }
    }

    /// Prints the phase's time, net retained heap and peak heap above its
    /// start, the working set it ends with and the page faults it took,
    /// followed by `detail`.
    fn end(self, detail: &str) {
        let elapsed = self.start.elapsed().as_secs_f64();
        let live = LIVE.load(Ordering::Relaxed);
        let peak = PHASE_PEAK.load(Ordering::Relaxed).saturating_sub(self.live);
        let (sign, retained) = if live >= self.live {
            ("+", live - self.live)
        } else {
            ("-", self.live - live)
        };
        let process = match (self.memory, Memory::read()) {
            (Some(before), Some(after)) => {
                let hard = match (before.hard_faults, after.hard_faults) {
                    (Some(before), Some(after)) => format!(" (hard +{})", after - before),
                    _ => String::new(),
                };
                format!(
                    "ws {:>10}  faults +{}{hard}  ",
                    mib(after.working_set),
                    after.faults - before.faults
                )
            }
            _ => String::new(),
        };
        eprintln!(
            "{:<9} {elapsed:>8.3}s  retained {sign}{:>10}  peak {:>10}  {process}{detail}",
            self.name,
            mib(retained),
            mib(peak),
        );
    }
}

/// A reading of the process's memory counters.
#[derive(Clone, Copy)]
struct Memory {
    /// The resident bytes right now.
    working_set: usize,
    /// The most resident bytes the process has held.
    peak_working_set: usize,
    /// Page faults so far: every fault on Windows, the minor ones on Linux.
    faults: u64,
    /// Faults that read from disk so far, where the platform tells them
    /// apart.
    hard_faults: Option<u64>,
}

impl Memory {
    /// Reads the counters, `None` where the platform's are not wired up.
    #[cfg(windows)]
    // The counters are reachable only through the Win32 API. The crate
    // denies `unsafe_code` everywhere else; the exemption stops at this call.
    #[allow(unsafe_code)]
    fn read() -> Option<Self> {
        let mut counters = win32::ProcessMemoryCounters::default();
        let size = mem::size_of::<win32::ProcessMemoryCounters>() as u32;
        // SAFETY: `counters` is a live, writable `PROCESS_MEMORY_COUNTERS` of
        // the size passed, and the pseudo-handle from `GetCurrentProcess`
        // is always valid for the calling process.
        let read = unsafe { win32::K32GetProcessMemoryInfo(win32::GetCurrentProcess(), &raw mut counters, size) };
        (read != 0).then_some(Memory {
            working_set: counters.working_set_size,
            peak_working_set: counters.peak_working_set_size,
            faults: u64::from(counters.page_fault_count),
            hard_faults: None,
        })
    }

    /// Reads the counters, `None` where the platform's are not wired up.
    #[cfg(target_os = "linux")]
    fn read() -> Option<Self> {
        // The fields after the parenthesized command name, which may itself
        // hold spaces: `minflt` is the 8th of them and `majflt` the 10th.
        let stat = fs::read_to_string("/proc/self/stat").ok()?;
        let mut fields = stat.rsplit_once(')')?.1.split_whitespace();
        let faults = fields.nth(7)?.parse().ok()?;
        let hard_faults = fields.nth(1)?.parse().ok()?;
        let status = fs::read_to_string("/proc/self/status").ok()?;
        let kib = |key: &str| -> Option<usize> {
            let line = status.lines().find(|line| line.starts_with(key))?;
            line.split_whitespace().nth(1)?.parse().ok()
        };
        Some(Memory {
            working_set: kib("VmRSS:")? * 1024,
            peak_working_set: kib("VmHWM:")? * 1024,
            faults,
            hard_faults: Some(hard_faults),
        })
    }

    /// Reads the counters, `None` where the platform's are not wired up.
    #[cfg(not(any(windows, target_os = "linux")))]
    fn read() -> Option<Self> {
        None
    }
}

/// The two Win32 calls behind [`Memory::read`], declared here since nothing
/// else in the example needs the Windows bindings.
#[cfg(windows)]
#[allow(unsafe_code)]
mod win32 {
    use std::ffi::c_void;

    /// `PROCESS_MEMORY_COUNTERS` from `psapi.h`.
    #[repr(C)]
    #[derive(Default)]
    pub struct ProcessMemoryCounters {
        pub cb: u32,
        pub page_fault_count: u32,
        pub peak_working_set_size: usize,
        pub working_set_size: usize,
        pub quota_peak_paged_pool_usage: usize,
        pub quota_paged_pool_usage: usize,
        pub quota_peak_non_paged_pool_usage: usize,
        pub quota_non_paged_pool_usage: usize,
        pub pagefile_usage: usize,
        pub peak_pagefile_usage: usize,
    }

    #[link(name = "kernel32")]
    unsafe extern "system" {
        pub fn GetCurrentProcess() -> *mut c_void;
        pub fn K32GetProcessMemoryInfo(process: *mut c_void, counters: *mut ProcessMemoryCounters, size: u32) -> i32;
    }
}

/// `bytes` as mebibytes with one decimal.
fn mib(bytes: usize) -> String {
    format!("{:.1} MiB", bytes as f64 / (1024.0 * 1024.0))
}

/// The bytes the elements of an array `value` occupy, `None` for a scalar.
/// Element types that own further heap (strings, tokens, paths, nested
/// values) count their inline size only.
fn array_bytes(value: &sdf::Value) -> Option<usize> {
    use sdf::Value as V;
    let bytes = match value {
        V::BoolVec(v) => mem::size_of_val(v.as_slice()),
        V::UcharVec(v) => mem::size_of_val(v.as_slice()),
        V::IntVec(v) => mem::size_of_val(v.as_slice()),
        V::UintVec(v) => mem::size_of_val(v.as_slice()),
        V::Int64Vec(v) => mem::size_of_val(v.as_slice()),
        V::Uint64Vec(v) => mem::size_of_val(v.as_slice()),
        V::HalfVec(v) => mem::size_of_val(v.as_slice()),
        V::FloatVec(v) => mem::size_of_val(v.as_slice()),
        V::DoubleVec(v) => mem::size_of_val(v.as_slice()),
        V::StringVec(v) => mem::size_of_val(v.as_slice()),
        V::TokenVec(v) => mem::size_of_val(v.as_slice()),
        V::AssetPathVec(v) => mem::size_of_val(v.as_slice()),
        V::QuathVec(v) => mem::size_of_val(v.as_slice()),
        V::QuatfVec(v) => mem::size_of_val(v.as_slice()),
        V::QuatdVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec2hVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec2fVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec2dVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec2iVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec3hVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec3fVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec3dVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec3iVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec4hVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec4fVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec4dVec(v) => mem::size_of_val(v.as_slice()),
        V::Vec4iVec(v) => mem::size_of_val(v.as_slice()),
        V::Matrix2dVec(v) => mem::size_of_val(v.as_slice()),
        V::Matrix3dVec(v) => mem::size_of_val(v.as_slice()),
        V::Matrix4dVec(v) => mem::size_of_val(v.as_slice()),
        V::PathVec(v) => mem::size_of_val(v.as_slice()),
        V::LayerOffsetVec(v) => mem::size_of_val(v.as_slice()),
        V::ValueVec(v) => mem::size_of_val(v.as_slice()),
        V::TimeCodeVec(v) => mem::size_of_val(v.as_slice()),
        V::PathExpressionVec(v) => mem::size_of_val(v.as_slice()),
        _ => return None,
    };
    Some(bytes)
}

/// System allocator wrapper that tracks live heap bytes, the peak over the
/// whole run, and the peak since the current phase began.
struct Tracking;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static PHASE_PEAK: AtomicUsize = AtomicUsize::new(0);

impl Tracking {
    /// Records `delta` more live bytes and bumps both high-water marks. A
    /// mark is written only when passed, so an allocation below it costs
    /// one atomic update and two loads.
    fn add(delta: usize) {
        let live = LIVE.fetch_add(delta, Ordering::Relaxed) + delta;
        for mark in [&PEAK, &PHASE_PEAK] {
            if live > mark.load(Ordering::Relaxed) {
                mark.fetch_max(live, Ordering::Relaxed);
            }
        }
    }
}

// A `GlobalAlloc` implementation cannot be written in safe Rust: the trait is
// unsafe to implement and its methods take raw pointers. The crate denies
// `unsafe_code` everywhere else, so the exemption stops at this impl.
#[allow(unsafe_code)]
// SAFETY: every method forwards to the system allocator with the same arguments,
// only updating the byte counters around the real call.
unsafe impl GlobalAlloc for Tracking {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: `layout` is passed through untouched, so it upholds whatever
        // the caller already guaranteed for it.
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            Tracking::add(layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` is the caller's, allocated by this allocator — and so by
        // `System` — with the same `layout`.
        unsafe { System.dealloc(ptr, layout) };
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: as for `dealloc`, plus `new_size` reaches `System` unchanged.
        let new_ptr = unsafe { System.realloc(ptr, layout, new_size) };
        if !new_ptr.is_null() {
            if new_size >= layout.size() {
                Tracking::add(new_size - layout.size());
            } else {
                LIVE.fetch_sub(layout.size() - new_size, Ordering::Relaxed);
            }
        }
        new_ptr
    }
}

#[global_allocator]
static ALLOCATOR: Tracking = Tracking;
