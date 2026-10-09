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
//! holds count while mapped pages, which belong to the OS, do not. Resident
//! memory, bytes read and page faults are measured around the process with
//! the platform's tools.
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
//! named on the command line is never written.

use std::alloc::{GlobalAlloc, Layout, System};
use std::mem;
use std::path::{Path, PathBuf};
use std::process;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;
use std::{env, fs};

use openusd::sdf;
use openusd::usd::{PrimPredicate, Stage, TimeCode};
use openusd::{Error, Result};

fn main() -> Result<()> {
    let Some(args) = Args::parse() else {
        eprintln!("usage: open_bench [--time <t>] [--save] <root.usd[a|c|z]>");
        process::exit(2);
    };
    let root = match args.save {
        true => copy_to_temp(&args.root)?,
        false => args.root.clone(),
    };
    let root = root.to_str().expect("a UTF-8 path");

    let phase = Phase::start("open");
    let stage = Stage::open(root)?;
    phase.end("");

    let phase = Phase::start("metadata");
    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT, |path| prims.push(path.clone()))?;
    for path in &prims {
        stage.prim(path.clone())?.type_name()?;
    }
    phase.end(&format!("prims: {}", prims.len()));

    let phase = Phase::start("arrays");
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

    if args.save {
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
    Ok(())
}

/// The command line: the root layer to open and the two optional switches.
struct Args {
    root: PathBuf,
    time: Option<f64>,
    save: bool,
}

impl Args {
    /// Parses the process arguments, `None` when they do not name a root.
    fn parse() -> Option<Self> {
        let mut args = env::args().skip(1);
        let mut parsed = Args {
            root: PathBuf::new(),
            time: None,
            save: false,
        };
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--time" => parsed.time = Some(args.next()?.parse().ok()?),
                "--save" => parsed.save = true,
                _ => parsed.root = PathBuf::from(arg),
            }
        }
        (!parsed.root.as_os_str().is_empty()).then_some(parsed)
    }
}

/// Copies the single-file root at `root` into the temporary directory, where
/// the save phase may overwrite it.
fn copy_to_temp(root: &Path) -> Result<PathBuf> {
    let name = root.file_name().expect("a root with a file name");
    let copy = env::temp_dir().join(format!("open_bench-{}-{}", process::id(), name.to_string_lossy()));
    fs::copy(root, &copy)?;
    Ok(copy)
}

/// One timed phase: the instant it began and the heap it began with.
struct Phase {
    name: &'static str,
    start: Instant,
    live: usize,
}

impl Phase {
    /// Starts timing `name` and resets the phase peak to the current heap.
    fn start(name: &'static str) -> Self {
        let live = LIVE.load(Ordering::Relaxed);
        PHASE_PEAK.store(live, Ordering::Relaxed);
        Phase {
            name,
            start: Instant::now(),
            live,
        }
    }

    /// Prints the phase's time, net retained heap and peak heap above its
    /// start, followed by `detail`.
    fn end(self, detail: &str) {
        let elapsed = self.start.elapsed().as_secs_f64();
        let live = LIVE.load(Ordering::Relaxed);
        let peak = PHASE_PEAK.load(Ordering::Relaxed).saturating_sub(self.live);
        let (sign, retained) = match live >= self.live {
            true => ("+", live - self.live),
            false => ("-", self.live - live),
        };
        eprintln!(
            "{:<9} {elapsed:>8.3}s  retained {sign}{:>10}  peak {:>10}  {detail}",
            self.name,
            mib(retained),
            mib(peak),
        );
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
    /// Records `delta` more live bytes and bumps both high-water marks.
    fn add(delta: usize) {
        let live = LIVE.fetch_add(delta, Ordering::Relaxed) + delta;
        PEAK.fetch_max(live, Ordering::Relaxed);
        PHASE_PEAK.fetch_max(live, Ordering::Relaxed);
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
