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
//! The run ends with the package work done (package file opens,
//! central-directory parses and requests a cache scope answered).
//!
//! # Usage
//! ```bash
//! cargo run --release -p openusd --example open_bench -- [--time <t>] [--save] [--mute] <root.usd[a|c|z]>
//! ```
//!
//! `--time <t>` reads arrays at time code `t`, resolving time samples;
//! without it the default value is read and no sample is touched. `--save`
//! adds a phase that authors one attribute and saves the root layer; it runs
//! on a copy of a single-file root in the temporary directory, so the file
//! named on the command line is never written. `--mute` adds a phase that
//! mutes one layer and unmutes it again, timing the two invalidations of
//! the populated stage: the root layer's first sublayer, or the layer
//! loaded last when the root has none. `--no-heap` turns the heap tracking
//! off, for a timing run: the phase times carry no tracking cost, and the
//! heap figures count only what the process held before the switch, so
//! they say nothing about the scene. `--no-arrays` skips the
//! array phase, for measuring what a stage that never reads its arrays
//! holds. `--proxies` walks instance subtrees as instance proxies and
//! `--all` walks every composed prim whatever its status, where the default
//! traversal stops at instances and skips inactive, unloaded, undefined and
//! abstract prims. `--mmap` opens the scene through a resolver that maps
//! files (the `mmap` feature), which asks that nothing write the scene's
//! files while the benchmark runs. `--until <phase>` ends the run after the
//! phase named (`open`, `metadata`, `retraverse`, `edit`, `arrays`, `mute`
//! or `save`).
//!
//! `--retraverse` adds a phase that runs the metadata traversal again on the
//! same stage, reading what the first one composed and cached. `--edit` adds
//! a phase that authors `active = true` on the first traversed prim, in the
//! session layer when the stage has one, and traverses again: the edit
//! clears the stage's population answers, so the traversal recomputes them.
//! `--status <file>` writes each prim the metadata phase traverses with its
//! active, loaded, defined, abstract, instance and instance-proxy bits, read
//! through the `Prim` queries, so two builds can be compared with `diff`.
//! `--load-none` opens with no payload loaded, and each `--load <path>` then
//! loads that prim but none of its descendants.
//!
//! `--stream` reads the scene one chunk at a time through the one stage, in
//! place of the phases after `open`: it loads each child of the default prim,
//! else of the lone top-level prim, else each top-level prim, with its
//! descendants, unloading the one before, traverses the stage, reads the
//! chunk's arrays, and prints the heap and working set after each. Paired with
//! `--load-none`, the heap it ends a chunk with is what an unload leaves
//! resident.

use std::alloc::{GlobalAlloc, Layout, System};
#[cfg(not(feature = "mmap"))]
use std::io;
use std::mem;
use std::path::{Path, PathBuf};
use std::process;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Instant;
use std::{env, fs};

use openusd::usd::{EditTarget, InitialLoadSet, LoadPolicy, PrimPredicate, Stage, TimeCode};
use openusd::{Error, Result, ar, pcp, sdf, usdz, vt};

fn main() -> Result<()> {
    let Some(args) = Args::parse() else {
        eprintln!(
            "usage: open_bench [--time <t>] [--save] [--mute] [--retraverse] [--edit] [--no-heap] [--no-arrays] \
             [--proxies | --all] [--mmap] [--status <file>] [--load-none] [--load <path>]... [--stream] [--until <phase>] \
             <root.usd[a|c|z]>"
        );
        process::exit(2);
    };
    TRACKED.store(!args.no_heap, Ordering::Relaxed);
    let copy = if args.save {
        Some(copy_to_temp(&args.root)?)
    } else {
        None
    };
    let root = copy.as_deref().unwrap_or(&args.root).to_str().expect("a UTF-8 path");

    let resolver = resolver(args.mmap)?;
    let phase = Phase::start("open");
    let load_set = if args.load_none {
        InitialLoadSet::LoadNone
    } else {
        InitialLoadSet::LoadAll
    };
    let stage = Stage::builder().resolver(resolver).load(load_set).open(root)?;
    for path in &args.load {
        stage.load(path.as_str(), LoadPolicy::WithoutDescendants)?;
    }
    phase.end("");

    if args.stream {
        stream(&stage, &args)?;
        print_tally(stage.tally());
        print_peaks();
        return Ok(());
    }

    let mut prims = Vec::new();
    if args.runs("metadata") {
        let phase = Phase::start("metadata");
        prims = traverse(&stage, args.predicate)?;
        phase.end(&format!("prims: {}", prims.len()));
        if let Some(file) = &args.status {
            write_status(&stage, &prims, file)?;
        }
    }

    if args.retraverse && args.runs("retraverse") {
        let phase = Phase::start("retraverse");
        let count = traverse(&stage, args.predicate)?.len();
        phase.end(&format!("prims: {count}"));
    }

    if args.edit && args.runs("edit") {
        let phase = Phase::start("edit");
        if let Some(prim) = prims.first() {
            let session = stage.session_layer().map(|layer| layer.identifier().to_owned());
            if let Some(session) = session {
                stage.set_edit_target(EditTarget::for_layer(session))?;
            }
            stage.override_prim(prim.clone())?.set_active(true)?;
        }
        let count = traverse(&stage, args.predicate)?.len();
        phase.end(&format!("prims: {count}"));
    }

    if !args.no_arrays && args.runs("arrays") {
        let phase = Phase::start("arrays");
        // One cache scope over the reads: resolving the asset paths of a
        // packaged scene opens each package once.
        let _scope = ar::CacheScope::begin();
        let (arrays, decoded) = read_arrays(&stage, &prims, args.time)?;
        phase.end(&format!("arrays: {arrays}  decoded: {}", mib(decoded)));
    }

    if args.mute && args.runs("mute") {
        let root = stage.root_layer().identifier().to_owned();
        let layer = stage
            .sub_layers(&root)
            .into_iter()
            .nth(1)
            .or_else(|| stage.layer_identifiers().pop())
            .filter(|layer| *layer != root);
        if let Some(layer) = layer {
            let phase = Phase::start("mute");
            let before = stage.tally();
            stage.mute_layer(layer.as_str());
            stage.unmute_layer(&layer);
            phase.end(&format!("layer: {layer}  {}", tally_delta(before, stage.tally())));
        }
    }

    if args.save && args.runs("save") {
        let phase = Phase::start("save");
        let before = stage.tally();
        let prim = prims.first().cloned().unwrap_or_else(sdf::Path::abs_root);
        stage.edit(|edit| -> Result<()> {
            let path = prim.append_property("openBench").map_err(Error::from)?;
            edit.attribute_builder(path, "int").set(1).build()?;
            Ok(())
        })?;
        let identifier = stage.root_layer().identifier().to_owned();
        stage
            .layer_handle(&identifier)
            .expect("the root layer is live")
            .save()?;
        phase.end(&tally_delta(before, stage.tally()));
    }

    let graphs = stage.graph_stats();
    eprintln!(
        "graphs: {}  shared node data {}  copies {}  nodes copied {}",
        graphs.graphs, graphs.shared, graphs.copies, graphs.nodes_copied,
    );
    print_tally(stage.tally());
    print_peaks();
    let packages = usdz::package_stats();
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
    mute: bool,
    no_heap: bool,
    no_arrays: bool,
    predicate: PrimPredicate,
    mmap: bool,
    retraverse: bool,
    edit: bool,
    /// Where to write the traversed prims' status bits.
    status: Option<PathBuf>,
    load_none: bool,
    /// The prims loaded after the stage opens.
    load: Vec<String>,
    /// The last phase to run, every phase when `None`.
    until: Option<String>,
    /// Whether to read the scene one top-level prim at a time.
    stream: bool,
}

impl Args {
    /// Parses the process arguments, `None` when they do not name a root.
    fn parse() -> Option<Self> {
        let mut args = env::args().skip(1);
        let mut parsed = Args {
            root: PathBuf::new(),
            time: None,
            save: false,
            mute: false,
            no_heap: false,
            no_arrays: false,
            predicate: PrimPredicate::DEFAULT,
            mmap: false,
            retraverse: false,
            edit: false,
            status: None,
            load_none: false,
            load: Vec::new(),
            until: None,
            stream: false,
        };
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--time" => parsed.time = Some(args.next()?.parse().ok()?),
                "--save" => parsed.save = true,
                "--mute" => parsed.mute = true,
                "--no-heap" => parsed.no_heap = true,
                "--no-arrays" => parsed.no_arrays = true,
                "--proxies" => parsed.predicate = PrimPredicate::DEFAULT_PROXIES,
                "--all" => parsed.predicate = PrimPredicate::ALL,
                "--mmap" => parsed.mmap = true,
                "--retraverse" => parsed.retraverse = true,
                "--edit" => parsed.edit = true,
                "--status" => parsed.status = Some(PathBuf::from(args.next()?)),
                "--load-none" => parsed.load_none = true,
                "--load" => parsed.load.push(args.next()?),
                "--stream" => parsed.stream = true,
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
const PHASES: [&str; 7] = ["open", "metadata", "retraverse", "edit", "arrays", "mute", "save"];

/// Traverses `stage` under `predicate` and reads each prim's type name,
/// returning the prims visited.
fn traverse(stage: &Stage, predicate: PrimPredicate) -> Result<Vec<sdf::Path>> {
    // One cache scope over the traversal, as over the array reads.
    let _scope = ar::CacheScope::begin();
    let mut prims = Vec::new();
    stage.traverse(predicate, |path| prims.push(path.clone()))?;
    for path in &prims {
        stage.prim(path.clone())?.type_name()?;
    }
    Ok(prims)
}

/// Reads `stage` one chunk at a time, a chunk being a child of the default
/// prim, else of the lone top-level prim, else a top-level prim: loads each
/// with its descendants, unloading the one before, traverses the stage and
/// reads the chunk's arrays, and prints the heap the chunk leaves.
fn stream(stage: &Stage, args: &Args) -> Result<()> {
    // A scene under one default prim, or one top-level prim, streams that
    // prim's children.
    let root = stage.prim(sdf::Path::abs_root())?.children()?;
    let parent = match (stage.default_prim(), root.as_slice()) {
        (Some(name), _) => sdf::default_prim_path(name.as_str()).unwrap_or_else(sdf::Path::abs_root),
        (None, [only]) => only.path().clone(),
        (None, _) => sdf::Path::abs_root(),
    };
    let tops: Vec<sdf::Path> = stage
        .prim(parent)?
        .children()?
        .iter()
        .map(|prim| prim.path().clone())
        .collect();
    let mut previous: Option<sdf::Path> = None;
    for top in &tops {
        let phase = Phase::start("chunk");
        stage.load_and_unload(
            [(top.clone(), LoadPolicy::WithDescendants)],
            previous.replace(top.clone()),
        )?;
        // The scope ends before the heap is read, so the packages it kept open
        // do not count as what the chunk leaves.
        let (prims, arrays) = {
            let _scope = ar::CacheScope::begin();
            let prims: Vec<sdf::Path> = traverse(stage, args.predicate)?
                .into_iter()
                .filter(|path| path.has_prefix(top))
                .collect();
            let (arrays, _) = read_arrays(stage, &prims, args.time)?;
            (prims, arrays)
        };
        phase.end(&format!(
            "{top}  prims: {}  arrays: {arrays}  heap: {}  layers: {}",
            prims.len(),
            mib(LIVE.load(Ordering::Relaxed)),
            stage.layer_count()
        ));
    }
    let phase = Phase::start("unload");
    if let Some(last) = previous {
        stage.unload(last)?;
    }
    phase.end(&format!(
        "heap: {}  layers: {}",
        mib(LIVE.load(Ordering::Relaxed)),
        stage.layer_count()
    ));
    Ok(())
}

/// Prints the most heap the run held and the process's working-set peak.
fn print_peaks() {
    eprintln!("heap peak: {}", mib(PEAK.load(Ordering::Relaxed)));
    if let Some(memory) = Memory::read() {
        eprintln!("working set peak: {}", mib(memory.peak_working_set));
    }
}

/// Reads every attribute of `prims` at `time` (the default value when `None`),
/// returning how many hold an array and the bytes the arrays decoded to.
fn read_arrays(stage: &Stage, prims: &[sdf::Path], time: Option<f64>) -> Result<(usize, usize)> {
    let time = time.map(TimeCode::new);
    let (mut arrays, mut decoded) = (0usize, 0usize);
    for path in prims {
        for attribute in stage.prim(path.clone())?.attributes()? {
            if let Some(value) = attribute.get_at::<vt::Value>(time)?
                && let Some(bytes) = array_bytes(&value)
            {
                arrays += 1;
                decoded += bytes;
            }
        }
    }
    Ok((arrays, decoded))
}

/// Writes one line per prim in `prims` to `file`: the path, then `1` or `0`
/// for active, loaded, defined, abstract, instance and instance proxy.
fn write_status(stage: &Stage, prims: &[sdf::Path], file: &Path) -> Result<()> {
    let bit = |value: bool| if value { '1' } else { '0' };
    let mut out = String::new();
    for path in prims {
        let prim = stage.prim(path.clone())?;
        out.push_str(&format!(
            "{path} {}{}{}{}{}{}\n",
            bit(prim.is_active()?),
            bit(prim.is_loaded()?),
            bit(prim.is_defined()?),
            bit(prim.is_abstract()?),
            bit(prim.is_instance()?),
            bit(prim.is_instance_proxy()?),
        ));
    }
    fs::write(file, out)?;
    Ok(())
}

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

/// Prints what composing and settling have cost over the whole run.
fn print_tally(tally: pcp::Tally) {
    eprintln!(
        "tally: visits {}  population checks {}  builds {}  demands {}",
        tally.visits, tally.population_checks, tally.builds, tally.demands,
    );
}

/// What a phase's settling cost, from the tallies before and after it.
fn tally_delta(before: pcp::Tally, after: pcp::Tally) -> String {
    format!(
        "settled: visits {}  population checks {}  builds {}",
        after.visits - before.visits,
        after.population_checks - before.population_checks,
        after.builds - before.builds,
    )
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
fn array_bytes(value: &vt::Value) -> Option<usize> {
    use vt::Value as V;
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
/// Whether allocations are counted. `--no-heap` clears it.
static TRACKED: AtomicBool = AtomicBool::new(true);

impl Tracking {
    /// Records `delta` more live bytes and bumps both high-water marks. A
    /// mark is written only when passed, so an allocation below it costs
    /// one atomic update and two loads.
    fn add(delta: usize) {
        if !TRACKED.load(Ordering::Relaxed) {
            return;
        }
        let live = LIVE.fetch_add(delta, Ordering::Relaxed) + delta;
        for mark in [&PEAK, &PHASE_PEAK] {
            if live > mark.load(Ordering::Relaxed) {
                mark.fetch_max(live, Ordering::Relaxed);
            }
        }
    }

    /// Records `delta` fewer live bytes.
    fn sub(delta: usize) {
        if TRACKED.load(Ordering::Relaxed) {
            LIVE.fetch_sub(delta, Ordering::Relaxed);
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
        Tracking::sub(layout.size());
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: as for `dealloc`, plus `new_size` reaches `System` unchanged.
        let new_ptr = unsafe { System.realloc(ptr, layout, new_size) };
        if !new_ptr.is_null() {
            if new_size >= layout.size() {
                Tracking::add(new_size - layout.size());
            } else {
                Tracking::sub(layout.size() - new_size);
            }
        }
        new_ptr
    }
}

#[global_allocator]
static ALLOCATOR: Tracking = Tracking;
