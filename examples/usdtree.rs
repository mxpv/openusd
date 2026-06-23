//! Print the composed prim hierarchy of a stage, like `usdtree --flatten`.
//!
//! This corresponds to `usdtree --flatten <file>`, which prints the flattened
//! (composed) stage tree; plain `usdtree` instead dumps the single root layer
//! uncomposed. It opens and fully composes the root layer, then walks the
//! resulting namespace depth-first, drawing one line per prim with its type
//! name. Prims outside the default predicate region (inactive, unloaded,
//! undefined, or abstract) are skipped.
//!
//! A tracking global allocator records the peak heap during composition and
//! traversal, printed (with the prim count and elapsed time) to stderr at the
//! end. Tracking the heap rather than the resident set isolates the composition
//! and layer-data allocations from the rest of the process image.
//!
//! # Usage
//! ```bash
//! cargo run --release --example usdtree -- <root.usd[a|c|z]>
//! ```

use std::alloc::{GlobalAlloc, Layout, System};
use std::io::{self, BufWriter, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use anyhow::{Context as _, Result};
use openusd::sdf;
use openusd::usd::{Prim, Stage};

fn main() -> Result<()> {
    let path = std::env::args().nth(1).context("usage: usdtree <root.usd[a|c|z]>")?;
    let start = Instant::now();

    let stage = Stage::open(&path).context("failed to open/compose stage")?;

    let out = io::stdout();
    let mut out = BufWriter::new(out.lock());
    writeln!(out, "/")?;

    // Explicit-stack depth-first walk; carries each prim's indentation prefix
    // and whether it is its parent's final child, so production scenes with
    // deep namespaces are drawn without recursing.
    let mut prims = 0u64;
    let mut stack: Vec<(Prim, String, bool)> = Vec::new();
    push_children(&mut stack, &stage.prim(sdf::Path::abs_root()), String::new())?;

    while let Some((prim, prefix, last)) = stack.pop() {
        prims += 1;
        let name = prim.path().name().unwrap_or_default();
        let branch = if last { "`-- " } else { "|-- " };
        match prim.type_name()? {
            Some(ty) if !ty.as_str().is_empty() => writeln!(out, "{prefix}{branch}{name} [{ty}]")?,
            _ => writeln!(out, "{prefix}{branch}{name}")?,
        }
        let child_prefix = format!("{prefix}{}", if last { "    " } else { "|   " });
        push_children(&mut stack, &prim, child_prefix)?;
    }

    out.flush()?;

    // Memory and timing summary on stderr, kept off the tree on stdout.
    let peak_mib = PEAK.load(Ordering::Relaxed) as f64 / (1024.0 * 1024.0);
    eprintln!("prims:     {prims}");
    eprintln!("elapsed:   {:.1}s", start.elapsed().as_secs_f64());
    eprintln!("heap peak: {peak_mib:.1} MiB");
    Ok(())
}

/// Pushes `parent`'s children onto `stack` in reverse order so they pop
/// left-to-right. Each entry carries `child_prefix` and a flag marking the
/// final child, which together select its branch glyph when it is drawn.
fn push_children(stack: &mut Vec<(Prim, String, bool)>, parent: &Prim, child_prefix: String) -> Result<()> {
    let children = parent.children()?;
    let count = children.len();
    for (i, child) in children.into_iter().enumerate().rev() {
        stack.push((child, child_prefix.clone(), i + 1 == count));
    }
    Ok(())
}

/// System allocator wrapper that tracks live and peak heap bytes, so the example
/// can report how much heap the composed stage holds.
struct Tracking;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

impl Tracking {
    /// Records `delta` more live bytes and bumps the peak high-water mark.
    fn add(delta: usize) {
        let live = LIVE.fetch_add(delta, Ordering::Relaxed) + delta;
        PEAK.fetch_max(live, Ordering::Relaxed);
    }
}

// SAFETY: every method forwards to the system allocator with the same arguments,
// only updating the byte counters around the real call.
unsafe impl GlobalAlloc for Tracking {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = System.alloc(layout);
        if !ptr.is_null() {
            Tracking::add(layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout);
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let new_ptr = System.realloc(ptr, layout, new_size);
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
