//! Print the composed prim hierarchy of a stage, like `usdtree --flatten`.
//!
//! This corresponds to `usdtree --flatten <file>`, which prints the flattened
//! (composed) stage tree; plain `usdtree` instead dumps the single root layer
//! uncomposed. It opens and fully composes the root layer, then walks the
//! resulting namespace depth-first, drawing one line per prim with its type
//! name. Prims outside the default predicate region (inactive, unloaded,
//! undefined, or abstract) are skipped.
//!
//! # Usage
//! ```bash
//! cargo run --release --example usdtree -- <root.usd[a|c|z]>
//! ```

use std::io::{self, BufWriter, Write};

use anyhow::{Context as _, Result};
use openusd::sdf;
use openusd::usd::{Prim, Stage};

fn main() -> Result<()> {
    let path = std::env::args().nth(1).context("usage: usdtree <root.usd[a|c|z]>")?;

    let stage = Stage::open(&path).context("failed to open/compose stage")?;

    let out = io::stdout();
    let mut out = BufWriter::new(out.lock());
    writeln!(out, "/")?;

    // Explicit-stack depth-first walk; carries each prim's indentation prefix
    // and whether it is its parent's final child, so production scenes with
    // deep namespaces are drawn without recursing.
    let mut stack: Vec<(Prim, String, bool)> = Vec::new();
    push_children(&mut stack, &stage.prim(sdf::Path::abs_root()), String::new())?;

    while let Some((prim, prefix, last)) = stack.pop() {
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
