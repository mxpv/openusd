# Code comments

Adapted from the samuelkarp/skills `writing-review` reference of the same name
(Apache-2.0); the rustdoc rules and the examples are this repository's.

Two rules that pull in different directions: cut hard, and keep what remains
grammatical. CLAUDE.md's Code Quality section carries the project's comment
rules (a doc comment documents only its own item, comments describe the code
as it stands, no planning-phase references, prose wrapped at 80 columns); this
page is the sentence-level pass on top of them.

## What rustdoc needs

- The first line of a `///` comment is a complete sentence that stands alone.
  rustdoc shows it in the item list without the rest, so it names what the
  item is, not how it works.
- Every identifier is in backticks or an intra-doc link. `clippy::doc_markdown`
  is denied, so a bare `LayerRegistry` in prose fails the build. Link with
  ``[`Foo`]`` when the reader would follow it; backtick when it is only named.
- A `//!` module doc is a page: what the module is, where to start reading,
  and the types that name its seams. It does not describe each item; the items
  do that.
- Wrap at 80 columns. rustfmt leaves comment text alone, so the wrap is by
  hand.

## Cut noise

A comment earns its place by saying something a reader of this codebase cannot
infer.

- **Meta-commentary about why code is structured for testing.** Do not explain
  that a helper was factored out to be testable.
- **Repeated caveats.** A caveat stated on each of four helpers is stated once,
  at the function that orchestrates them.
- **A doc comment on an obvious test function.** Test names are terse and
  self-documenting; a comment on a test describes the scenario when the name
  cannot carry it, and nothing else.
- **Incidental asides.** A note on an alternative considered, a scoping
  rationale the code already makes obvious.
- **Edit history.** "X was removed because", "now keyed by path", "no separate
  pre-check is needed here". A fresh reader never saw the prior version.
  CLAUDE.md states this rule; the sweep enforces it.

## Do not describe the lines below

A comment that narrates the next few lines is a restatement. Above two calls
that pass a pair of values together, keep the requirement ("the two travel
together because the offset scales the sample") and drop the tail ("so both
are passed").

## Explain from the constraint

A comment explaining why a mechanism exists is where contrast framing bites
hardest.

```
BAD   The clip times are read from the manifest directly rather than taken
      from the layer, so that a time the manifest omits stays distinct from
      one it sets to zero.
GOOD  The layer stores the time as a plain f64, and an omitted time and a
      time of zero have to stay distinct.
```

The rewrite drops the road not taken and states the data-model fact that
forces the design.

## Name the actor

Attribute a behaviour to the component that performs it, and check the actor
sentence by sentence. A paragraph whose subject is the stage will carry the
stage into a sentence about behaviour composition performs, or the parser, or
the C++ library being mirrored.

```
BAD   the stage drops a sample at infinity
GOOD  Interval::full is open at both ends, so time_samples_in_interval
      leaves out a sample at infinity
```

Name the call that changes state, not the one you observed it through.
Anchor a behaviour to the concrete resulting value where one exists: "the
walk stops at the pseudo-root (`/`)".

## C++ parity claims

"Mirrors C++ `UsdAttribute::GetTimeSamplesInInterval`" and "C++ differs
here" are claims about another codebase. Before keeping or writing one, read
the C++ function. A parity claim copied from a neighbouring comment has been
wrong in this repository before. Where the Rust deliberately differs, say what
this code does first, then the C++ behaviour in one flat sentence, without
defending the choice.

## Stay grammatical

Terse does not mean fragmentary.

```
BAD   Used to filter test-only layers
GOOD  so the sweep can tell them apart from unrelated layers

BAD   any layer left open is closed first
GOOD  it closes anything left open
```

No subjectless fragments, no reflexive passive. State what a thing is, or why
it is non-obvious, once, in a plain active sentence.

## TODO comments

A `TODO` names the missing feature or generalisation, in the present tense:
"TODO(perf): the interval is applied after every sample time has been
resolved; carrying it into `IndexCache::time_sample_times` would clip each
source first." Not the planning step it belongs to, and not the history of
why it is not done yet. `TODO(rayon)` and `TODO(perf)` say what is
independent or parallelisable so the seam is actionable later.
