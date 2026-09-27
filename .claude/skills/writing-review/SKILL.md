---
name: writing-review
description: |
  Revise drafted prose into the plain, reader-facing register this project
  uses: commit messages, doc comments and inline comments, README and docs/
  pages, ROADMAP notes, and the prose in plans and reports. Use after writing
  or editing any of those and before committing or handing them over, and
  whenever asked to review, tighten, or clean up wording. Covers framing the
  reader cannot verify (contrast tails, historical framing, restated
  consequences, answers to concerns only the author had), the sentence-level
  tics that mark model-drafted prose, the project's commit subject and body
  conventions, doc altitude and causal attribution, and the claim
  re-verification a wording sweep requires. Given paths, it sweeps those files
  and applies the fixes in place.
argument-hint: "[paths...] [notes]"
disable-model-invocation: false
allowed-tools: Read Edit Grep Glob Bash(git *) Bash(rg *) Bash(cargo *)
---

# Writing review

A revision pass over text that already exists. The project's comment and doc
rules live in CLAUDE.md's Code Quality and ROADMAP.md Style sections; this
skill is the sentence-level pass on top of them, and where the two overlap
CLAUDE.md wins. The reference files carry the longer derivations; open one
when the summary here is not enough.

- [references/register.md](references/register.md): the ten sentence-level
  tics, a worked rewrite from this repository, coined terms, metaphors, and
  filler.
- [references/commit-messages.md](references/commit-messages.md): subject and
  body conventions, when a body earns its place, what never goes in one, and
  how to sample the maintainer's voice from the history.
- [references/code-comments.md](references/code-comments.md): what to cut from
  a comment, what rustdoc needs, and what has to stay grammatical.
- [references/docs-and-readmes.md](references/docs-and-readmes.md): stating the
  rule, writing at the document's altitude, ROADMAP rows, self-standing plans,
  and README audience.

The arguments are: $ARGUMENTS

## Two ways to run

**Bounded.** With no paths, the pass is bounded by the working tree: the
comments and docs the current diff touches, and the commit message being
drafted. This is how the commit skill runs it. Rewording a neighbouring comment
the change did not require draws "why this change?" in review and gets
reverted, so a line the diff does not touch stays as it is.

**Sweep.** With paths (files, directories, or a glob), read every comment and
doc page under them, apply steps 2 through 5 in place with the Edit tool, run
step 6 over the result, and report what changed and what was left alone with
the reason. A sweep fixes meaning: contrast tails, historical framing,
restatements, unverifiable claims, fragments. It does not chase punctuation
tics through untouched sentences; rules 7 and 10 below apply to sentences the
sweep is rewriting anyway. After editing Rust files, run
`cargo clippy -p <crate> --all-targets --all-features -- -D warnings`, since
`clippy::doc_markdown` is denied and a bare identifier in a doc comment fails
the build, and `cargo doc -p <crate> --no-deps` when an intra-doc link moved.

## Scope

Apply this to prose written for a reader: commit messages, `///` and `//!`
doc comments, `//` comments, README files, `docs/` pages, ROADMAP notes, and
the prose in plans and reports.

Five kinds of text are out of scope.

- Instruction files written for a model: CLAUDE.md, the skills under
  `.claude/`, agent memory. The contrast and negation rules do not apply to
  them.
- Generated text. The schema views `openusd-build` emits, and the golden
  files under its `tests/` and `fixtures/`, are generator output: a wording
  problem there is fixed in the generator (`doc.rs`), and the goldens are
  regenerated, never edited by hand.
- Vendored material under `vendor/`, and quoted text anywhere: a passage from
  the AOUSD spec or a C++ doc comment. Fix the framing around a quotation,
  never the quotation.
- Deliberate authored voice. A warning a README carries on purpose stays.
- Lines the current change does not touch, in the bounded mode.

## Step 1: name the artifact and its reader

Each rule below resolves differently depending on who is reading.

| Artifact | Reader |
| --- | --- |
| Commit message | Someone reading `git log`, who sees this diff against its parent and no earlier state |
| `///` doc comment | Someone reading rustdoc, who sees the signature and the first sentence in an item list, and never the body of the function |
| `//!` module doc | Someone deciding where to start reading, who has the module's item list beside the text |
| `//` comment | A reader of the code, who can see the next lines |
| README | A user of the crate deciding whether and how to depend on it |
| `docs/` page or plan | Someone who did not attend the discussion, deciding or implementing from the page alone |
| ROADMAP row | Someone checking what is supported and what remains |
| Report | A disinterested reader with no memory of the deliberation |

## Step 2: cut what the reader never asked for

**A concern that was only yours.** Before keeping an explanatory sentence, ask
whether a reader who sees only the final artifact has that question. If the
question exists because you worked through an alternative or hit a worry, cut
it. A commit body that says a helper's return "sufficed" answers the author's
earlier worry; the reader sees the diff and never had it.

**A contrast against something the reader cannot see.** Strip trailing
`instead of`, `rather than`, `not just`, `unlike`, and `no longer` clauses,
and drop promotional intensifiers (`powerful`, `seamlessly`). Explain from the
constraint that forces the design. CLAUDE.md states the same rule for
comments: "we use A so we don't B", "instead of calling Z", "a subtree walk
rather than a full scan" only make sense to someone who saw the alternative.

```
BAD   An empty taxonomy or interval is refused rather than answering with
      nothing.
GOOD  An empty taxonomy or interval is refused.
```

A contrast is wanted when both sides are in front of the reader: a body that
names a problem and the approach taken, two tests that coexist in the tree,
the C++ behaviour a doc comment says this code departs from. The rule targets
defending a design against a rejected alternative the reader never raised.

**Historical framing.** Describe current behaviour in the present tense. No
"no longer X", no "used to X", no "now keyed by path". This bites hardest in a
squashed commit, where the contrast points at a state that never exists in
history.

```
BAD   asks the attributes whether they may vary over time rather than
      recording that at construction
GOOD  asks the attributes whether they may vary over time
```

**A sentence that restates the one before it.** Three forms, all cut:

1. A closing sentence re-expressing a term already used. "`EARLIEST` is
   `f64::MIN`. The read reaches the earliest sample." The name already says
   it; the second sentence goes.
2. A comment describing the lines directly beneath it. Keep the requirement,
   drop the "so both are passed" tail.
3. An example re-deriving the rule stated above it.

Check each sentence against the one before it and against the code beneath
it. If a reader who understood the previous sentence learns nothing, cut it.

**A hypothetical written in the present indicative.** An option that was
evaluated and not adopted does not have real behaviour. Put its consequences
in the conditional: "a per-prim bump would under-invalidate", not "a per-prim
bump under-invalidates". Drop concessions that grant a merit before the
disqualifying property. Cut forward-looking Status sections; describe the
current state.

**Vague filler.** "wire up the plumbing", "lay the groundwork", "improve
robustness". Name the concrete file, function, or change, or say nothing.

## Step 3: flatten the register

Ten tics. The derivation, on a sentence from this repository, is in
[references/register.md](references/register.md).

1. **Proposition as modifier.** A complete claim folded into a trailing
   `that`- or `where`-clause hanging off a noun. Assert one proposition per
   sentence.
2. **Definition by negation.** Saying what does not happen, to whom, under
   what condition. Find the positive form.
3. **Preemptive qualifier.** A trailing phrase answering an objection no
   reader raised.
4. **`so`-chaining.** More than one `so` clause performs the derivation
   instead of stating the result. State cause, then effect, once.
5. **Counterfactual narration.** Describing the behaviour of a design that
   does not exist.
6. **Diff-anchored imperative.** "Keep the sort after the merge" means
   something only to someone reading the change. Describe the code: "Sort
   after the merge."
7. **Clause-joining commas.** A comma before `and` or `but` linking two
   independent clauses reads as a pause for drama. This is a frequency
   correction: prefer two sentences, keep the join when it earns the pause.
   List commas are unaffected.
8. **Plain verb over the compressed negative.** "does not check the type"
   over "performs no type check"; "does not require a registry" over
   "requires no registry". `has no X` stays where X is the noun the reader is
   looking for ("an attribute with no samples").
9. **Keep the noun.** "are privileged operations", not "are privileged". "A
   layer with ...", not "A layer created with ..." when the participle adds
   nothing.
10. **No comma before a restrictive `because` or `so`.** Delete the comma
    before `because`. At `so`, split into two sentences, which also clears
    rule 4.

Three more that belong to the same pass:

- **No metaphors.** "the first run leaks the layer, the second fails on it",
  not "seed then bite". The reader has to decode a metaphor back into the
  literal fact.
- **No coined terms.** Use the name the domain already has: the C++ OpenUSD
  name for a concept (`UsdResolveInfo`, "prim index", "layer stack"), the
  exact identifier, the field name. If a word needs a footnote, or you reached
  for it because no ordinary verb fit, it is the wrong word. A coined term
  does not stay in the prose: it reaches the plan, then a type name.
- **Terse does not mean fragmentary.** No subjectless fragments, no reflexive
  passive. "so the sweep can tell them apart from unrelated layers", not "Used
  to filter test-only layers".

Dashes are project style in doc comments and Markdown. A sentence with two of
them, or a dash carrying a whole second clause, reads better as two sentences.

## Step 4: apply the artifact rules

Open the matching reference.

- Commit message:
  [references/commit-messages.md](references/commit-messages.md)
- Doc or inline comment:
  [references/code-comments.md](references/code-comments.md)
- README, `docs/` page, plan, or ROADMAP row:
  [references/docs-and-readmes.md](references/docs-and-readmes.md)

## Step 5: re-verify every claim you rewrote

A wording sweep across many sites is where a true statement quietly becomes a
false one. A scoped claim and a general one read as stylistic variants of each
other, and the edit feels lossless while dropping the qualifier that made it
true.

When a sweep touches a sentence carrying a technical claim, re-derive the
claim against the source before writing the replacement, and keep the scope
explicit by naming the operations. Three sources matter here:

- The code the comment sits on. Read the function, not the neighbouring
  comment.
- The C++ OpenUSD source, for any "as C++ does" or "C++ differs" claim. A
  parity claim echoed from a nearby doc comment has been wrong before; check
  it against the C++ file before keeping it.
- The AOUSD core spec in `docs/`, for a claim about what the spec requires.

A claim you cannot verify is left as it was and named in the report, not
rewritten.

## Step 6: grep for the tells

Run these over the finished text. A correction applies to the pattern, not to
the phrase that was quoted, so sweep the whole change. `rg` scopes the Rust
searches to comment lines.

```sh
# Contrast tails and historical framing, in comments and Markdown
rg -n --type rust '^\s*(//|///|//!).*\b(instead of|rather than|not just|unlike |no longer|used to |previously|formerly|now )' PATHS
rg -nEi 'instead of|rather than|not just|unlike |no longer|used to |previously|formerly' FILE.md

# Compressed negatives (rule 8)
rg -n --type rust '^\s*(//|///|//!).*\b(requires?|needs?|performs?|provides?|makes?|offers?) no [a-z]' PATHS

# Comma before a restrictive clause (rule 10), in the sentences being rewritten
rg -n --type rust '^\s*(//|///|//!).*, (because|so) ' PATHS

# Planning-phase references, which CLAUDE.md forbids in code and comments
rg -n --type rust '\b(Phase|Step) [0-9]' PATHS
```

A match can span a line break. Join the lines before searching a file:

```sh
tr '\n' ' ' < FILE | grep -oE '.{60}(instead of|rather than|no longer).{60}'
```

For a commit message, check the subject length and the body wrap before
committing:

```sh
git log -1 --format=%s | awk 'length>50'
git log -1 --format=%b | awk 'length>72'
```

## Provenance

Adapted from the `writing-review` skill in
<https://github.com/samuelkarp/skills>, copyright 2026 Samuel Karp, licensed
under the Apache License 2.0 (see [LICENSE](LICENSE)). The rules are kept; the
examples, the artifact table, the trailer policy, and the sweep mode are this
project's.
