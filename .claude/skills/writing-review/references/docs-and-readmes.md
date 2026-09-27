# Docs, READMEs, plans, and the ROADMAP

Adapted from the samuelkarp/skills `writing-review` reference
`docs-and-readmes.md` (Apache-2.0); the ROADMAP and plan sections are this
repository's.

## State the rule

A reference doc states the constraint as a flat rule. The mechanism and the
reasoning go in the code comment or the commit body.

```
BAD   A relocate under a variant confuses the map function, so composition
      refuses it alongside the variant selection.
GOOD  A relocate whose source lies under a variant selection is invalid and
      is reported as a composition error.
```

Passive voice is acceptable here because it states the rule directly. Do not
turn a plainly stated rule back into an explanatory active sentence.

Prefer the literal action a function takes: "returns an error" over "rejects
them with an error". Where a semicolon splices two related facts, use the
connective that names the relation.

## Write at the document's altitude

State each rule at the altitude of the document's subject, and give the
specific case its own heading. A page about asset resolution in general is
written in terms of `@...@` asset paths, not in terms of the one `.usdz`
archive that was in front of the author; the archive case gets its own
section. A rule written at the wrong altitude implies the general mechanism
applies only to the one case in front of you.

Values that belong in the code and the spec do not belong in a document about
the mechanism. "Enums are passed as integers" is the rule; the integer for
each variant is in the code.

## Do not re-derive the rule

After stating a rule, do not walk through an example that only re-derives it.
The rule above already said it.

## Present tense only

Describe current behaviour. No "no longer X", no "used to X". Say what the
code does today, not what it changed from. Tracking historical behaviour in a
doc adds noise. Cut forward-looking sections too: a "Status" section saying a
future change "will reuse it" describes nothing that exists.

## Rejected alternatives in the conditional

In an "Alternatives considered" section, state consequences in the
conditional. The option does not exist in the running system, and the present
indicative asserts a hypothetical as fact.

```
BAD   a naive per-prim bump under-invalidates
GOOD  a naive per-prim bump would under-invalidate
```

State the disqualifying property. Do not grant a merit first.

## ROADMAP rows

The ROADMAP tells a reader what is supported and what remains, laconically.
CLAUDE.md's ROADMAP.md Style section gives the shape; the pass checks it:

- The status emoji says whether the row is done. The Notes cell does not
  restate it.
- The Notes cell names the key types or traits a reader would look for, and
  does not describe what they do. Their doc comments are the source of truth.
- Anything materially incomplete is a short `Remaining — X; Y` clause, or a
  `Remaining:` list when there are several distinct items. It goes once
  nothing is left.
- No enumeration of every method, variant, or edge case handled. If the
  implementation is complete and unremarkable, the row is one line.

A row that reads as a changelog of what landed is rewritten to what a user can
rely on.

## Plans and handoff docs are self-standing

A plan is read by an agent or a person who has the repository and none of the
authoring conversation. In-repo cross-references are fine. Every external
resource is written into the doc: the C++ file a step ports, the spec section,
the vendor asset a test uses. A plan that says "port this from C++" without
naming the file is useless to whoever runs it.

A plan describes what each step does. It does not carry the phase and step
numbers into the code, comments, fixtures, or commit messages it produces;
CLAUDE.md forbids those there.

## README audience

A README is for a user of the crate: what it is, how to depend on it, which
feature flags enable what, a quick start, and the limitations. Keep it there.

Maintainer mechanics go elsewhere: the release workflow lives in the release
skill, CI in `.github/`, contribution rules in CONTRIBUTING.md. A README
mentions them only where a user needs them to use the project.

Preserve deliberate authored voice. A warning a README carries on purpose
stays as written.
