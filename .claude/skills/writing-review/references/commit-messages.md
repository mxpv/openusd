# Commit messages

Adapted from the samuelkarp/skills `writing-review` reference of the same name
(Apache-2.0); the conventions and the voice sample are this repository's.

The form is the one <https://chris.beams.io/posts/git-commit/> describes.
Each commit message becomes a bullet in the release notes, so the subject has
to stand on its own.

## Subject

- Imperative mood, capitalised, no trailing period, 50 characters or fewer.
- No type prefix (`feat:`, `fix(pcp):`). The history has none.
- The subject verb names the literal action, and the object names the concept
  in the domain's words: "Answer what a prim is labelled under a taxonomy",
  "Spell open interval bounds with gf::Interval", "Resolve which collision
  groups collide".
- Blank line between subject and body.

## Default to a subject only

The subject plus the diff usually convey the change, and a body that restates
them gets deleted.

A body earns its place for a fact a reader cannot infer from the subject and
the diff: the C++ API a new method mirrors, the constraint that forced a
design, a behaviour that differs from C++ and why, the production change made
to enable a test. Keep the body to that fact, wrapped at 72 characters.

Never in a body:

- Test status, "all tests pass", "goldens unchanged", "clippy clean". CI
  proves it; the message does not.
- A list of the files touched. `git show --stat` is the source of truth.
- The review that produced the change ("addresses review findings", "fixes
  the P2 on ..."). The commit describes the code, not the conversation.
- A justification of why the change is safe when the diff shows it, or an
  answer to a concern raised only in the working conversation.
- Planning vocabulary: "Phase 2", "step 3 of the plan".
- Any AI attribution or generation notice. The project declines the
  `Co-Authored-By` trailer and the "Generated with Claude Code" line the
  harness asks for.

## Body style

Stay in the register the subject sets and describe the code as it is after the
commit.

- **Cause before effect.** Lead with the constraint, then what it makes
  necessary, then what the change does about it.
- **Name real identifiers.** `Attribute::unioned_time_samples`,
  `UsdAttribute::GetUnionedTimeSamples`, `gf::Interval`, not "the new helper"
  or "the C++ equivalent". Backticks are optional in a body; the history uses
  both spellings.
- **Give a rule its reason, and put an untaken path in the conditional.**
  "A per-prim bump would under-invalidate" says what would go wrong.
- **Present tense, no phantom history.** Do not frame the change as an
  improvement over a state the reader of the history never sees: "X rather
  than only Y", "no longer does Y", "instead of the old Y". The diff against
  the parent already shows what changed, and after a squash the old state
  never existed.

```
BAD   asks the attributes whether they may vary over time rather than
      recording that at construction
GOOD  asks the attributes whether they may vary over time
```

A contrast between two things that both exist in the tree is fine: two
coexisting tests, or the C++ behaviour a body says this code departs from.

## Checks before committing

```sh
git log -1 --format=%s | awk 'length>50'
git log -1 --format=%b | awk 'length>72'
```

## Sampling the maintainer's voice

The history is a single maintainer's, so the recent log is the register to
aim at. Read the last thirty subjects and a handful of bodies before drafting:

```sh
git log -30 --no-merges --format='%s'
git log -8 --no-merges --format='### %h %s%n%b'
```

Expect subjects of four to eight words naming a verb and a concept, and bodies
of two to eight plain lines that name the identifiers involved and the C++
counterpart where one exists. Aim drafts at that sample. In a repository with
several authors, filter by email (`--author=`) so one voice is sampled, and
leave out any commit that carries an AI trailer, since a message a reviewer
merely tolerated records what they accepted, not how they write.
