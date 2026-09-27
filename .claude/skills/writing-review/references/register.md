# Register

Adapted from the samuelkarp/skills `writing-review` reference of the same name
(Apache-2.0); the worked example is this repository's.

Each tic compresses reasoning into syntax. The text then reads as a model
showing its work instead of a description of the system. The register the
project wants is flat positive assertions, one proposition each, with no
subordination carrying the claim.

## A rejected sentence

A doc comment on `LabelsQuery::over` in `openusd-schemas` was drafted as:

> A start of negative infinity reaches the earliest sample authored. C++
> reaches it for positive infinity too, since `GfInterval::IsMinFinite`
> rejects both, where a start above every sample holds the last one here.

Every clause is accurate. Review rejected it anyway.

1. **Proposition as modifier.** "where a start above every sample holds the
   last one here" is a complete claim (condition, behaviour, and the contrast
   with C++) folded into a trailing clause so the sentence can keep moving.
   Assert one proposition per sentence.
2. **Definition by negation.** "rejects both" says what the C++ predicate
   fails to accept. The positive form is what C++ does: it treats a start at
   either infinity as the earliest time.
3. **Preemptive qualifier.** "here" answers an objection no reader raised.
4. **Justification by mechanism.** Naming `GfInterval::IsMinFinite` explains
   the Rust rule by way of a C++ implementation detail the reader of this
   crate cannot see. A doc comment states what this code does; the C++
   difference is one flat sentence after it.

The rewrite:

> A start below every sample reaches the earliest one authored, and a start
> above every sample reads what is held after the last, which is what the prim
> is labelled from then on. C++ treats a start at either infinity as the
> earliest time.

Own terms first, one proposition per clause, then the difference stated
without defending it.

## The ten tics

1. **Proposition as modifier.** A complete claim folded into a trailing
   `that`- or `where`-clause hanging off a noun.
2. **Definition by negation.** What does not happen, to whom, under what
   condition. Find the positive form. The kernel's own framing of a permission
   is "processes with uid 0 have privilege", not "does not grant to uid 0".
3. **Preemptive qualifier.** A trailing phrase answering an objection nobody
   raised.
4. **`so`-chaining.** Three `so` clauses in six lines performs the derivation.
   State cause, then effect, once.
5. **Counterfactual narration.** "nothing in the stage can reach the layer"
   describes a design that does not exist.
6. **Diff-anchored imperative.** "Keep the dedup after the sort" means
   something only to a reader of the change. "Dedup after the sort" describes
   the code.
7. **Clause-joining commas, used sparingly.** A comma before `and` or `but`
   joining two independent clauses reads as a pause indicating too much
   drama. Independent clauses can be joined, with taste, and model training
   reaches for the join more often than is tasteful. Prefer two sentences.
   List commas ("the real, effective, and saved uids") are unaffected.
8. **Plain verb over the compressed negative.**

   ```
   BAD   requires no registry          GOOD  does not require a registry
   BAD   performs no type check        GOOD  does not check the type
   BAD   needs no schema               GOOD  does not need a schema
   ```

   This is the rule most often under-applied: after one fix lands, the same
   shape survives elsewhere in the change. When a correction lands, grep the
   change for the pattern, not the phrase that was quoted. `has no X` stays
   where X is the noun the reader is looking for ("an attribute with no
   samples").
9. **Keep the noun.** "are privileged operations", not "are privileged". "A
   layer with ...", not "A layer created with ..." when the participle adds
   nothing.
10. **No comma before a restrictive `because` or `so` clause.**

    ```
    BAD   resolves it before the walk, because the walk reads the offset
    BAD   holds the view, so the accessors resolve once
    ```

    Delete the comma before `because`. At `so`, split into two sentences,
    which also clears rule 4.

## Metaphors

No metaphorical or flowery language in commit messages, docs, or comments. The
reader has to decode a metaphor back into the literal fact.

```
BAD   seed then bite
GOOD  the first run leaks the layer, the second fails on it

BAD   waits for a start that never comes
GOOD  stays blocked on the load barrier
```

Deliberate authored voice in a README is the one exception. Do not extend that
voice into routine docs, commit messages, or explanations.

## Coined terms

Write with the plain verb and the name the domain already uses. This project
mirrors C++ OpenUSD, so most concepts already have a name: `UsdResolveInfo`,
"prim index", "layer stack", "composition arc", "spec". Use that name, the
exact identifier, or the field name.

If a word needs a footnote, or you reached for it because no ordinary verb
fit, it is the wrong word. Coining a label for something that already has a
name (a function, a file, a field, a diagnostic) forces the reader to ask what
you mean, and the answer is always the real name. Say "`Fill`'s error
branch", not "the refusal path".

A coined term does not stay in the prose. A word invented in a plan to group
two checks ran across a dozen messages and then appeared as a field in a
proposed error struct, where the existing `reason` field already said which
check failed. The cost is not one confusing sentence: the term reaches the
design document and then the code. Coining a word for a grouping is often the
tell that the grouping is not real.

## Vague filler

Do not use filler that sounds meaningful and is not: "wire up the plumbing",
"lay the groundwork", "improve robustness". Name the concrete action, file, or
change, or say nothing. When offering a next step, name the specific file or
function.

## Learning the register from the repository

Sample the commits the maintainer wrote; see
[commit-messages.md](commit-messages.md) for the command and what to expect.
