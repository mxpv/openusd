---
name: commit
description: Stage and commit changes with pre-flight checks, doc updates, and roadmap tracking.
argument-hint: "[description]"
disable-model-invocation: false
allowed-tools: Bash(cargo *) Bash(git *)
---

Commit the current changes. Additional context from the user: $ARGUMENTS

Follow these steps:

1. **Pre-flight checks** (skip if no `.rs`, `Cargo.toml`, or `Cargo.lock` files were changed):
   Run these in parallel:
   - `cargo fmt --all -- --check --files-with-diff`
   - `cargo clippy --all-targets --all-features -- -D warnings`
   - `cargo test --all-targets --all-features`
   - If a check fails, try to fix it automatically for simple cases (e.g. run `cargo fmt` for formatting failures). For complex failures, stop and report.

2. **Verify test coverage** (skip if no code changes):
   - Check if the changes are covered by existing tests.
   - If new functionality was added without tests, add them before proceeding.

3. **Analyze changes**:
   - Run `git status` and `git diff` to understand staged and unstaged changes.
   - If there are both staged and unstaged changes, ask the user whether to add the unstaged changes or commit only what's staged — unless all changes clearly belong to the same logical change, in which case stage everything.
   - The additional context above, when the user gave any, goes into the commit message. If none was given and the changes are non-trivial, ask the user before proceeding.

4. **Update documentation**:
   - Verify doc comments are up to date with the code changes.
   - Run the `writing-review` skill in its bounded mode over the comments and docs the diff touches, and apply what it finds.
   - If the changes affect module structure or public API, update the Architecture section in CLAUDE.md.
   - Stage any doc changes alongside the code changes.

5. **Update roadmap**:
   - If the changes implement a feature listed in ROADMAP.md, update the Version column to `main`.
   - Keep the row's Notes cell laconic: it says what is supported and what remains, not every feature handled. The ROADMAP.md Style section in CLAUDE.md has the shape.
   - Stage ROADMAP.md alongside the other changes.

6. **Generate commit message**:
   - Draft the message, then revise it with the `writing-review` skill's commit-message rules (`references/commit-messages.md`): an imperative subject of 50 characters or fewer, a body wrapped at 72 only for what the subject and diff cannot say, present tense, no phantom history, and nothing about test status or the review.
   - Keep commits focused and atomic — one logical change per commit.
   - Proofread for grammar, technical accuracy, and completeness.
   - Show the commit message to the user and wait for confirmation before committing.
   - Don't list the staged files in the confirmation message or the commit body — `git status` is the source of truth. Show only the commit title and body.

7. **Commit**: Stage the relevant files, then create the commit.
   - The commit runs through the **Bash** tool, which is POSIX `bash` and may
     differ from the contributor's interactive shell. Pass the message on
     **stdin** via a quoted heredoc so shell quoting cannot corrupt it:

     ```
     git commit -F - <<'COMMIT_MSG'
     <subject line>

     <body wrapped at 72>
     COMMIT_MSG
     ```

   - Do NOT use `git commit -m "…"` for a multiline or special-character
     message, and do not reach for your interactive shell's own here-string or
     quoting idioms — they may not be valid `bash` and can inject stray
     characters into the message. The quoted delimiter (`'COMMIT_MSG'`) keeps
     `$`, backticks, and `!` literal; UTF-8 (em-dashes, etc.) passes through
     fine.

The harness's own commit guidance asks for an AI co-author trailer and a
"Generated with Claude Code" line. This project declines both: the commit
message and any PR text carry no AI attribution or generation notice.
