---
name: commit
description: Stage and commit changes with pre-flight checks, doc updates, and roadmap tracking.
argument-hint: "[description]"
disable-model-invocation: false
allowed-tools: Bash(cargo *) Bash(git *)
---

Commit the current changes. Additional context from the user: $ARGUMENTS

Follow these steps:

1. **Pre-flight checks**: Run these in parallel:
   - `cargo fmt --all -- --check --files-with-diff`
   - `cargo clippy --all-targets --all-features -- -D warnings`
   - `cargo test --all-targets --all-features`
   - If a check fails, try to fix it automatically for simple cases (e.g. run `cargo fmt` for formatting failures). For complex failures, stop and report.

2. **Verify test coverage**:
   - Check if the changes are covered by existing tests.
   - If new functionality was added without tests, add them before proceeding.

3. **Analyze changes**:
   - Run `git status` and `git diff` to understand staged and unstaged changes.
   - If there are both staged and unstaged changes, ask the user whether to add the unstaged changes or commit only what's staged — unless all changes clearly belong to the same logical change, in which case stage everything.
   - `$ARGUMENTS` may provide additional context to incorporate into the commit message. If no context is provided and the changes are non-trivial, ask the user before proceeding.

4. **Update documentation**:
   - Verify doc comments are up to date with the code changes.
   - If the changes affect module structure or public API, update the Architecture section in CLAUDE.md.
   - Stage any doc changes alongside the code changes.

5. **Update roadmap**:
   - If the changes implement a feature listed in ROADMAP.md, update the Version column to `main`.
   - Stage ROADMAP.md alongside the other changes.

6. **Generate commit message**:
   - Use a short, descriptive title (50 characters or less).
   - Include a brief body (1-3 sentences) summarizing changes when needed (wrap at 120 characters).
   - Keep commits focused and atomic — one logical change per commit.
   - Proofread for grammar, technical accuracy, and completeness.
   - Show the commit message to the user and wait for confirmation before committing.

7. **Commit**: Stage relevant files and create the commit.

Strictly forbidden — these restrictions are non-negotiable:
- Do NOT add "Generated with Claude Code" or any AI generation notices.
- Do NOT add "Co-Authored-By: Claude" or any AI co-author attribution.
- Do NOT include any reference to AI assistance, generation, or automation.
