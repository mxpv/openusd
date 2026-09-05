---
name: release
description: Publish a new release of the openusd workspace crates. Use when cutting a release, bumping the version, or publishing to crates.io.
argument-hint: "[version] [highlights or other instructions]"
disable-model-invocation: true
allowed-tools: Bash(cargo *) Bash(git *) Bash(gh *)
---

Publish a new release of the openusd workspace. Every crate in `crates/`
shares one version, one tag, and one set of release notes, and they publish
together. The version argument is: $ARGUMENTS

Follow these steps:

1. **Validate version**: The arguments may include a version, highlights for the changelog, and/or other instructions — parse them out.
   - If a version is given, it must follow semver (e.g. `0.3.0`) and must NOT include a `v` prefix.
   - If no version is given, default to the next minor version above the current `version` in the root Cargo.toml's `[workspace.package]`: bump the minor component and reset the patch to `0` (e.g. `0.3.0` → `0.4.0`, `0.9.1` → `0.10.0`, `1.2.3` → `1.3.0`).
   - Treat any non-version text in the arguments as guidance for the changelog summary or extra instructions to follow during the release.

2. **Pre-flight checks**: Run these in parallel and stop if any fail:
   - `cargo clippy --workspace --all-targets --all-features -- -D warnings`
   - `cargo fmt --all -- --check --files-with-diff`
   - `cargo test --workspace --all-targets --all-features`

3. **Generate changelog**:
   - Run `git describe --tags --abbrev=0` to find the previous tag, then `git log <prev_tag>..HEAD --pretty=format:"- %s (%h)"` to list commits.
   - Start with a brief, natural summary (2-4 sentences). Write it like a human would in a project update — e.g. "This release introduces the PCP composition engine with full LIVRPS arc support including relocates." Don't enumerate changes in the summary — capture the overall narrative in plain language.
   - After the summary, add a "Compliance" section. Introduce it with "New [AOUSD Core Spec](docs/aousd_core_spec_1.0.1.pdf) coverage in this release:" then list newly covered spec items. Check ROADMAP.md for features marked with `main` (about to become this version). Format each item as `` `<section>` <name> `` (e.g. `` `10.3.2.6` Relocates ``). Skip this section if no new spec coverage was added.
   - Then list the detailed changes: group commits by area (composition engine, text parser, binary reader, stage, asset resolution, etc.) and then by type (features, fixes, dependencies). Keep each commit as its own line — do not merge distinct features into one bullet.
   - Filter out noise (formatting, CI, README updates, CLAUDE.md).
   - Wrap code identifiers (types, functions, methods, traits, modules, flags, etc.) and crate names/versions in backticks, e.g. `- Add \`ListOp::compose_over\` for list-edit composition (82845fd)`.
   - Write the changelog to a temp file (e.g. `/tmp/CHANGELOG-<version>.md`), NOT to the repo. It is only used for the GitHub release notes.
   - Show the changelog to the user and wait for confirmation before proceeding.

4. **Bump version and commit**: The version lives in two places in the root Cargo.toml and both must move together:
   - `[workspace.package] version` — the version every crate inherits.
   - `[workspace.dependencies] openusd.version` — what `openusd-schemas` requires of `openusd`. A stale value here publishes a crate that depends on the previous release.

   Then update the dependency examples to the new version (use the `major.minor` form, e.g. `openusd = "0.5"` for `0.5.0`) in all three READMEs: `README.md`, `crates/openusd/README.md`, and `crates/openusd-schemas/README.md` (which pins both crates). Stage the root Cargo.toml and the three READMEs (Cargo.lock is gitignored). Commit with message `Bump crate version to <version>`.

5. **Tag**: Create tag `v<version>` on the version bump commit. Do NOT move the tag later — it must stay on this commit.

6. **Update roadmap**: In ROADMAP.md, replace every occurrence of the literal string `` `main` `` with `` `<version>` `` — this includes both the Version column cells and any `` `main` — `` annotations inside the Notes column. Use the Edit tool to make each replacement individually and precisely; do NOT use sed, awk, or any shell one-liner (they mangle backticks on macOS). After editing, run `grep -n '`main`' ROADMAP.md` to confirm zero matches remain, then show the full `git diff ROADMAP.md` to the user and wait for confirmation before staging or committing anything. Commit with message `Update ROADMAP` only after the user approves the diff.

7. **Publish to crates.io**: Run `cargo publish --workspace` from the repository root. It publishes every member in dependency order, so `openusd` lands before `openusd-schemas`. Publishing is NOT atomic: if the registry fails partway, some crates are published at the new version and others are not — report exactly which succeeded rather than retrying blindly, since a published version cannot be replaced. Wait for confirmation from the user before running this step.

8. **Push**: Run `git push --atomic origin HEAD v<version>` to push commits and tag together. Wait for confirmation from the user before running this step.

9. **Create GitHub release**: Run `gh release create v<version> --notes-file /tmp/CHANGELOG-<version>.md --latest`.

Important:
- Always wait for user confirmation before publishing to crates.io (step 7) and pushing (step 8).
- Always wait for user confirmation before committing the ROADMAP update (step 6).
- Do NOT use `--dry-run` unless the user explicitly asks for a dry run.
- Do NOT add "Co-Authored-By" or "Generated with Claude Code" to commits or the release.
