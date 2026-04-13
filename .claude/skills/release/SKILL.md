---
name: release
description: Publish a new release of the openusd crate. Use when cutting a release, bumping the version, or publishing to crates.io.
argument-hint: "[version]"
disable-model-invocation: true
allowed-tools: Bash(cargo *) Bash(git *) Bash(gh *)
---

Publish a new release of the openusd crate. The version argument is: $ARGUMENTS

Follow these steps:

1. **Validate version**: Ensure the version argument is provided and follows semver (e.g. `0.3.0`). If missing, ask for it. The version must NOT include a `v` prefix.

2. **Pre-flight checks**: Run these in parallel and stop if any fail:
   - `cargo clippy --all-targets --all-features -- -D warnings`
   - `cargo fmt --all -- --check --files-with-diff`
   - `cargo test --all-targets --all-features`

3. **Generate changelog**:
   - Run `git describe --tags --abbrev=0` to find the previous tag, then `git log <prev_tag>..HEAD --pretty=format:"- %s (%h)"` to list commits.
   - Start with a brief, natural summary (2-4 sentences). Write it like a human would in a project update — e.g. "This release introduces the PCP composition engine with full LIVRPS arc support including relocates." Don't enumerate changes in the summary — capture the overall narrative in plain language.
   - Then list the detailed changes: group commits by area (composition engine, text parser, binary reader, stage, asset resolution, etc.) and then by type (features, fixes, dependencies). Keep each commit as its own line — do not merge distinct features into one bullet.
   - Filter out noise (formatting, CI, README updates, CLAUDE.md).
   - Wrap code identifiers (types, functions, methods, traits, modules, flags, etc.) and crate names/versions in backticks, e.g. `- Add \`ListOp::compose_over\` for list-edit composition (82845fd)`.
   - Write the changelog to a temp file (e.g. `/tmp/CHANGELOG-<version>.md`), NOT to the repo. It is only used for the GitHub release notes.
   - Show the changelog to the user and wait for confirmation before proceeding.

4. **Bump version and commit**: Edit the `version` field in Cargo.toml to `<version>`. Stage Cargo.toml (Cargo.lock is gitignored). Commit with message `Bump crate version to <version>`.

5. **Tag**: Create tag `v<version>` on the version bump commit. Do NOT move the tag later — it must stay on this commit.

6. **Update roadmap**: In ROADMAP.md, replace all occurrences of `main` in the Version column with the release version (e.g. `0.3.0`). Stage ROADMAP.md and commit with message `Update ROADMAP`. This commit comes after the tag, which is intentional.

7. **Publish to crates.io**: Run `cargo publish`. Wait for confirmation from the user before running this step.

8. **Push**: Run `git push --atomic origin HEAD v<version>` to push commits and tag together. Wait for confirmation from the user before running this step.

9. **Create GitHub release**: Run `gh release create v<version> --notes-file /tmp/CHANGELOG-<version>.md --latest`.

Important:
- Always wait for user confirmation before publishing to crates.io (step 7) and pushing (step 8).
- Do NOT use `--dry-run` unless the user explicitly asks for a dry run.
- Do NOT add "Co-Authored-By" or "Generated with Claude Code" to commits or the release.
