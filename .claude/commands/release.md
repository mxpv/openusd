Publish a new release of the openusd crate. The version argument is: $ARGUMENTS

Follow these steps:

1. **Validate version**: Ensure the version argument is provided and follows semver (e.g. `0.3.0`). If missing, ask for it. The version must NOT include a `v` prefix.

2. **Pre-flight checks**: Run these in parallel and stop if any fail:
   - `cargo clippy --all-targets --all-features -- -D warnings`
   - `cargo fmt --all -- --check --files-with-diff`
   - `cargo test`

3. **Set version**: Run `cargo set-version <version>` to update Cargo.toml.

4. **Generate changelog**: Run `git describe --tags --abbrev=0` to find the previous tag, then `git log <prev_tag>..HEAD --pretty=format:"- %s (%h)"` to list commits. Group commits into meaningful categories (features, fixes, dependencies, etc.) and filter out noise (formatting, CI, README updates, CLAUDE.md). Wrap any code identifiers (types, functions, methods, traits, modules, flags, etc.) and crate names/versions in backticks, e.g. `- Add \`ListOp::compose_over\` for list-edit composition (82845fd)`. Write the result to CHANGELOG.md.

5. **Commit and tag**: Stage only Cargo.toml and Cargo.lock (if changed), commit with message `Bump crate version to <version>`, then create tag `v<version>`.

6. **Publish to crates.io**: Run `cargo publish --allow-dirty`. Wait for confirmation from the user before running this step.

7. **Push**: Run `git push --atomic origin HEAD v<version>` to push the commit and tag together.

8. **Create GitHub release**: Run `gh release create v<version> --notes-file CHANGELOG.md --latest`.

Important:
- Always wait for user confirmation before publishing to crates.io (step 6).
- Do NOT use `--dry-run` unless the user explicitly asks for a dry run.
- Do NOT add "Co-Authored-By" or "Generated with Claude Code" to commits or the release.
