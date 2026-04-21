# Contributing to openusd

The project is under active development and contributions are welcome in any form — feedback,
bug reports, feature requests, and code improvements.

## Submission Guidelines

- Large Changes:
  - If you're planning a large changeset, please [open an issue](https://github.com/mxpv/openusd/issues)
    first so we can discuss the approach before you invest significant effort
- Code Quality:
  - Write clean and idiomatic Rust code that follows existing patterns in the codebase
  - Unit test coverage is highly recommended
  - Make sure all CI checks pass (`cargo build`, `cargo test`, `cargo clippy`, `cargo fmt`)
- Spec Compliance: If your change implements a feature tracked in [ROADMAP.md](ROADMAP.md), update the
  corresponding row to mark the status as :white_check_mark: and set the Version column to `main`
- Issue References: If your PR fixes an existing issue, mention it in the PR description (e.g., "Fixes #123")
- Commit Messages:
  - Each commit message represents a bullet in the release notes, so it must be descriptive and clear
  - Add any additional context in the commit body
  - If you're using Claude Code, the `/commit` skill can generate the title and summary automatically
- Submit a pull request following standard
  [GitHub practices](https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/proposing-changes-to-your-work-with-pull-requests/about-pull-requests)

## License

By contributing, you agree that your contributions will be licensed under the [MIT License](LICENSE).

Thank you for contributing to openusd!
