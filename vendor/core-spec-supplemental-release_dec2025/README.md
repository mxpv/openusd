# core-spec-supplemental
This repository is dedicated to host code for compliance testing and other efforts supplemental to the draft specification content in the core-spec-wg repo.

## Dependencies

### Python

At a minumum, this code requires Python 3.12 to run.

### Managing dependencies via uv

We recommend using [uv](https://github.com/astral-sh/uv) to manage dependencies
and run tests. To do so, simply install uv if you do not already have it
installed - follow the instructions on the uv README here:

- https://github.com/astral-sh/uv?tab=readme-ov-file#installation

Then, to run tests or other scripts, simply use `uv run <cmd>` in place of
`python3 <cmd>`, and uv will automatically download / refresh dependencies as
needed before running the given script.

### Running tests

To run ALL tests in this repository, run this from the repository root:

```
uv run -m unittest discover
```

See individual subdirectories for instructions on running the tests just for
that directory.

### File Formats

See the [File Formats Readme](./file_formats/README.md).

### Composition

See the [Composition Readme](./composition/README.md).

### Value Resolution

See the [Value Resolution Readme](./value_resolution/README.md)