# File Formats Parsing

This directory provides a sample implementation of reading USD binary and text files, per the AOUSD Core Specification.

## Running Tests

### All file format tests

To run all tests within the file_formats subdirectory, run this from the
repository root:

```
uv run -m unittest discover file_formats
```

### Binary Tests

To run the tests for the binary parser and file format, run this from the
repository root:

```
uv run -m unittest file_formats.tests.test_binary
```


### Text Tests

To run the tests for the binary parser and file format, run this from the
repository root:

```
uv run -m unittest file_formats.tests.test_text
```

## Manually invoking the text parser

For the text parser, you can run it on any sample string content with the following block:

```
from file_formats.parsers.text.usda import grammar, 

data = grammar.parse(content)
visitor = UsdaVisitor()
output = visitor.visit(data)
```

#### Generator

To run `generator.py`, you will need OpenUSD's Python API to create the files.
This is only needed to generate the sample files which will be included in the repo itself, so should not be
required to run often.

If you use `uv`, or another tool which manages dependencies via the
`pyproject.toml`, it should handle installing an appropriate version of the
`usd-core` PyPI module for you.

The generator has been tested with USD 24.3 and newer but should run with older versions.
Some features require newer versions of USD, but should be gated behind a USD version check.
