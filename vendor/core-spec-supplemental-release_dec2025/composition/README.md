# Composition

This directory contains an experimental sample implementation of the USD composition engine, per the AOUSD Core Specification.

## Running Tests

To run all composition tests, run this from the repository root:

`uv run -m unittest discover composition`

## Converter

The tests rely on usd binary assets, however to streamline creation of these files there are text versions of these
files as well.

Therefore, every test has text versions in a usda directory, and binary versions outside of that directory.
To quickly convert them, you can run this command:

`uv run ./composition/tests/assets/converter.py`