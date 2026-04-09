import sys

# Ensure Python 3.12+
if sys.version_info < (3, 12):
    sys.stderr.write("Error: This script requires Python 3.12 or later.\n")
    sys.exit(1)

import argparse
import os
import time
from pathlib import Path
from pprint import pprint

from parsers.binary.binary_parser import BinaryParser

# Constants
USD_SEARCH_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tests/assets/binary")
OUTPUT_DIR = "output"


def find_usd_files(base_path):
    """Recursively find USD files under the specified path."""
    print(f"Searching for USD files in: {base_path}")
    usd_files = {}
    for usd_path in Path(base_path).rglob("*.usdc"):
        # skip files that contain /usda/
        if "/usda/" in str(usd_path):
            continue
        parent_dir = usd_path.parent.parent.name  # Gets the direct folder name
        usd_files.setdefault(parent_dir, []).append(usd_path)
    return usd_files


def display_menu(usd_files):
    """Display a menu and allow the user to choose files."""
    print("\nAvailable USD files:")
    indexed_files = []  # List to store (index, file_path)

    idx = 1
    for group, files in usd_files.items():
        print(f"{group}:")
        for file in files:
            print(f"  [{idx}] {file.name}")
            indexed_files.append(file)
            idx += 1

    print("\nEnter a comma-separated list of numbers to select files, or 'A' to run all:")

    selections = input("> ").strip()

    if selections.lower() == "a":
        return indexed_files  # Select all files

    selected_files = []
    for sel in selections.split(","):
        try:
            file_idx = int(sel.strip()) - 1
            selected_files.append(indexed_files[file_idx])
        except (ValueError, IndexError):
            print(f"Warning: Invalid selection '{sel.strip()}'. Skipping.")

    return selected_files


def process_file(usd_file):
    """Parse a USD file and save the output JSON."""
    usd_file = Path(usd_file)
    parent_dir = usd_file.parent.parent.name
    output_file = Path(OUTPUT_DIR) / f"{parent_dir}_{usd_file.stem}.json"
    output_file.parent.mkdir(parents=True, exist_ok=True)

    print(f"Processing: {usd_file} -> {output_file}")

    start_time = time.time()
    parser = BinaryParser(str(usd_file))
    scene = parser.build_scene(output=str(output_file))
    # scene.to_usda()  # Uncomment if needed

    pprint(scene)
    print(f"Parsing took {time.time() - start_time:.2f} seconds.")


def main():
    parser = argparse.ArgumentParser(description="Parse USD files and generate JSON output.")
    parser.add_argument("usd_file", nargs="?", help="Path to a USD file to process.")
    parser.add_argument("--all", action="store_true", help="Process all available USD files.")

    args = parser.parse_args()

    if args.all:
        # Run all files automatically
        usd_files = find_usd_files(USD_SEARCH_PATH)
        selected_files = [file for files in usd_files.values() for file in files]
    elif args.usd_file:
        # Process a single file
        selected_files = [Path(args.usd_file)]
    else:
        # Interactive mode: Display menu
        usd_files = find_usd_files(USD_SEARCH_PATH)
        if not usd_files:
            print("No USD files found.")
            return
        selected_files = display_menu(usd_files)

    if not selected_files:
        print("No valid files selected. Exiting.")
        return

    for usd_file in selected_files:
        process_file(usd_file)


if __name__ == "__main__":
    main()
