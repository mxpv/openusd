import argparse
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path


def convert_test(entry: Path, fresh=False):
    parent = entry.parent
    file_base = os.path.splitext(entry.name)[0]
    test_base = parent.name
    test_dir = Path(__file__).parent / f"{test_base}_{file_base}" / "usda"
    if fresh and test_dir.parent.exists():
        shutil.rmtree(test_dir.parent)

    os.makedirs(test_dir, exist_ok=True)

    for root, dirs, files in os.walk(parent):
        root = Path(root)
        rel_path = root.relative_to(parent)
        target_dir = test_dir / rel_path
        os.makedirs(target_dir, exist_ok=True)
        for f in files:
            file_path = root / f
            with open(file_path, "r", encoding="utf-8") as fp:
                content = fp.read()
                content = content.replace(".usda", ".usd")

            target_path = target_dir / f.replace(".usda", ".usd")
            with open(target_path, "w", encoding="utf-8") as fp:
                fp.write(content)


def write_pcp_results(usd_root, entry, tester):
    root_dir = Path(__file__).parents[3]
    parent = entry.parent
    file_base = os.path.splitext(entry.name)[0]
    test_base = parent.name
    test_dir = Path(__file__).parent / f"{test_base}_{file_base}"

    usda = test_dir / "usda" / f"{file_base}.usd"
    results = test_dir / "pcp.txt"
    if results.exists():
        return

    command = [sys.executable, tester.as_posix(), "--usd", usda.relative_to(root_dir).as_posix()]
    try:
        result = subprocess.run(command, capture_output=True, text=True, cwd=root_dir)
        stdout, stderr = result.stdout, result.stderr
    except subprocess.CalledProcessError as e:
        print(f"Failed to process {usda}")
        stdout, stderr = e.stdout, e.stderr

    out = stdout or ""
    if stderr:
        if not stderr.startswith("--"):
            out += os.linesep + "-" * 80
        stderr = stderr.replace(rf"{str(usd_root)}", "").replace(f"{usd_root.as_posix()}", "")
        stderr = stderr.replace(rf"{str(root_dir)}", "").replace(f"{root_dir.as_posix()}", "")
        out += os.linesep + stderr

    with open(results, "w", encoding="utf-8", newline="\n") as f:
        f.write(out)


def validate_usd_version(usd_root):
    version_cmake = usd_root / "cmake/defaults/Version.cmake"
    if not version_cmake.exists():
        raise OSError(f"Could not find {version_cmake}")

    version_numbers = []
    pattern = re.compile(r'^set\(PXR_.*_VERSION "([0-9]+)"\)')
    with open(version_cmake, "r") as fp:
        for line in fp.readlines():
            if match := pattern.match(line):
                ver = int(match.groups()[0])
                version_numbers.append(ver)

    required = (0, 25, 8)
    if version_numbers[1] < required[1] or (version_numbers[1] >= required[1] and version_numbers[2] < required[2]):
        raise RuntimeError(f"Found OpenUSD version {version_numbers} but require {required}")

    return True


def find_pcp_tests(pcp_cmake):
    tests = {}
    with open(pcp_cmake, "r", encoding="utf-8") as fp:
        for line in fp.readlines():
            if "tests/testPcpCompositionResults" not in line:
                continue

            tokens = [t.strip() for t in line.split("tests/testPcpCompositionResults")[-1].split() if t]
            test = tokens[-1].replace('"', "")
            test = test.split("/")
            if len(test) < 2:
                continue

            tests.setdefault(test[0], []).append(test[1])
    return tests


def copy_tests(usd_root, tests, fresh=False):
    test_root = usd_root / "pxr/usd/pcp/testenv"
    if not test_root.exists():
        raise OSError(f"Could not find {test_root}")

    tester = usd_root / "pxr/usd/pcp/testenv/testPcpCompositionResults.py"
    if not tester.exists():
        raise OSError(f"Could not find {tester}")

    skip = []

    for sub in os.listdir(test_root):
        sub = test_root / sub
        if not sub.is_dir():
            continue

        name = sub.name.split("_", 1)[-1].split(".testenv")[0]
        if name not in tests or name in skip:
            continue

        subdir = sub / name
        if not subdir.exists():
            raise OSError(f"Could not find {subdir}")

        for entry in tests[name]:
            entry = subdir / entry
            if not entry.exists():
                raise OSError(f"Could not find {entry}")

            convert_test(entry, fresh=fresh)
            write_pcp_results(usd_root, entry, tester)


def process(usd_root, fresh=False):
    validate_usd_version(usd_root)

    pcp_cmake = usd_root / "pxr/usd/pcp/CMakeLists.txt"
    if not pcp_cmake.exists():
        raise OSError(f"Could not find {pcp_cmake}")

    tests = find_pcp_tests(pcp_cmake)
    copy_tests(usd_root, tests, fresh=fresh)


def main():
    parser = argparse.ArgumentParser(description="Convert Pixar's OpenUSD PCP Museum to our own tests")

    parser.add_argument(
        "-u",
        "--usdPaths",
        type=str,
        nargs="*",
        default=("~/Projects/OpenUSD", "~/Projects/usd"),
        help="The root location of your OpenUSD source code",
    )
    parser.add_argument("--fresh", action="store_true", help="Create directories fresh")
    args = parser.parse_args()
    for path in args.usdPaths:
        path = Path(os.path.expanduser(path))
        if path.exists():
            usd_root = path
            break
    else:
        raise OSError(f"Could not locate any of the search paths: {args.usdPaths}")

    process(usd_root, fresh=args.fresh)


if __name__ == "__main__":
    main()
