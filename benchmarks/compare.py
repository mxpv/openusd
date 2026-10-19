"""Compare fresh-process USD benchmarks sequentially and retain raw output."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import time


def measure(command, timeout):
    start = time.monotonic()
    process = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
    elapsed = time.monotonic() - start
    output = process.stdout + process.stderr
    if process.returncode:
        raise RuntimeError(f"{command!r} exited {process.returncode}:\n{output}")
    phases = {
        name: float(seconds)
        for name, seconds in re.findall(
            r"^(open|metadata|retraverse|arrays)\s+([\d.]+)s", output, re.MULTILINE
        )
    }
    if not {"open", "metadata", "arrays"}.issubset(phases):
        raise RuntimeError(f"Missing benchmark phases:\n{output}")
    counts = {}
    for key in ("prims", "arrays", "elements"):
        match = re.search(rf"\b{key}: (\d+)", output)
        if match:
            counts[key] = int(match[1])
    if not {"prims", "arrays"}.issubset(counts):
        raise RuntimeError(f"Missing benchmark counts:\n{output}")
    match = re.search(r"rss_kib: (\d+)", output)
    if match:
        rss = int(match[1]) / 1024
    else:
        match = re.search(r"working set peak: ([\d.]+) MiB", output)
        rss = float(match[1]) if match else None
    return {
        "phases": phases,
        "total": sum(phases.values()),
        "process_seconds": elapsed,
        "peak_rss_mib": rss,
        "counts": counts,
        "output": output,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("--rust", type=Path, required=True)
    parser.add_argument("--cpp", type=Path, required=True)
    parser.add_argument("--before", type=Path)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=600)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check-status", action="store_true")
    args = parser.parse_args()
    if args.runs < 1 or args.warmups < 0:
        parser.error("runs must be positive and warmups nonnegative")
    binaries = {"rust": args.rust, "cpp": args.cpp}
    if args.before:
        binaries = {"before": args.before, **binaries}
    results = {name: [] for name in binaries}
    report = {
        "root": str(args.root.resolve()),
        "platform": platform.platform(),
        "cpu_count": os.cpu_count(),
        "binaries": {name: str(path.resolve()) for name, path in binaries.items()},
        "binary_sha256": {
            name: hashlib.sha256(path.read_bytes()).hexdigest()
            for name, path in binaries.items()
        },
        "options": ["--proxies", "--authored", "--no-heap"],
        "commands": {},
        "warmups": args.warmups,
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    expected = {}
    for run in range(-args.warmups, args.runs):
        for name, binary in binaries.items():
            # Older Rust benchmarks enumerate the same authored-only domain
            # properties through their core-only schema registry.
            options = ["--proxies", "--no-heap"]
            if name != "before":
                options.append("--authored")
            command = [str(binary.resolve()), *options, str(args.root.resolve())]
            report["commands"][name] = command
            result = measure(command, args.timeout)
            for key, count in result["counts"].items():
                if key in expected and count != expected[key]:
                    raise RuntimeError(f"{name}: {key}={count}, expected {expected[key]}")
                expected[key] = count
            print(f"{name} run {run + 1}: {result['total']:.3f}s", flush=True)
            if run >= 0:
                results[name].append(result)
                args.output.write_text(json.dumps(report, indent=2) + "\n")
    for name, runs in results.items():
        values = [run["total"] for run in runs]
        print(f"{name}: median {statistics.median(values):.3f}s "
              f"range {min(values):.3f}–{max(values):.3f}s")
    if args.check_status:
        expected_status = None
        for name, binary in binaries.items():
            status = args.output.with_suffix(f".{name}.status")
            command = [str(binary.resolve()), "--proxies", "--no-heap",
                       "--until", "metadata", "--status", str(status.resolve()),
                       str(args.root.resolve())]
            process = subprocess.run(command, capture_output=True, text=True,
                                     timeout=args.timeout)
            if process.returncode:
                raise RuntimeError(process.stdout + process.stderr)
            records = sorted(status.read_text().splitlines())
            if expected_status is not None and records != expected_status:
                raise RuntimeError(f"{name}: traversal status differs")
            expected_status = records
        report["status_records_matched"] = len(expected_status)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(f"Matched {len(expected_status)} traversal status records")


if __name__ == "__main__":
    main()
