"""Build the native benchmark against a matching usd-core wheel and checkout."""

import argparse
from pathlib import Path
import re
import subprocess
import sys
import sysconfig

from pxr import Usd


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--compiler", default="c++")
    args = parser.parse_args()
    source = args.source.resolve()
    output = args.output.resolve()
    version = Usd.GetVersion()
    config = (source / "cmake/defaults/Version.cmake").read_text()
    for name, value in zip(("MAJOR", "MINOR", "PATCH"), version):
        match = re.search(rf'set\(PXR_{name}_VERSION "(\d+)"\)', config)
        if not match or int(match[1]) != value:
            parser.error("OpenUSD checkout and usd-core wheel versions must match")

    generated = output.parent / "generated"
    (generated / "pxr/base/work").mkdir(parents=True, exist_ok=True)
    values = {
        "PXR_MAJOR_VERSION": version[0],
        "PXR_MINOR_VERSION": version[1],
        "PXR_PATCH_VERSION": version[2],
        "PXR_VERSION": version[0] * 10000 + version[1] * 100 + version[2],
        "PXR_USE_NAMESPACES": 1,
        "PXR_EXTERNAL_NAMESPACE": "pxr",
        "PXR_INTERNAL_NAMESPACE": "pxrInternal_v" + "_".join(map(str, version)),
        "PXR_PYTHON_SUPPORT_ENABLED": 1,
        "PXR_PREFER_SAFETY_OVER_SPEED": 0,
        "PXR_ARCH_PREFER_TSC_TIMING": 1,
    }
    header = (source / "pxr/pxr.h.in").read_text()
    for name, value in values.items():
        header = header.replace(f"@{name}@", str(value))
    (generated / "pxr/pxr.h").write_text(header)
    header = (source / "pxr/base/work/impl.h.in").read_text()
    header = header.replace("@PXR_WORK_IMPL_HEADER@", '"pxr/base/work/workTBB/impl.h"')
    (generated / "pxr/base/work/impl.h").write_text(header)

    libs = Path(sysconfig.get_path("purelib")) / "usd_core.libs"
    usd, = libs.glob("libusd_ms-*.so")
    tbb, = libs.glob("libtbb-*.so.*")
    python_lib = Path(sysconfig.get_config_var("LIBDIR"))
    command = [
        args.compiler, "-std=c++17", "-O3", "-Wno-deprecated",
        f"-I{generated}", f"-I{source}", f"-I{Path(sys.prefix) / 'include'}",
        f"-I{sysconfig.get_path('include')}",
        str(Path(__file__).with_name("open_bench.cpp")),
        "-Wl,--no-as-needed", str(tbb), "-Wl,--as-needed", str(usd),
        str(python_lib / sysconfig.get_config_var("LDLIBRARY")),
        "-Wl,--disable-new-dtags", f"-Wl,-rpath,{libs}",
        f"-Wl,-rpath,{python_lib}", "-o", str(output),
    ]
    subprocess.run(command, check=True)
    print(f"Built {output} against OpenUSD {'.'.join(map(str, version))}")


if __name__ == "__main__":
    main()
