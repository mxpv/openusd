"""Converts the various .usda files to usdc for the binary parser to read into  a standard format"""

import json
import os
import re
from pathlib import Path

from pxr import Sdf

assets_dir = Path(os.path.dirname(os.path.abspath(__file__)))


def process_composition_block(block):
    sections = []
    section = []
    for line in block:
        if line.endswith(":") and line[0].isalpha():
            if section:
                sections.append(section)

            section = []

        section.append(line)
    else:
        if section:
            sections.append(section)

    data = {}

    for section in sections:
        key = section.pop(0)[:-1]
        if key == "Prim Stack":
            stack = {}
            for line in section:
                if line.startswith("ERROR:"):
                    data.setdefault("Errors", []).append(line)
                    continue
                k, v = line.split()
                stack[k] = v
            data[key] = stack
        elif key in ("Child names", "Property names", "Prohibited child names"):
            value = section[0].strip()
            value = eval(value)
            data[key] = value
        elif key in ["Property stacks"]:
            properties = data.setdefault(key, {})
            for line in section:
                if line.startswith("/"):
                    prop = properties.setdefault(line[:-1], {})
                    continue
                if line.startswith("ERROR:"):
                    data.setdefault("Errors", []).append(line)
                    continue
                k, v = line.split()
                prop[k] = v
        elif key in ["Attribute connections", "Relationship targets", "Deleted target paths"]:
            attributes = data.setdefault(key, {})
            for line in section:
                if line.startswith("/"):
                    attr = attributes.setdefault(line[:-1], [])
                    continue
                attr.append(line.lstrip())
        elif key in ["Variant Selections"]:
            variants = data.setdefault(key, {})
            for line in section:
                k, v = line.split("=")
                variants[k.strip()[1:]] = v.strip()[:-1]
        elif key in "Time Offsets":
            offsets = data.setdefault(key, [])
            pattern = re.compile(
                r"^ *(?P<layer>[\w\d]+.usd) *(?P<prim>\/[\w\d\/]+)? *(?P<type>\w*) *\(offset=(?P<offset>[\d\.]+), scale=(?P<scale>[\d\.]+)\)"
            )
            for line in section:
                if match := pattern.match(line):
                    match = match.groupdict()
                    if match["prim"]:
                        top_data = {"children": []}
                        top_data.update(match)
                        offsets.append(top_data)
                    else:
                        match.pop("prim")
                        top_data["children"].append(match)
                else:
                    raise RuntimeError(f"Failed to parse time offset: {line}")
        else:
            print(section)
            raise RuntimeError(f"Failed to process section: {key}")

    return data


def convert_pcp_log(root, errors=None):
    root = Path(root)
    pcp = root / "pcp.txt"
    if not pcp.exists():
        return
    print(f"Processing {pcp}")

    with open(pcp, "r", encoding="utf-8") as f:
        lines = f.readlines()

    data = {"Entry": os.path.basename(lines.pop(0).split("@")[1]), "Composing": {}}
    if errors:
        if not isinstance(errors, list):
            raise RuntimeError("Errors is not a list")
        data["Errors"] = errors
    blocks = []
    block = []
    for line in lines:
        if line.startswith("-----------"):
            if block:
                blocks.append(block)
            block = []
            continue

        line = line.rstrip()

        if line:
            block.append(line)

    else:
        if block:
            blocks.append(block)

    for block in blocks:
        block_key = block.pop(0)
        if block_key.startswith("Results for composing"):
            composing = block_key.split("<")[1].split(">")[0]
            data["Composing"].setdefault(composing, process_composition_block(block))
        elif block_key.endswith(":"):
            block_key = block_key[:-1]
            if block_key == "Layer Stack":
                layers = [l.strip() for l in block]
                data[block_key] = layers
                continue
        elif block_key.startswith("Error"):
            data.setdefault("Errors", []).append(block_key + "\n" + " ".join(block))
        elif block_key.startswith("Warning"):
            data.setdefault("Warnings", []).append(block_key + "\n" + " ".join(block))
        else:
            raise RuntimeError(f"Unsupported Block Key: {block_key}")

    out = root / "pcp.json"
    with open(out, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=4)


for child in os.listdir(assets_dir):
    path = assets_dir / child
    if not path.is_dir():
        continue

    usda_dir = path / "usda"
    errors = []
    for root, dirs, files in os.walk(usda_dir):
        root = Path(root)
        for f in files:
            if not f.endswith(".usd"):
                continue

            file_path = root / f
            target_path = path / file_path.relative_to(usda_dir)

            try:
                layer = Sdf.Layer.FindOrOpen(file_path.as_posix())
                layer.Export(target_path.as_posix(), args={"format": "usdc"})
            except Exception as e:
                print(f"Failed to convert {file_path}: {e}")
                errors.append(str(e))

    convert_pcp_log(path, errors)
