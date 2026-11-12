#!/usr/bin/env python3
"""
Helper to apply OPS from /tmp/c1b_ops.py, /tmp/c1a_ops.py, /tmp/c1c_ops.py
against $HUB/toolchain/turbo-lean.

Supports multiple flexible OPS schemas:
  - list of dicts:
      {"file"|"path": rel_or_abs, "op"|"kind": "replace"|"insert_after"|"insert_before"|"append"|"prepend"|"write",
       "old"|"anchor"|"target": ..., "new"|"content"|"replacement": ..., "count": 1}
  - list of tuples:
      (file, old, new)
      (op, file, old, new)
      (op, file, content)
  - dict mapping file -> list of (old, new) orop dicts
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import sys
from pathlib import Path
from typing import Any


DEFAULT_ROOT = os.environ.get(
    "TURBO_LEAN_ROOT",
    "/var/lib/orb-node/work/caches/xmss-hub-v3/toolchain/turbo-lean",
)


def load_ops_module(mod_path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(mod_path.stem, str(mod_path))
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load module from {mod_path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    if hasattr(mod, "OPS"):
        return mod.OPS
    if hasattr(mod, "ops"):
        return mod.ops
    raise AttributeError(f"Module {mod_path} has no OPS attribute")


def resolve_path(root: Path, p: str) -> Path:
    path = Path(p)
    if path.is_absolute():
        return path
    return root / path


def normalize_ops(raw_ops: Any) -> list[dict[str, Any]]:
    norm: list[dict[str, Any]] = []
    if isinstance(raw_ops, dict):
        for fpath, edits in raw_ops.items():
            if isinstance(edits, str):
                norm.append({"op": "write", "file": fpath, "new": edits})
            elif isinstance(edits, list):
                for e in edits:
                    if isinstance(e, dict):
                        d = dict(e)
                        d.setdefault("file", fpath)
                        norm.append(d)
                    elif isinstance(e, (tuple, list)) and len(e) == 2:
                        norm.append({"op": "replace", "file": fpath, "old": e[0], "new": e[1]})
                    elif isinstance(e, (tuple, list)) and len(e) == 3:
                        norm.append({"op": e[0], "file": fpath, "old": e[1], "new": e[2]})
                    else:
                        raise ValueError(f"Unsupported edit entry for {fpath}: {e!r}")
            else:
                raise ValueError(f"Unsupported dict value for {fpath}: {type(edits)}")
        return norm

    if not isinstance(raw_ops, (list, tuple)):
        raise ValueError(f"Unsupported OPS container type: {type(raw_ops)}")

    for item in raw_ops:
        if isinstance(item, dict):
            norm.append(dict(item))
        elif isinstance(item, (tuple, list)):
            if len(item) == 3 and item[0] in ("write", "append", "prepend", "create"):
                norm.append({"op": item[0], "file": item[1], "new": item[2]})
            elif len(item) == 3:
                norm.append({"op": "replace", "file": item[0], "old": item[1], "new": item[2]})
            elif len(item) == 4:
                norm.append({"op": item[0], "file": item[1], "old": item[2], "new": item[3]})
            else:
                raise ValueError(f"Unsupported tuple length in OPS: {item!r}")
        else:
            raise ValueError(f"Unsupported OPS item: {item!r}")
    return norm


def apply_single_op(buffers: dict[Path, str], root: Path, op_dict: dict[str, Any], idx: int, source_name: str) -> str:
    fpath_raw = op_dict.get("file") or op_dict.get("path") or op_dict.get("rel")
    if not fpath_raw:
        raise ValueError(f"[{source_name}#{idx}] Missing 'file'/'path'/'rel' in {op_dict.keys()}")
    fpath = resolve_path(root, fpath_raw)
    kind = (op_dict.get("op") or op_dict.get("kind") or op_dict.get("tool") or "replace").lower()
    if kind == "edit":
        kind = "replace"

    if fpath not in buffers:
        if fpath.exists():
            buffers[fpath] = fpath.read_text(encoding="utf-8")
        elif kind in ("write", "create", "append"):
            buffers[fpath] = ""
        else:
            raise FileNotFoundError(f"[{source_name}#{idx}] Target file does not exist: {fpath}")

    cur = buffers[fpath]
    old = op_dict.get("old") if "old" in op_dict else op_dict.get("anchor", op_dict.get("target"))
    new = op_dict.get("new") if "new" in op_dict else op_dict.get("content", op_dict.get("replacement"))
    desc = op_dict.get("desc") or op_dict.get("id") or f"{kind}:{fpath.name}"

    if kind in ("write", "create"):
        if new is None:
            raise ValueError(f"[{source_name}#{idx}] '{kind}' requires 'new'/'content'")
        buffers[fpath] = new
        return f"OK [{source_name}#{idx}] {desc} ({kind} {len(new)} bytes)"

    if kind == "append":
        if new is None:
            raise ValueError(f"[{source_name}#{idx}] 'append' requires 'new'/'content'")
        if op_dict.get("idempotent", True) and new in cur:
            return f"SKIP-IDEMPOTENT [{source_name}#{idx}] {desc}"
        buffers[fpath] = cur + new
        return f"OK [{source_name}#{idx}] {desc} (append {len(new)} bytes)"

    if kind == "prepend":
        if new is None:
            raise ValueError(f"[{source_name}#{idx}] 'prepend' requires 'new'/'content'")
        if op_dict.get("idempotent", True) and new in cur:
            return f"SKIP-IDEMPOTENT [{source_name}#{idx}] {desc}"
        buffers[fpath] = new + cur
        return f"OK [{source_name}#{idx}] {desc} (prepend {len(new)} bytes)"

    if old is None or new is None:
        raise ValueError(f"[{source_name}#{idx}] '{kind}' requires old/anchor and new/content")

    occurrences = cur.count(old)
    expected_count = op_dict.get("count", 1)

    if occurrences == 0:
        if kind == "replace" and new in cur:
            return f"SKIP-ALREADY-APPLIED [{source_name}#{idx}] {desc}"
        snippet = old[:120].replace("\n", "\\n")
        raise RuntimeError(
            f"CONFLICT [{source_name}#{idx}] {desc} in {fpath}:\n"
            f"  anchor/old not found ({len(old)} chars): {snippet!r}"
        )

    if expected_count is not None and expected_count > 0 and occurrences != expected_count:
        if not op_dict.get("allow_multiple", False):
            snippet = old[:120].replace("\n", "\\n")
            raise RuntimeError(
                f"AMBIGUOUS [{source_name}#{idx}] {desc} in {fpath}:\n"
                f"  expected {expected_count} match(es), found {occurrences}: {snippet!r}"
            )

    if kind == "replace":
        if expected_count is None or expected_count <= 0:
            buffers[fpath] = cur.replace(old, new)
        else:
            buffers[fpath] = cur.replace(old, new, expected_count)
    elif kind == "insert_after":
        buffers[fpath] = cur.replace(old, old + new, 1 if expected_count == 1 else occurrences)
    elif kind == "insert_before":
        buffers[fpath] = cur.replace(old, new + old, 1 if expected_count == 1 else occurrences)
    else:
        raise ValueError(f"[{source_name}#{idx}] Unknown op kind: {kind!r}")

    return f"OK [{source_name}#{idx}] {desc}"


def main() -> int:
    ap = argparse.ArgumentParser(description="Apply C1 ops modules to turbo-lean")
    ap.add_argument(
        "modules",
        nargs="*",
        default=["/tmp/c1b_ops.py", "/tmp/c1a_ops.py", "/tmp/c1c_ops.py"],
        help="Ops python files to apply in order",
    )
    ap.add_argument("--root", default=DEFAULT_ROOT, help="turbo-lean root directory")
    ap.add_argument("--dry-run", action="store_true", help="Validate without writing files")
    ap.add_argument("--keep-going", action="store_true", help="Report all conflicts instead of stopping at first")
    args = ap.parse_args()

    root = Path(args.root).resolve()
    buffers: dict[Path, str] = {}
    logs: list[str] = []
    errors: list[str] = []

    for mod_str in args.modules:
        mod_path = Path(mod_str)
        if not mod_path.exists():
            errors.append(f"MISSING MODULE: {mod_path}")
            if not args.keep_going:
                break
            continue
        raw_ops = load_ops_module(mod_path)
        ops = normalize_ops(raw_ops)
        for idx, op_dict in enumerate(ops):
            try:
                msg = apply_single_op(buffers, root, op_dict, idx, mod_path.name)
                logs.append(msg)
            except Exception as exc:
                errors.append(str(exc))
                if not args.keep_going:
                    break
        if errors and not args.keep_going:
            break

    for line in logs:
        print(line)
    if errors:
        for err in errors:
            print(err, file=sys.stderr)
        return 1

    summary = []
    for fpath, content in sorted(buffers.items()):
        sha = hashlib.sha256(content.encode("utf-8")).hexdigest()
        if not args.dry_run:
            fpath.parent.mkdir(parents=True, exist_ok=True)
            fpath.write_text(content, encoding="utf-8")
        summary.append({"file": str(fpath), "bytes": len(content), "sha256": sha})

    print(json.dumps({"dry_run": args.dry_run, "updated": summary}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
