#!/usr/bin/env python3
"""
Wave 3 Maxwell Gate Check (`Tests/Audit/maxwell_gate_check.py`)
===============================================================
Standalone verification script enforcing all Wave 3 Maxwell purity, axiom,
strict-proofs, native binary AVX-512/zero-FFI, and 34-mutant dual-verifier
soundness gates:

  1. Static Purity Gate (`Spec/**`, `Model/**`, `Native/**`, `Proofs/**`):
     Zero `@[extern]`, zero `extern`, zero `unsafe`, zero `sorry`,
     zero `._unsafe_rec`, and zero C/Rust FFI files.
  2. Native Binary Symbol & ISA Gate (`e2e-aggregate`, `e2e-check`, `lean-mutant-suite`):
     - `nm -u` / `nm` confirms zero Rust/C crypto FFI symbols (only GLIBC + Lean runtime).
     - `objdump -d` confirms hardware AVX-512 (`%zmm*`) and carryless multiply (`vpclmul*qdq`).
  3. Whole-Repo Axiom & Strict-Proofs Audit Gate:
     - `WholeRepoAxiomAudit.lean`: `0` rejections, axioms strictly `<= {propext, Quot.sound}`.
     - `turbo-lean --json audit-spec --policy strict-proofs Proofs Spec`:
       `0` bad specs, `0` vacuous specs, `0` trivial specs, `0` warnings.
  4. 34-Mutant Dual-Verifier Soundness Gate:
     - Runs the pure-Lean verifier (`lean-mutant-suite`, backed by `Model.Aggregate.Verify`
       and refined to `Spec.Aggregate.Verify` via `Proofs.Aggregate.Verify`) AND the
       unmodified Rust reference verifier (`mutant-suite --verify-34-dir`) on the exact
       same baseline + 34 deterministic mutations across all 6 soundness groups.
     - Asserts `34/34` baseline proofs accepted and `34/34` mutated proofs rejected by BOTH.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def no_core_dump() -> None:
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def run_cmd(
    argv: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 600,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        argv,
        cwd=str(cwd) if cwd else None,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
        preexec_fn=no_core_dump,
    )


def strip_lean_comments(src: str) -> str:
    # Strip nested-free block comments `/- ... -/` iteratively, then `--` line comments.
    prev = None
    cur = src
    while prev != cur:
        prev = cur
        cur = re.sub(r"/-((?!/-).)*?-/", " ", cur, flags=re.S)
    cur = re.sub(r"--[^\n]*", "", cur)
    return cur


def check_static_purity(project_dir: Path) -> dict:
    target_dirs = ["Spec", "Model", "Native", "Proofs"]
    forbidden_patterns = {
        "at_extern": re.compile(r"@\s*\[\s*extern\b"),
        "extern_kw": re.compile(r"\bextern\b"),
        "unsafe_kw": re.compile(r"\bunsafe\b"),
        "sorry_kw": re.compile(r"\bsorry\b"),
        "unsafe_rec": re.compile(r"\._unsafe_rec\b"),
    }
    scanned_files = 0
    non_lean_files: list[str] = []
    violations: list[dict] = []

    for sub in target_dirs:
        root = project_dir / sub
        if not root.is_dir():
            continue
        for path_str in sorted(glob.glob(str(root / "**" / "*"), recursive=True)):
            p = Path(path_str)
            if not p.is_file():
                continue
            rel = str(p.relative_to(project_dir))
            if p.suffix != ".lean":
                non_lean_files.append(rel)
                continue
            scanned_files += 1
            cleaned = strip_lean_comments(p.read_text(encoding="utf-8"))
            for label, pat in forbidden_patterns.items():
                m = pat.search(cleaned)
                if m:
                    violations.append({"file": rel, "rule": label, "match": m.group(0)})

    ok = len(non_lean_files) == 0 and len(violations) == 0
    return {
        "ok": ok,
        "scanned_lean_files": scanned_files,
        "non_lean_files": non_lean_files,
        "violations": violations,
    }


def ensure_binaries(hub: Path, project_dir: Path, env: dict[str, str]) -> dict[str, Path]:
    bins_dir = hub / "artifacts" / "p2-e2e-bins"
    bins_dir.mkdir(parents=True, exist_ok=True)
    lean_mut_bin = bins_dir / "lean-mutant-suite"
    if not lean_mut_bin.is_file():
        cm = run_cmd(
            [sys.executable, "Tests/Hub/cache_manager.py", "Tests.Audit.Mutants", "Tests.Audit.MutantSuiteMain"],
            cwd=project_dir,
            env=env,
            timeout=600,
        )
        if cm.returncode != 0:
            raise RuntimeError(f"cache_manager failed:\n{cm.stdout}\n{cm.stderr}")
        bn = run_cmd(
            [
                "lean-native",
                "build-exe",
                "--input",
                "Tests/Audit/MutantSuiteMain.lean",
                "-o",
                str(lean_mut_bin),
                "--dynamic-runtime",
            ],
            cwd=project_dir,
            env=env,
            timeout=600,
        )
        if bn.returncode != 0:
            raise RuntimeError(f"lean-native build-exe failed:\n{bn.stdout}\n{bn.stderr}")

    cargo_target = Path(env.get("CARGO_TARGET_DIR", str(hub / "targets" / "rust")))
    rust_mut_bin = cargo_target / "release" / "mutant-suite"
    manifest = project_dir / "Tests" / "Audit" / "Rust" / "Cargo.toml"
    cb = run_cmd(
        ["cargo", "build", "--release", "--offline", "--manifest-path", str(manifest)],
        cwd=project_dir,
        env=env,
        timeout=600,
    )
    if cb.returncode != 0:
        raise RuntimeError(f"cargo build mutant-suite failed:\n{cb.stdout}\n{cb.stderr}")

    return {
        "e2e_aggregate": bins_dir / "e2e-aggregate",
        "e2e_check": bins_dir / "e2e-check",
        "lean_mutant_suite": lean_mut_bin,
        "rust_mutant_suite": rust_mut_bin,
    }


def check_native_binaries(bins: list[Path]) -> dict:
    allowed_undef = re.compile(
        r"^(_ITM_|__cxa_finalize|__gmon_start__|__libc_start_main|"
        r"memcpy@|memmove@|memset@|memcmp@|malloc@|free@|abort@|"
        r"initialize_Init|initialize_Std|l_|lean_)"
    )
    forbidden_sym = re.compile(
        r"(^rust_|^__rust|lean_xmss_ffi|keccak_f1600_ffi|libcrypto|EVP_|SHA3_|xkcp|XKCP)"
    )
    reports = []
    all_ok = True
    for b in bins:
        if not b.is_file():
            all_ok = False
            reports.append({"binary": str(b), "ok": False, "error": "missing"})
            continue
        nm_u = run_cmd(["nm", "-u", str(b)], timeout=120)
        nm_all = run_cmd(["nm", str(b)], timeout=120)
        objd = run_cmd(["objdump", "-d", str(b)], timeout=180)

        unexpected_undef = []
        for line in nm_u.stdout.splitlines():
            parts = line.strip().split()
            if parts:
                sym = parts[-1]
                if not allowed_undef.match(sym):
                    unexpected_undef.append(sym)

        forbidden_defined = []
        for line in nm_all.stdout.splitlines():
            parts = line.strip().split()
            if parts:
                sym = parts[-1]
                if forbidden_sym.search(sym):
                    forbidden_defined.append(sym)

        zmm_count = len(re.findall(r"%zmm\d+", objd.stdout))
        vpclmul_count = len(re.findall(r"\bvpclmul\w*qdq\b", objd.stdout))
        ok = (
            nm_u.returncode == 0
            and nm_all.returncode == 0
            and objd.returncode == 0
            and len(unexpected_undef) == 0
            and len(forbidden_defined) == 0
            and zmm_count > 0
            and vpclmul_count > 0
        )
        if not ok:
            all_ok = False
        reports.append(
            {
                "binary": b.name,
                "ok": ok,
                "unexpected_undefined_symbols": unexpected_undef,
                "forbidden_ffi_symbols": forbidden_defined,
                "avx512_zmm_operands": zmm_count,
                "vpclmulqdq_insns": vpclmul_count,
            }
        )
    return {"ok": all_ok, "binaries": reports}


def check_axioms_and_specs(project_dir: Path, env: dict[str, str], work_tmp: Path) -> dict:
    audit_out = work_tmp / "w5-audit"
    audit_out.mkdir(parents=True, exist_ok=True)
    env_ax = dict(env)
    env_ax["W5_AUDIT_OUT"] = str(audit_out)

    ax_res = run_cmd(
        ["lean", "Tests/Audit/WholeRepoAxiomAudit.lean"],
        cwd=project_dir,
        env=env_ax,
        timeout=600,
    )
    repo_json_path = audit_out / "axiom-audit-repo.json"
    axiom_data = json.loads(repo_json_path.read_text(encoding="utf-8")) if repo_json_path.is_file() else {}
    allowed_axioms = {"propext", "Quot.sound"}
    used_axioms = set(axiom_data.get("axioms_used", []))
    axiom_ok = (
        ax_res.returncode == 0
        and axiom_data.get("rejected", -1) == 0
        and axiom_data.get("total", 0) > 0
        and used_axioms.issubset(allowed_axioms)
    )

    spec_res = run_cmd(
        ["turbo-lean", "--json", "audit-spec", "--policy", "strict-proofs", "Proofs", "Spec"],
        cwd=project_dir,
        env=env,
        timeout=600,
    )
    spec_json = json.loads(spec_res.stdout) if spec_res.stdout.strip() else {"ok": False}
    checked_total = spec_json.get("total_specs_audited", 0)
    tight_total = spec_json.get("tight_specs", 0)
    vacuous_total = spec_json.get("vacuous_specs", -1)
    trivial_total = spec_json.get("trivial_specs", -1)
    warn_list = spec_json.get("warnings", [])
    warn_total = len(warn_list) if isinstance(warn_list, list) else int(warn_list)
    bad_total = max(0, checked_total - tight_total)
    spec_ok = (
        spec_res.returncode == 0
        and spec_json.get("ok") is True
        and bad_total == 0
        and vacuous_total == 0
        and trivial_total == 0
        and warn_total == 0
        and checked_total > 0
    )

    return {
        "ok": axiom_ok and spec_ok,
        "axiom_audit": {
            "ok": axiom_ok,
            "total_declarations": axiom_data.get("total", 0),
            "rejected": axiom_data.get("rejected", -1),
            "modules": axiom_data.get("modules", 0),
            "axioms_used": sorted(used_axioms),
        },
        "strict_proofs_audit": {
            "ok": spec_ok,
            "checked_specs": checked_total,
            "bad_specs": bad_total,
            "vacuous_specs": vacuous_total,
            "trivial_specs": trivial_total,
            "warnings": warn_total,
        },
        "_raw_repo_axiom_json": axiom_data,
    }


def check_unmodified_rust_ref(hub: Path) -> dict:
    ref_repo = hub / "references" / "leanVM"
    st = run_cmd(["git", "status", "--porcelain"], cwd=ref_repo, timeout=60)
    head = run_cmd(["git", "rev-parse", "HEAD"], cwd=ref_repo, timeout=60)
    clean = st.returncode == 0 and st.stdout.strip() == ""
    return {
        "ok": clean,
        "commit": head.stdout.strip(),
        "dirty_entries": st.stdout.splitlines(),
    }


def run_dual_34_mutant_harness(
    hub: Path,
    lean_bin: Path,
    rust_bin: Path,
    env: dict[str, str],
    work_tmp: Path,
) -> dict:
    wires_dir = work_tmp / "mut34-wires"
    wires_dir.mkdir(parents=True, exist_ok=True)
    lean_json_path = work_tmp / "mutants34-lean.json"
    rust_json_path = work_tmp / "mutants34-rust.json"

    lean_run = run_cmd(
        [
            str(lean_bin),
            "--oracle-xmss4",
            str(hub / "oracle" / "xmss4"),
            "--core-proof",
            str(hub / "artifacts" / "p2-e2e-proofs" / "xmss4.ethproof"),
            "--json",
            str(lean_json_path),
            "--dump-dir",
            str(wires_dir),
        ],
        env=env,
        timeout=600,
    )
    if lean_run.returncode != 0:
        raise RuntimeError(f"Lean 34-mutant binary failed:\n{lean_run.stdout}\n{lean_run.stderr}")

    rust_run = run_cmd(
        [
            str(rust_bin),
            "--verify-34-dir",
            str(wires_dir),
            "--json",
            str(rust_json_path),
        ],
        env=env,
        timeout=600,
    )
    if rust_run.returncode != 0:
        raise RuntimeError(f"Rust 34-mutant binary failed:\n{rust_run.stdout}\n{rust_run.stderr}")

    lean_report = json.loads(lean_json_path.read_text(encoding="utf-8"))
    rust_report = json.loads(rust_json_path.read_text(encoding="utf-8"))

    lean_rows = {m["id"]: m for m in lean_report.get("mutants", [])}
    rust_rows = {m["id"]: m for m in rust_report.get("mutants", [])}

    combined_rows = []
    disagreements = []
    for mid in range(1, 35):
        lm = lean_rows.get(mid)
        rm = rust_rows.get(mid)
        if lm is None or rm is None:
            disagreements.append({"id": mid, "reason": "missing_mutant_row"})
            continue
        row_ok = (
            lm["name"] == rm["name"]
            and lm["group"] == rm["group"]
            and lm["baseline_accepted"] is True
            and rm["baseline_accepted"] is True
            and lm["mutated_rejected"] is True
            and rm["mutated_rejected"] is True
            and lm["mutated_bytes"] == rm["mutated_bytes"]
        )
        if not row_ok:
            disagreements.append({"id": mid, "lean": lm, "rust": rm})
        combined_rows.append(
            {
                "id": mid,
                "group": lm["group"],
                "name": lm["name"],
                "mutated_bytes": lm["mutated_bytes"],
                "lean_baseline_accepted": lm["baseline_accepted"],
                "lean_mutated_rejected": lm["mutated_rejected"],
                "rust_baseline_accepted": rm["baseline_accepted"],
                "rust_mutated_rejected": rm["mutated_rejected"],
                "rust_rejection_reason": rm.get("error", ""),
            }
        )

    ok = (
        lean_report.get("baseline_accepted_count") == 34
        and lean_report.get("mutated_rejected_count") == 34
        and rust_report.get("baseline_accepted_count") == 34
        and rust_report.get("mutated_rejected_count") == 34
        and len(combined_rows) == 34
        and len(disagreements) == 0
    )
    return {
        "ok": ok,
        "mutant_total": 34,
        "lean_baseline_accepted": lean_report.get("baseline_accepted_count"),
        "lean_mutated_rejected": lean_report.get("mutated_rejected_count"),
        "lean_elapsed_ms": lean_report.get("elapsed_ms"),
        "rust_baseline_accepted": rust_report.get("baseline_accepted_count"),
        "rust_mutated_rejected": rust_report.get("mutated_rejected_count"),
        "rust_elapsed_ms": rust_report.get("elapsed_ms"),
        "disagreements": disagreements,
        "mutants": combined_rows,
    }


def build_hub_env(hub: Path) -> dict[str, str]:
    cmd = f"source {hub / 'env.sh'} && env -0"
    res = subprocess.run(["bash", "-c", cmd], capture_output=True, text=True, check=True)
    out: dict[str, str] = {}
    for entry in res.stdout.split("\0"):
        if "=" in entry:
            k, v = entry.split("=", 1)
            out[k] = v
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description="Wave 3 Maxwell Gate Check")
    parser.add_argument(
        "--hub",
        default=os.environ.get("HUB", "/var/lib/orb-node/work/caches/xmss-hub-v3"),
        help="Path to xmss-hub-v3 root",
    )
    parser.add_argument(
        "--report-out",
        default=None,
        help="Optional path for combined Maxwell gate JSON report",
    )
    parser.add_argument(
        "--update-evidence",
        action="store_true",
        help="Write updated audit evidence files into Tests/Audit/evidence/",
    )
    args = parser.parse_args()

    t_start = time.monotonic()
    hub = Path(args.hub).resolve()
    project_dir = hub / "LeanVmXmss"
    env = build_hub_env(hub)

    tmp_base = Path("/tmp/opencode") if Path("/tmp/opencode").is_dir() else Path(tempfile.gettempdir())
    work_tmp = Path(tempfile.mkdtemp(prefix="maxwell-gate-", dir=str(tmp_base)))

    try:
        print("[1/5] Static purity scan across Spec/, Model/, Native/, Proofs/...", flush=True)
        static_report = check_static_purity(project_dir)
        print(f"      ok={static_report['ok']} scanned={static_report['scanned_lean_files']} files", flush=True)

        print("[2/5] Checking unmodified Rust reference & ensuring binaries...", flush=True)
        rust_ref_report = check_unmodified_rust_ref(hub)
        bins = ensure_binaries(hub, project_dir, env)
        bin_report = check_native_binaries(
            [bins["e2e_aggregate"], bins["e2e_check"], bins["lean_mutant_suite"]]
        )
        print(f"      rust_ref_clean={rust_ref_report['ok']} native_bins_ok={bin_report['ok']}", flush=True)

        print("[3/5] Running WholeRepoAxiomAudit.lean & turbo-lean strict-proofs audit...", flush=True)
        audit_report = check_axioms_and_specs(project_dir, env, work_tmp)
        raw_repo_axiom = audit_report.pop("_raw_repo_axiom_json", None)
        print(
            f"      axioms={audit_report['axiom_audit']['axioms_used']} "
            f"decls={audit_report['axiom_audit']['total_declarations']} "
            f"specs={audit_report['strict_proofs_audit']['checked_specs']} "
            f"ok={audit_report['ok']}",
            flush=True,
        )

        print("[4/5] Running 34-mutant dual-verifier soundness harness (Pure Lean + Rust)...", flush=True)
        mutant34_report = run_dual_34_mutant_harness(
            hub, bins["lean_mutant_suite"], bins["rust_mutant_suite"], env, work_tmp
        )
        print(
            f"      lean={mutant34_report['lean_baseline_accepted']}/34 accepted, "
            f"{mutant34_report['lean_mutated_rejected']}/34 rejected | "
            f"rust={mutant34_report['rust_baseline_accepted']}/34 accepted, "
            f"{mutant34_report['rust_mutated_rejected']}/34 rejected",
            flush=True,
        )

        overall_ok = (
            static_report["ok"]
            and rust_ref_report["ok"]
            and bin_report["ok"]
            and audit_report["ok"]
            and mutant34_report["ok"]
        )
        elapsed_s = round(time.monotonic() - t_start, 2)

        summary = {
            "gate": "wave3_maxwell_soundness_and_purity",
            "overall_ok": overall_ok,
            "elapsed_seconds": elapsed_s,
            "static_purity": static_report,
            "rust_reference_integrity": rust_ref_report,
            "native_binary_audit": bin_report,
            "formal_verification_audit": audit_report,
            "dual_verifier_34_mutants": mutant34_report,
        }

        evidence_dir = project_dir / "Tests" / "Audit" / "evidence"
        out_path = (
            Path(args.report_out)
            if args.report_out
            else evidence_dir / "maxwell-gate-34-mutants.json"
        )
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

        if args.update_evidence and raw_repo_axiom:
            (evidence_dir / "axiom-audit-repo.json").write_text(
                json.dumps(raw_repo_axiom, separators=(",", ":")) + "\n",
                encoding="utf-8",
            )

        print(f"[5/5] MAXWELL_GATE_OVERALL={'PASS' if overall_ok else 'FAIL'} report={out_path}", flush=True)
        return 0 if overall_ok else 1
    finally:
        shutil.rmtree(work_tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
