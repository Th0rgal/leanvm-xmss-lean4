# Reproducible bootstrap handoff to C1a/coordinator

Public compiler source: https://github.com/Th0rgal/turbo-lean.git
Exact base: 29d85f7da2d963750f77d76d5323408a73386f14 (P2_E2E_REPORT.md).
Checkout: /var/lib/orb-node/work/pcs-turbo-lean.
Toolchain: leanprover/lean4:v4.35.0, existing shared ELAN_HOME preserved.
Dependency lean-sys pin: 077775ba387f1eeb2976cb8763b4633b8d5ce313.

Apply the application's committed meta/compiler-fix.patch, whose SHA-256 is
05d8024587ec0046b363a8821a899a5bd7c75a5eea56a68515dd558e1b8d526d.
It applies cleanly to this public base. Expected patched hashes:

- lean/LeanNative/Backend/LLVM.lean:
  9b319d50d7c9bf2ab6198dd68652290fddef41a8adee7281d18a1e10d38196b1
- lean/LeanNative/Driver/BuildExe.lean:
  43ce3d562558347906b68f356fff194b87bd723431d760454a3e57b710bbbc26

Build via installed turbo-lean:
LEAN_NUM_THREADS=1 TURBO_LEAN_MAX_MEMORY_MB=6144 turbo-lean build --project-dir lean lean-native
Installed turbo build lacks a --jobs flag; LEAN_NUM_THREADS=1 is used and actual
process monitoring shows one Lean worker at a time. No raw lake build invoked.
Log: /var/lib/orb-node/work/pcs-opening-evidence/bootstrap-native435.log.
Binary expected at lean/.lake/build/bin/lean-native. Use this task-local binary;
do not overwrite /opt/orb/bin/lean-native or alter another worker's compiler.

Required before proving: P0 native canary (K/E/UInt64 bit63/ABI/unique-symbol and
instruction checks) using scripts/test_build_exe_p0.py with LEAN_SYSROOT set.
Then sequential app Tests/Hub/cache_manager.py and build-exe. The script needs
this rebuilt binary on PATH. Do not use baseline objects made by a different
compiler; preserve generated output manifests and executable hashes.

This worker has no exposed cross-mission messaging tool. This committed file
and exported bundle are the reproducible-needs handoff; coordinator owns TTL.
No credentials, snapshots, new VM provisioning or VM deletion are requested.
