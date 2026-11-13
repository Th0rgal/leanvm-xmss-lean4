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

## Bootstrap completed

The 352-target build passed in 351.508 s. Executable SHA-256 exactly matches
the historical report: 79b805002e329a6eee167403265daa91b50467a4169c8e735d0e843eca3cc6ba.
Canary passed after adding the lean-sys dependency directory to LEAN_PATH:
/var/lib/orb-node/work/pcs-turbo-lean/lean/.lake/packages/lean-sys/.lake/build/lib/lean.
262 K and 131 E vectors, UInt64 bit63/all-ones, native CLMUL, ABI boxing,
standalone/unique symbols, unsupported exports and tool-failure regressions pass.
See bootstrap-p0.log and bootstrap-p0/result.json.

All four omitted full1400 files match committed SHA-256/size; seed, statement
and bytecode value are byte-equal to committed files. Public exporters were
rebuilt at pcs-fixture-tools with only local path relocation. Fixture roots:
/var/lib/orb-node/work/pcs-restored-oracle/{xmss4,xmss16,xmss1400,fresh5}.
No compiler installation or system-binary replacement was made.

The unchanged full prover now links at pcs-opening-evidence/baseline-native435-e2e
(SHA-256 581d2ac79b2e9dbd2c6d8bd0087a89886b6005e9363d59b89a7e81ad576f6863).
It imports sequentially compiled native objects; its CLI wrapper has zero local
LCNF kernels. nm shows unique shard_a_mul and karatsuba definitions; objdump
shows vpclmul in the linked field multiplication. The historical ABI P0 suite
passes, so wrapper-only success is not being counted as kernel evidence.

Always set RUSTFLAGS='-C target-cpu=native' explicitly for the oracle harness:
its external Cargo.toml does not inherit references/leanVM/.cargo/config.toml.
The first paired attempt used generic Rust flags; it was stopped and retained
as INVALID_BUILD_FLAGS_RESTART_REQUIRED. It is excluded from all comparisons.
Corrected native Rust build uses separate rust-native-target, CARGO_BUILD_JOBS=1.

perf task-clock access is denied (perf_event_paranoid=4); preserve that result
and use phase diagnostics plus generated native code for cost attribution.

## Exact strict-proofs CLI restored locally

The installed audit-spec only accepts one file and rejects --policy. The public
pinned source contains the required strict-proofs/multi-directory API. Built its
unchanged Rust turbo-lean CLI with cargo build --release --locked -p turbo-lean,
CARGO_BUILD_JOBS=1, CARGO_TARGET_DIR=/var/lib/orb-node/work/pcs-cli-target,
LEAN_NUM_THREADS=1 and TURBO_LEAN_MAX_MEMORY_MB=6144 (3m43s).
No shared binary was overwritten; existing compiler P0 patches are the only
source diff in the public tool checkout. Use pcs-cli-target/release/turbo-lean
for the exact strict gate. 1102/1102 tight specs, zero vacuous/trivial/warnings.
The original installed-CLI combined failure is retained. Consolidated gate JSON
replaces only that unsupported invocation with the exact pinned CLI result and
records input/executable SHA-256s; all other gates retain actual executed evidence.

The external Rust CLI harness generated lockfile is retained as evidence/rust-cli.Cargo.lock
(SHA-256 a40b53ed2b85caa85b1036678d80b5f89b3f76be1269e7a026a26f303bc1cb96). Restore it to
LeanVmXmss/Tests/Cli/Rust/Cargo.lock before rebuilding with --locked; the public
reference checkout and its committed lockfile remain unchanged.
