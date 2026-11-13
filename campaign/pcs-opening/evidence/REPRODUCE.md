# Resume prerequisites and reproduction

The application sources are unchanged from 299c689373ef3e98e0f150ff4bec21ca5e3aaea1.
Do not optimize until the native toolchain mismatch is corrected by its owner.

On this host the following commands reproduce the failures:

```sh
cd /var/lib/orb-node/work/pcs-opening/LeanVmXmss
export LEAN_NUM_THREADS=1
export TURBO_LEAN_MAX_MEMORY_MB=6144
export LEAN_PATH=.lake/build/lib/lean
turbo-lean build --project-dir . Model.Cli.E2EMain
lean-native compile-llvm --input Tests/Hub/ShardAHw.lean -o /var/lib/orb-node/work/pcs-opening-evidence/reprobe.ll
lean-native build-exe --input Model/Cli/E2EMain.lean -o /var/lib/orb-node/work/pcs-opening-evidence/reprobe-e2e --dynamic-runtime
```

Both native commands fail with an incompatible Init.olean header. No target
executable exists. See native-embedded-version.txt and environment.json.

After provisioning the correct toolchain, use the committed
Tests/Hub/cache_manager.py sequentially before build-exe, exactly matching
baseline and candidate builds. Preserve source/tool hashes and generated-code
inspection. Do not substitute stock scalar execution for native benchmark data.
The cgroup limit adjustment is session-local; re-read actual nested limits.

Regenerate the four omitted full1400 fixtures and match LARGE_FIXTURES_MANIFEST.json
before the unchanged full baseline. Existing e2e-oracle was built with:

```sh
CARGO_BUILD_JOBS=1 CARGO_TARGET_DIR=/var/lib/orb-node/work/pcs-opening-evidence/rust-target cargo build --release --manifest-path LeanVmXmss/Tests/Cli/Rust/Cargo.toml
```

Its crates point to the unchanged reference checkout under references/leanVM.
The legacy absolute includes resolve via
/var/lib/orb-node/work/caches/xmss-hub-v3/references/leanVM -> that checkout.
Cargo.lock is untracked and preserved for reproducibility, not an app change.

No TTL API, provisioned push capability, or coordinator messaging API is available
in this session. The final response serves as the coordinator harvest notice.
Do not destroy the host before harvest acknowledgement.
