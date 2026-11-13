# Read-only compiler finding from GKR

No compiler source was edited in this campaign. The following is code-generation
evidence and a measured hot-path diagnosis, not a compiler benchmark acceptance.

The actual GKR packed-word reader runs inside tens of billions of product-bit
iterations. Candidate5's `bytes.size < USize.size` adds a generic Nat comparison
against the boxed platform-size constant. Candidate6 replaced the bound with
`2^32`; its linked reader unexpectedly calls `lean_cstr_to_nat("4294967296")`
on every successful read.

Lean4.35's `Lean/Compiler/LCNF/EmitC.lean:703` emits Nat literals below
`UInt32.size` using `lean_unsigned_to_nat`; larger literals use
`lean_cstr_to_nat`. This happens even when the value fits a tagged Nat on this
64-bit target. Runtime assembly constructs an `mpz` from the decimal string,
checks whether it fits `size_t`, returns a tagged Nat when possible, and destroys
the temporary. Generated-C constructor and UInt64-box counters do not cover all
of this internal runtime work.

Minimal source forms for an owner to inspect:

```lean
@[noinline] def largeGuard (n : Nat) : Bool := decide (n < 4294967296)
@[noinline] def smallGuard (n : Nat) : Bool := decide (n < 4294967295)
```

The external, all-buffer-refined GKR reader prototype using `4294967295`
emits an immediate tagged-Nat comparison (`0x1ffffffff`) and a machine-sized
word load, with no literal-parsing call. The app keeps its exact old reader as
fallback, so the optimization does not impose a new protocol or input bound.
The queued candidate7 workflow asserts these properties in the linked reader,
then repeats all correctness, purity, full-size diagnostic and matched gates.

Candidate6's full-size diagnostic completed with byte-identical proof and
independent frozen Rust verification. Its nested aggregate product-loop thread
CPU was6572.803335869s versus480.810701046s for candidate5's diagnostic. These
are selective, instrumented thread-CPU measurements with possible inlining and
host differences; they are not a native E2E speed ratio. Native matched samples
are recorded separately, including the regression.

Evidence root `/var/lib/orb-node/work/keccak-gkr-evidence`:
`candidate6-readWordLE.asm`, `runtime-cstr-to-nat.asm`,
`candidate6-profile-gkr.c`, `candidate6-profile-xmss1400-gkr-summary.json`,
`readcap-prototype.{lean,c,asm}`, and the candidate status/log/phase files.
Compiler SHA25679b805002e329a6eee167403265daa91b50467a4169c8e735d0e843eca3cc6ba.

Any general literal-hoisting or lowering change belongs to the compiler owner
and needs its own correctness and full-pipeline validation. This report requests
no compiler edit in the GKR branch.
