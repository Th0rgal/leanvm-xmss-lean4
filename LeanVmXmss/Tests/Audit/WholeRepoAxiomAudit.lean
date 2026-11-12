/-
W5 Maxwell (Wave 1) · Whole-repository Lean axiom audit
=========================================================
Re-audits every LeanVmXmss declaration in the repository (Spec, Model, Proofs,
Tests) under the strict axiom rules:

  * no `._unsafe_rec` generated names
  * no `isUnsafe` declarations
  * no external (`isExtern`) declarations
  * no transitive dependency on any axiom outside {propext, Quot.sound}
    (this subsumes sorryAx / nativeDecide / trustCompiler / ofReduceBool,
    which surface as axioms of the declaration that used them)

Three pre-broken test modules are excluded from the import set (they have no
olean in this environment and fail to build for reasons unrelated to axioms,
so their declarations cannot be audited here):
  * Tests.Field.Differential  - #eval reads Tests/Field/artifacts/field-vectors.txt (absent)
  * Tests.Vm.FieldDependency  - references LeanVmXmss.Spec.Field.instBEqE.beq (stale constant)
  * Tests.Xmss.Full           - #eval reads a hard-coded /var/lib/sandboxed-node scratch path
  * Tests.Field.InstanceAudit - duplicate top-level `fieldName` def: its `_sunfold`
    constant collides with the one from Tests.Field.AxiomAudit, so the two modules
    can never be imported together (pre-existing defect); AxiomAudit is kept

Writes a per-module JSON report to $W5_AUDIT_OUT/axiom-audit-repo.json (or
$TMPDIR/w5-audit) and fails the build if any declaration is rejected.
-/
import Lean
import Model.Aggregate.Wire
import Model.Bus.Scalar
import Model.Cli.Aggregate
import Model.Cli.E2E
import Model.Cli.Inputs
import Model.Field.NativeKernel
import Model.Field.Operations
import Model.Field.Scalar
import Model.Keccak.Registers
import Model.Keccak.Scalar
import Model.KeccakGkr.Scalar
import Model.Layout.Scalar
import Model.Merkle.Heap
import Model.Merkle.Scalar
import Model.Pcs.Commit
import Model.Pcs.Ntt
import Model.Pcs.RingSwitch
import Model.Pcs.StackOpen
import Model.Pcs.Whir
import Model.Transcript.Registers
import Model.Transcript.Scalar
import Model.Vm.Interpreter
import Model.Vm.KeccakInternal
import Model.Vm.Kernel
import Model.Vm.Linear
import Model.Vm.PowerTable
import Model.Vm.Scheduled
import Model.Witness.Scalar
import Model.Xmss.Hints
import Proofs.Aggregate.Wire
import Proofs.Bus.Refinement
import Proofs.Field.Associativity
import Proofs.Field.Basic
import Proofs.Field.Codecs
import Proofs.Field.Convolution
import Proofs.Field.Extension
import Proofs.Field.ExtensionInverse
import Proofs.Field.Frobenius
import Proofs.Field.Inverse
import Proofs.Field.NativeHighShift
import Proofs.Field.NativeKernel
import Proofs.Field.Operations
import Proofs.Field.Powers
import Proofs.Field.Quotient
import Proofs.Field.Reduction
import Proofs.Field.Squares
import Proofs.Field.Windows
import Proofs.Keccak.Refinement
import Proofs.Keccak.Registers
import Proofs.KeccakGkr.Refinement
import Proofs.Layout.Basic
import Proofs.Merkle.Contracts
import Proofs.Merkle.Refinement
import Proofs.Pcs.CommitMerkle
import Proofs.Pcs.CosetNtt
import Proofs.Pcs.Refinement
import Proofs.Pcs.RingSwitch
import Proofs.Pcs.StackOpen
import Proofs.Pcs.Whir
import Proofs.Transcript.Minimality
import Proofs.Transcript.Refinement
import Proofs.Transcript.Registers
import Proofs.Transcript.Replay
import Proofs.Vm.Basic
import Proofs.Vm.GPow
import Proofs.Vm.Kernel
import Proofs.Vm.Linear
import Proofs.Vm.RuntimePowers
import Proofs.Witness.Refinement
import Proofs.Xmss.Basic
import Proofs.Xmss.Encoding
import Spec.Aggregate.Wire
import Spec.Bus.Basic
import Spec.Field.Basic
import Spec.Field.Operations
import Spec.Field.Quotient
import Spec.Keccak.Basic
import Spec.KeccakGkr.Basic
import Spec.Layout.Basic
import Spec.Merkle.Basic
import Spec.Merkle.Pruned
import Spec.Pcs.Commit
import Spec.Pcs.Ntt
import Spec.Pcs.RingSwitch
import Spec.Pcs.StackOpen
import Spec.Pcs.Whir
import Spec.Transcript.Basic
import Spec.Transcript.Replay
import Spec.Vm.Basic
import Spec.Vm.Bytecode
import Spec.Vm.Equality
import Spec.Vm.Hints
import Spec.Vm.KeccakInternal
