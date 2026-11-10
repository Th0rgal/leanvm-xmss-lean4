import Spec.Field.Basic

namespace LeanVmXmss.Spec.Vm

def wordBEq (a b : Spec.Field.E) : Bool :=
  a.c0.toNat == b.c0.toNat && a.c1.toNat == b.c1.toNat && a.c2.toNat == b.c2.toNat

scoped instance : BEq Spec.Field.E := ⟨wordBEq⟩

end LeanVmXmss.Spec.Vm
