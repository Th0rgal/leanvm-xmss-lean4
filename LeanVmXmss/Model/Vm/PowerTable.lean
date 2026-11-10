import Spec.Vm.Basic

namespace LeanVmXmss.Model.Vm

def lookupPower (powers : Array UInt64) (i : Nat) : Except Spec.Vm.Fault Spec.Field.E :=
  if h : i < powers.size then .ok ⟨powers[i], 0, 0⟩ else .error .badProgram

end LeanVmXmss.Model.Vm
