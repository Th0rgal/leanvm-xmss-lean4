import Std
namespace LeanVmXmss.Tests.Field
 theorem toolProbe (a b : Bool) : (a ^^ b) ^^ b = a := by
  cases a <;> cases b <;> rfl
#print axioms toolProbe
end LeanVmXmss.Tests.Field
