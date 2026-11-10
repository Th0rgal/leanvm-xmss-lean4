import Model.Witness.Scalar

namespace LeanVmXmss.Proofs.Witness

theorem executeTrace_refines (fuel : Nat) (program : Array Spec.Vm.Op)
    (hints : Array (Array Spec.Vm.RHint)) (runtime : Spec.Vm.Runtime) :
    Model.Witness.executeTrace fuel program hints runtime =
      Spec.Witness.executeTrace fuel program hints runtime := rfl

theorem bundleOf_refines (program : Array Spec.Vm.Op) (iv : ByteArray)
    (publicInput : Array Spec.Field.E) (trace : Spec.Witness.ExecutionTrace) :
    Model.Witness.bundleOf program iv publicInput trace =
      Spec.Witness.bundleOf program iv publicInput trace := rfl

theorem proveBundle_refines (fuel : Nat) (program : Array Spec.Vm.Op)
    (hints : Array (Array Spec.Vm.RHint)) (runtime : Spec.Vm.Runtime) (iv : ByteArray) :
    Model.Witness.proveBundle fuel program hints runtime iv =
      Spec.Witness.proveBundle fuel program hints runtime iv := rfl

theorem sizeRun_refines (program : Array Spec.Vm.Op) (trace : Spec.Witness.ExecutionTrace) :
    Model.Witness.sizeRun program trace = Spec.Witness.sizeRun program trace := rfl

theorem announce_refines (sized : Spec.Witness.SizedRun) :
    Model.Witness.announceDigest sized = Spec.Witness.announceDigest sized := rfl

theorem root_refines (message : Array Spec.Field.K) (shape : Spec.Layout.Shape) :
    Model.Witness.l0Root message shape = Spec.Witness.l0Root message shape := rfl

end LeanVmXmss.Proofs.Witness
