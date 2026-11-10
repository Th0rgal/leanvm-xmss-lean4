import Model.Keccak.Scalar

namespace LeanVmXmss.Proofs.Keccak

theorem round_refines_spec (a : Spec.Keccak.State) (r : UInt64) :
    Model.Keccak.round a r = Spec.Keccak.round a r := rfl

theorem permutation_refines_spec (a : Spec.Keccak.State) :
    Model.Keccak.permute a = Spec.Keccak.permute a := rfl

theorem padding_block_split (b : ByteArray) (d : UInt8) :
    Model.Keccak.blocks b d = Spec.Keccak.blocks b d := rfl

theorem hash_refines_spec (b : ByteArray) :
    Model.Keccak.keccak256 b = Spec.Keccak.keccak256 b := rfl

end LeanVmXmss.Proofs.Keccak
