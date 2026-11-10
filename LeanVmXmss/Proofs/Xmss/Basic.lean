import Model.Xmss.Hints

namespace LeanVmXmss.Proofs.Xmss

theorem hints_refines_spec (raw : Spec.Xmss.RawSignature) :
    Model.Xmss.signatureHints raw = Spec.Xmss.signatureHints raw := rfl

theorem claim_group_bytes : Spec.Xmss.claimGroup * 64 = 8 * 136 := by decide

theorem signature_size : 4 + 2 * (16 + 58 * 16 + 16 * 16) = Spec.Xmss.recordSize - 64 := by decide

theorem layer_flag : Spec.Xmss.top = 8388608 := by decide

end LeanVmXmss.Proofs.Xmss
