import Tests.Unit.NativeBusKernelSuite

#print axioms LeanVmXmss.Model.Prim.Slice64.usize_lt_imp_size_lt
#print axioms LeanVmXmss.Model.Prim.Slice64.byteAtU
#print axioms LeanVmXmss.Model.Prim.Slice64.readU64LEU
#print axioms LeanVmXmss.Model.Prim.Slice64.readU64LE
#print axioms LeanVmXmss.Model.Prim.Slice64.readU64LEOr
#print axioms LeanVmXmss.Model.Prim.Slice64.pushU64LE
#print axioms LeanVmXmss.Model.Prim.Slice64.packU64Array
#print axioms LeanVmXmss.Model.Prim.Slice64.unpackU64Array
#print axioms LeanVmXmss.Model.Prim.Slice64.packSliceE
#print axioms LeanVmXmss.Model.Prim.Slice64.unpackSliceE
#print axioms LeanVmXmss.Native.Kernels.busGf64Mul
#print axioms LeanVmXmss.Native.Kernels.busExtAdd0
#print axioms LeanVmXmss.Native.Kernels.busExtAdd1
#print axioms LeanVmXmss.Native.Kernels.busExtAdd2
#print axioms LeanVmXmss.Native.Kernels.busExtMul0
#print axioms LeanVmXmss.Native.Kernels.busExtMul1
#print axioms LeanVmXmss.Native.Kernels.busExtMul2
#print axioms LeanVmXmss.Native.Kernels.busMulBase0
#print axioms LeanVmXmss.Native.Kernels.busMulBase1
#print axioms LeanVmXmss.Native.Kernels.busMulBase2
#print axioms LeanVmXmss.Native.Kernels.busInterp0
#print axioms LeanVmXmss.Native.Kernels.busInterp1
#print axioms LeanVmXmss.Native.Kernels.busInterp2
#print axioms LeanVmXmss.Native.Kernels.busInterpK0
#print axioms LeanVmXmss.Native.Kernels.busInterpK1
#print axioms LeanVmXmss.Native.Kernels.busInterpK2
#print axioms LeanVmXmss.Native.Kernels.busSliceFoldAt
#print axioms LeanVmXmss.Native.Kernels.busSliceMleTerm
#print axioms LeanVmXmss.Native.Kernels.busSliceJoinLeftAt
#print axioms LeanVmXmss.Native.Kernels.busQuarticSummand
#print axioms LeanVmXmss.Native.Kernels.busTreeRoundMessageSlice
#print axioms LeanVmXmss.Native.Kernels.busFoldTreeSlice
#print axioms LeanVmXmss.Native.Kernels.busNextLevelSlice
#print axioms LeanVmXmss.Native.Kernels.busFoldTableStateSlice
#print axioms LeanVmXmss.Native.Kernels.busTableMessageESlice
#print axioms LeanVmXmss.Native.Kernels.busTableMessageKSlice
#print axioms LeanVmXmss.Native.Kernels.busJoinTableStateSlice
#print axioms LeanVmXmss.Native.Kernels.busMleEvalSlice
#print axioms LeanVmXmss.Native.Kernels.busTreeRoundMessagePar
#print axioms LeanVmXmss.Native.Kernels.busFoldTreePar
#print axioms LeanVmXmss.Native.Kernels.busNextLevelPar
#print axioms LeanVmXmss.Native.Kernels.busFoldTableStatePar
#print axioms LeanVmXmss.Native.Kernels.busJoinTableStatePar
#print axioms LeanVmXmss.Native.Kernels.busTableMessageEPar
#print axioms LeanVmXmss.Native.Kernels.busTableMessageKPar
#print axioms LeanVmXmss.Native.Kernels.busMleEvalPar

def main : IO Unit :=
  LeanVmXmss.Tests.Unit.runNativeBusKernelSuite
