import Native.Kernels.FieldSimd

namespace LeanVmXmss.Native.Kernels

@[noinline, export ln_xmss_bus_fold_base_c0]
def busFoldBaseC0 (k0 k1 r0 _r1 _r2 : UInt64) : UInt64 :=
  k0 ^^^ fieldMul64 (k0 ^^^ k1) r0

@[noinline, export ln_xmss_bus_fold_base_c1]
def busFoldBaseC1 (k0 k1 _r0 r1 _r2 : UInt64) : UInt64 :=
  fieldMul64 (k0 ^^^ k1) r1

@[noinline, export ln_xmss_bus_fold_base_c2]
def busFoldBaseC2 (k0 k1 _r0 _r1 r2 : UInt64) : UInt64 :=
  fieldMul64 (k0 ^^^ k1) r2

@[noinline, export ln_xmss_bus_dot_base_c0]
def busDotBaseC0 (k : UInt64) (e0 _e1 _e2 acc0 : UInt64) : UInt64 :=
  acc0 ^^^ fieldMul64 k e0

@[noinline, export ln_xmss_bus_dot_base_c1]
def busDotBaseC1 (k : UInt64) (_e0 e1 _e2 acc1 : UInt64) : UInt64 :=
  acc1 ^^^ fieldMul64 k e1

@[noinline, export ln_xmss_bus_dot_base_c2]
def busDotBaseC2 (k : UInt64) (_e0 _e1 e2 acc2 : UInt64) : UInt64 :=
  acc2 ^^^ fieldMul64 k e2

end LeanVmXmss.Native.Kernels
