import Model.Field.NativeKernel

@[export shard_a_probe_mul]
def nativeMulProbe (a b : UInt64) : UInt64 :=
  LeanVmXmss.Model.Field.nativeReduce
    (LeanVmXmss.Model.Field.nativeClmulLo a b)
    (LeanVmXmss.Model.Field.nativeClmulHi a b)

theorem nativeMulProbe_correct (a b : UInt64) :
    nativeMulProbe a b = LeanVmXmss.Model.Field.nativeMul a b := rfl

def main (args : List String) : IO Unit := do
  if args.length != 2 then throw (IO.userError "expected two words")
  IO.println (nativeMulProbe args[0]!.toNat!.toUInt64 args[1]!.toNat!.toUInt64).toNat
