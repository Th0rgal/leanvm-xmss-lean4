import Model.Field.NativeKernel

@[export shard_a_probe_byte]
def nativeByteProbe (a b : UInt64) : UInt64 :=
  LeanVmXmss.Model.Field.nativeClmulByte a b

def main : IO Unit :=
  IO.println (nativeByteProbe 3 3).toNat
