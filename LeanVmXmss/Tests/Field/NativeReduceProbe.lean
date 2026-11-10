import Model.Field.NativeKernel

@[export shard_a_probe_reduce]
def nativeReduceProbe (lo hi : UInt64) : UInt64 :=
  LeanVmXmss.Model.Field.nativeReduce lo hi

def main : IO Unit :=
  IO.println (nativeReduceProbe 0 1).toNat
