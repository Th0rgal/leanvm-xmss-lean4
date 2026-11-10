namespace LeanVmXmss.Model.Vm

def scalarGeneratorStep (x : UInt64) : UInt64 :=
  (x <<< 1) ^^^ (((0 : UInt64) - (x >>> 63)) &&& 0x1b)

@[export shard_c_xor_kernel, noinline]
def xorKernel (x y : UInt64) : UInt64 := x ^^^ y

@[export shard_c_keccak_theta, noinline]
def thetaKernel (x y : UInt64) : UInt64 := x ^^^ ((y <<< 1) ||| (y >>> 63))

@[export shard_c_keccak_chi, noinline]
def chiKernel (x y z : UInt64) : UInt64 := x ^^^ ((~~~y) &&& z)

@[export shard_c_rotate_left, noinline]
def rotateLeftKernel (x n : UInt64) : UInt64 := x <<< n

@[export shard_c_rotate_right, noinline]
def rotateRightKernel (x n : UInt64) : UInt64 := x >>> n


end LeanVmXmss.Model.Vm
