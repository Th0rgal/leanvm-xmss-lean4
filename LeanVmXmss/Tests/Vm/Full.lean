import Tests.Vm.RuntimeIO

@[export shard_c_bin_xor_kernel, noinline]
def binXorKernel (x y : UInt64) : UInt64 := x ^^^ y

@[export shard_c_bin_keccak_theta, noinline]
def binThetaKernel (x y : UInt64) : UInt64 := x ^^^ ((y <<< 1) ||| (y >>> 63))

@[export shard_c_bin_keccak_chi, noinline]
def binChiKernel (x y z : UInt64) : UInt64 := x ^^^ ((~~~y) &&& z)

@[export shard_c_bin_rotate_left, noinline]
def binRotateLeftKernel (x n : UInt64) : UInt64 := x <<< n

@[export shard_c_bin_rotate_right, noinline]
def binRotateRightKernel (x n : UInt64) : UInt64 := x >>> n

@[export shard_c_bin_generator_step, noinline]
def binGeneratorStep (x : UInt64) : UInt64 :=
  (x <<< 1) ^^^ (((0 : UInt64) - (x >>> 63)) &&& 0x1b)

def main (args : List String) : IO Unit := do
  let check := binXorKernel (binThetaKernel 1 2)
    (binChiKernel (binRotateLeftKernel 3 1) (binRotateRightKernel 8 1) (binGeneratorStep 5))
  if check == 0 then IO.eprintln "unexpected kernel canary"
  match args with
  | [input, output] => LeanVmXmss.Tests.Vm.runFull input output
  | _ => throw (IO.userError "expected raw input and oracle directory")
