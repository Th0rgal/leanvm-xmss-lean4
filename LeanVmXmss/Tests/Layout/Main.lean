import Tests.Layout.Differential

@[export p2_layout_canary_xor, noinline]
def layoutCanaryXor (x y : UInt64) : UInt64 := x ^^^ y

def main (args : List String) : IO Unit := do
  if layoutCanaryXor 3 3 != 0 then
    IO.eprintln "unexpected layout canary"
  LeanVmXmss.Tests.Layout.runDifferential args
