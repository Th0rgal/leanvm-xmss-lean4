import Tests.Xmss.Differential

def main (args : List String) : IO Unit := do
  match args with
  | [input, output] => LeanVmXmss.Tests.Xmss.execute input output
  | _ => throw (IO.userError "expected raw input and oracle output directory")
