import Tests.Audit.Mutants

def parseArgs (args : List String) (oracle core out : String) (dump : Option String) :
    IO (String × String × String × Option String) :=
  match args with
  | [] => pure (oracle, core, out, dump)
  | "--oracle-xmss4" :: v :: rest => parseArgs rest v core out dump
  | "--core-proof" :: v :: rest => parseArgs rest oracle v out dump
  | "--json" :: v :: rest => parseArgs rest oracle core v dump
  | "--dump-dir" :: v :: rest => parseArgs rest oracle core out (some v)
  | other :: _ => throw (IO.userError s!"unknown argument: {other}")

def main (args : List String) : IO Unit := do
  let hub := (← IO.getEnv "HUB").getD "/var/lib/orb-node/work/caches/xmss-hub-v3"
  let (oracle, core, out, dump) ← parseArgs args
    (hub ++ "/oracle/xmss4")
    (hub ++ "/artifacts/p2-e2e-proofs/xmss4.ethproof")
    "/tmp/opencode/lean-mutants34.json"
    none
  LeanVmXmss.Tests.Audit.Mutants.runMutantSuite34 oracle core out dump
