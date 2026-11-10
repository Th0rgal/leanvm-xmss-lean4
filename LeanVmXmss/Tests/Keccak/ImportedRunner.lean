import Tests.Keccak.ImportedNative

def main : IO Unit := do
  for (x, y) in ([(0, 0), (1, 0), (0, 1), (0xffffffffffffffff, 7), (17, 31)] : List (UInt64 × UInt64)) do
    let actual := LeanVmXmss.Tests.Keccak.ImportedNative.permutation x y
    let state : LeanVmXmss.Model.Keccak.State25 :=
      ⟨x, y, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let expected := (LeanVmXmss.Model.Keccak.keccakF1600 state).a00
    unless actual.toNat = expected.toNat do throw (IO.userError "Imported permutation mismatch")
    IO.println actual
