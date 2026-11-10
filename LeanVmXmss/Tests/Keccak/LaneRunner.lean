import Model.Transcript.Registers

def main : IO Unit := do
  let mut state : LeanVmXmss.Model.Keccak.State25 :=
    ⟨1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25⟩
  for i in [:24] do
    state := LeanVmXmss.Model.Keccak.round25 state (LeanVmXmss.Model.Keccak.roundConstant i)
  IO.println s!"{state.a00} {state.a01} {state.a02} {state.a16} {state.a24}"
  let seed : LeanVmXmss.Model.Keccak.State25 :=
    ⟨11, 22, 33, 44, 55, 66, 77, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  let mut sponge : LeanVmXmss.Model.Transcript.Registers.Sponge :=
    ⟨LeanVmXmss.Model.Keccak.keccakF1600 seed, default, default, default, default, 0⟩
  for i in [:6] do
    let k := UInt64.ofNat i
    sponge := LeanVmXmss.Model.Transcript.Registers.observe sponge ⟨k + 1, k * 17 + 3, k * 31 + 5⟩
  let (ch, sponge1) := LeanVmXmss.Model.Transcript.Registers.sample sponge
  IO.println s!"{ch.c0} {ch.c1} {ch.c2}"
  let some (nonce, sponge2) := LeanVmXmss.Model.Transcript.Registers.grind sponge1 6 100000
    | throw (IO.userError "grind exhausted")
  let (ch2, _) := LeanVmXmss.Model.Transcript.Registers.sample sponge2
  IO.println s!"{nonce} {ch2.c0} {ch2.c1} {ch2.c2}"
