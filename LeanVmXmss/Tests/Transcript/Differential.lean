import Model.Transcript.Scalar

open LeanVmXmss

def printBytes (b : ByteArray) : IO Unit :=
  IO.println (String.intercalate " " (b.data.toList.map fun x => toString x.toNat))

def printScalar (x : Spec.Field.E) : IO Unit := IO.println s!"{x.c0} {x.c1} {x.c2}"

def pattern (n : Nat) : ByteArray := ⟨(Array.range n).map fun i => UInt8.ofNat (i * 7 + 3)⟩

def main : IO Unit := do
  for n in [0, 1, 135, 136, 137, 272, 1000] do
    printBytes (Model.Keccak.keccak256 (pattern n))
  let abc := Model.Keccak.keccak256 "abc".toUTF8
  printBytes abc
  if abc == Spec.Keccak.hashWithDomain "abc".toUTF8 6 then throw (IO.userError "SHA3 mutant")
  let halves := Model.Merkle.hashToScalars abc
  unless decide (halves = (⟨5740196073438511950, 7482387899283657927, 0⟩,
      ⟨3936256278416249280, 5002423458029978860, 0⟩)) do throw (IO.userError "digest halves")
  printScalar halves.1
  printScalar halves.2
  for width in [1, 2, 4, 8] do
    let leaves := (Array.range width).map fun i => Model.Merkle.hashRow #[UInt64.ofNat (i + 1), UInt64.ofNat (i * 11)] 5
    let tree := Model.Merkle.build leaves
    let root := Spec.Merkle.treeRoot tree
    printBytes (Spec.Merkle.digestBytes root)
    for i in [:width] do
      let path := Model.Merkle.inclusionPath tree i
      unless Model.Merkle.verifyPath root leaves[i]! i path.toList do throw (IO.userError "opening failed")
      for d in path do printBytes (Spec.Merkle.digestBytes d)
  let l := Model.Merkle.hashLeaf (pattern 1)
  let r := Model.Merkle.hashLeaf (pattern 2)
  if Model.Merkle.compress l r == Model.Merkle.compress r l then throw (IO.userError "swapped children mutant")
  let seeded := Model.Transcript.fromLabel "shard-b".toUTF8
  let tagged := Spec.Transcript.absorb seeded ⟨0, 0, 0⟩ 1
  let untagged := Spec.Transcript.absorb seeded ⟨0, 0, 0⟩ 0
  if decide ((Model.Transcript.challenge tagged).1 = (Model.Transcript.challenge untagged).1) then
    throw (IO.userError "missing domain mutant")
  let raw := Spec.Keccak.permute seeded.state
  let xorInput := raw.set! 0 (raw[0]! ^^^ 7)
  let overwriteInput := ((Array.range 25).map fun i => if i < 16 then (0 : UInt64) else raw[i]!).set! 0 7
  if Spec.Keccak.permute xorInput == Spec.Keccak.permute overwriteInput then
    throw (IO.userError "xor duplex mutant")
  let mut p := Model.Transcript.proverFromLabel "shard-b".toUTF8
  for i in [:11] do
    p := Model.Transcript.addScalar p ⟨UInt64.ofNat (i + 1), UInt64.ofNat (i * 17), UInt64.ofNat (i * 31)⟩
    if i % 3 == 2 then
      let (x, q) := Model.Transcript.sample p
      printScalar x
      p := q
  p := Model.Transcript.addRoot p abc
  p := Model.Transcript.addRoundPoly p #[⟨1, 2, 3⟩, ⟨4, 5, 6⟩, ⟨7, 8, 9⟩] false
  p := Model.Transcript.addRoundPoly p #[⟨11, 12, 13⟩, ⟨14, 15, 16⟩, ⟨17, 18, 19⟩] true
  for bits in [0, 4, 8] do
    let before := p.sponge
    let some (n, q) := Model.Transcript.grind p bits 100000 | throw (IO.userError "grind exhausted")
    unless (Model.Transcript.verifyPow before ⟨n, 0, 0⟩ bits).1 do throw (IO.userError "pow rejected")
    for candidate in [:n.toNat] do
      if bits > 0 && Model.Transcript.powBitsOk before ⟨UInt64.ofNat candidate, 0, 0⟩ bits then
        throw (IO.userError "nonce not minimal")
    if bits == 8 then
      let some weak := Spec.Transcript.searchNonce before 1 100000 0 | throw (IO.userError "weak grind exhausted")
      if (Model.Transcript.verifyPow before ⟨weak, 0, 0⟩ bits).1 then
        throw (IO.userError "insufficient pow witness did not discriminate")
    IO.println n
    p := q
    let (x, q) := Model.Transcript.sample p
    printScalar x
    p := q
  printBytes (Model.Transcript.proofBytes p)

#eval main
