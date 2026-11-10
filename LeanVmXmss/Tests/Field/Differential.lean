import Model.Field.Operations

namespace LeanVmXmss.Tests.Field

open Spec.Field (E)

def run : IO Unit := do
  let input ← IO.FS.readFile "Tests/Field/artifacts/field-vectors.txt"
  for line in input.splitOn "\n" do
    if line.isEmpty then continue
    let ns := (line.splitOn " ").filterMap String.toNat?
    if ns.length != 7 then throw (IO.userError "vector length")
    let a : E := ⟨UInt64.ofNat ns[0]!, UInt64.ofNat ns[1]!, UInt64.ofNat ns[2]!⟩
    let b : E := ⟨UInt64.ofNat ns[3]!, UInt64.ofNat ns[4]!, UInt64.ofNat ns[5]!⟩
    let k := UInt64.ofNat ns[6]!
    let sum := Model.Field.eadd a b
    let prod := Model.Field.karatsubaMul a b
    let mixed := Model.Field.mulBase a k
    let sq := Model.Field.esquare a
    if prod != Model.Field.polynomialMul a b then throw (IO.userError "Karatsuba mismatch")
    if prod != Spec.Field.emul a b then throw (IO.userError "specification mismatch")
    if mixed != Spec.Field.mulBase a k then throw (IO.userError "mulBase mismatch")
    if sq != Spec.Field.esquare a then throw (IO.userError "square mismatch")
    if Spec.Field.decode (Spec.Field.encode a) != a then throw (IO.userError "encoding mismatch")
    let inverse := Model.Field.einv a
    let frob := Model.Field.frobenius a
    let power := Model.Field.epow a (k.toNat % 17)
    let scaled := Model.Field.scaledMul (Model.Field.scaled a) b
    if scaled != prod then throw (IO.userError "Scaled mismatch")
    if Model.Field.decodeBytesK? (Model.Field.encodeBytesK a.c0) != some a.c0 then
      throw (IO.userError "base codec mismatch")
    if Model.Field.decodeBytesE? (Model.Field.encodeBytesE a) != some a then
      throw (IO.userError "extension codec mismatch")
    if (Model.Field.decodeBytesK? (Model.Field.encodeBytesK a.c0 ++ ⟨#[0]⟩)).isSome then
      throw (IO.userError "base trailing bytes accepted")
    if (Model.Field.decodeBytesE? (Model.Field.encodeBytesE a ++ ⟨#[0]⟩)).isSome then
      throw (IO.userError "extension trailing bytes accepted")
    let values := [Model.Field.add a.c0 b.c0, Model.Field.mul a.c0 b.c0, Model.Field.square a.c0,
      sum.c0, sum.c1, sum.c2, prod.c0, prod.c1, prod.c2,
      mixed.c0, mixed.c1, mixed.c2, sq.c0, sq.c1, sq.c2,
      Model.Field.inv a.c0, inverse.c0, inverse.c1, inverse.c2,
      power.c0, power.c1, power.c2, frob.c0, frob.c1, frob.c2,
      scaled.c0, scaled.c1, scaled.c2, Model.Field.pow a.c0 (k.toNat % 17)]
    let hex := fun (bytes : ByteArray) => String.ofList (bytes.data.toList.flatMap fun b =>
      ["0123456789abcdef".toList[b.toNat / 16]!, "0123456789abcdef".toList[b.toNat % 16]!])
    IO.println (String.intercalate " " ((values.map (fun x => toString x.toNat)) ++
      [hex (Model.Field.encodeBytesK a.c0), hex (Model.Field.encodeBytesE a)]))

#eval run

end LeanVmXmss.Tests.Field
