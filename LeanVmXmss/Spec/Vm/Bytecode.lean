import Spec.Vm.Basic

namespace LeanVmXmss.Spec.Vm

def encodeOp (op : Op) : ByteArray := Id.run do
  let (tag, words) : Nat × Array UInt64 := match op with
    | .xor a b c => (0, #[a.toUInt64,b.toUInt64,c.toUInt64])
    | .mul a b c => (1, #[a.toUInt64,b.toUInt64,c.toUInt64])
    | .set o k => (2, #[o.toUInt64,k.c0,k.c1,k.c2])
    | .deref a b c mode => (3, #[a.toUInt64,b.toUInt64,c.toUInt64,
        match mode with | .cell => 0 | .pc => 1 | .fp => 2])
    | .jump a b c => (4, #[a.toUInt64,b.toUInt64,c.toUInt64])
    | .keccak m tail b8 cap out i o => (5, m.map Nat.toUInt64 ++
        #[tail.toUInt64,b8.toUInt64,cap.toUInt64,out.toUInt64,if i then 1 else 0,if o then 1 else 0])
  return words.foldl (fun acc n => acc ++ Xmss.writeLE n 8) ⟨#[tag.toUInt8]⟩

def decodeOp (bytes : ByteArray) (offset : Nat) : Except String (Op × Nat) := do
  if offset >= bytes.size then throw "missing opcode"
  let tag := bytes[offset]!.toNat
  let n := if tag == 5 then 10 else if tag == 2 || tag == 3 then 4 else 3
  let endOffset := offset+1+8*n
  if endOffset > bytes.size then throw "truncated instruction"
  let words := (Array.range n).map fun i => Xmss.readLE bytes (offset+1+8*i) 8
  let a := words[0]!.toNat
  let b := words[1]!.toNat
  let c := words[2]!.toNat
  let op ← match tag with
    | 0 => pure (.xor a b c)
    | 1 => pure (.mul a b c)
    | 2 => pure (.set a ⟨words[1]!,words[2]!,words[3]!⟩)
    | 3 => do
      let mode ← match words[3]!.toNat with
        | 0 => pure DerefMode.cell
        | 1 => pure DerefMode.pc
        | 2 => pure DerefMode.fp
        | _ => throw "invalid dereference mode"
      pure (.deref a b c mode)
    | 4 => pure (.jump a b c)
    | 5 => do
      if words[8]!.toNat > 1 || words[9]!.toNat > 1 then throw "invalid Keccak parity"
      pure (.keccak ((words.extract 0 4).map UInt64.toNat) words[4]!.toNat words[5]!.toNat
        words[6]!.toNat words[7]!.toNat (words[8]!.toNat == 1) (words[9]!.toNat == 1))
    | _ => throw "unknown opcode"
  return (op,endOffset)

def load (bytes : ByteArray) : Except String (Array Op) := do
  let mut offset := 0
  let mut out := #[]
  for _ in [:bytes.size+1] do
    if offset == bytes.size then return out
    let (op, next) ← decodeOp bytes offset
    offset := next
    out := out.push op
  throw "bytecode load limit"

def exportBytes (ops : Array Op) : ByteArray := ops.foldl (fun acc op => acc ++ encodeOp op) ByteArray.empty

end LeanVmXmss.Spec.Vm
