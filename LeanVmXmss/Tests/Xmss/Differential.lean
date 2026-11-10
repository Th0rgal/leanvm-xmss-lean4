import Model.Xmss.Hints
import Spec.Vm.Bytecode

namespace LeanVmXmss.Tests.Xmss

open Spec.Xmss

def childPath (base : System.FilePath) (name : String) : System.FilePath :=
  ⟨base.toString ++ "/" ++ name⟩

def hintBytes (hints : Array HintEntry) : ByteArray := hints.foldl (fun acc h =>
  let name := h.name.toUTF8
  let header := writeLE name.size.toUInt64 4 ++ name ++ writeLE h.values.size.toUInt64 4
  let words := h.values.foldl (fun bytes x => bytes ++ writeLE x.c0 8 ++ writeLE x.c1 8 ++ writeLE x.c2 8) ByteArray.empty
  acc ++ header ++ words) ByteArray.empty

def hex (bytes : ByteArray) : String := String.ofList (bytes.data.toList.flatMap fun b =>
  let digits := #[ '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f' ]
  [digits[b.toNat/16]!, digits[b.toNat%16]!])

def execute (input output : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile input
  let raw ← match parseRaw bytes with
    | .ok raw => pure raw
    | .error e => throw (IO.userError e)
  let seed ← IO.FS.readBinFile (childPath output "seed.bin")
  let value ← IO.FS.readBinFile (childPath output "bytecode-value.bin")
  let value : Spec.Field.E := ⟨readLE value 0 8,0,0⟩
  for x in raw do
    unless verifySignature x do throw (IO.userError "Lean signature verification failed")
  let hints ← match workloadHints #[packCell seed, packCell seed 16] raw value with
    | .ok hints => pure hints
    | .error e => throw (IO.userError e)
  let encoded := hintBytes hints
  let expected ← IO.FS.readBinFile (childPath output "hints.bin")
  unless encoded == expected do throw (IO.userError "Lean/Rust hint byte mismatch")
  let digest := statementDigest seed (sortedUnique raw) value
  let expectedDigest ← IO.FS.readBinFile (childPath output "statement.bin")
  unless digest == expectedDigest do throw (IO.userError "Lean/Rust statement mismatch")
  let bytecode ← IO.FS.readBinFile (childPath output "bytecode.bin")
  let ops ← match Spec.Vm.load bytecode with
    | .ok ops => pure ops
    | .error e => throw (IO.userError e)
  unless Spec.Vm.exportBytes ops == bytecode do throw (IO.userError "bytecode roundtrip failed")
  IO.println s!"records={raw.size} hint_entries={hints.size} hint_bytes={encoded.size} instructions={ops.size}"
  IO.println s!"statement_digest={hex digest}"
  IO.println s!"hints_keccak256={hex (Spec.Vm.KeccakInternal.hash encoded)}"

end LeanVmXmss.Tests.Xmss

