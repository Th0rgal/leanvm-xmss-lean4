import Proofs.Layout.Basic
import Spec.Vm.Bytecode

namespace LeanVmXmss.Tests.Layout

open Spec.Field (K E)
open Spec.Layout
open Model.Layout

def hexByte (b : UInt8) : String :=
  let digits : Array Char :=
    #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']
  let hi := digits[(b.toNat >>> 4) % 16]?.getD '0'
  let lo := digits[b.toNat % 16]?.getD '0'
  String.ofList [hi, lo]

def hexBytes (bytes : ByteArray) : String :=
  bytes.data.foldl (fun acc b => acc ++ hexByte b) ""

def hashWords (words : Array K) : String :=
  hexBytes (keccak256Stream (wordsBytesFast words))

def formatAtom (a : Atom) : String :=
  match a with
  | .const v => s!"K({v.toNat})"
  | .col i => s!"C({i})"
  | .gcol i k => s!"G({i},{k})"
  | .prod i j k => s!"P({i},{j},{k})"

def formatCoord (c : Coord) : String :=
  match c with
  | .atom a => formatAtom a
  | .index => "I"
  | .publicCol s => s!"B({s})"
  | .sum ts =>
    let inner := String.intercalate "+" (ts.toList.map formatAtom)
    s!"S[{inner}]"

def formatBlock (b : Block) : String :=
  let cs := String.intercalate "," (b.coords.toList.map formatCoord)
  let ps := String.intercalate "," (b.padding.toList.map fun p => toString p.toNat)
  s!"{b.kappa}|{b.rows}|[{cs}]|[{ps}]"

def formatSource (logBytecode col : Nat) : String :=
  match kappaSource logBytecode col with
  | some (src, adj) => s!"{src}:{adj}"
  | none => "none"

def formatKeccakVal (col : Nat) : String :=
  match keccakValue col with
  | some (.slot s) => s!"S({s})"
  | some (.output o) => s!"O({o})"
  | none => "N"

def formatPlacement (p : Option Placement) : String :=
  match p with
  | some pl => s!"{pl.variables}:{pl.index}"
  | none => "none"

def syntheticProg : Array Spec.Vm.Op :=
  #[.xor 2 3 4,
    .mul 5 6 7,
    .set 8 ⟨0x123456789abcdef0, 0xfedcba9876543210, 0x1122334455667788⟩,
    .deref 2 3 9 .cell,
    .deref 2 1 10 .pc,
    .deref 4 2 11 .fp,
    .jump 2 7 0,
    .keccak #[1, 3, 5, 7] 9 11 13 15 true false]

def emitCase (name : String) (prog : Array Spec.Vm.Op) (logMem : Nat) (rows : Array Nat) : IO Unit := do
  let logBc ← match log2Strict? prog.size with
    | some k => pure k
    | none => throw (IO.userError "program size is not a power of two")
  unless validateSizes logMem logBc 1 rows do
    throw (IO.userError s!"invalid sizes for {name}")
  let cols := bytecodeColumnsFast prog
  let table := stackBytecodeColumnsFast logBc cols
  let iv := fiatShamirIvFast table
  let lay := buildPublicLayout logMem logBc rows
  let bases : List String :=
    [tableBase ⟨0, by decide⟩, tableBase ⟨1, by decide⟩, tableBase ⟨2, by decide⟩,
     tableBase ⟨3, by decide⟩, tableBase ⟨4, by decide⟩, tableBase ⟨5, by decide⟩].map toString
  IO.println s!"CASE|{name}"
  IO.println s!"SCHEMA|{nColumns}|{qKeccakSpare}|{String.intercalate "," bases}"
  let sources := (List.range nColumns).map (formatSource logBc)
  IO.println s!"SOURCES|{String.intercalate "," sources}"
  let kv := (List.range nColumns).map formatKeccakVal
  IO.println s!"KECCAK_VAL|{String.intercalate "," kv}"
  IO.println s!"IV|{hexBytes iv}"
  IO.println s!"BC_LEN|{table.size}"
  IO.println s!"BC_WORD0|{(table[0]?.getD 0).toNat}"
  IO.println s!"BC_HASH|{hashWords table}"
  let tausStr := String.intercalate "," (lay.taus.toList.map toString)
  IO.println s!"TAUS|{tausStr}"
  IO.println s!"SHAPE|{lay.shape.mu}|{lay.shape.nLanes}|{committedLen lay.shape}|{lay.placed}"
  let plcStr := String.intercalate "," (lay.placements.toList.map formatPlacement)
  IO.println s!"PLACEMENTS|{plcStr}"
  let pushOff := String.intercalate "," (lay.pushLayout.offsets.toList.map toString)
  let pullOff := String.intercalate "," (lay.pullLayout.offsets.toList.map toString)
  let cntOff := String.intercalate "," (lay.countLayout.offsets.toList.map toString)
  IO.println s!"BUS_PUSH_LAY|{lay.pushLayout.mu}|{pushOff}"
  IO.println s!"BUS_PULL_LAY|{lay.pullLayout.mu}|{pullOff}"
  IO.println s!"BUS_COUNT_LAY|{lay.countLayout.mu}|{cntOff}"
  for i in [:lay.push.size] do
    if let some b := lay.push[i]? then
      IO.println s!"PUSH|{i}|{formatBlock b}"
  for i in [:lay.pull.size] do
    if let some b := lay.pull[i]? then
      IO.println s!"PULL|{i}|{formatBlock b}"
  for i in [:lay.count.size] do
    if let some b := lay.count[i]? then
      IO.println s!"COUNT|{i}|{formatBlock b}"

def runDifferential (args : List String) : IO Unit := do
  let syn := syntheticProg
  emitCase "syn_tiny" syn 16 #[0, 1, 2, 3, 4, 5]
  emitCase "syn_keccak_heavy" syn 20 #[1000, 2048, 0, 513, 17, 600]
  match args with
  | [bcPath] =>
    let bcBytes ← IO.FS.readBinFile bcPath
    let xmssProg ← match Spec.Vm.load bcBytes with
      | .ok ops => pure ops
      | .error err => throw (IO.userError err)
    emitCase "xmss1400" xmssProg 24 #[262098, 237184, 169439, 159273, 57477, 261066]
  | [] => pure ()
  | _ => throw (IO.userError "expected optional bytecode.bin path")

end LeanVmXmss.Tests.Layout
