import Spec.Pcs.Commit
import Model.Pcs.Commit

open LeanVmXmss.Spec.Pcs.Ntt
open LeanVmXmss.Spec.Pcs.Commit
open LeanVmXmss.Spec.Field (K add mul)

def hexByte (b : UInt8) : String :=
  let digits : Array Char :=
    #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']
  let hi := digits[(b.toNat >>> 4) % 16]?.getD '0'
  let lo := digits[b.toNat % 16]?.getD '0'
  String.ofList [hi, lo]

def hexBytes (bytes : ByteArray) : String :=
  bytes.data.foldl (fun acc b => acc ++ hexByte b) ""

def showK (k : K) : String := toString k.toNat

def genMsg (n : Nat) : Array K :=
  LeanVmXmss.Model.Pcs.Ntt.foldRange n
    (fun acc i => acc.push (UInt64.ofNat (i * 0x9e3779b97f4a7c15 + 1)))
    (Array.emptyWithCapacity n)

def main : IO Unit := do
  let msg : Array K := #[1, 2, 3, 4]
  let rtSpec := root msg 1 2 1
  let rtModel := LeanVmXmss.Model.Pcs.Commit.rootBytes msg 1 2 1
  IO.println ("ROOT_SPEC|" ++ hexBytes rtSpec)
  IO.println ("ROOT_MODEL|" ++ hexBytes rtModel)
  for lanes in [1, 7, 8, 9, 16, 17, 32, 51, 56, 64] do
    let m := genMsg (lanes * 8)
    let rs := root m lanes 3 1
    let rm := LeanVmXmss.Model.Pcs.Commit.rootBytes m lanes 3 1
    if rs != rm then
      throw (IO.userError s!"mismatch at lanes={lanes}: {hexBytes rs} != {hexBytes rm}")
  IO.println "PARITY_ALL_WIDTHS|PASS"
  let benchMsg ← IO.lazyPure (fun () => genMsg (51 * (1 <<< 15)))
  let t0 ← IO.monoMsNow
  let rb ← IO.lazyPure (fun () => LeanVmXmss.Model.Pcs.Commit.rootBytes benchMsg 51 15 1)
  let t1 ← IO.monoMsNow
  IO.println s!"BENCH_LOG15_MS|{t1 - t0}|{hexBytes rb}"
