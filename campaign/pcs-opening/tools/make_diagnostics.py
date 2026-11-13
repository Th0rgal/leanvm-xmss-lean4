"""Generate an isolated IO replay of the actual PCS call graph; never certify it."""
from pathlib import Path
root = Path(__file__).resolve().parents[3] / 'LeanVmXmss'
flat = (root / 'Model/Pcs/FlatWhir.lean').read_text()
e2e = (root / 'Model/Cli/E2E.lean').read_text()

def section(text, start, end):
    return text[text.index(start):text.index(end)]

def replace(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)

header = '''import Model.Cli.E2E

namespace LeanVmXmss.PcsOpeningDiagnostics
open Spec.Field (K E)
open Spec.Vm
open Model.Merkle (Digest32)
open Model.Pcs.Ntt (Vec8 foldRange)
open Model.Pcs.Whir
open Model.Pcs.FlatWhir
open Model.Cli

-- A noinline IO call forces the pure result before the stop-clock read.
-- This module is diagnostics only and is excluded from matched certification.
@[noinline] def forceResult (x : α) : IO α := pure x

def measured (name : String) (f : Unit → α) : IO α := do
  let start ← IO.monoNanosNow
  let value ← forceResult (f ())
  let stop ← IO.monoNanosNow
  IO.println s!"PCS_DIAG|{name}|nanos={stop-start}"
  return value

def need (x : Option α) : OptionT IO α := ⟨pure x⟩

'''
stream = section(flat, 'def streamCosetsOpen ', 'def openL0Cosets ')
stream = replace(stream, '(encodeCoset : Nat → Array Vec8)', '(encodeCoset : Nat → IO (Array Vec8))')
stream = replace(stream, 'Option Spec.Merkle.PrunedMerklePaths := do', 'OptionT IO Spec.Merkle.PrunedMerklePaths := do')
stream = replace(stream, 'let encoded := encodeCoset curC', 'let encoded ← encodeCoset curC')
stream = replace(stream, 'let r := fastSubRoot encoded subK (m <<< subK)', 'let r ← measured s!"unqueried_merkle|coset={curC}|sub={m}|k={subK}" (fun _ => fastSubRoot encoded subK (m <<< subK))')
stream = replace(stream, 'let leaves := foldRange subSize (fun acc j =>\n                  acc.push (leafAt encoded ((m <<< subK) + j))) (Array.emptyWithCapacity subSize)', 'let leaves ← measured s!"queried_leaves|coset={curC}|sub={m}|k={subK}" (fun _ => foldRange subSize (fun acc j =>\n                  acc.push (leafAt encoded ((m <<< subK) + j))) (Array.emptyWithCapacity subSize))')
stream = replace(stream, 'let subTree ← Model.Merkle.buildFlat subK leaves', 'let subTree ← need (← measured "queried_buildFlat" (fun _ => Model.Merkle.buildFlat subK leaves))')
stream = replace(stream, 'let topTree ← Model.Merkle.buildFlat (blockLog - subK) subRoots', 'let topTree ← need (← measured "top_buildFlat" (fun _ => Model.Merkle.buildFlat (blockLog - subK) subRoots))')
stream = stream.replace('some (', 'pure (').replace('some ⟨', 'pure ⟨')

l0 = section(flat, 'def openL0Cosets ', '@[inline] def extFirstWord ')
l0 = replace(l0, 'Option Spec.Merkle.PrunedMerklePaths := do', 'OptionT IO Spec.Merkle.PrunedMerklePaths := do')
l0 = replace(l0, 'then none', 'then failure')
l0 = replace(l0, '(fun curC =>\n        let first := firstCosetFromBytes bytes lanes nVecs logRows\n        Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate curC)', '(fun curC => do\n        let first ← measured s!"firstCoset|coset={curC}|logRows={logRows}|nVecs={nVecs}" (fun _ => firstCosetFromBytes bytes lanes nVecs logRows)\n        measured s!"nttL0|coset={curC}|logRows={logRows}|nVecs={nVecs}" (fun _ => Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate curC))')
ext = section(flat, 'def openExtCosets ', 'def openQueriesFlat ')
ext = replace(ext, 'Option Spec.Merkle.PrunedMerklePaths := do', 'OptionT IO Spec.Merkle.PrunedMerklePaths := do')
ext = replace(ext, 'then none', 'then failure')
ext = replace(ext, '(fun curC =>\n        Model.Pcs.Ntt.encodeCosetVec8 table prep.first nVecs logRows logInvRate curC)', '(fun curC => measured s!"nttExt|coset={curC}|logRows={logRows}|nVecs={nVecs}" (fun _ => Model.Pcs.Ntt.encodeCosetVec8 table prep.first nVecs logRows logInvRate curC))')
level = section(flat, 'def proveLevelPlanar ', 'def provePcsOpenFlat ')
level = replace(level, 'Option (PlanarFoldState × Option ExtPrepared) := do', 'OptionT IO (PlanarFoldState × Option ExtPrepared) := do')
level = replace(level, '  let p :=\n', '  let p ← measured s!"fold|level={level}|foldCount={foldCount}" (fun _ =>\n')
level = replace(level, 'foldRange foldCount (fun cur _ => stepFoldPlanar cur) p\n', 'foldRange foldCount (fun cur _ => stepFoldPlanar cur) p)\n')
level = replace(level, 'let (prep, root) := commitExtPlanar p.f (messageLog - nextFold) nextFold nextRate', 'let (prep, root) ← measured s!"commitExt|level={level}|logRows={messageLog-nextFold}|fold={nextFold}|rate={nextRate}" (fun _ => commitExtPlanar p.f (messageLog - nextFold) nextFold nextRate)')
level = replace(level, 'let (ood, s) := introduceOodPlanar p.f s messageLog', 'let (ood, s) ← measured "introduceOod" (fun _ => introduceOodPlanar p.f s messageLog)')
level = replace(level, 'let s ← grindWhirFast s queryGrindingBits', 'let s ← need (← measured "grindWhir" (fun _ => grindWhirFast s queryGrindingBits))')
level = replace(level, 'then none', 'then failure')
level = replace(level, '| none => none', '| none => failure')
level = replace(level, 'let basisI := inducedBasisPlanar messageLog rate queries weights', 'let basisI ← measured s!"inducedBasis|level={level}" (fun _ => inducedBasisPlanar messageLog rate queries weights)')
level = replace(level, 'let (u0, u2) := msgPlanar p.f basisI', 'let (u0, u2) ← measured s!"msgPlanar|level={level}" (fun _ => msgPlanar p.f basisI)')
level = replace(level, '    some (⟨', '    pure (⟨')
prove = section(flat, 'def provePcsOpenFlat ', 'def provePcsOpenFlatPlanar ')
prove = replace(prove, 'Option Spec.Transcript.ProverState := do', 'OptionT IO Spec.Transcript.ProverState := do')
prove = replace(prove, 'let config ← deriveConfig stackLog logInvRate', 'let config ← need (deriveConfig stackLog logInvRate)')
prove = prove.replace('then none', 'then failure')
prove = replace(prove, 'let terms := termsOf nWords laneVars lam points ring ringWeights', 'let terms ← measured s!"termsOf|nWords={nWords}|lanes={lanes}|stackLog={stackLog}" (fun _ => termsOf nWords laneVars lam points ring ringWeights)')
prove = replace(prove, '      some done.state', '      pure done.state')
passfn = section(e2e, 'def proveLeafEthereumTimedPass ', 'def proveLeafEthereumCore ')
passfn = replace(passfn, '  let ps1 ← match Model.Pcs.FlatWhir.provePcsOpenFlat ps0 mu logInvRate wq points ring with', '  let result ← (provePcsOpenFlat ps0 mu logInvRate wq points ring).run\n  let ps1 ← match result with')
main = '''end LeanVmXmss.PcsOpeningDiagnostics

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := ⟨args[0]?.getD ""⟩
  let outPath : System.FilePath := ⟨args[1]?.getD "diag.ethproof"⟩
  let records ← LeanVmXmss.Model.Cli.loadRawInputs (LeanVmXmss.Model.Cli.childPath dir "xmss-inputs.bin")
  let seed ← LeanVmXmss.Model.Cli.loadSeed (LeanVmXmss.Model.Cli.childPath dir "seed.bin")
  let bc ← LeanVmXmss.Model.Cli.loadBytecodeValue (LeanVmXmss.Model.Cli.childPath dir "bytecode-value.bin")
  let (program, frame, schedule) ← LeanVmXmss.Model.Cli.loadGuest dir
  let cols := LeanVmXmss.Model.Layout.bytecodeColumnsFast program
  let iv := LeanVmXmss.Model.Cli.ivOfCols program cols
  let (_, _, _, _, wire, timings) ← LeanVmXmss.PcsOpeningDiagnostics.proveLeafEthereumTimedPass
    program frame schedule seed bc records 1 iv cols
  IO.FS.writeBinFile outPath wire
  IO.println (LeanVmXmss.Model.Cli.phaseTimingsJson 0 timings)
'''
out = root / 'Tests/Hub/PcsOpeningDiagnostics.lean'
out.write_text(header + stream + l0 + ext + level + prove + passfn + main)
print(out)
