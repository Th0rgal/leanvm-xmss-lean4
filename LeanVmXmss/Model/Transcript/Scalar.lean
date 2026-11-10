import Spec.Transcript.Basic
import Model.Keccak.Scalar
import Model.Merkle.Scalar

namespace LeanVmXmss.Model.Transcript

abbrev Sponge := Spec.Transcript.Sponge
abbrev ProverState := Spec.Transcript.ProverState

def duplex (s : Sponge) : Spec.Field.E × Sponge :=
  let a := Keccak.permute s.state
  (⟨a[0]!, a[1]!, a[2]!⟩,
    ⟨(Array.range 25).map (fun i => if i < 16 then 0 else a[i]!), 0⟩)

def absorb := Spec.Transcript.absorb
def observe := Spec.Transcript.observe
def challenge := duplex
def init := Spec.Transcript.init
def fromLabel := Spec.Transcript.fromLabel
def observeDigest := Spec.Transcript.observeDigest
def powBitsOk := Spec.Transcript.powBitsOk
def verifyPow := Spec.Transcript.verifyPow
def powGrinding := Spec.Transcript.powGrinding
def proverNew := Spec.Transcript.proverNew
def proverFromLabel := Spec.Transcript.proverFromLabel
def addScalar := Spec.Transcript.addScalar
def addScalars := Spec.Transcript.addScalars
def addRoot := Spec.Transcript.addRoot
def addRoundPoly := Spec.Transcript.addRoundPoly
def hintMerkle := Spec.Transcript.hintMerkle
def sample := Spec.Transcript.sample
def grind := Spec.Transcript.grind
def proofBytes := Spec.Transcript.proofBytes

end LeanVmXmss.Model.Transcript
