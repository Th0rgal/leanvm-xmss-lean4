import Spec.Field.Basic

namespace LeanVmXmss.Spec.Field

def polynomialMultiple (m : Nat) : List Nat → Nat :=
  List.foldr (fun i prev => (m <<< i) ^^^ prev) 0

@[simp] theorem polynomialMultiple.nil (m : Nat) : polynomialMultiple m [] = 0 := rfl

@[simp] theorem polynomialMultiple.cons (m i : Nat) (rest : List Nat) :
    polynomialMultiple m (i :: rest) = (m <<< i) ^^^ polynomialMultiple m rest := rfl

def PolynomialCongruent (m a b : Nat) : Prop :=
  ∃ shifts : List Nat, a ^^^ b = polynomialMultiple m shifts

def extendRepresentative (a : E) : Fin 5 → K
  | 0 => a.c0
  | 1 => a.c1
  | 2 => a.c2
  | 3 => 0
  | 4 => 0

def extensionMultiple (r s : K) : Fin 5 → K
  | 0 => r
  | 1 => r ^^^ s
  | 2 => s
  | 3 => r
  | 4 => s

def ExtensionCongruent (a b : Fin 5 → K) : Prop :=
  ∃ r s : K, ∀ i, a i ^^^ b i = extensionMultiple r s i

end LeanVmXmss.Spec.Field
