import Cdclt.Boolean

open proof
open proof.sort proof.term
open rules

def mkPlus : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm plus (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkPlusN : List (OptionM term) → OptionM term :=
    constructNaryTerm plus (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkMinus : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm minus (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkMult : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm mult (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkMultN : List (OptionM term) → OptionM term :=
    constructNaryTerm mult (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkGt : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm gt (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkGte : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm gte (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkLt : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm lt (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkLte : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm lte (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

namespace arithRules

/-
  ======== Sum Upper Bounds
  Children: (P1 P2)
            where each Pi has form (><i, Li, Ri)
            for ><i in {<, <=, ==}
  Conclusion: (>< L R)
            where >< is < if any ><i is <, and <= otherwise.
                  L is (+ L1 L2)
                  R is (+ R1 R2)
-/
def sumBounds : OptionM term → OptionM term → OptionM term
| f₁ • t₁₁ • t₁₂, f₂ • t₂₁ • t₂₂ =>
  mkPlus t₁₁ t₂₁ >>= λ l =>
  mkPlus t₁₂ t₂₂ >>= λ r =>
  match f₁, f₂ with
  | ltConst, ltConst => mkLt l r
  | ltConst, lteConst => mkLt l r
  | ltConst, eqConst => mkLt l r
  | lteConst, ltConst => mkLt l r
  | lteConst, lteConst => mkLte l r
  | lteConst, eqConst => mkLte l r
  | eqConst, ltConst => mkLt l r
  | eqConst, lteConst => mkLte l r
  | eqConst, eqConst => mkLte l r
  | _, _ => none
| _, _ => none

axiom sumUb : ∀ {t₁ t₂ : OptionM term}, thHolds t₁ → thHolds t₂ → thHolds (sumBounds t₁ t₂)

/-
======= Multiplication with positive factor
Children: none
Arguments: (m, (rel lhs rhs))
---------------------
Conclusion: (=> (and (> m 0) (rel lhs rhs)) (rel (* m lhs) (* m rhs)))
Where rel is a relation symbol.
-/

def multPosFactorAux (m : OptionM term) (t : OptionM term) : OptionM term :=
  m >>= λ m' =>
  match t with
  | f • t₁ • t₂ =>
    mkGt m' (val (value.integer 0) intSort) >>= λ ph₁ =>
    mkAnd ph₁ t >>= λ ph₂ =>
    mkMult m' t₁ >>= λ ph₃ =>
    mkMult m' t₂ >>= λ ph₄ =>
    (match f with
    | gtConst => mkGt ph₃ ph₄
    | gteConst => mkGte ph₃ ph₄
    | ltConst => mkLt ph₃ ph₄
    | lteConst => mkLte ph₃ ph₄
    | eqConst => mkEq ph₃ ph₄
    | _ => none) >>= λ ph₄ => mkImplies ph₂ ph₄
  | _ => none

axiom multPosFactor : ∀ {t : OptionM term} (m : OptionM term),
  thHolds (multPosFactorAux m t)

def multNegFactorAux (m : OptionM term) (t : OptionM term) : OptionM term :=
  m >>= λ m' =>
  match t with
  | f • t₁ • t₂ =>
    mkLt m' (val (value.integer 0) intSort) >>= λ ph₁ =>
    mkAnd ph₁ t >>= λ ph₂ =>
    mkMult m' t₁ >>= λ ph₃ =>
    mkMult m' t₂ >>= λ ph₄ =>
    (match f with
    | gtConst => mkLt ph₃ ph₄
    | gteConst => mkLte ph₃ ph₄
    | ltConst => mkGt ph₃ ph₄
    | lteConst => mkGte ph₃ ph₄
    | eqConst => mkEq ph₃ ph₄
    | _ => none) >>= λ ph₄ => mkImplies ph₂ ph₄
  | _ => none

axiom multNegFactor : ∀ {t : OptionM term} (m : OptionM term),
  thHolds (multNegFactorAux m t)

end arithRules
