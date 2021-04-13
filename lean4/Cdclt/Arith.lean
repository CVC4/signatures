import Cdclt.Boolean

open proof
open proof.sort proof.Term
open rules

def mkPlus : Option Term → Option Term → Option Term :=
  constructBinaryTerm plus (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkPlusN : List (Option Term) → Option Term :=
    constructNaryTerm plus (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkMinus : Option Term → Option Term → Option Term :=
  constructBinaryTerm minus (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkMult : Option Term → Option Term → Option Term :=
  constructBinaryTerm mult (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkMultN : List (Option Term) → Option Term :=
    constructNaryTerm mult (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkGt : Option Term → Option Term → Option Term :=
  constructBinaryTerm gt (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkGte : Option Term → Option Term → Option Term :=
  constructBinaryTerm gte (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkLt : Option Term → Option Term → Option Term :=
  constructBinaryTerm lt (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkLte : Option Term → Option Term → Option Term :=
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
def sumBounds : Option Term → Option Term → Option Term :=
| f₁ t₁₁ t₁₂, f₂ t₂₁ t₂₂ =>
  mkPlus t₁₁ t₂₁ >>= λ l =>
  mkPlus t₁₂ t₂₂ >>= λ r =>
  match f₁, f₂ with
  | lt, lt => mkLt l r
  | lt, lte => mkLt l r
  | lt, eq => mkLt l r
  | lte, lt => mkLt l r
  | lte, lte => mkLte l r
  | lte, eq => mkLte l r
  | eq, lt => mkLt l r
  | eq, lte => mkLte l r
  | eq, eq => mkLte l r
  | _, _ => none
| _, _ => none



axiom sumUb : ∀ {t₁ t₂ : Option Term}, thHolds t₁ → thHolds t₂ → thHolds (sumBounds t₁ t₂)

/-
======= Multiplication with positive factor
Children: none
Arguments: (m, (rel lhs rhs))
---------------------
Conclusion: (=> (and (> m 0) (rel lhs rhs)) (rel (* m lhs) (* m rhs)))
Where rel is a relation symbol.
-/

def multPosFactorAux (m : Option Term) (t : Option Term) : Option Term :=
  m >>= λ m' =>
  match t with
  | f • t₁ • t₂ =>
    mkGt m' (val (Value.integer 0) intSort) >>= λ ph₁ =>
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

axiom multPosFactor : ∀ {t : Option Term} (m : Option Term),
  thHolds (multPosFactorAux m t)

def multNegFactorAux (m : Option Term) (t : Option Term) : Option Term :=
  m >>= λ m' =>
  match t with
  | f • t₁ • t₂ =>
    mkLt m' (val (Value.integer 0) intSort) >>= λ ph₁ =>
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

axiom multNegFactor : ∀ {t : Option Term} (m : Option Term),
  thHolds (multNegFactorAux m t)

end arithRules
