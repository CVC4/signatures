import Cdclt.Boolean

open proof
open proof.sort proof.Term
open rules

-- arith

@[matchPattern] def plus : Term → Term → Term := liftBinary plusConst
@[matchPattern] def minus : Term → Term → Term := liftBinary minusConst
@[matchPattern] def mult : Term → Term → Term := liftBinary multConst
@[matchPattern] def gt : Term → Term → Term := liftBinary gtConst
@[matchPattern] def gte : Term → Term → Term := liftBinary gteConst
@[matchPattern] def lt : Term → Term → Term := liftBinary ltConst
@[matchPattern] def lte : Term → Term → Term := liftBinary lteConst


def mkPlus : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm plus (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkPlusN : List (OptionM Term) → OptionM Term :=
    constructNaryTerm plus (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkMinus : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm minus (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkMult : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm mult (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkMultN : List (OptionM Term) → OptionM Term :=
    constructNaryTerm mult (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkGt : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm gt (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkGte : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm gte (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkLt : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm lt (λ s₁ s₂ => s₁ = intSort ∧ s₂ = intSort)

def mkLte : OptionM Term → OptionM Term → OptionM Term :=
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
def sumBounds (o₁ o₂ : OptionM Term) : OptionM Term :=
   o₁ >>= λ t₁ =>
   o₂ >>= λ t₂ =>
   match (t₁,t₂) with
   | (lt t₁₁ t₁₂, lt t₂₁ t₂₂) =>
     mkPlus t₁₁ t₂₁ >>= λ l =>
     mkPlus t₁₂ t₂₂ >>= λ r => mkLt l r
   | (lt t₁₁ t₁₂, lte t₂₁ t₂₂) =>
     mkPlus t₁₁ t₂₁ >>= λ l =>
     mkPlus t₁₂ t₂₂ >>= λ r => mkLt l r
   | (lt t₁₁ t₁₂, eq t₂₁ t₂₂) =>
     mkPlus t₁₁ t₂₁ >>= λ l =>
     mkPlus t₁₂ t₂₂ >>= λ r => mkLt l r
   | (lte t₁₁ t₁₂, lt t₂₁ t₂₂) =>
     mkPlus t₁₁ t₂₁ >>= λ l =>
     mkPlus t₁₂ t₂₂ >>= λ r => mkLt l r
   | (lte t₁₁ t₁₂, lte t₂₁ t₂₂) =>
     mkPlus t₁₁ t₂₁ >>= λ l =>
     mkPlus t₁₂ t₂₂ >>= λ r => mkLte l r
   | (lte t₁₁ t₁₂, eq t₂₁ t₂₂) =>
     mkPlus t₁₁ t₂₁ >>= λ l =>
     mkPlus t₁₂ t₂₂ >>= λ r => mkLte l r
   | (eq t₁₁ t₁₂, lt t₂₁ t₂₂) =>
     mkPlus t₁₁ t₂₁ >>= λ l =>
     mkPlus t₁₂ t₂₂ >>= λ r => mkLt l r
   | (eq t₁₁ t₁₂, lte t₂₁ t₂₂) =>
     mkPlus t₁₁ t₂₁ >>= λ l =>
     mkPlus t₁₂ t₂₂ >>= λ r => mkLte l r
   | (eq t₁₁ t₁₂, eq t₂₁ t₂₂) =>
     mkPlus t₁₁ t₂₁ >>= λ l =>
     mkPlus t₁₂ t₂₂ >>= λ r => mkLte l r
   | (_,_) => none



axiom sumUb : ∀ {t₁ t₂ : OptionM Term}, thHolds t₁ → thHolds t₂ → thHolds (sumBounds t₁ t₂)

/-
======= Multiplication with positive factor
Children: none
Arguments: (m, (rel lhs rhs))
---------------------
Conclusion: (=> (and (> m 0) (rel lhs rhs)) (rel (* m lhs) (* m rhs)))
Where rel is a relation symbol.
-/

def multPosFactorAux (m : OptionM Term) (t : OptionM Term) : OptionM Term :=
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

axiom multPosFactor : ∀ {t : OptionM Term} (m : OptionM Term),
  thHolds (multPosFactorAux m t)

def multNegFactorAux (m : OptionM Term) (t : OptionM Term) : OptionM Term :=
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

axiom multNegFactor : ∀ {t : OptionM Term} (m : OptionM Term),
  thHolds (multNegFactorAux m t)

end arithRules
