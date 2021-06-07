import Cdclt.Boolean

open proof
open proof.sort proof.term
open rules

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
def sumBounds : term → term → term
| f₁ • t₁₁ • t₁₂, f₂ • t₂₁ • t₂₂ =>
  let l := plus t₁₁ t₂₁
  let r := plus t₁₂ t₂₂
  match f₁, f₂ with
  | ltConst, ltConst => lt l r
  | ltConst, lteConst => lt l r
  | ltConst, eqConst => lt l r
  | lteConst, ltConst => lt l r
  | lteConst, lteConst => lte l r
  | lteConst, eqConst => lte l r
  | eqConst, ltConst => lt l r
  | eqConst, lteConst => lte l r
  | eqConst, eqConst => lte l r
  | _,_ => term.undef
| _,_ => term.undef

axiom sumUb : ∀ {t₁ t₂ : term}, thHolds t₁ → thHolds t₂ → thHolds (sumBounds t₁ t₂)

/-
======= Multiplication with positive factor
Children: none
Arguments: (m, (rel lhs rhs))
---------------------
Conclusion: (=> (and (> m 0) (rel lhs rhs)) (rel (* m lhs) (* m rhs)))
Where rel is a relation symbol.
-/

def multPosFactorAux (m : term) (t : term) : term :=
  match t with
  | f • t₁ • t₂ =>
    let ph₁ := gt m (val (value.integer 0) intSort)
    let ph₂ := and ph₁ t
    let ph₃ := mult m t₁
    let ph₄ := mult m t₂
    implies ph₂ (match f with
    | gtConst => gt ph₃ ph₄
    | gteConst => gte ph₃ ph₄
    | ltConst => lt ph₃ ph₄
    | lteConst => lte ph₃ ph₄
    | eqConst => eq ph₃ ph₄
    | _ => undef)
  | _ => undef

axiom multPosFactor : ∀ {t : term} (m : term),
  thHolds (multPosFactorAux m t)

def multNegFactorAux (m : term) (t : term) : term :=
  match t with
  | f • t₁ • t₂ =>
    let ph₁ := lt m (val (value.integer 0) intSort)
    let ph₂ := and ph₁ t
    let ph₃ := mult m t₁
    let ph₄ := mult m t₂
    implies ph₂ (match f with
    | gtConst => lt ph₃ ph₄
    | gteConst => lte ph₃ ph₄
    | ltConst => gt ph₃ ph₄
    | lteConst => gte ph₃ ph₄
    | eqConst => eq ph₃ ph₄
    | _ => undef)
  | _ => undef

axiom multNegFactor : ∀ {t : term} (m : term),
  thHolds (multNegFactorAux m t)


end arithRules
