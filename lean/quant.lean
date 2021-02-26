import cdclt

open proof
open proof.sort proof.term
open rules

namespace quantRules

/-*************** instantiation ***************-/

def substitute : ℕ → term → term → option term
-- Constant case
| n (val _ s) t := t

-- if finds shadowing, break
| n₁ (qforall n₂ body) t :=
   if n₁ = n₂ then option.none else
                               do res ← (substitute n₁ body t), (qforall n₂ res)
-- if found variable, replace by instantiation term *if types match*,
-- otherwise fail
| n₁ (const n₂ os) t :=
  do s ← os, st ← sortof t,
    if n₁ ≠ n₂ then (const n₂ s) else if s = st then t else option.none
-- replace each term in application
| n (f • t₁) t :=
  do fs ← (substitute n f t), t₁s ← (substitute n t₁ t), fs • t₁s

constant instForall : Π {v : ℕ} {body : term} (term : term),
  thHolds (qforall v body) → thHolds (substitute v body term)


end quantRules
