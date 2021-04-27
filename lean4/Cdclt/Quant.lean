import Cdclt.Boolean

open proof
open proof.sort proof.term
open rules

namespace quantRules

def substitute (v : Nat) (t : term) : term → OptionM term
-- replace each term in application
| f • t₁ => substitute v t f >>= λ fs =>
            substitute v t t₁ >>= λ t₁s => fs • t₁s
-- if found variable, replace by instantiation term *if types match*,
-- otherwise fail
| body@(const v' s) => if v ≠ v' then body
                else
                  s >>= λ s' =>
                  sortOf t >>= λ st =>
                  if s' = st then t else none
-- if finds shadowing, break
| qforall v' body' => if v = v' then none
                      else mkForall v' (substitute v t body')
-- otherwise no change
| body => body

axiom instForall : ∀ {v : Nat} {body : term} (t : term),
  thHolds (qforall v body) → thHolds (substitute v t body)

end quantRules
