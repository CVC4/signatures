import Cdclt.Boolean

open proof
open proof.sort proof.Term
open rules

namespace quantRules
#check Repr
def substitute (v : Name) (t : Term) : Term → Option Term
-- replace each Term in application
| f • t₁ => substitute v t f >>= λ fs =>
            substitute v t t₁ >>= λ t₁s => fs • t₁s
-- if found variable, replace by instantiation Term *if types match*,
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

axiom instForall : ∀ {v : Name} {body : Term} (t : Term),
  thHolds (qforall v body) → thHolds (substitute v t body)

end quantRules
