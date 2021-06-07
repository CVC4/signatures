import Cdclt.Boolean

open proof
open proof.sort proof.term
open rules

namespace quantRules

def substitute (v : Nat) (t : term) : term → term
-- replace each term in application
| f • t₁ => let fs := substitute v t f
            let t₁s := substitute v t t₁
            fs • t₁s
-- if found variable, replace by instantiation term *if types match*,
-- otherwise fail
| body@(const v' s) => if v ≠ v' then body else t
-- if finds shadowing, break
| qforall v' body' => if v = v' then term.undef
                      else mkForall v' (substitute v t body')
-- otherwise no change
| body => body

axiom instForall : ∀ {v : Nat} {body : term} (t : term),
  thHolds (qforall v body) → thHolds (substitute v t body)

end quantRules
