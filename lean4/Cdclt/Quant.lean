import Cdclt.Boolean

open proof
open proof.sort proof.term
open rules

namespace quantRules

def t := val (value.bitvec [true, false])

def substitute (body : term) (v : Nat) (t : term) : Option term :=
  match body with
  -- replace each term in application
  | f • t₁ => substitute f v t >>= λ fs =>
              substitute t₁ v t >>= λ t₁s => fs • t₁s
  -- if found variable, replace by instantiation term *if types match*,
  -- otherwise fail
  | const v' s => if v ≠ v' then body
                  else
                    s >>= λ s' =>
                    sortOf t >>= λ st =>
                    if s' = st then t else none
  -- if finds shadowing, break
  | qforall v' body' => if v = v' then none
                        else mkForall v' (substitute body' v t)
  -- otherwise no change
  | _ => body

axiom instForall : ∀ {v : Nat} {body : term} (t : term),
  thHolds (qforall v body) → thHolds (substitute body v t)

end quantRules
