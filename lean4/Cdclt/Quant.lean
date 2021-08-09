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

/- TODO
- need to have the ability to replace variable
- need to have rule take a substitution so that a I can guarantee that new var is valid
- need to operate in terms of a scope so that

--------------------------- scope
x₁ ≠ y₁ ∨ x₂ ≠ y₂ ∨ F ≃ F'
---------------------------- bind
∀x₁ (∀x₂ F) ≃ ∀y₁ (∀y₂ F')

can be simulated. The above is not safe depending on:
- y₁,y₂ maybe being captured or introducing free variables
- other assumptions in context mapping any of the variables to others
  so that capturing or escape happens

The way to address this is to have judgements take subs as in Barbosa
et al. CADE'17, so that no assumptions are put in place for variables
and they can only be replaced via this sub. The sub needs to be only
in terms of nats and at creation one would check the regular
properties.

-/
axiom bind : ∀ {v : Nat} {t₁ t₂ : term},
  thHolds (eq t₂ t₂) → thHolds (eq (qforall v t₁) (qforall v t₂))

axiom bindLambda : ∀ {v : Nat} {t₁ t₂ : term},
  thHolds (eq t₁ t₂) → thHolds (eq (lambda v t₁) (lambda v t₂))

end quantRules
