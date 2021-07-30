import Cdclt.Boolean

open proof
open proof.sort proof.term
open rules

namespace arrayRules

axiom readOverWrite : ∀ {a e i₁ i₂ : term},
  thHolds (not (eq i₁ i₂)) →
    thHolds (eq (select (store a i₁ e) i₂) (select a i₂))

axiom readOverWriteContra : ∀ {a e i₁ i₂ : term},
  thHolds (not (eq (select (store a i₂ e) i₁) (select a i₁))) →
    thHolds (eq i₁ i₂)

axiom readOverWriteIdentity : ∀ {a e i : term},
  thHolds (eq (select (store a i e) i) e)

axiom arrayExt : ∀ {a₁ a₂ : term},
  thHolds (not (eq a₁ a₂)) → (x : Nat) → (s : sort) →
    let c := const x s
    let k := (choice x (implies (not (eq a₁ a₂))
                                (not (eq (select a₁ c) (select a₂ c)))))
    thHolds (not (eq (select a₁ k) (select a₂ k)))

end arrayRules
