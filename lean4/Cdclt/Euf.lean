import Cdclt.Boolean

open proof
open proof.sort proof.term
open rules

namespace eufRules

axiom refl {t : Option term} : thHolds $ mkEq t t

axiom symm : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq t₁ t₂) → thHolds (mkEq t₂ t₁)

axiom negSymm : ∀ {t₁ t₂ : Option term},
  thHolds (mkNot $ mkEq t₁ t₂) → thHolds (mkNot $ mkEq t₂ t₁)

axiom trans : ∀ {t₁ t₂ t₃ : Option term},
  thHolds (mkEq t₁ t₂) → thHolds (mkEq t₂ t₃) → thHolds (mkEq t₁ t₃)

axiom cong : ∀ {f₁ t₁ : Option term} {f₂ t₂ : Option term},
  thHolds (mkEq f₁ f₂) → thHolds (mkEq t₁ t₂) →
        thHolds (mkEq (mkApp f₁ t₁) (mkApp f₂ t₂))

end eufRules
