import Cdclt.Boolean

open proof
open proof.sort proof.term
open rules

namespace eufRules

axiom refl {t : term} : thHolds $ eq t t

axiom symm : ∀ {t₁ t₂ : term},
  thHolds (eq t₁ t₂) → thHolds (eq t₂ t₁)

axiom negSymm : ∀ {t₁ t₂ : term},
  thHolds (not $ eq t₁ t₂) → thHolds (not $ eq t₂ t₁)

axiom trans : ∀ {t₁ t₂ t₃ : term},
  thHolds (eq t₁ t₂) → thHolds (eq t₂ t₃) → thHolds (eq t₁ t₃)

axiom cong : ∀ {f₁ t₁ : term} {f₂ t₂ : term},
  thHolds (eq f₁ f₂) → thHolds (eq t₁ t₂) →
        thHolds (eq (app f₁ t₁) (app f₂ t₂))

axiom trueIntro : ∀ {t : term}, thHolds t → thHolds (eq t top)
axiom trueElim : ∀ {t : term}, thHolds (eq t top) → thHolds t

axiom falseIntro : ∀ {t : term}, thHolds (not t) → thHolds (eq t bot)
axiom falseElim : ∀ {t : term}, thHolds (eq t bot) → thHolds (not t)

end eufRules
