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

axiom trueIntro : ∀ {t : Option term}, thHolds t → thHolds (mkEq t top)
axiom trueElim : ∀ {t : Option term}, thHolds (mkEq t top) → thHolds t

axiom falseIntro : ∀ {t : Option term}, thHolds (mkNot t) → thHolds (mkEq t bot)
axiom falseElim : ∀ {t : Option term}, thHolds (mkEq t bot) → thHolds (mkNot t)

axiom myrefl {t : term} : thHolds $ eq t t

axiom mysymm : ∀ {t₁ t₂ : term},
  thHolds (eq t₁ t₂) → thHolds (eq t₂ t₁)

axiom mynegSymm : ∀ {t₁ t₂ : term},
  thHolds (mkNot $ eq t₁ t₂) → thHolds (mkNot $ eq t₂ t₁)

axiom mytrans : ∀ {t₁ t₂ t₃ : term},
  thHolds (eq t₁ t₂) → thHolds (eq t₂ t₃) → thHolds (eq t₁ t₃)

axiom mycong : ∀ {f₁ t₁ : term} {f₂ t₂ : term},
  thHolds (eq f₁ f₂) → thHolds (eq t₁ t₂) →
        thHolds (eq (app f₁ t₁) (app f₂ t₂))

axiom mytrueIntro : ∀ {t : term}, thHolds t → thHolds (eq t top)
axiom mytrueElim : ∀ {t : term}, thHolds (eq t top) → thHolds t

axiom myfalseIntro : ∀ {t : term}, thHolds (mkNot t) → thHolds (eq t bot)
axiom myfalseElim : ∀ {t : term}, thHolds (eq t bot) → thHolds (mkNot t)


end eufRules
