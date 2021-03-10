import cdclt

open proof
open proof.sort proof.term
open rules

namespace eufRules

/------------------ congruence ------------------/

/-
            t₁ = t₂      t₁ ≠ t₂   
-----refl   -------symm  -------negSymm
t = t       t₂ = t₁      t₂ ≠ t₁

t₁ = t₂  t₂ = t₃          t₁ = t₂
----------------trans   -----------cong
       t₁ = t₃          f t₁ = f t₂

f₁ = f₂  t₁ = t₂
-----------------congHO
  f₁ t₁ = f₂ t₂ 
-/
constant refl {t : option term} : thHolds $ mkEq t t

constant symm : Π {t₁ t₂ : option term},
  thHolds (mkEq t₁ t₂) → thHolds (mkEq t₂ t₁)

constant negSymm : Π {t₁ t₂ : option term},
  thHolds (mkIneq t₁ t₂) → thHolds (mkIneq t₂ t₁)

constant trans : Π {t₁ t₂ t₃ : option term},
  thHolds (mkEq t₁ t₂) → thHolds (mkEq t₂ t₃) → thHolds (mkEq t₁ t₃)

constant cong : Π {t₁ t₂ : option term} (f : term),
  thHolds (mkEq t₁ t₂) → thHolds (mkEq (mkApp f t₁) (mkApp f t₂))

constant congHO : Π {f₁ t₁ : option term} {f₂ t₂ : option term},
  thHolds (mkEq f₁ f₂) → thHolds (mkEq t₁ t₂) →
        thHolds (mkEq (mkApp f₁ t₁) (mkApp f₂ t₂))

end eufRules
