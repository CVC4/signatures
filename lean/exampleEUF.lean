import euf

open proof
open proof.sort proof.term
open rules
open eufRules

def U := atom 0
def a₁ := const 0 U
def a₂ := const 1 U
def a₃ := const 2 U
def a₄ := const 3 U
def b₁ := const 4 U
def b₂ := const 5 U
def f₁ := const 6 (mkArrowN [U, U, U])
def f₂ := const 7 (mkArrowN [U, U, U])
def f₃ := const 8 (mkArrowN [U, U])

noncomputable theorem binCong :
  thHolds (mkEq a₁ a₂) → thHolds (mkEq b₁ b₂) → (thHolds (mkEq (mkApp (mkApp f₁ a₁) b₁) (mkApp (mkApp f₁ a₂) b₂))) :=
assume s0 : thHolds (mkEq a₁ a₂),
assume s1 : thHolds (mkEq b₁ b₂),
show (thHolds (mkEq (mkApp (mkApp f₁ a₁) b₁) (mkApp (mkApp f₃ a₂) b₂))), from congHO (cong f₁ s0) s1

noncomputable theorem rwCong :
  thHolds (mkEq a₁ a₂) → thHolds (mkEq (mkEq (mkApp f₃ a₁) b₁) (mkEq (mkApp f₃ a₂) b₁)) :=
assume s0 : thHolds (mkEq a₁ a₂),
have s1 : thHolds (mkEq (mkApp f₃ a₁) (mkApp f₃ a₂)), from (cong f₃ s0),
have s2 : thHolds (mkEq b₁ b₁), from refl,
show thHolds (mkEq (mkEq (mkApp f₃ a₁) b₁) (mkEq (mkApp f₃ a₂) b₁)), from congHO (cong (const eq_num dep) s1) s2

noncomputable theorem threeTrans :
  thHolds (mkEq a₁ a₂) → thHolds (mkEq a₂ a₃) → thHolds (mkEq a₃ a₄) → thHolds (mkEq a₁ a₄) :=
assume s0 : thHolds (mkEq a₁ a₂),
assume s1 : thHolds (mkEq a₂ a₃),
assume s2 : thHolds (mkEq a₃ a₄),
have s3 : thHolds (mkEq a₁ a₃), from trans s0 s1,
show thHolds (mkEq a₁ a₄), from trans s3 s2
