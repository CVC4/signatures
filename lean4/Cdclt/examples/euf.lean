import Cdclt.Euf

open proof
open proof.sort proof.term
open rules eufRules

def U := atom 50
def a₁ := const 100 U
def a₂ := const 101 U
def a₃ := const 102 U
def a₄ := const 103 U
def b₁ := const 104 U
def b₂ := const 105 U
def f₁ := const 106 (mkArrowN [U, U, U])
def f₂ := const 107 (mkArrowN [U, U, U])
def f₃ := const 108 (mkArrowN [U, U])

theorem binCong :
  thHolds (mkEq a₁ a₂) → thHolds (mkEq b₁ b₂) → (thHolds (mkEq (mkApp (mkApp f₁ a₁) b₁) (mkApp (mkApp f₁ a₂) b₂))) :=
λ s0 : thHolds (mkEq a₁ a₂) =>
λ s1 : thHolds (mkEq b₁ b₂) =>
have s2 : thHolds (mkEq f₁ f₁) from refl
show (thHolds (mkEq (mkApp (mkApp f₁ a₁) b₁) (mkApp (mkApp f₁ a₂) b₂))) from cong (cong s2 s0) s1

def a1a2 := mkEq a₁ a₂
def f3a1 := (mkApp f₃ a₁)
def f3a2 := (mkApp f₃ a₂)
def f3a1f3a2 := mkEq f3a1 f3a2
def nf3a1f3a2 := mkNot f3a1f3a2

theorem test1 : thHolds a1a2 → thHolds nf3a1f3a2 → holds [] :=
λ s0 : thHolds a1a2 =>
λ s1 : thHolds nf3a1f3a2 =>
have s2 : thHolds (mkEq f₃ f₃) from refl
have s3 : thHolds f3a1f3a2 from cong s2 s0
have s4 : holds [mkNot a1a2, f3a1f3a2] from clOr (scope s0 s3)
show holds [] from R0 (R0 (clAssume s0) s4 a1a2) (clAssume s1) f3a1f3a2
