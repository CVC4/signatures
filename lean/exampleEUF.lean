import cdclt
import cdclt
import euf

open proof
open proof.sort proof.term
open rules

open eufRules

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

noncomputable theorem binCong :
  thHolds (mkEq a₁ a₂) → thHolds (mkEq b₁ b₂) → (thHolds (mkEq (mkApp (mkApp f₁ a₁) b₁) (mkApp (mkApp f₁ a₂) b₂))) :=
assume s0 : thHolds (mkEq a₁ a₂),
assume s1 : thHolds (mkEq b₁ b₂),
show (thHolds (mkEq (mkApp (mkApp f₁ a₁) b₁) (mkApp (mkApp f₁ a₂) b₂))), from congHO (cong f₁ s0) s1

-- constant c0 : thHolds (mkEq (mkApp f₃ a₁) (mkApp f₃ a₂))
-- #check c0
-- #check (const eq_num dep)
-- #check cong

-- #eval mkApp (const eq_num dep) (mkApp f₃ a₁)

-- constant c1 : (cong (const eq_num dep) c0)

-- noncomputable theorem rwCong :
--   thHolds (mkEq a₁ a₂) → thHolds (mkEq (mkEq (mkApp f₃ a₁) b₁) (mkEq (mkApp f₃ a₂) b₁)) :=
-- assume s0 : thHolds (mkEq a₁ a₂),
-- have s1 : thHolds (mkEq (mkApp f₃ a₁) (mkApp f₃ a₂)), from (cong f₃ s0),
-- have s2 : thHolds (mkEq b₁ b₁), from refl,
-- show thHolds (mkEq (mkEq (mkApp f₃ a₁) b₁) (mkEq (mkApp f₃ a₂) b₁)), from congHO (cong (const eq_num dep) s1) s2

noncomputable theorem threeTrans :
  thHolds (mkEq a₁ a₂) → thHolds (mkEq a₂ a₃) → thHolds (mkEq a₃ a₄) → thHolds (mkEq a₁ a₄) :=
assume s0 : thHolds (mkEq a₁ a₂),
assume s1 : thHolds (mkEq a₂ a₃),
assume s2 : thHolds (mkEq a₃ a₄),
show thHolds (mkEq a₁ a₄), from trans (trans s0 s1) s2

def a1a2 := mkEq a₁ a₂
def f3a1 := (mkApp f₃ a₁)
def f3a2 := (mkApp f₃ a₂)
def f3a1f3a2 := mkEq f3a1 f3a2
def nf3a1f3a2 := mkNot f3a1f3a2

noncomputable theorem test1 :
  thHolds a1a2 → thHolds nf3a1f3a2 → holds [] :=
assume s0 : thHolds a1a2,
assume s1 : thHolds nf3a1f3a2,
have s2 : thHolds f3a1f3a2, from cong f₃ s0,
have s3 : holds [mkNot a1a2, f3a1f3a2], from clOr (scope s0 s2),
show holds [], from R0 (R0 (clAssume s0) s3 a1a2) (clAssume s1) f3a1f3a2

def p := const 109 boolsort
def np := mkNot p

noncomputable theorem test2 :
  thHolds a1a2 → thHolds (mkOr np nf3a1f3a2) → thHolds p → holds [] :=
assume s0 : thHolds a1a2,
assume s1 : thHolds (mkOr np nf3a1f3a2),
assume s2 : thHolds p,
have s3 : holds [np, nf3a1f3a2], from clOr s1,
have s4 : thHolds f3a1f3a2, from cong f₃ s0,
have s5 : holds [mkNot a1a2, f3a1f3a2], from clOr (scope s0 s4),
show holds [], from R0 (R0 (clAssume s0) s5 a1a2) (R0 (clAssume s2) s3 p) f3a1f3a2

def b1b2 := mkEq b₁ b₂
def f1a1 := mkApp f₁ a₁
def f1a1b1 := mkApp f1a1 b₁
def f1a2 := mkApp f₁ a₂
def f1a2b2 := mkApp f1a2 b₂
def eqf1ab := mkEq f1a1b1 f1a2b2
def neqf1ab := mkNot eqf1ab

noncomputable theorem test3 :
  thHolds a1a2 → thHolds b1b2 → thHolds neqf1ab  → holds [] :=
assume s0 : thHolds a1a2,
assume s1 : thHolds b1b2,
assume s2 : thHolds neqf1ab,
have s3 : thHolds eqf1ab, from congHO (cong f₁ s0) s1,
have s4 : holds [mkNot a1a2, mkNot b1b2, eqf1ab], from clOr (scope s0 (scope s1 s3)),
show holds [], from R0 (R0 (clAssume s1) (R0 (clAssume s0) s4 a1a2) b1b2) (clAssume s2) eqf1ab
