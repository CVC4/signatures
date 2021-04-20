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

/-
(SCOPE |:conclusion| (not (and (= a b) (or (not p3) (not (= (f a) (f b)))) p1 (or (not p1) (and p2 p3))))
  (EQ_RESOLVE |:conclusion| false
    (CHAIN_RESOLUTION |:conclusion| (not (= (f a) (f b)))
      (ASSUME |:conclusion| (or (not p3) (not (= (f a) (f b)))) |:args| ((or (not p3) (not (= (f a) (f b))))))
      (AND_ELIM |:conclusion| p3
        (CHAIN_RESOLUTION |:conclusion| (and p2 p3)
          (ASSUME |:conclusion| (or (not p1) (and p2 p3)) |:args| ((or (not p1) (and p2 p3))))
          (ASSUME |:conclusion| p1 |:args| (p1)) |:args| (false p1))
        |:args| (1))
      |:args| (false p3))
    (TRANS |:conclusion| (= (not (= (f a) (f b))) false)
      (CONG |:conclusion| (= (not (= (f a) (f b))) (not (= (f b) (f b))))
        (CONG |:conclusion| (= (= (f a) (f b)) (= (f b) (f b)))
          (CONG |:conclusion| (= (f a) (f b))
            (ASSUME |:conclusion| (= a b) |:args| ((= a b))) |:args| (23 f))
          (REFL |:conclusion| (= (f b) (f b)) |:args| ((f b))) |:args| (6))
        |:args| (17))
      (TRANS |:conclusion| (= (not (= (f b) (f b))) false)
        (CONG |:conclusion| (= (not (= (f b) (f b))) (not true))
          (THEORY_REWRITE |:conclusion| (= (= (f b) (f b)) true) |:args| ((= (= (f b) (f b)) true) 2 5))
          |:args| (17))
        (THEORY_REWRITE |:conclusion| (= (not true) false) |:args| ((= (not true) false) 1 6)))))
  |:args| ((= a b) (or (not p3) (not (= (f a) (f b)))) p1 (or (not p1) (and p2 p3))))
-/

def a := const 1000 U
def b := const 1001 U
def p₁ := const 1002 boolSort
def p₂ := const 1003 boolSort
def p₃ := const 1004 boolSort
def f := const 1005 (mkArrowN [U, U])
def fa := mkApp f a
def fb := mkApp f b

def eqab := mkEq a b
def eqfafb := mkEq fa fb
def eqfbfb := mkEq fb fb
def eqfbfbtop := mkEq eqfbfb top
def neqfbfb := mkNot eqfbfb
def eqneqfbfbbot := mkEq neqfbfb bot
def eqeqfafbeqfbfb := mkEq eqfafb eqfbfb
def eqneqfafbneqfbfb := mkEq (mkNot eqfafb) (mkNot eqfbfb)
def neqfafb := mkNot eqfafb
def eqneqfafbbot := mkEq neqfafb bot
def np₁ := mkNot p₁
def np₃ := mkNot p₃
def andp₂p₃ := mkAnd p₂ p₃
def ornp₁andp₂p₃ := mkOr np₁ andp₂p₃
def ornp₃neqfafb := mkOr np₃ neqfafb

theorem simpleCongRw :
  thHolds eqab → thHolds ornp₃neqfafb → thHolds p₁ → thHolds ornp₁andp₂p₃ → thHolds bot :=
λ s0 : thHolds eqab =>
λ s1 : thHolds ornp₃neqfafb =>
λ s2 : thHolds p₁ =>
λ s3 : thHolds ornp₁andp₂p₃ =>

have s4 : thHolds andp₂p₃ from thAssume (R1 (clOr s3) (clAssume s2) p₁)
have s5 : thHolds p₃ from andElim s4 1
have s6 : thHolds neqfafb from thAssume (R1 (clOr s1) (clAssume s5) p₃)

have s7 : thHolds eqfafb from cong refl s0
have s8 : thHolds eqeqfafbeqfbfb from cong (cong (@refl eqConst) s7) (@refl fb)
have s9 : thHolds eqneqfafbneqfbfb from cong (@refl notConst) s8
have s10 : thHolds (mkEq (mkNot top) bot) from thTrustValid
have s11 : thHolds eqfbfbtop from thTrustValid
have s12 : thHolds ((mkEq neqfbfb) (mkNot top)) from cong (@refl notConst) s11
have s13 : thHolds (mkEq neqfbfb bot) from trans s12 s10
have s14 : thHolds eqneqfafbbot from trans s9 s13

show thHolds bot from eqResolve s6 s14

/-
(SCOPE |:conclusion| (not (and (= a b) (or (not p3) (not (= (f a) (f b)))) p1 (or (not p1) (and p2 p3))))
  (CHAIN_RESOLUTION |:conclusion| false
    (REORDERING |:conclusion| (or (= (f a) (f b)) (not (= a b)))
      (IMPLIES_ELIM |:conclusion| (or (not (= a b)) (= (f a) (f b)))
        (SCOPE |:conclusion| (=> (= a b) (= (f a) (f b)))
          (CONG |:conclusion| (= (f a) (f b))
            (SYMM |:conclusion| (= a b)
              (SYMM |:conclusion| (= b a)
                (ASSUME |:conclusion| (= a b) |:args| ((= a b))))) |:args| (23 f))
          |:args| ((= a b))))
      |:args| ((or (= (f a) (f b)) (not (= a b)))))
    (CHAIN_RESOLUTION |:conclusion| (not (= (f a) (f b)))
      (ASSUME |:conclusion| (or (not p3) (not (= (f a) (f b)))) |:args| ((or (not p3) (not (= (f a) (f b))))))
      (CHAIN_RESOLUTION |:conclusion| p3
        (REORDERING |:conclusion| (or p3 (not (and p2 p3)))
          (CNF_AND_POS |:conclusion| (or (not (and p2 p3)) p3) |:args| ((and p2 p3) 1)) |:args| ((or p3 (not (and p2 p3)))))
        (CHAIN_RESOLUTION |:conclusion| (and p2 p3)
          (ASSUME |:conclusion| (or (not p1) (and p2 p3)) |:args| ((or (not p1) (and p2 p3))))
          (ASSUME |:conclusion| p1 |:args| (p1)) |:args| (false p1))
        |:args| (false (and p2 p3)))
      |:args| (false p3))
    (ASSUME |:conclusion| (= a b) |:args| ((= a b)))
    |:args| (true (= (f a) (f b)) false (= a b)))
  |:args| ((= a b) (or (not p3) (not (= (f a) (f b)))) p1 (or (not p1) (and p2 p3))))
-/

theorem simpleCong :
  thHolds eqab → thHolds ornp₃neqfafb → thHolds p₁ → thHolds ornp₁andp₂p₃ → holds [] :=
fun a0 : thHolds eqab =>
fun a1 : thHolds ornp₃neqfafb =>
fun a2 : thHolds p₁ =>
fun a3 : thHolds ornp₁andp₂p₃ =>

have s0 : holds [mkNot eqab, eqfafb] from (
  fun a0 : thHolds eqab =>
  have s0 : thHolds (mkEq b a) from symm a0
  have s1 : thHolds eqab from symm s0
  have s2 : thHolds eqfafb from cong (@refl f) s1
  show holds [mkNot eqab, eqfafb] from clOr (scope a0 s2)
  ) a0
have s1 : holds [eqfafb, mkNot eqab] from reorder [1,0] s0

have s2 : holds [andp₂p₃] from R1 (clOr a3) (clAssume a2) p₁
have s3 : holds [mkNot andp₂p₃, p₃] from @cnfAndPos [p₂, p₃] 1
have s4 : holds [p₃, mkNot andp₂p₃] from reorder [1,0] s3
have s5 : holds [p₃] from R1 s4 s2 andp₂p₃
have s6 : holds [neqfafb] from R1 (clOr a1) s5 p₃

show holds [] from R1 s6 (R0 (clAssume a0) s1 eqab) eqfafb
