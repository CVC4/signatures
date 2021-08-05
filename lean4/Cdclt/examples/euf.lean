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
def f₁ := const 106 (arrowN [U, U, U])
def f₂ := const 107 (arrowN [U, U, U])
def f₃ := const 108 (arrowN [U, U])

theorem binCong :
  thHolds (eq a₁ a₂) → thHolds (eq b₁ b₂) → (thHolds (eq (app (app f₁ a₁) b₁) (app (app f₁ a₂) b₂))) :=
fun s0 : thHolds (eq a₁ a₂) =>
fun s1 : thHolds (eq b₁ b₂) =>
  have s2 : thHolds (eq f₁ f₁) := refl
  show (thHolds (eq (app (app f₁ a₁) b₁) (app (app f₁ a₂) b₂))) from cong (cong s2 s0) s1

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
def f := const 1005 (arrowN [U, U])
def fa := app f a
def fb := app f b

def eqab := eq a b
def eqfafb := eq fa fb
def eqfbfb := eq fb fb
def eqfbfbtop := eq eqfbfb top
def neqfbfb := not eqfbfb
def eqneqfbfbbot := eq neqfbfb bot
def eqeqfafbeqfbfb := eq eqfafb eqfbfb
def eqneqfafbneqfbfb := eq (not eqfafb) (not eqfbfb)
def neqfafb := not eqfafb
def eqneqfafbbot := eq neqfafb bot
def np₁ := not p₁
def np₃ := not p₃
def andp₂p₃ := and p₂ p₃
def ornp₁andp₂p₃ := or np₁ andp₂p₃
def ornp₃neqfafb := or np₃ neqfafb

theorem simpleCongRw :
  thHolds eqab → thHolds ornp₃neqfafb → thHolds p₁ → thHolds ornp₁andp₂p₃ → thHolds bot :=
λ s0 : thHolds eqab =>
λ s1 : thHolds ornp₃neqfafb =>
λ s2 : thHolds p₁ =>
λ s3 : thHolds ornp₁andp₂p₃ =>
have s4 : thHolds andp₂p₃ := thAssume (R1 (clOr s3) (clAssume s2) p₁)
have s5 : thHolds p₃ := andElim s4 1
have s6 : thHolds neqfafb := thAssume (R1 (clOr s1) (clAssume s5) p₃)

have s7 : thHolds eqfafb := cong refl s0
let s8_1 := @refl eqConst
let s8_2 := (cong s8_1 s7)
have s8 : thHolds eqeqfafbeqfbfb := cong s8_2 (@refl fb)
have s9 : thHolds eqneqfafbneqfbfb := cong (@refl notConst) s8
have s10 : thHolds (eq (not top) bot) := thTrustValid
have s11 : thHolds eqfbfbtop := thTrustValid
have s12 : thHolds ((eq neqfbfb) (not top)) := cong (@refl notConst) s11
have s13 : thHolds (eq neqfbfb bot) := trans s12 s10
have s14 : thHolds eqneqfafbbot := trans s9 s13
show thHolds bot from eqResolve s6 s14

/-
(SCOPE |:conclusion| (not (and (= a b) (and p1 true) (or (not p1) (and p2 p3)) (or (not p3) (not (= (f a) (f b))))))
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
          (EQ_RESOLVE |:conclusion| p1
            (ASSUME |:conclusion| (and p1 true) |:args| ((and p1 true)))
            (THEORY_REWRITE |:conclusion| (= (and p1 true) p1) |:args| ((= (and p1 true) p1) 1 5)))
          |:args| (false p1))
        |:args| (false (and p2 p3)))
      |:args| (false p3))
    (ASSUME |:conclusion| (= a b) |:args| ((= a b))) |:args| (true (= (f a) (f b)) false (= a b)))
  |:args| ((= a b) (and p1 true) (or (not p1) (and p2 p3)) (or (not p3) (not (= (f a) (f b))))))
-/

def andp₁t := and p₁ (val (value.bool true) boolSort)

theorem simpleCong :
 thHolds eqab → thHolds andp₁t → thHolds ornp₃neqfafb → thHolds p₁ → thHolds ornp₁andp₂p₃ → holds [] :=
fun a0 : thHolds eqab =>
fun a1 : thHolds andp₁t =>
fun a2 : thHolds ornp₃neqfafb =>
fun a3 : thHolds p₁ =>
fun a4 : thHolds ornp₁andp₂p₃ =>
have s0 : thHolds (or (not eqab) eqfafb) :=
 (scope (fun a0 : thHolds eqab =>
   have s0 : thHolds (eq b a) := symm a0
   have s1 : thHolds eqab := symm s0
   have s2 :thHolds eqfafb := cong (@refl f) s1
   show thHolds eqfafb from s2
 ))
have s00 : holds [not eqab, eqfafb] := clOr (impliesElim (liftNOrToImp s0 1 eqfafb))
have s1 : holds [eqfafb, not eqab] := reorder s00 [1,0]

have s2 : holds [andp₂p₃] := R1 (clOr a4) (clAssume a3) p₁
have s3 : holds ([(not (andN [p₂, p₃])), p₃]) := @cnfAndPos ([p₂, p₃]) 1
have s4 : holds [p₃, not andp₂p₃] := reorder s3 [1,0]

have s5 : thHolds (eq andp₁t p₁) := thTrustValid
have s6 : thHolds p₁ := eqResolve a1 s5
have s7 : holds [andp₂p₃] := R1 (clOr a4) (clAssume s6) p₁
have s8 : holds [p₃] := R1 s4 s7 andp₂p₃

have s9 : holds [neqfafb] := R1 (clOr a2) s8 p₃

show holds [] from R1 (R0 s1 s9 eqfafb) (clOr a0) eqab
