import term
import cdclt

open rules
open proof
open proof.sort proof.term

#eval monad.join (some (some 1))
#eval mynth [top, bot, const 20 boolsort, const 21 boolsort] 0
#eval list.nth [top, bot, const 20 boolsort, const 21 boolsort] 0
#eval get_last [top, bot, const 20 boolsort, const 21 boolsort]

#check (λ (p₀ : holds [const 20 boolsort])
          (p₁ : holds [mkNot (const 20 boolsort)]),
         (R0 p₀ p₁ (const 20 boolsort) : holds []))
#check (λ (p₀ : holds [const 20 boolsort])
          (p₁ : holds [mkNot (const 20 boolsort)]),
         (R0 p₀ p₁ (const 20 boolsort))
  : holds [const 20 boolsort] → holds [mkNot (const 20 boolsort)] → holds [])
def l1 := some (const 20 boolsort)
def l2 := some (const 21 boolsort)
constant c₁ : holds [l1, l2]
constant c₂ : holds [mkNot l1, l2]

#check rules.R0 c₁ c₂ l1

def s := boolsort
def f := const 50 (arrow s s)
def x₁ := const 51 s
def x₂ := const 52 s


noncomputable lemma lem : holds [mkIneq x₁ x₂, mkEq (mkApp f x₁) (mkApp f x₂)] :=
  let s₀ := @smtcong f x₁ f x₂ in
  let s₁ := @smtrefl f in
   R0 s₁ s₀ (mkEq f f)

noncomputable theorem test_theorem (s₀ : holds [mkEq x₁ x₂]) (s₁ : holds [mkIneq (mkApp f x₁) (mkApp f x₂)]) : holds [] :=
 have s₂ : holds [mkEq (mkApp f x₁) (mkApp f x₂)], from R0 s₀ lem (mkEq x₁ x₂),
   R0 s₂ s₁ (mkEq (mkApp f x₁) (mkApp f x₂))

-- does not go through
--noncomputable lemma wrong :
--  holds ([mkIneq x₁ x₂, mkIneq f x₂, mkEq (mkApp f x₂) (mkApp f x₂)]) :=
--    @smtcong f f a b



def u1 := atom 1
def u2 := atom 2
def x := (const 60 u1)
def f1 := const 61 (arrow u1 u1)
def t1  := const 62 u1
def t2 := const 63 u2
def p1 := const 64 (arrow u1 boolsort)

def myquant := qforall 60 (f1 • x) -- this binds the variable
def myquant2 := qforall 60 x -- this binds the variable

noncomputable lemma testInst : holds [mkNot myquant, f1 • t1] :=
  inst_forall t1

-- does not go through since t2 has different type from x
-- noncomputable lemma testInst2 : holds [mkNot myquant2, t2] :=
--   inst_forall t2
