import term
import cdclt

open rules
open proof
open proof.sort proof.term

#eval monad.join (some (some 1))
#eval nTh [top, bot, const 20 boolsort, const 21 boolsort] 0
#eval list.nth [top, bot, const 20 boolsort, const 21 boolsort] 0
#eval getLast [top, bot, const 20 boolsort, const 21 boolsort]

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

-- does not go through
--noncomputable lemma wrong :
--  holds ([mkUneq x₁ x₂, mkUneq f x₂, mkEq (mkApp f x₂) (mkApp f x₂)]) :=
--    @smtcong f f a b
