import term

open proof
open proof.sort proof.term

namespace rules
-- define calculus
notation `clause` := list (option term)

-- clause manipulation rules
def nTh : clause → ℕ → option term := comp2 monad.join (@list.nth (option term))
def getLast : clause → option term := λ c, nTh c (c.length - 1)
def concatCl : clause → clause → clause := @list.append (option term)
def removeDuplicates : clause → clause
| [] := []
| (h::t) := if h ∈ t then removeDuplicates t else h::(removeDuplicates t)


-- eventually should give Prop
constant holds : clause → Type
constant thHolds : option term → Type


-- collect all terms in OR chain (right-associative)
def reduceOrAux : term → clause
| ((const orNum _) • t₀ • ((const orNum _) • t₁ • t₂))
          := t₀::t₁::(reduceOrAux t₂)
| ((const orNum _) • t₀ • t₁) := [t₀, t₁]
| t                            := [t]
def reduceOr : option term → clause
| (some t) := reduceOrAux t
| none     := [none]
#eval reduceOr (mkOrN [top, bot, and top bot, bot])

-- clausal reasoning
def resolveR₀ (n : option term) (c₁ c₂: clause) : clause :=
  concatCl (remove n c₁) (remove (mkNot n) c₂)

def resolveR₁ (n : option term) (c₁ c₂: clause) : clause :=
  concatCl (remove (mkNot n) c₁) (remove n c₂)

constant R0 : Π {c₁ c₂ : clause}
  (p₁ : holds c₁) (p₂ : holds c₂) (n : option term),
  holds (resolveR₀ n c₁ c₂)

constant R1 : Π {c₁ c₂ : clause}
  (p₁ : holds c₁) (p₂ : holds c₂) (n : term),
  holds (resolveR₁ n c₁ c₂)

constant factoring : Π {c : clause} (p : holds c),
  holds (removeDuplicates c)


-- connecting theory reasoning and clausal reasoning

constant clAssume : Π {t : option term}, thHolds t → holds [t]

constant clOr : Π {t : option term} (p : thHolds t), holds (reduceOr t)

constant scope : Π {t₁ t₂ : option term}
  (p₁ : thHolds t₁) (p₂ : thHolds t₂), thHolds (mkOr (mkNot t₁) t₂)


/-------------------- Holes ----------------------------------/

constant trust : Π {c₁ : clause} (p : holds c₁) {c₂ : clause},
  holds c₂

constant thTrust : Π {t₁ t₂ : option term}, thHolds t₁ → thHolds t₂


/-------------------- Boolean rules ---------------/

constant split {t : option term} : holds [t, mkNot t]

constant eqResolve : Π {t₁ t₂ : option term},
  thHolds t₁ → thHolds (mkEq t₁ t₂) → thHolds t₂

constant modusPonens : Π {t₁ t₂ : option term},
  thHolds t₁ → thHolds (mkImplies t₁ t₂) → thHolds t₂

constant notNotElim : Π {t : option term}, thHolds (mkNot $ mkNot t) → thHolds t

constant contradiction : Π {t : option term},
  thHolds t → thHolds (mkNot t) → holds []

/- reduceAndNth and reduceOrNth were broken when
   we started using ℕ instead of pos_num in term.lean -/
-- get n-th element in AND chain (right-associative)
def reduceAndNth : ℕ → term → option term
| 0            (and t _)           := t
| 1            (and _ t)           := t
| (n+1) (and  _ (and t₀ t₁)) :=  reduceAndNth n (and t₀ t₁)
| _            _                   := none

def reduceAnd (n : ℕ) : option term → option term :=
  λ t, do t' ← t, reduceAndNth n t'

constant andElim : Π {t : option term} (p : thHolds t) (n : ℕ),
  thHolds (reduceAnd n t)

constant andIntro : Π {t₁ t₂ : option term},
  thHolds t₁ → thHolds t₂ → thHolds (mkAnd t₁ t₂)

-- get n-th in NOT-OR chain (right-associative)
def reduceOrNth : ℕ → term → option term
| 0            (or t _)          := t
| 1            (or _ t)          := t
| (n+1) (or _ (or t₀ t₁))        := reduceOrNth n (or t₀ t₁)
| _            _                 := none

def reduceNotOr (n : ℕ) : option term → option term :=
  λ t, do t' ← t,
    match t' with
    | not t'' := mkNot $ reduceOrNth n t''
    | _       := none
    end

constant notOrElim : Π {t : option term} (p : thHolds t) (n : ℕ),
  thHolds (reduceNotOr n t)

constant impliesElim : Π {t₁ t₂ : option term},
  thHolds (mkImplies t₁ t₂) → holds [mkNot t₁, t₂]

constant notImplies1 : Π {t₁ t₂ : option term},
  thHolds (mkNot $ mkImplies t₁ t₂) → thHolds t₁
constant notImplies2 : Π {t₁ t₂ : option term},
  thHolds (mkNot $ mkImplies t₁ t₂) → thHolds (mkNot t₁)

constant equivElim1 : Π {t₁ t₂}, thHolds (mkEq t₁ t₂) → holds [mkNot t₁, t₂]
constant equivElim2 : Π {t₁ t₂}, thHolds (mkEq t₁ t₂) → holds [t₁, mkNot t₂]

constant notEquivElim1 : Π {t₁ t₂}, thHolds (mkNot $ mkEq t₁ t₂) → holds [t₁, t₂]
constant notEquivElim2 : Π {t₁ t₂},
  thHolds (mkNot $ mkEq t₁ t₂) → holds [mkNot t₁, mkNot t₂]

constant xorElim1 : Π {t₁ t₂ : option term},
  thHolds (mkXor t₁ t₂) → holds [t₁, t₂]
constant xorElim2 : Π {t₁ t₂ : option term},
  thHolds (mkXor t₁ t₂) → holds [mkNot t₁, mkNot t₂]

constant notXorElim1 : Π {t₁ t₂ : option term},
  thHolds (mkNot $ mkXor t₁ t₂) → holds [t₁, mkNot t₂]
constant notXorElim2 : Π {t₁ t₂ : option term},
  thHolds (mkNot $ mkXor t₁ t₂) → holds [mkNot t₁, t₂]

constant iteElim1 : Π {c t₁ t₂ : option term}, thHolds (mkIte c t₁ t₂) →
  holds [mkNot c, t₁]
constant iteElim2 : Π {c t₁ t₂ : option term}, thHolds (mkIte c t₁ t₂) →
  holds [c, t₂]

constant notIteElim1 : Π {c t₁ t₂ : option term},
  thHolds (mkNot $ mkIte c t₁ t₂) → holds [mkNot c, mkNot t₁]
constant notIteElim2 : Π {c t₁ t₂ : option term},
  thHolds (mkNot $ mkIte c t₁ t₂) → holds [c, mkNot t₂]

def reduceNotAndAux : term → clause
| ((const andNum _) • t₀ • ((const andNum _) • t₁ • t₂))
          := mkNot t₀::mkNot t₁::(reduceNotAndAux t₂)
| ((const andNum _) • t₀ • t₁) := [mkNot t₀, mkNot t₁]
| t                            := [t]
def reduceNotAnd : option term → clause
| (some t) := reduceNotAndAux t
| none     := [none]
constant notAnd : Π {t : option term} (p : thHolds t), holds (reduceNotAnd t)

/-------------------- CNF rules (introduce valid clauses) ---------------/

def mkNotList : clause → clause
| [] := []
| (h::t) := mkNot h :: mkNotList t

/-
l₁ ∧ ... ∧ lₖ     1 ≤ n ≤ k             ¬(x₁ ∧ ... ∧ xₙ)
----------------------------cnfAndPos   ----------------cnfAndNeg
             lᵢ                          ¬x₁ ∨ ... ∨ ¬xₙ 
-/
constant cnfAndPos {l : clause} {n : ℕ} : holds [mkNot $ mkAndN l, nTh l n]
constant cnfAndNeg {l : clause} : holds $ mkAndN l :: mkNotList l

/-
x₁ ∨ ... ∨ xₙ           ¬(l₁ ∨ ... ∨ lₖ)     1 ≤ n ≤ k 
-------------cnfOrPos   ------------------------------cnfOrNeg
x₁ ∨ ... ∨ xₙ                         ¬lᵢ
-/
constant cnfOrPos {l : clause} : holds $ (mkNot $ mkOrN l) :: l
constant cnfOrNeg {l : clause} {n : ℕ} : holds [mkOrN l, mkNot $ nTh l n]

/-
t₁ → t₂  t₁                 ¬(t₁ → t₂)                ¬(t₁ → t₂)
-----------cnfImpliesPos    ----------cnfImpliesNeg1  ----------cnfImpliesNeg2
     t₂                         t₁                        ¬t₂
-/
constant cnfImpliesPos {t₁ t₂ : option term} :
  holds [mkNot $ mkImplies t₁ t₂, mkNot t₁, t₂]
constant cnfImpliesNeg1 {t₁ t₂ : option term} : 
holds [mkImplies t₁ t₂, t₁]
constant cnfImpliesNeg2 {t₁ t₂ : option term} :
  holds [mkImplies t₁ t₂, mkNot t₂]

/-
t₁ = t₂  ¬t₁              t₁ = t₂  t₁
------------cnfEquivPos1  ------------cnfEquivPos2
    ¬t₂                        t₂
-/
constant cnfEquivPos1 {t₁ t₂ : option term} :
  holds [mkNot $ mkEq t₁ t₂, t₁, mkNot t₂]
constant cnEquivPos2 {t₁ t₂ : option term} :
  holds [mkNot $ mkEq t₁ t₂, mkNot t₁, t₂]

/-
¬(t₁ = t₂)  t₁              ¬(t₁ = t₂)  ¬t₁
--------------cnfEquivNeg1  --------------cnfEquivPos2
      ¬t₂                         t₂
-/
constant cnfEquivNeg1 {t₁ t₂ : option term} :
  holds [mkEq t₁ t₂, mkNot t₁, mkNot t₂]
constant cnfEquivNeg2 {t₁ t₂ : option term} : 
  holds [mkEq t₁ t₂, t₁, t₂]

/-
t₁ ⊕ t₂  ¬t₁              t₁ ⊕ t₂  t₁
------------cnfXorPos1    -----------cnfXorPos2
     t₂                        ¬t₂
-/
constant cnfXorPos1 {t₁ t₂ : option term} : 
  holds [mkNot $ mkXor t₁ t₂, t₁, t₂]
constant cnfXorPos2 {t₁ t₂ : option term} :
  holds [mkNot $ mkXor t₁ t₂, mkNot t₁, mkNot t₂]

/-
¬(t₀ ⊕ t₁)  ¬t₁            ¬(t₀ ⊕ t₁)  t₁
---------------cnfXorNeg1  --------------cnfXorNeg2
      ¬t₂                        ¬t₂
-/
constant cnfXorNeg1 {t₁ t₂ : option term} : 
  holds [mkXor t₁ t₂, t₁, mkNot t₂]
constant cnfXorNeg2 {t₁ t₂ : option term} : 
  holds [mkXor t₁ t₂, mkNot t₁, t₂]

/-
ite c t₁ t₂  c             ite c t₁ t₂  ¬c             ite c t₁ t₂  ¬t₁
---------------cnfItePos1  ---------------cnfItePos2   ----------------cnfItePos3
       t₁                         t₂                           t₂
-/
constant cnfItePos1 {c t₁ t₂ : option term} :
  holds [mkNot $ mkIte c t₁ t₂, mkNot c, t₁]
constant cnfItePos2 {c t₁ t₂ : option term} :
  holds [mkNot $ mkIte c t₁ t₂, c, t₂]
constant cnfItePos3 {c t₁ t₂ : option term} :
  holds [mkNot $ mkIte c t₁ t₂, t₁, t₂]

/-
¬(ite c t₁ t₂)  ¬c            ¬(ite c t₁ t₂)  c             ¬(ite c t₁ t₂)  t₁
------------------cnfIteNeg1  ------------------cnfIteNeg2  ------------------cnfIteNeg3
       ¬t₁                            ¬t₁                           ¬t₂
-/
constant cnfIteNeg1 {c t₁ t₂ : option term} : 
  holds [mkIte c t₁ t₂, c, mkNot t₁]
constant cnfIteNeg2 {c t₁ t₂ : option term} :
  holds [mkIte c t₁ t₂, mkNot c, mkNot t₂]
constant cnfIteNeg3 {c t₁ t₂ : option term} :
  holds [mkIte c t₁ t₂, mkNot t₁, mkNot t₂]

end rules
