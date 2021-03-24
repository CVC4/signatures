import Cdclt.Term

open proof
open proof.sort proof.term
open List

namespace rules

notation "clause" => List (Option term)

-- clause manipulation rules
def join : Option (Option α) → Option α
| some t => t
| _ => none

universes u v w
def comp {α : Sort u} {β : Sort v} {φ : Sort w}
  (f : β → φ) (g : α → β) : α → φ := fun x => f (g x)

def nTh : clause → Nat → Option term :=
  λ c n => join (@List.get? (Option term) n c)
def getLast : clause → Option term := λ c => nTh c (c.length - 1)
def concatCl : clause → clause → clause := @List.append (Option term)
def removeDuplicates : clause → clause
| [] => []
| (h::t) => if elem h t then removeDuplicates t else h::(removeDuplicates t)


-- eventually should give Prop
axiom holds : clause → Type
axiom thHolds : Option term → Type

-- collect all terms in OR chain (right-associative)
def reduceOrAux : term → clause
| term.or t₀ (term.or t₁ t₂) => t₀::t₁::(reduceOrAux t₂)
| term.or t₀ t₁              => [t₀, t₁]
| t                          => [t]
def reduceOr : Option term → clause
| some t => reduceOrAux t
| none   => [none]

------------------------------- Clausal Reasoning -------------------------------

def resolveR₀ (n : Option term) (c₁ c₂: clause) : clause :=
  concatCl (List.erase c₁ n) (List.erase c₂ (mkNot n) )

def resolveR₁ (n : Option term) (c₁ c₂: clause) : clause :=
  concatCl (List.erase c₁ (mkNot n)) (List.erase c₂ n)

axiom R0 : ∀ {c₁ c₂ : clause} 
  (p₁ : holds c₁) (p₂ : holds c₂) (n : Option term), holds (resolveR₀ n c₁ c₂)

axiom R1 : ∀ {c₁ c₂ : clause}
  (p₁ : holds c₁) (p₂ : holds c₂) (n : Option term), holds (resolveR₁ n c₁ c₂)

axiom factoring : ∀ {c : clause} (p : holds c), holds (removeDuplicates c)

axiom reorder {c₁ : clause} (perm : List Nat) :
  holds c₁ → holds (List.map (nTh c₁) perm)

axiom eqResolve : ∀ {t₁ t₂ : Option term},
  thHolds t₁ → thHolds (mkEq t₁ t₂) → thHolds t₂

axiom modusPonens : ∀ {t₁ t₂ : Option term},
  thHolds t₁ → thHolds (mkImplies t₁ t₂) → thHolds t₂

axiom notNotElim : ∀ {t : Option term}, thHolds (mkNot $ mkNot t) → thHolds t

axiom contradiction : ∀ {t : Option term},
  thHolds t → thHolds (mkNot t) → holds []


-------------------- Natural Deduction Style Reasoning --------------------

/-
l₁ ∧ ... ∧ lₙ
-------------andElim
      lᵢ
-/
-- get n-th element in AND chain (right-associative)
def reduceAndNth : Nat → term → Option term
| 0,     (term.and t v)                 => t
| 1,     (term.and _ t)                 => t
| (n+1), (term.and  _ (term.and t₀ t₁)) =>  reduceAndNth n (and t₀ t₁)
| _,     _                              => none
def reduceAnd (n : Nat) : Option term → Option term :=
  λ t => t >>= λ t' => reduceAndNth n t'
axiom andElim : ∀ {t : Option term} (p : thHolds t) (n : Nat),
  thHolds (reduceAnd n t)

/-
l₁  ...  lₙ
-----------andIntro
l₁ ∧ ... ∧ lₙ
-/
axiom andIntro : ∀ {t₁ t₂ : Option term},
  thHolds t₁ → thHolds t₂ → thHolds (mkAnd t₁ t₂)

/-
¬(l₁ ∨ ... ∨ lₙ)
----------------notOrElim
        lᵢ
-/
-- get n-th in NOT-OR chain (right-associative)
def reduceOrNth : Nat → term → Option term
| 0,     (term.or t _)               => t
| 1,     (term.or _ t)               => t
| (n+1), (term.or _ (term.or t₀ t₁)) => reduceOrNth n (or t₀ t₁)
| _,     _                           => none
def reduceNotOr (n : Nat) (t : Option term) : Option term :=
  t >>= λ t' =>
    match t' with
    | term.not t'' => mkNot $ reduceOrNth n t''
    | _            => none
axiom notOrElim : ∀ {t : Option term} (p : thHolds t) (n : Nat),
  thHolds (reduceNotOr n t)

axiom impliesElim : ∀ {t₁ t₂ : Option term},
  thHolds (mkImplies t₁ t₂) → holds [mkNot t₁, t₂]

axiom notImplies1 : ∀ {t₁ t₂ : Option term},
  thHolds (mkNot $ mkImplies t₁ t₂) → thHolds t₁

axiom notImplies2 : ∀ {t₁ t₂ : Option term},
  thHolds (mkNot $ mkImplies t₁ t₂) → thHolds (mkNot t₁)

axiom equivElim1 : ∀ {t₁ t₂}, 
  thHolds (mkEq t₁ t₂) → holds [mkNot t₁, t₂]

axiom equivElim2 : ∀ {t₁ t₂}, 
  thHolds (mkEq t₁ t₂) → holds [t₁, mkNot t₂]

axiom notEquivElim1 : ∀ {t₁ t₂}, 
  thHolds (mkNot $ mkEq t₁ t₂) → holds [t₁, t₂]

axiom notEquivElim2 : ∀ {t₁ t₂},
  thHolds (mkNot $ mkEq t₁ t₂) → holds [mkNot t₁, mkNot t₂]

axiom xorElim1 : ∀ {t₁ t₂ : Option term},
  thHolds (mkXor t₁ t₂) → holds [t₁, t₂]

axiom xorElim2 : ∀ {t₁ t₂ : Option term},
  thHolds (mkXor t₁ t₂) → holds [mkNot t₁, mkNot t₂]

axiom notXorElim1 : ∀ {t₁ t₂ : Option term},
  thHolds (mkNot $ mkXor t₁ t₂) → holds [t₁, mkNot t₂]

axiom notXorElim2 : ∀ {t₁ t₂ : Option term},
  thHolds (mkNot $ mkXor t₁ t₂) → holds [mkNot t₁, t₂]

axiom iteElim1 : ∀ {c t₁ t₂ : Option term}, thHolds (mkIte c t₁ t₂) →
  holds [mkNot c, t₁]

axiom iteElim2 : ∀ {c t₁ t₂ : Option term}, thHolds (mkIte c t₁ t₂) →
  holds [c, t₂]

axiom notIteElim1 : ∀ {c t₁ t₂ : Option term},
  thHolds (mkNot $ mkIte c t₁ t₂) → holds [mkNot c, mkNot t₁]

axiom notIteElim2 : ∀ {c t₁ t₂ : Option term},
  thHolds (mkNot $ mkIte c t₁ t₂) → holds [c, mkNot t₂]

/-
¬(l₁ ∧ ... ∧ lₙ)
----------------notAnd
¬l₁ ∨ ... ∨ ¬lₙ
-/
def reduceNotAndAux : term → clause
| term.and t₀ (term.and t₁ t₂) => mkNot t₀ :: mkNot t₁ :: reduceNotAndAux t₂
| term.and t₀ t₁               => [mkNot t₀, mkNot t₁]
| t                            => [t]
def reduceNotAnd : Option term → clause
| (some t) => reduceNotAndAux t
| none     => [none]
axiom notAnd : ∀ {t : Option term}, 
  thHolds (mkNot t) → holds (reduceNotAnd t)


-------------------- CNF Reasoning (to introduce valid clauses) --------------------

def mkNotList : clause → clause
| [] => []
| (h::t) => mkNot h :: mkNotList t

/-
l₁ ∧ ... ∧ lₖ     1 ≤ n ≤ k             ¬(x₁ ∧ ... ∧ xₙ)
----------------------------cnfAndPos   ----------------cnfAndNeg
             lᵢ                          ¬x₁ ∨ ... ∨ ¬xₙ
-/
axiom cnfAndPos {l : clause} {n : Nat} : holds [mkNot $ mkAndN l, nTh l n]
axiom cnfAndNeg {l : clause} : holds $ mkAndN l :: mkNotList l

/-
x₁ ∨ ... ∨ xₙ           ¬(l₁ ∨ ... ∨ lₖ)     1 ≤ n ≤ k
-------------cnfOrPos   ------------------------------cnfOrNeg
x₁ ∨ ... ∨ xₙ                         ¬lᵢ
-/
axiom cnfOrPos {l : clause} : holds $ (mkNot $ mkOrN l) :: l
axiom cnfOrNeg {l : clause} {n : Nat} : holds [mkOrN l, mkNot $ nTh l n]

/-
t₁ → t₂  t₁                 ¬(t₁ → t₂)                ¬(t₁ → t₂)
-----------cnfImpliesPos    ----------cnfImpliesNeg1  ----------cnfImpliesNeg2
     t₂                         t₁                        ¬t₂
-/
axiom cnfImpliesPos {t₁ t₂ : Option term} :
  holds [mkNot $ mkImplies t₁ t₂, mkNot t₁, t₂]
axiom cnfImpliesNeg1 {t₁ t₂ : Option term} :
holds [mkImplies t₁ t₂, t₁]
axiom cnfImpliesNeg2 {t₁ t₂ : Option term} :
  holds [mkImplies t₁ t₂, mkNot t₂]

/-
t₁ = t₂  ¬t₁              t₁ = t₂  t₁
------------cnfEquivPos1  ------------cnfEquivPos2
    ¬t₂                        t₂
-/
axiom cnfEquivPos1 {t₁ t₂ : Option term} :
  holds [mkNot $ mkEq t₁ t₂, t₁, mkNot t₂]
axiom cnEquivPos2 {t₁ t₂ : Option term} :
  holds [mkNot $ mkEq t₁ t₂, mkNot t₁, t₂]

/-
¬(t₁ = t₂)  t₁              ¬(t₁ = t₂)  ¬t₁
--------------cnfEquivNeg1  --------------cnfEquivPos2
      ¬t₂                         t₂
-/
axiom cnfEquivNeg1 {t₁ t₂ : Option term} :
  holds [mkEq t₁ t₂, mkNot t₁, mkNot t₂]
axiom cnfEquivNeg2 {t₁ t₂ : Option term} :
  holds [mkEq t₁ t₂, t₁, t₂]

/-
t₁ ⊕ t₂  ¬t₁              t₁ ⊕ t₂  t₁
------------cnfXorPos1    -----------cnfXorPos2
     t₂                        ¬t₂
-/
axiom cnfXorPos1 {t₁ t₂ : Option term} :
  holds [mkNot $ mkXor t₁ t₂, t₁, t₂]
axiom cnfXorPos2 {t₁ t₂ : Option term} :
  holds [mkNot $ mkXor t₁ t₂, mkNot t₁, mkNot t₂]

/-
¬(t₀ ⊕ t₁)  ¬t₁            ¬(t₀ ⊕ t₁)  t₁
---------------cnfXorNeg1  --------------cnfXorNeg2
      ¬t₂                        ¬t₂
-/
axiom cnfXorNeg1 {t₁ t₂ : Option term} :
  holds [mkXor t₁ t₂, t₁, mkNot t₂]
axiom cnfXorNeg2 {t₁ t₂ : Option term} :
  holds [mkXor t₁ t₂, mkNot t₁, t₂]

/-
ite c t₁ t₂  c             ite c t₁ t₂  ¬c
---------------cnfItePos1  ---------------cnfItePos2
       t₁                         t₂

ite c t₁ t₂  ¬t₁
----------------cnfItePos3
        t₂
-/
axiom cnfItePos1 {c t₁ t₂ : Option term} :
  holds [mkNot $ mkIte c t₁ t₂, mkNot c, t₁]
axiom cnfItePos2 {c t₁ t₂ : Option term} :
  holds [mkNot $ mkIte c t₁ t₂, c, t₂]
axiom cnfItePos3 {c t₁ t₂ : Option term} :
  holds [mkNot $ mkIte c t₁ t₂, t₁, t₂]

/-
¬(ite c t₁ t₂)  ¬c            ¬(ite c t₁ t₂)  c
------------------cnfIteNeg1  ------------------cnfIteNeg2
       ¬t₁                            ¬t₁


¬(ite c t₁ t₂)  t₁
------------------cnfIteNeg3
        ¬t₂
-/
axiom cnfIteNeg1 {c t₁ t₂ : Option term} :
  holds [mkIte c t₁ t₂, c, mkNot t₁]
axiom cnfIteNeg2 {c t₁ t₂ : Option term} :
  holds [mkIte c t₁ t₂, mkNot c, mkNot t₂]
axiom cnfIteNeg3 {c t₁ t₂ : Option term} :
  holds [mkIte c t₁ t₂, mkNot t₁, mkNot t₂]

-- connecting theory reasoning and clausal reasoning
---------------- Connecting Theory Reasoning and Clausal Reasoning ----------------
axiom clAssume : ∀ {t : Option term}, thHolds t → holds [t]

axiom clOr : ∀ {t : Option term} (p : thHolds t), holds (reduceOr t)

axiom scope : ∀ {t₁ t₂ : Option term}
  (p₁ : thHolds t₁) (p₂ : thHolds t₂), thHolds (mkOr (mkNot t₁) t₂)

------------------------------------ Holes ------------------------------------

axiom trust : ∀ {c₁ c₂ : clause}, holds c₁ → holds c₂

axiom thTrust : ∀ {t₁ t₂ : Option term}, thHolds t₁ → thHolds t₂

end rules