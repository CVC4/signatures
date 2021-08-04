import Cdclt.Term

open proof
open proof.sort proof.term
open List

namespace rules

notation "clause" => List term

-- clause manipulation rules

universe u v w
def comp {α : Sort u} {β : Sort v} {φ : Sort w}
  (f : β → φ) (g : α → β) : α → φ := fun x => f (g x)

def nTh : clause → Nat → term :=
  λ c n => List.get! n c

def getLast : clause → term := λ c => nTh c (c.length - 1)
def concatCl : clause → clause → clause := @List.append term

def removeDuplicates : clause → clause → clause
| [], _ => []
| (h::t), s => if elem h s then removeDuplicates t s else h::(removeDuplicates t (h::s))

-- eventually should give Prop
axiom holds : clause → Type
axiom thHolds : term → Type

-- collect all terms in OR chain (right-associative)
def reduceOr : term → clause
| term.or t₀ (term.or t₁ t₂) => t₀::t₁::(reduceOr t₂)
| term.or t₀ t₁              => [t₀, t₁]
| t                          => [t]

------------------------------- Clausal Reasoning -------------------------------

def resolveR₀ (n : term) (c₁ c₂: clause) : clause :=
  concatCl (List.erase c₁ n) (List.erase c₂ (not n) )

def resolveR₁ (n : term) (c₁ c₂: clause) : clause :=
  concatCl (List.erase c₁ (not n)) (List.erase c₂ n)

axiom R0 : ∀ {c₁ c₂ : clause},
  holds c₁ → holds c₂ → (n : term) → holds (resolveR₀ n c₁ c₂)

axiom R1 : ∀ {c₁ c₂ : clause},
  holds c₁ → holds c₂ → (n : term) → holds (resolveR₁ n c₁ c₂)

axiom factoring : ∀ {c : clause}, holds c → holds (removeDuplicates c [])

axiom reorder : ∀ {c₁ : clause},
  holds c₁ → (perm : List Nat) → holds (List.map (nTh c₁) perm)

axiom eqResolve : ∀ {t₁ t₂ : term},
  thHolds t₁ → thHolds (eq t₁ t₂) → thHolds t₂

axiom modusPonens : ∀ {t₁ t₂ : term},
  thHolds t₁ → thHolds (implies t₁ t₂) → thHolds t₂

axiom notNotElim : ∀ {t : term}, thHolds (not $ not t) → thHolds t

axiom contradiction : ∀ {t : term},
  thHolds t → thHolds (not t) → holds []


-------------------- Natural Deduction Style Reasoning --------------------

/-
l₁ ∧ ... ∧ lₙ
-------------andElim
      lᵢ
-/
-- get n-th element in AND chain (right-associative)
def reduceAnd : Nat → term → term
| 0,     (term.and t _)                 => t
| 1,     (term.and _ (term.and t _))    => t
| 1,     (term.and _ t)                 => t
| (n+1), (term.and _ t@(term.and _ _))  => reduceAnd n t
| _,     t                              => t

axiom andElim : ∀ {t : term},
  thHolds t → (n : Nat) → thHolds (reduceAnd n t)

/-
l₁  ...  lₙ
-----------andIntro
l₁ ∧ ... ∧ lₙ
-/
axiom andIntro : ∀ {t₁ t₂ : term},
  thHolds t₁ → thHolds t₂ → thHolds (and t₁ t₂)

/-
¬(l₁ ∨ ... ∨ lₙ)
----------------notOrElim
        lᵢ
-/
def reduceNotOr : Nat → term → term
| 0,     (term.or t _)               => t
| 1,     (term.or _ (term.or t _))   => t
| 1,     (term.or _ t)               => t
| (n+1), (term.or _ t@(term.or _ _)) => reduceNotOr n t
| _,     t                           => t

axiom notOrElim : ∀ {t : term} (p : thHolds (not t)) (n : Nat),
  thHolds (not $ reduceNotOr n t)

/-
¬(l₁ ∧ ... ∧ lₙ)
----------------notAnd
¬l₁ ∨ ... ∨ ¬lₙ
-/
def reduceNotAnd : term → clause
| term.and t₀ (term.and t₁ t₂) => not t₀ :: not t₁ :: reduceNotAnd t₂
| term.and t₀ t₁               => [not t₀, not t₁]
| t                            => [not t]

axiom notAnd : ∀ {t : term},
  thHolds (not t) → holds (reduceNotAnd t)

axiom impliesElim : ∀ {t₁ t₂ : term},
  thHolds (implies t₁ t₂) → thHolds (or (not t₁) t₂)

axiom notImplies1 : ∀ {t₁ t₂ : term},
  thHolds (not $ implies t₁ t₂) → thHolds t₁

axiom notImplies2 : ∀ {t₁ t₂ : term},
  thHolds (not $ implies t₁ t₂) → thHolds (not t₂)

axiom equivElim1 : ∀ {t₁ t₂},
  thHolds (eq t₁ t₂) → holds [not t₁, t₂]

axiom equivElim2 : ∀ {t₁ t₂},
  thHolds (eq t₁ t₂) → holds [t₁, not t₂]

axiom notEquivElim1 : ∀ {t₁ t₂},
  thHolds (not $ eq t₁ t₂) → holds [t₁, t₂]

axiom notEquivElim2 : ∀ {t₁ t₂},
  thHolds (not $ eq t₁ t₂) → holds [not t₁, not t₂]

axiom xorElim1 : ∀ {t₁ t₂ : term},
  thHolds (xor t₁ t₂) → holds [t₁, t₂]

axiom xorElim2 : ∀ {t₁ t₂ : term},
  thHolds (xor t₁ t₂) → holds [not t₁, not t₂]

axiom notXorElim1 : ∀ {t₁ t₂ : term},
  thHolds (not $ xor t₁ t₂) → holds [t₁, not t₂]

axiom notXorElim2 : ∀ {t₁ t₂ : term},
  thHolds (not $ xor t₁ t₂) → holds [not t₁, t₂]

axiom iteElim1 : ∀ {c t₁ t₂ : term}, thHolds (fIte c t₁ t₂) →
  holds [not c, t₁]

axiom iteElim2 : ∀ {c t₁ t₂ : term}, thHolds (fIte c t₁ t₂) →
  holds [c, t₂]

axiom notIteElim1 : ∀ {c t₁ t₂ : term},
  thHolds (not $ fIte c t₁ t₂) → holds [not c, not t₁]

axiom notIteElim2 : ∀ {c t₁ t₂ : term},
  thHolds (not $ fIte c t₁ t₂) → holds [c, not t₂]

-------------------- CNF Reasoning (to introduce valid clauses) --------------------

def notList : clause → clause
| [] => []
| (h::t) => not h :: notList t

/-
l₁ ∧ ... ∧ lₖ     1 ≤ n ≤ k             ¬(x₁ ∧ ... ∧ xₙ)
----------------------------cnfAndPos   ----------------cnfAndNeg
             lᵢ                          ¬x₁ ∨ ... ∨ ¬xₙ
-/
axiom cnfAndPos {l : clause} {n : Nat} : holds [not $ andN l, nTh l n]
axiom cnfAndNeg {l : clause} : holds $ andN l :: notList l

/-
x₁ ∨ ... ∨ xₙ           ¬(l₁ ∨ ... ∨ lₖ)     1 ≤ n ≤ k
-------------cnfOrPos   ------------------------------cnfOrNeg
x₁ ∨ ... ∨ xₙ                         ¬lᵢ
-/
axiom cnfOrPos {l : clause} : holds $ (not $ orN l) :: l
axiom cnfOrNeg {l : clause} {n : Nat} : holds [orN l, not $ nTh l n]

/-
t₁ → t₂  t₁                 ¬(t₁ → t₂)                ¬(t₁ → t₂)
-----------cnfImpliesPos    ----------cnfImpliesNeg1  ----------cnfImpliesNeg2
     t₂                         t₁                        ¬t₂
-/
axiom cnfImpliesPos {t₁ t₂ : term} :
  holds [not $ implies t₁ t₂, not t₁, t₂]
axiom cnfImpliesNeg1 {t₁ t₂ : term} :
holds [implies t₁ t₂, t₁]
axiom cnfImpliesNeg2 {t₁ t₂ : term} :
  holds [implies t₁ t₂, not t₂]

/-
t₁ = t₂  ¬t₁              t₁ = t₂  t₁
------------cnfEquivPos1  ------------cnfEquivPos2
    ¬t₂                        t₂
-/
axiom cnfEquivPos1 {t₁ t₂ : term} :
  holds [not $ eq t₁ t₂, not t₁, t₂]

axiom cnfEquivPos2 {t₁ t₂ : term} :
  holds [not $ eq t₁ t₂, t₁, not t₂]

/-
¬(t₁ = t₂)  t₁              ¬(t₁ = t₂)  ¬t₁
--------------cnfEquivNeg1  --------------cnfEquivPos2
      ¬t₂                         t₂
-/
axiom cnfEquivNeg1 {t₁ t₂ : term} :
  holds [eq t₁ t₂, t₁, t₂]
axiom cnfEquivNeg2 {t₁ t₂ : term} :
  holds [eq t₁ t₂, not t₁, not t₂]

/-
t₁ ⊕ t₂  ¬t₁              t₁ ⊕ t₂  t₁
------------cnfXorPos1    -----------cnfXorPos2
     t₂                        ¬t₂
-/
axiom cnfXorPos1 {t₁ t₂ : term} :
  holds [not $ xor t₁ t₂, t₁, t₂]
axiom cnfXorPos2 {t₁ t₂ : term} :
  holds [not $ xor t₁ t₂, not t₁, not t₂]

/-
¬(t₀ ⊕ t₁)  ¬t₁            ¬(t₀ ⊕ t₁)  t₁
---------------cnfXorNeg1  --------------cnfXorNeg2
      ¬t₂                        ¬t₂
-/
axiom cnfXorNeg1 {t₁ t₂ : term} :
  holds [xor t₁ t₂, not t₁, t₂]
axiom cnfXorNeg2 {t₁ t₂ : term} :
  holds [xor t₁ t₂, t₁, not t₂]

/-
ite c t₁ t₂  c             ite c t₁ t₂  ¬c
---------------cnfItePos1  ---------------cnfItePos2
       t₁                         t₂

ite c t₁ t₂  ¬t₁
----------------cnfItePos3
        t₂
-/
axiom cnfItePos1 {c t₁ t₂ : term} :
  holds [not $ fIte c t₁ t₂, not c, t₁]
axiom cnfItePos2 {c t₁ t₂ : term} :
  holds [not $ fIte c t₁ t₂, c, t₂]
axiom cnfItePos3 {c t₁ t₂ : term} :
  holds [not $ fIte c t₁ t₂, t₁, t₂]

/-
¬(ite c t₁ t₂)  ¬c            ¬(ite c t₁ t₂)  c
------------------cnfIteNeg1  ------------------cnfIteNeg2
       ¬t₁                            ¬t₁


¬(ite c t₁ t₂)  t₁
------------------cnfIteNeg3
        ¬t₂
-/
axiom cnfIteNeg1 {c t₁ t₂ : term} :
  holds [fIte c t₁ t₂, not c, not t₁]
axiom cnfIteNeg2 {c t₁ t₂ : term} :
  holds [fIte c t₁ t₂, c, not t₂]
axiom cnfIteNeg3 {c t₁ t₂ : term} :
  holds [fIte c t₁ t₂, not t₁, not t₂]

-- connecting theory reasoning and clausal reasoning
---------------- Connecting Theory Reasoning and Clausal Reasoning ----------------
axiom thAssume : ∀ {l : clause}, holds l → thHolds (orN l)

axiom clSingleton : ∀ {l : clause}, holds l → holds [orN l]

axiom clAssume : ∀ {t : term}, thHolds t → holds [t]

axiom clOr : ∀ {t : term} (p : thHolds t), holds (reduceOr t)

axiom scope : ∀ {t₁ t₂ : term},
  (thHolds t₁ → thHolds t₂) → thHolds (or (not t₁) t₂)

-- collect all terms in OR chain (right-associative)
def collectNOrNegArgs : term → Nat → clause
| term.or (term.not t₀) t₁, 1 => [t₀]
| term.or (term.not t₀) t₁, n+1 => t₀::(collectNOrNegArgs t₁ n)
| t, _               => [t]

def liftOrToImpAux (t : term) (n : Nat) (tail : term) :
  term :=
 implies (andN (collectNOrNegArgs t n)) tail

axiom liftNOrToImp : ∀ {t : term},
  (p : thHolds t) → (n : Nat) → (tail : term) → thHolds (liftOrToImpAux t n tail)

def liftOrToNegAux (t : term) (n : Nat) :
  term :=
 not (andN (collectNOrNegArgs t n))

axiom liftNOrToNeg : ∀ {t : term},
  (p : thHolds t) → (n : Nat) → thHolds (liftOrToNegAux t n)

------------------------------------ Holes ------------------------------------

axiom trust : ∀ {c₁ c₂ : clause}, holds c₁ → holds c₂
axiom trustValid : ∀ {c : clause}, holds c

axiom thTrust : ∀ {t₁ t₂ : term}, thHolds t₁ → thHolds t₂

axiom thTrustValid : ∀ {t : term}, thHolds t

end rules
