import Cdclt.Term

open proof
open proof.sort proof.term
open List

namespace rules

notation "clause" => List (OptionM term)

-- clause manipulation rules
def join : OptionM (OptionM α) → OptionM α
| some t => t
| _ => none

universes u v w
def comp {α : Sort u} {β : Sort v} {φ : Sort w}
  (f : β → φ) (g : α → β) : α → φ := fun x => f (g x)

def nTh : clause → Nat → OptionM term :=
  λ c n => join (@List.get? (OptionM term) n c)
def getLast : clause → OptionM term := λ c => nTh c (c.length - 1)
def concatCl : clause → clause → clause := @List.append (OptionM term)

def removeDuplicates : clause → clause → clause
| [], _ => []
| (h::t), s => if elem h s then removeDuplicates t s else h::(removeDuplicates t (h::s))

-- eventually should give Prop
axiom holds : clause → Type
axiom thHolds : OptionM term → Type

-- collect all terms in OR chain (right-associative)
def reduceOrAux : term → clause
| term.or t₀ (term.or t₁ t₂) => t₀::t₁::(reduceOrAux t₂)
| term.or t₀ t₁              => [t₀, t₁]
| t                          => [t]
def reduceOr : OptionM term → clause
| some t => reduceOrAux t
| none   => [none]

------------------------------- Clausal Reasoning -------------------------------

def resolveR₀ (n : OptionM term) (c₁ c₂: clause) : clause :=
  concatCl (List.erase c₁ n) (List.erase c₂ (mkNot n) )

def resolveR₁ (n : OptionM term) (c₁ c₂: clause) : clause :=
  concatCl (List.erase c₁ (mkNot n)) (List.erase c₂ n)

axiom R0 : ∀ {c₁ c₂ : clause},
  holds c₁ → holds c₂ → (n : OptionM term) → holds (resolveR₀ n c₁ c₂)

axiom R1 : ∀ {c₁ c₂ : clause},
  holds c₁ → holds c₂ → (n : OptionM term) → holds (resolveR₁ n c₁ c₂)

axiom factoring : ∀ {c : clause}, holds c → holds (removeDuplicates c [])

axiom reorder : ∀ {c₁ : clause},
  holds c₁ → (perm : List Nat) → holds (List.map (nTh c₁) perm)

axiom eqResolve : ∀ {t₁ t₂ : OptionM term},
  thHolds t₁ → thHolds (mkEq t₁ t₂) → thHolds t₂

axiom modusPonens : ∀ {t₁ t₂ : OptionM term},
  thHolds t₁ → thHolds (mkImplies t₁ t₂) → thHolds t₂

axiom notNotElim : ∀ {t : OptionM term}, thHolds (mkNot $ mkNot t) → thHolds t

axiom contradiction : ∀ {t : OptionM term},
  thHolds t → thHolds (mkNot t) → holds []


-------------------- Natural Deduction Style Reasoning --------------------

/-
l₁ ∧ ... ∧ lₙ
-------------andElim
      lᵢ
-/
-- get n-th element in AND chain (right-associative)
def reduceAndNth : Nat → term → OptionM term
| 0,     (term.and t v)                 => t
| 1,     (term.and _ t)                 => t
| (n+1), (term.and  _ (term.and t₀ t₁)) =>  reduceAndNth n (and t₀ t₁)
| _,     _                              => none
def reduceAnd (n : Nat) : OptionM term → OptionM term :=
  λ t => t >>= λ t' => reduceAndNth n t'
axiom andElim : ∀ {t : OptionM term},
  thHolds t → (n : Nat) → thHolds (reduceAnd n t)

/-
l₁  ...  lₙ
-----------andIntro
l₁ ∧ ... ∧ lₙ
-/
axiom andIntro : ∀ {t₁ t₂ : OptionM term},
  thHolds t₁ → thHolds t₂ → thHolds (mkAnd t₁ t₂)

/-
¬(l₁ ∨ ... ∨ lₙ)
----------------notOrElim
        lᵢ
-/
-- get n-th in NOT-OR chain (right-associative)
def reduceOrNth : Nat → term → OptionM term
| 0,     (term.or t _)               => t
| 1,     (term.or _ t)               => t
| (n+1), (term.or _ (term.or t₀ t₁)) => reduceOrNth n (or t₀ t₁)
| _,     _                           => none

def reduceNotOr (n : Nat) (t : OptionM term) : OptionM term :=
  t >>= λ t' =>
    match t' with
    | term.not t'' => mkNot $ reduceOrNth n t''
    | _            => none
axiom notOrElim : ∀ {t : OptionM term} (p : thHolds t) (n : Nat),
  thHolds (reduceNotOr n t)

axiom impliesElim : ∀ {t₁ t₂ : OptionM term},
  thHolds (mkImplies t₁ t₂) → thHolds (mkOr (mkNot t₁) t₂)

axiom myimpliesElim : ∀ {t₁ t₂ : term},
  thHolds (implies t₁ t₂) → thHolds (or (not t₁) t₂)

axiom notImplies1 : ∀ {t₁ t₂ : OptionM term},
  thHolds (mkNot $ mkImplies t₁ t₂) → thHolds t₁

axiom notImplies2 : ∀ {t₁ t₂ : OptionM term},
  thHolds (mkNot $ mkImplies t₁ t₂) → thHolds (mkNot t₂)

axiom equivElim1 : ∀ {t₁ t₂},
  thHolds (mkEq t₁ t₂) → holds [mkNot t₁, t₂]

axiom equivElim2 : ∀ {t₁ t₂},
  thHolds (mkEq t₁ t₂) → holds [t₁, mkNot t₂]

axiom notEquivElim1 : ∀ {t₁ t₂},
  thHolds (mkNot $ mkEq t₁ t₂) → holds [t₁, t₂]

axiom notEquivElim2 : ∀ {t₁ t₂},
  thHolds (mkNot $ mkEq t₁ t₂) → holds [mkNot t₁, mkNot t₂]

axiom xorElim1 : ∀ {t₁ t₂ : OptionM term},
  thHolds (mkXor t₁ t₂) → holds [t₁, t₂]

axiom xorElim2 : ∀ {t₁ t₂ : OptionM term},
  thHolds (mkXor t₁ t₂) → holds [mkNot t₁, mkNot t₂]

axiom notXorElim1 : ∀ {t₁ t₂ : OptionM term},
  thHolds (mkNot $ mkXor t₁ t₂) → holds [t₁, mkNot t₂]

axiom notXorElim2 : ∀ {t₁ t₂ : OptionM term},
  thHolds (mkNot $ mkXor t₁ t₂) → holds [mkNot t₁, t₂]

axiom iteElim1 : ∀ {c t₁ t₂ : OptionM term}, thHolds (mkIte c t₁ t₂) →
  holds [mkNot c, t₁]

axiom iteElim2 : ∀ {c t₁ t₂ : OptionM term}, thHolds (mkIte c t₁ t₂) →
  holds [c, t₂]

axiom notIteElim1 : ∀ {c t₁ t₂ : OptionM term},
  thHolds (mkNot $ mkIte c t₁ t₂) → holds [mkNot c, mkNot t₁]

axiom notIteElim2 : ∀ {c t₁ t₂ : OptionM term},
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
def reduceNotAnd : OptionM term → clause
| (some t) => reduceNotAndAux t
| none     => [none]
axiom notAnd : ∀ {t : OptionM term},
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
axiom cnfImpliesPos {t₁ t₂ : OptionM term} :
  holds [mkNot $ mkImplies t₁ t₂, mkNot t₁, t₂]
axiom cnfImpliesNeg1 {t₁ t₂ : OptionM term} :
holds [mkImplies t₁ t₂, t₁]
axiom cnfImpliesNeg2 {t₁ t₂ : OptionM term} :
  holds [mkImplies t₁ t₂, mkNot t₂]

/-
t₁ = t₂  ¬t₁              t₁ = t₂  t₁
------------cnfEquivPos1  ------------cnfEquivPos2
    ¬t₂                        t₂
-/
axiom cnfEquivPos1 {t₁ t₂ : OptionM term} :
  holds [mkNot $ mkEq t₁ t₂, t₁, mkNot t₂]
axiom cnEquivPos2 {t₁ t₂ : OptionM term} :
  holds [mkNot $ mkEq t₁ t₂, mkNot t₁, t₂]

/-
¬(t₁ = t₂)  t₁              ¬(t₁ = t₂)  ¬t₁
--------------cnfEquivNeg1  --------------cnfEquivPos2
      ¬t₂                         t₂
-/
axiom cnfEquivNeg1 {t₁ t₂ : OptionM term} :
  holds [mkEq t₁ t₂, mkNot t₁, mkNot t₂]
axiom cnfEquivNeg2 {t₁ t₂ : OptionM term} :
  holds [mkEq t₁ t₂, t₁, t₂]

/-
t₁ ⊕ t₂  ¬t₁              t₁ ⊕ t₂  t₁
------------cnfXorPos1    -----------cnfXorPos2
     t₂                        ¬t₂
-/
axiom cnfXorPos1 {t₁ t₂ : OptionM term} :
  holds [mkNot $ mkXor t₁ t₂, t₁, t₂]
axiom cnfXorPos2 {t₁ t₂ : OptionM term} :
  holds [mkNot $ mkXor t₁ t₂, mkNot t₁, mkNot t₂]

/-
¬(t₀ ⊕ t₁)  ¬t₁            ¬(t₀ ⊕ t₁)  t₁
---------------cnfXorNeg1  --------------cnfXorNeg2
      ¬t₂                        ¬t₂
-/
axiom cnfXorNeg1 {t₁ t₂ : OptionM term} :
  holds [mkXor t₁ t₂, t₁, mkNot t₂]
axiom cnfXorNeg2 {t₁ t₂ : OptionM term} :
  holds [mkXor t₁ t₂, mkNot t₁, t₂]

/-
ite c t₁ t₂  c             ite c t₁ t₂  ¬c
---------------cnfItePos1  ---------------cnfItePos2
       t₁                         t₂

ite c t₁ t₂  ¬t₁
----------------cnfItePos3
        t₂
-/
axiom cnfItePos1 {c t₁ t₂ : OptionM term} :
  holds [mkNot $ mkIte c t₁ t₂, mkNot c, t₁]
axiom cnfItePos2 {c t₁ t₂ : OptionM term} :
  holds [mkNot $ mkIte c t₁ t₂, c, t₂]
axiom cnfItePos3 {c t₁ t₂ : OptionM term} :
  holds [mkNot $ mkIte c t₁ t₂, t₁, t₂]

/-
¬(ite c t₁ t₂)  ¬c            ¬(ite c t₁ t₂)  c
------------------cnfIteNeg1  ------------------cnfIteNeg2
       ¬t₁                            ¬t₁


¬(ite c t₁ t₂)  t₁
------------------cnfIteNeg3
        ¬t₂
-/
axiom cnfIteNeg1 {c t₁ t₂ : OptionM term} :
  holds [mkIte c t₁ t₂, c, mkNot t₁]
axiom cnfIteNeg2 {c t₁ t₂ : OptionM term} :
  holds [mkIte c t₁ t₂, mkNot c, mkNot t₂]
axiom cnfIteNeg3 {c t₁ t₂ : OptionM term} :
  holds [mkIte c t₁ t₂, mkNot t₁, mkNot t₂]

-- connecting theory reasoning and clausal reasoning
---------------- Connecting Theory Reasoning and Clausal Reasoning ----------------
axiom thAssume : ∀ {l : clause}, holds l → thHolds (maybeMkOr l)

axiom clAssume : ∀ {t : OptionM term}, thHolds t → holds [t]

axiom clOr : ∀ {t : OptionM term} (p : thHolds t), holds (reduceOr t)

axiom scope : ∀ {t₁ t₂ : OptionM term},
  (thHolds t₁ → thHolds t₂) → thHolds (mkOr (mkNot t₁) t₂)

-- collect all terms in OR chain (right-associative)
def collectNOrNegArgs : term → Nat → clause
| term.or (term.not t₀) t₁, 1 => [t₀]
| term.or (term.not t₀) t₁, n+1 => t₀::(collectNOrNegArgs t₁ n)
| t, _               => [t]

def liftOrToImpAux (ot : OptionM term) (n : Nat) (otail : OptionM term) :
  OptionM term :=
 ot >>= λ t => otail >>= λ tail => mkImplies (maybeMkAnd (collectNOrNegArgs t n)) tail

axiom liftNOrToImp : ∀ {t : OptionM term},
  (p : thHolds t) → (n : Nat) → (tail : OptionM term) → thHolds (liftOrToImpAux t n tail)

def liftOrToNegAux (ot : OptionM term) (n : Nat) :
  OptionM term :=
 ot >>= λ t => mkNot (maybeMkAnd (collectNOrNegArgs t n))

axiom liftNOrToNeg : ∀ {t : OptionM term},
  (p : thHolds (mkNot t)) → (n : Nat) → thHolds (liftOrToNegAux t n)

------------------------------------ Holes ------------------------------------

axiom trust : ∀ {c₁ c₂ : clause}, holds c₁ → holds c₂
axiom trustValid : ∀ {c : clause}, holds c

axiom thTrust : ∀ {t₁ t₂ : OptionM term}, thHolds t₁ → thHolds t₂

axiom thTrustValid : ∀ {t : OptionM term}, thHolds t

end rules
