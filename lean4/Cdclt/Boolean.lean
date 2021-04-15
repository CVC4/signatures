import Cdclt.Term

open proof
open proof.sort proof.Term
open List

namespace rules

notation "clause" => List (OptionM Term)

instance : BEq (OptionM Term) :=
 ⟨λ a b => do decide ((← a) = (← b))⟩

-- clause manipulation rules
def join : OptionM (OptionM α) → OptionM α
| some t => t
| _ => none

universes u v w
def comp {α : Sort u} {β : Sort v} {φ : Sort w}
  (f : β → φ) (g : α → β) : α → φ := fun x => f (g x)

def nTh : clause → Nat → OptionM Term :=
  λ c n => join (@List.get? (OptionM Term) n c)
def getLast : clause → OptionM Term := λ c => nTh c (c.length - 1)
def concatCl : clause → clause → clause := @List.append (OptionM Term)
def removeDuplicates : clause → clause
| [] => []
| (h::t) => if elem h t then removeDuplicates t else h::(removeDuplicates t)


-- eventually should give Prop
axiom holds : clause → Type
axiom thHolds : OptionM Term → Type

-- collect all Terms in OR chain (right-associative)
def reduceOrAux : Term → clause
| Term.or t₀ (Term.or t₁ t₂) => t₀::t₁::(reduceOrAux t₂)
| Term.or t₀ t₁              => [t₀, t₁]
| t                          => [t]
def reduceOr : OptionM Term → clause
| some t => reduceOrAux t
| none   => [none]

------------------------------- Clausal Reasoning -------------------------------

def resolveR₀ (n : OptionM Term) (c₁ c₂: clause) : clause :=
  concatCl (List.erase c₁ n) (List.erase c₂ (mkNot n) )

def resolveR₁ (n : OptionM Term) (c₁ c₂: clause) : clause :=
  concatCl (List.erase c₁ (mkNot n)) (List.erase c₂ n)

axiom R0 : ∀ {c₁ c₂ : clause},
  holds c₁ → holds c₂ → (n : OptionM Term) → holds (resolveR₀ n c₁ c₂)

axiom R1 : ∀ {c₁ c₂ : clause},
  holds c₁ → holds c₂ → (n : OptionM Term) → holds (resolveR₁ n c₁ c₂)

axiom factoring : ∀ {c : clause}, holds c → holds (removeDuplicates c)

axiom reorder {c₁ : clause} (perm : List Nat) :
  holds c₁ → holds (List.map (nTh c₁) perm)

axiom eqResolve : ∀ {t₁ t₂ : OptionM Term},
  thHolds t₁ → thHolds (mkEq t₁ t₂) → thHolds t₂

axiom modusPonens : ∀ {t₁ t₂ : OptionM Term},
  thHolds t₁ → thHolds (mkImplies t₁ t₂) → thHolds t₂

axiom notNotElim : ∀ {t : OptionM Term}, thHolds (mkNot $ mkNot t) → thHolds t

axiom contradiction : ∀ {t : OptionM Term},
  thHolds t → thHolds (mkNot t) → holds []


-------------------- Natural Deduction Style Reasoning --------------------

/-
l₁ ∧ ... ∧ lₙ
-------------andElim
      lᵢ
-/
-- get n-th element in AND chain (right-associative)
def reduceAndNth : Nat → Term → OptionM Term
| 0,     (Term.and t v)                 => t
| 1,     (Term.and _ t)                 => t
| (n+1), (Term.and  _ (Term.and t₀ t₁)) =>  reduceAndNth n (and t₀ t₁)
| _,     _                              => none
def reduceAnd (n : Nat) : OptionM Term → OptionM Term :=
  λ t => t >>= λ t' => reduceAndNth n t'
axiom andElim : ∀ {t : OptionM Term},
  thHolds t → (n : Nat) → thHolds (reduceAnd n t)

/-
l₁  ...  lₙ
-----------andIntro
l₁ ∧ ... ∧ lₙ
-/
axiom andIntro : ∀ {t₁ t₂ : OptionM Term},
  thHolds t₁ → thHolds t₂ → thHolds (mkAnd t₁ t₂)

/-
¬(l₁ ∨ ... ∨ lₙ)
----------------notOrElim
        lᵢ
-/
-- get n-th in NOT-OR chain (right-associative)
def reduceOrNth : Nat → Term → OptionM Term
| 0,     (Term.or t _)               => t
| 1,     (Term.or _ t)               => t
| (n+1), (Term.or _ (Term.or t₀ t₁)) => reduceOrNth n (or t₀ t₁)
| _,     _                           => none

def reduceNotOr (n : Nat) (t : OptionM Term) : OptionM Term :=
  t >>= λ t' =>
    match t' with
    | Term.not t'' => mkNot $ reduceOrNth n t''
    | _            => none
axiom notOrElim : ∀ {t : OptionM Term} (p : thHolds t) (n : Nat),
  thHolds (reduceNotOr n t)

axiom impliesElim : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkImplies t₁ t₂) → holds [mkNot t₁, t₂]

axiom notImplies1 : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkNot $ mkImplies t₁ t₂) → thHolds t₁

axiom notImplies2 : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkNot $ mkImplies t₁ t₂) → thHolds (mkNot t₁)

axiom equivElim1 : ∀ {t₁ t₂},
  thHolds (mkEq t₁ t₂) → holds [mkNot t₁, t₂]

axiom equivElim2 : ∀ {t₁ t₂},
  thHolds (mkEq t₁ t₂) → holds [t₁, mkNot t₂]

axiom notEquivElim1 : ∀ {t₁ t₂},
  thHolds (mkNot $ mkEq t₁ t₂) → holds [t₁, t₂]

axiom notEquivElim2 : ∀ {t₁ t₂},
  thHolds (mkNot $ mkEq t₁ t₂) → holds [mkNot t₁, mkNot t₂]

axiom xorElim1 : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkXor t₁ t₂) → holds [t₁, t₂]

axiom xorElim2 : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkXor t₁ t₂) → holds [mkNot t₁, mkNot t₂]

axiom notXorElim1 : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkNot $ mkXor t₁ t₂) → holds [t₁, mkNot t₂]

axiom notXorElim2 : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkNot $ mkXor t₁ t₂) → holds [mkNot t₁, t₂]

axiom iteElim1 : ∀ {c t₁ t₂ : OptionM Term}, thHolds (mkIte c t₁ t₂) →
  holds [mkNot c, t₁]

axiom iteElim2 : ∀ {c t₁ t₂ : OptionM Term}, thHolds (mkIte c t₁ t₂) →
  holds [c, t₂]

axiom notIteElim1 : ∀ {c t₁ t₂ : OptionM Term},
  thHolds (mkNot $ mkIte c t₁ t₂) → holds [mkNot c, mkNot t₁]

axiom notIteElim2 : ∀ {c t₁ t₂ : OptionM Term},
  thHolds (mkNot $ mkIte c t₁ t₂) → holds [c, mkNot t₂]

/-
¬(l₁ ∧ ... ∧ lₙ)
----------------notAnd
¬l₁ ∨ ... ∨ ¬lₙ
-/
def reduceNotAndAux : Term → clause
| Term.and' t₀ (Term.and' t₁ t₂) => mkNot t₀ :: mkNot t₁ :: reduceNotAndAux t₂
| Term.and' t₀ t₁               => [mkNot t₀, mkNot t₁]
| t                            => [t]
def reduceNotAnd : OptionM Term → clause
| (some t) => reduceNotAndAux t
| none     => [none]
axiom notAnd : ∀ {t : OptionM Term},
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
axiom cnfImpliesPos {t₁ t₂ : OptionM Term} :
  holds [mkNot $ mkImplies t₁ t₂, mkNot t₁, t₂]
axiom cnfImpliesNeg1 {t₁ t₂ : OptionM Term} :
holds [mkImplies t₁ t₂, t₁]
axiom cnfImpliesNeg2 {t₁ t₂ : OptionM Term} :
  holds [mkImplies t₁ t₂, mkNot t₂]

/-
t₁ = t₂  ¬t₁              t₁ = t₂  t₁
------------cnfEquivPos1  ------------cnfEquivPos2
    ¬t₂                        t₂
-/
axiom cnfEquivPos1 {t₁ t₂ : OptionM Term} :
  holds [mkNot $ mkEq t₁ t₂, t₁, mkNot t₂]
axiom cnEquivPos2 {t₁ t₂ : OptionM Term} :
  holds [mkNot $ mkEq t₁ t₂, mkNot t₁, t₂]

/-
¬(t₁ = t₂)  t₁              ¬(t₁ = t₂)  ¬t₁
--------------cnfEquivNeg1  --------------cnfEquivPos2
      ¬t₂                         t₂
-/
axiom cnfEquivNeg1 {t₁ t₂ : OptionM Term} :
  holds [mkEq t₁ t₂, mkNot t₁, mkNot t₂]
axiom cnfEquivNeg2 {t₁ t₂ : OptionM Term} :
  holds [mkEq t₁ t₂, t₁, t₂]

/-
t₁ ⊕ t₂  ¬t₁              t₁ ⊕ t₂  t₁
------------cnfXorPos1    -----------cnfXorPos2
     t₂                        ¬t₂
-/
axiom cnfXorPos1 {t₁ t₂ : OptionM Term} :
  holds [mkNot $ mkXor t₁ t₂, t₁, t₂]
axiom cnfXorPos2 {t₁ t₂ : OptionM Term} :
  holds [mkNot $ mkXor t₁ t₂, mkNot t₁, mkNot t₂]

/-
¬(t₀ ⊕ t₁)  ¬t₁            ¬(t₀ ⊕ t₁)  t₁
---------------cnfXorNeg1  --------------cnfXorNeg2
      ¬t₂                        ¬t₂
-/
axiom cnfXorNeg1 {t₁ t₂ : OptionM Term} :
  holds [mkXor t₁ t₂, t₁, mkNot t₂]
axiom cnfXorNeg2 {t₁ t₂ : OptionM Term} :
  holds [mkXor t₁ t₂, mkNot t₁, t₂]

/-
ite c t₁ t₂  c             ite c t₁ t₂  ¬c
---------------cnfItePos1  ---------------cnfItePos2
       t₁                         t₂

ite c t₁ t₂  ¬t₁
----------------cnfItePos3
        t₂
-/
axiom cnfItePos1 {c t₁ t₂ : OptionM Term} :
  holds [mkNot $ mkIte c t₁ t₂, mkNot c, t₁]
axiom cnfItePos2 {c t₁ t₂ : OptionM Term} :
  holds [mkNot $ mkIte c t₁ t₂, c, t₂]
axiom cnfItePos3 {c t₁ t₂ : OptionM Term} :
  holds [mkNot $ mkIte c t₁ t₂, t₁, t₂]

/-
¬(ite c t₁ t₂)  ¬c            ¬(ite c t₁ t₂)  c
------------------cnfIteNeg1  ------------------cnfIteNeg2
       ¬t₁                            ¬t₁


¬(ite c t₁ t₂)  t₁
------------------cnfIteNeg3
        ¬t₂
-/
axiom cnfIteNeg1 {c t₁ t₂ : OptionM Term} :
  holds [mkIte c t₁ t₂, c, mkNot t₁]
axiom cnfIteNeg2 {c t₁ t₂ : OptionM Term} :
  holds [mkIte c t₁ t₂, mkNot c, mkNot t₂]
axiom cnfIteNeg3 {c t₁ t₂ : OptionM Term} :
  holds [mkIte c t₁ t₂, mkNot t₁, mkNot t₂]

-- connecting theory reasoning and clausal reasoning
---------------- Connecting Theory Reasoning and Clausal Reasoning ----------------
axiom thAssume : ∀ {t : OptionM Term}, holds [t] → thHolds t

axiom clAssume : ∀ {t : OptionM Term}, thHolds t → holds [t]

axiom clOr : ∀ {t : OptionM Term} (p : thHolds t), holds (reduceOr t)

axiom scope : ∀ {t₁ t₂ : OptionM Term},
  thHolds t₁ → thHolds t₂ → thHolds (mkOr (mkNot t₁) t₂)

------------------------------------ Holes ------------------------------------

axiom trust : ∀ {c₁ c₂ : clause}, holds c₁ → holds c₂

axiom thTrust : ∀ {t₁ t₂ : OptionM Term}, thHolds t₁ → thHolds t₂

axiom thTrustValid : ∀ {t : OptionM Term}, thHolds t

end rules
