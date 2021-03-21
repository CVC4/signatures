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

def nTh : Nat → clause → Option term := λ a b => join (@List.get? (Option term) a b)
def getLast : clause → Option term := λ c => nTh (c.length - 1) c
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

-- clausal reasoning
def resolveR₀ (n : Option term) (c₁ c₂: clause) : clause :=
  concatCl (List.erase c₁ n) (List.erase c₂ (mkNot n) )

def resolveR₁ (n : Option term) (c₁ c₂: clause) : clause :=
  concatCl (List.erase c₁ (mkNot n)) (List.erase c₂ n)

axiom R0 : ∀ {c₁ c₂ : clause}
  (p₁ : holds c₁) (p₂ : holds c₂) (n : Option term), holds (resolveR₀ n c₁ c₂)

axiom R1 : ∀ {c₁ c₂ : clause}
  (p₁ : holds c₁) (p₂ : holds c₂) (n : Option term), holds (resolveR₁ n c₁ c₂)

axiom factoring : ∀ {c : clause} (p : holds c), holds (removeDuplicates c)

-- connecting theory reasoning and clausal reasoning

axiom clAssume : ∀ {t : Option term}, thHolds t → holds [t]

axiom clOr : ∀ {t : Option term} (p : thHolds t), holds (reduceOr t)

axiom scope : ∀ {t₁ t₂ : Option term}
  (p₁ : thHolds t₁) (p₂ : thHolds t₂), thHolds (mkOr (mkNot t₁) t₂)

end rules
