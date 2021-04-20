import Cdclt.Term
import Cdclt.Boolean
import Cdclt.TermEval

open proof
open proof.sort proof.term
open rules 

namespace proof

namespace term

-- bit-vector sort definition
@[matchPattern] def bvSort := sort.bv


/-
Endian-ness:
We represent a BV as:
MSB ... LSB
(bv 4) representation of decimal 1:
0001
-/


--------------------------------------- Bit Of ---------------------------------------

/- mkBitOf bv n returns the nth element
   of bv if it exists; none otherwise -/
def mkBitOf : Option term → Option term → Option term :=
λ ot₁ ot₂ => 
  ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
  sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
match (s₁, s₂) with
| (bv n, intSort) =>
  match t₂ with
  -- integer index has to be an in-range value
  | val (value.integer i) _ => if (i >= 0 ∧ i < n) then
    (match t₁ with
    -- BV can be a constant
    | val (value.bitvec l) _ =>
        match (List.get? (Int.toNat i) l) with
        | some b => if b then top else bot
        | none => none
    -- or BV can be a var
    | _ => bitOf n t₁ t₂) else none
  | _ => none
| (_, _) => none
#eval mkBitOf (val (value.bitvec [true, false, true, false]) (bv 4)) (val (value.integer 0) intSort)
#eval mkBitOf (val (value.bitvec [true, false, true, false]) (bv 4)) (val (value.integer 1) intSort)
#eval mkBitOf (val (value.bitvec [true, false, true, false]) (bv 4)) (val (value.integer 4) intSort)
#eval mkBitOf (const 21 (bv 4)) (val (value.integer 0) intSort)
#eval mkBitOf (const 21 (bv 4)) (val (value.integer 1) intSort)
#eval mkBitOf (const 21 (bv 4)) (val (value.integer 4) intSort)

/- bitOfN t n
   bit-blasts a BV constant or variable.
   t is the BV term and n is its length.
   bitOfN t n returns a list of length n
   with option terms representing each bit.
-/
def bitOfNAux : term → Nat → Nat → List (Option term)
| t, 0, _ => []
| t, (n₁+1), n₂ => (mkBitOf t (val (value.integer (Int.ofNat (n₂ - n₁ - 1))) intSort)) 
                    :: (bitOfNAux t n₁ n₂)

def bitOfN : term → Nat → List (Option term) :=
  λ t n => bitOfNAux t n n

#eval bitOfN (const 21 (bv 4)) 4
#eval bitOfN (val (value.bitvec [true, true, true, false]) (bv 4)) 4
/- The following bad calls create bad bit-blasted terms
   because the nat argument to bitOfN and the length
   of the BV term don't match.-/
#eval bitOfN (const 21 (bv 3)) 4
#eval bitOfN (val (value.bitvec [true, true, true, false]) (bv 4)) 3


/- bitOfNRev works like bitOfN but in reverse -/
def bitOfNRevAux : term → Nat → List (Option term)
| t, 0 => (mkBitOf t (val (value.integer (Int.ofNat 0)) intSort)) :: []
| t, (n + 1) => (mkBitOf t (val (value.integer (Int.ofNat (n + 1))) intSort))
                    :: (bitOfNRevAux t n)

def bitOfNRev : term → Nat → List (Option term) :=
  λ t n => bitOfNRevAux t (n-1)

#eval bitOfNRev (const 21 (bv 4)) 4
#eval bitOfNRev (val (value.bitvec [true, true, true, false]) (bv 4)) 4
/- The following bad calls create bad bit-blasted terms
   because the nat argument to bitOfN and the length
   of the BV term don't match.-/
#eval bitOfNRev (const 21 (bv 3)) 4
#eval bitOfNRev (val (value.bitvec [true, true, true, false]) (bv 4)) 3


--------------------------------------- Bitwise Operators ---------------------------------------

/-
mkBbT l
Construct a BV term that is a bbT (bit-blasted term) 
of the bools in l
-/
@[matchPattern] def mkBbT (l : List (Option term)) : Option term :=
  mkAppN (bbT (List.length l)) l

#eval mkBbT ([some top, some top, some top, some top])

/-
checkBinaryBV ot₁ ot₂ constr
If ot₁ and ot₂ are BVs of the same length, then
construct a bitwise op of (constr ot₁ ot₂)
-/
def checkBinaryBV : Option term → Option term →
  (Nat → term → term → term) → Option term :=
  λ ot₁ ot₂ constr =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ =>
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
  match (s₁, s₂) with
  | (bv m, bv n) => if (m = n) then (constr m t₁ t₂) else none
  | (_, _) => none

/- Given two lists, and a function that transforms elements of 
   each list into a third type, apply the function index-wise 
   on the lists -/
def zip {α β γ : Type} : List α → List β →  (α → β → γ) → List γ
   | (h₁ :: t₁), (h₂ :: t₂), p => (p h₁ h₂) :: (zip t₁ t₂ p)
   | _, _, _ => []

-- For bitwise ops
/-
bblastBvBitwise ot₁ ot₂ const
checks that ot₁ and ot₂ are BVs of the same length
and returns an Option List of Option terms that
has the bitwise application of const to the
respective elements of ot₁ and ot₂
-/
def bblastBvBitwise (ot₁ ot₂ : Option term)
 (constructor : Option term → Option term → Option term) : Option term :=
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
      match (s₁, s₂) with
      |  (bv m, bv n) =>
          if (m = n) then
            mkBbT (zip (bitOfN t₁ m) (bitOfN t₂ m) constructor)
          else none
      | (_, _) => none


/- -----------
 BV equality
----------- -/

-- If terms are well-typed, construct their BV Eq application
def mkBvEq : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvEq

/-
If terms are well-typed, construct their bit-blasted BV eq
[x₀, x₁, ... , xₙ] = [y₀, y₁, ... , yₙ]
---------------------------------------
       x₀ = y₀ ∧ ... ∧ xₙ = yₙ
-/
def bblastBvEq : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ =>
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ => 
    match (s₁, s₂) with
    |  (bv m, bv n) =>
      if (m = n) then (
            mkAndN (zip (bitOfN t₁ m) (bitOfN t₂ m) mkEq)
      ) else none
    | (_, _) => none
-- 0000 = 1111
#eval bblastBvEq (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvEq (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 010 = 010
#eval bblastBvEq (val (value.bitvec [false, true, false]) (bv 3))
  (val (value.bitvec [false, true, false]) (bv 3))
#eval termEval (bblastBvEq (val (value.bitvec [false, true, false]) (bv 3))
  (val (value.bitvec [false, true, false]) (bv 3)))
-- Using variables
#eval bblastBvEq (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvEq (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvEq rule
axiom bbBvEq : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvEq t₁ t₂) (bblastBvEq t₁ t₂))


/- ------
 BV not
------- -/

-- If term is a BV, construct its BV Not application
def mkBvNot : Option term → Option term :=
  λ ot => ot >>= λ t => sortOf t >>= λ s =>
  match s with
  | bv n => bvNot n t
  | _ => none 

/-
If term is a BV, construct its bit-blasted BV not
¬bv [x₀, x₁, ... , xₙ]
----------------------
 [¬x₀, ¬x₁, ... , ¬x]
-/
def bblastBvNot (ot : Option term) : Option term :=
  ot >>= λ t => sortOf t >>= λ s =>
    match s with
    | bv n => mkBbT (List.map mkNot (bitOfN t n))
    | _ => none
-- ¬0000
#eval bblastBvNot (val (value.bitvec [false, false, false, false]) (bv 4))
#eval termEval (bblastBvNot (val (value.bitvec [false, false, false, false]) (bv 4)))
-- ¬ 1010
#eval bblastBvNot (val (value.bitvec [true, false, true, false]) (bv 4))
#eval termEval (bblastBvNot (val (value.bitvec [true, false, true, false]) (bv 4)))
-- Using variables
#eval bblastBvNot (const 21 (bv 4))

-- Bit-blasting BvNot rule
axiom bbBvNot : ∀ {t : Option term},
  thHolds (mkEq (mkBvNot t) (bblastBvNot t))


/- -------
 BV and
-------- -/

-- If terms are well-typed, construct their BV And application
def mkBvAnd : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvAnd

/-
If terms are well-typed, construct their bit-blasted BV and
[x₀ x₁ ... xₙ] ∧bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ∧ y₀, x₁ ∧ x₂, ... xₙ ∧ yₙ]
-/
def bblastBvAnd : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkAnd

-- 0000 ∧ 1111
#eval bblastBvAnd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvAnd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 0111 ∧ 1101
#eval bblastBvAnd (val (value.bitvec [false, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, false, true]) (bv 4))
#eval termEval (bblastBvAnd (val (value.bitvec [false, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, false, true]) (bv 4)))
-- Using variables
#eval bblastBvAnd (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvAnd rule
axiom bbBvAnd : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvAnd t₁ t₂) (bblastBvAnd t₁ t₂))


/- -----
 BV or
----- -/

-- If terms are well-typed, construct their BV Or application
def mkBvOr : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvOr

/-
If terms are well-typed, construct their bit-blasted BV or
[x₀ x₁ ... xₙ] ∨bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ∨ y₀, x₁ ∨ x₂, ... xₙ ∨ yₙ]
-/
def bblastBvOr : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkOr

-- 0000 ∨ 1111
#eval bblastBvOr (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvOr (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 0101 ∨ 1010
#eval bblastBvOr (val (value.bitvec [false, true, false, true]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4))
#eval termEval (bblastBvOr (val (value.bitvec [false, true, false, true]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4)))
-- Using variables
#eval bblastBvOr (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvOr (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvOr rule
axiom bbBvOr : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvOr t₁ t₂) (bblastBvOr t₁ t₂))


/- ------
 BV Xor
------ -/

-- If terms are well-typed, construct their BV Xor application
def mkBvXor : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvXor

/-
If terms are well-typed, construct their bit-blasted BV xor
[x₀ x₁ ... xₙ] ⊕bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ⊕ y₀, x₁ ⊕ x₂, ... xₙ ⊕ yₙ]
-/
def bblastBvXor : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkXor

-- 0000 ⊕ 1111
#eval bblastBvXor (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvXor (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 1111 ⊕ 1111
#eval bblastBvXor (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvXor (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- Using variables
#eval bblastBvXor (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvXor (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvXor rule
axiom bbBvXor : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvXor t₁ t₂) (bblastBvXor t₁ t₂))


/- -------
 BV Nand
------- -/

-- If terms are well-typed, construct their BV Nand application
def mkBvNand : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvNand

/-
If terms are well-typed, construct their bit-blasted BV Nand
[x₀ x₁ ... xₙ] ¬∧bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ¬∧ y₀, x₁ ¬∧ x₂, ... xₙ ¬∧ yₙ]
-/
def bblastBvNand : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkNand

-- 0000 ¬∧ 1111
#eval bblastBvNand (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvNand (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 0111 ¬∧ 1101
#eval bblastBvNand (val (value.bitvec [false, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, false, true]) (bv 4))
#eval termEval (bblastBvNand (val (value.bitvec [false, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, false, true]) (bv 4)))
-- Using variables
#eval bblastBvNand (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvNand (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvNand rule
axiom bbBvNand : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvNand t₁ t₂) (bblastBvNand t₁ t₂))


/- -------
 BV Nor
------- -/

-- If terms are well-typed, construct their BV Nor application
def mkBvNor : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvNor

/-
If terms are well-typed, construct their bit-blasted BV Nand
[x₀ x₁ ... xₙ] ¬∨bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ¬∨ y₀, x₁ ¬∨ x₂, ... xₙ ¬∨ yₙ]
-/
def bblastBvNor : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkNor

-- 0000 ¬∨ 1111
#eval bblastBvNor (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvNor (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 0111 ¬∨ 1101
#eval bblastBvNor (val (value.bitvec [false, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, false, true]) (bv 4))
#eval termEval (bblastBvNor (val (value.bitvec [false, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, false, true]) (bv 4)))
-- Using variables
#eval bblastBvNor (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvNor (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvNor rule
axiom bbBvNor : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvNor t₁ t₂) (bblastBvNor t₁ t₂))


/- -------
 BV Xnor
------- -/

-- If terms are well-typed, construct their BV Xnor application
def mkBvXnor : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvXnor

/-
If terms are well-typed, construct their bit-blasted BV Nand
[x₀ x₁ ... xₙ] ¬⊕ [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ↔ y₀, x₁ ↔ x₂, ... xₙ ↔ yₙ]
-/
def bblastBvXnor : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkIff

-- 1111 ¬⊕ 1111
#eval bblastBvXnor (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvXnor (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 0111 ¬⊕ 1101
#eval bblastBvXnor (val (value.bitvec [false, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, false, true]) (bv 4))
#eval termEval (bblastBvXnor (val (value.bitvec [false, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, false, true]) (bv 4)))
-- Using variables
#eval bblastBvNor (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvNor (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvNor rule
axiom bbBvXnor : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvXnor t₁ t₂) (bblastBvXnor t₁ t₂))


--------------------------------------- Comparison Operators ---------------------------------------

/- ------
BV Comp
------ -/

-- If terms are well-typed, construct their BV Comp application
def mkBvComp : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvComp

/-
If terms are well-typed, construct their bit-blasted 
bv comp
bvComp [x₀, x₁, ... , xₙ] [y₀, y₁, ... , yₙ] = 
  ite ((x₀ = y₀) ∧ (x₁ = x₂) ∧ ... ∧ (xₙ = yₙ)) [true] [false]
-/
def bblastBvComp : Option term → Option term → Option term :=
  λ ot₁ ot₂ => mkIte (bblastBvEq ot₁ ot₂) (mkBbT [some top]) (mkBbT [some bot])

-- bvComp 0000 1111
#eval bblastBvComp (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvComp (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- bvComp 0010 0010
#eval bblastBvComp (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.bitvec [false, false, true, false]) (bv 4))
#eval termEval (bblastBvComp (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.bitvec [false, false, true, false]) (bv 4)))
-- Using variables
#eval bblastBvComp (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvComp (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvComp rule
axiom bbBvComp : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvComp t₁ t₂) (bblastBvComp t₁ t₂))


/- -------------------
 BV unsigned less than
--------------------- -/

-- If terms are well-typed, construct their BV Ult application
def mkBvUlt : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUlt

/-
[x₀, x₁, ... , xₙ] <ᵤ [y₀, y₁, ... , yₙ] = 
  (¬x₀ ∧ y₀) ∨ ((x₀ ↔ y₀) ∧ ([x₁, ... , xₙ] <ᵤ [y₁, ... , yₙ]))
-/
def boolListUlt : List (Option term) → List (Option term) → Option term
| [h₁], [h₂] => mkAnd (mkNot h₁) h₂
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd (mkNot h₁) h₂) (mkAnd (mkEq h₁ h₂) (boolListUlt t₁ t₂)))
| _, _ => none

/-
If terms are well-typed, construct their bit-blasted 
unsigned less than comparison
-/
def bblastBvUlt : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListUlt (bitOfN t₁ m) (bitOfN t₂ m)
      ) else none
    | (_, _) => none

-- 0000 <ᵤ 1111
#eval bblastBvUlt (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvUlt (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 0010 <ᵤ 0011
#eval bblastBvUlt (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.bitvec [false, false, true, true]) (bv 4))
#eval termEval (bblastBvUlt (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.bitvec [false, false, true, true]) (bv 4)))
-- 10 <ᵤ 01
#eval bblastBvUlt (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2))
#eval termEval (bblastBvUlt (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2)))
-- Using variables
#eval bblastBvUlt (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvUlt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUlt rule
axiom bbBvUlt : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvUlt t₁ t₂) (bblastBvUlt t₁ t₂))


/- -----------------------------------
 BV unsigned less than or equal to
----------------------------------- -/

-- If terms are well-typed, construct their BV Ule application
def mkBvUle : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUle

/-
If terms are well-typed, construct their bit-blasted 
unsigned less than or equal to comparison
x ≤ᵤ y = (x <ᵤ y) ∨ (x = y)
-/
def bblastBvUle : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            mkOr (boolListUlt (bitOfN t₁ m) (bitOfN t₂ m)) 
                 (mkAndN (zip (bitOfN t₁ m) (bitOfN t₂ m) mkEq))
      ) else none
    | (_, _) => none

-- 0000 ≤ᵤ 1111
#eval bblastBvUle (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvUle (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 0010 ≤ᵤ 0010
#eval bblastBvUle (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.bitvec [false, false, true, false]) (bv 4))
#eval termEval (bblastBvUle (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.bitvec [false, false, true, false]) (bv 4)))
-- 10 ≤ᵤ 01
#eval bblastBvUle (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2))
#eval termEval (bblastBvUle (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2)))
-- Using variables
#eval bblastBvUle (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvUlt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUle rule
axiom bbBvUle : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvUle t₁ t₂) (bblastBvUle t₁ t₂))


/- ----------------------
 BV unsigned greater than
----------------------- -/

-- If terms are well-typed, construct their BV Ugt application
def mkBvUgt : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUgt

/-
[x₀, x₁, ... , xₙ] >ᵤ [y₀, y₁, ... , yₙ] = 
  (x₀ ∧ ¬y₀) ∨ ((x₀ ↔ y₀) ∧ ([x₁, ... , xₙ] >ᵤ [y₁, ... , yₙ]))
-/
def boolListUgt : List (Option term) → List (Option term) → Option term
| [h₁], [h₂] => mkAnd h₁ (mkNot h₂)
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd h₁ (mkNot h₂)) (mkAnd (mkEq h₁ h₂) (boolListUgt t₁ t₂)))
| _, _ => none

/-
If terms are well-typed, construct their bit-blasted 
unsigned greater than comparison
-/
def bblastBvUgt : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListUgt (bitOfN t₁ m) (bitOfN t₂ m)
      ) else none
    | (_, _) => none

-- 1111 >ᵤ 0000
#eval bblastBvUgt (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval termEval (bblastBvUgt (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4)))
-- 0011 >ᵤ 0010
#eval bblastBvUgt (val (value.bitvec [false, false, true, true]) (bv 4))
  (val (value.bitvec [false, false, true, false]) (bv 4))
#eval termEval (bblastBvUgt (val (value.bitvec [false, false, true, true]) (bv 4))
  (val (value.bitvec [false, false, true, false]) (bv 4)))
-- 01 >ᵤ 10
#eval bblastBvUgt (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2))
#eval termEval (bblastBvUgt (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2)))
-- Using variables
#eval bblastBvUgt (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvUgt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUgt rule
axiom bbBvUgt : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvUgt t₁ t₂) (bblastBvUgt t₁ t₂))


/- ------------------------------------
 BV unsigned greater than pr equal to
------------------------------------- -/

-- If terms are well-typed, construct their BV Uge application
def mkBvUge : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUge

/-
If terms are well-typed, construct their bit-blasted 
unsigned greater than or equal to comparison
x ≥ᵤ y = (x >ᵤ y) ∨ (x = y)
-/
def bblastBvUge : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            mkOr (boolListUgt (bitOfN t₁ m) (bitOfN t₂ m)) 
                 (mkAndN (zip (bitOfN t₁ m) (bitOfN t₂ m) mkEq))
      ) else none
    | (_, _) => none


-- 1111 ≥ᵤ 0000
#eval bblastBvUge (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval termEval (bblastBvUge (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4)))
-- 0011 ≥ᵤ 0011
#eval bblastBvUge (val (value.bitvec [false, false, true, true]) (bv 4))
  (val (value.bitvec [false, false, true, true]) (bv 4))
#eval termEval (bblastBvUge (val (value.bitvec [false, false, true, true]) (bv 4))
  (val (value.bitvec [false, false, true, true]) (bv 4)))
-- 01 ≥ᵤ 10
#eval bblastBvUge (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2))
#eval termEval (bblastBvUge (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2)))
-- Using variables
#eval bblastBvUge (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvUgt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUge rule
axiom bbBvUge : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvUge t₁ t₂) (bblastBvUge t₁ t₂))


/- -------------------
 BV signed less than
------------------- -/

-- If terms are well-typed, construct their BV Slt application
def mkBvSlt : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSlt

/-
[x₀, x₁, ... , xₙ] <ₛ [y₀, y₁, ... , yₙ] = 
  (x₀ ∧ ¬y₀) ∨ (x₀ = y₀ ∧ ([x₁, ..., xₙ] <ᵤ [y₁, ..., yₙ]))
-/
def boolListSlt : List (Option term) → List (Option term) → Option term
| [h₁], [h₂] => (mkAnd h₁ (mkNot h₂))
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd h₁ (mkNot h₂)) (mkAnd (mkEq h₁ h₂) (boolListUlt t₁ t₂)))
| _, _ => none

/-
If terms are well-typed, construct their bit-blasted 
signed less than comparison
-/
def bblastBvSlt : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListSlt (bitOfN t₁ m) (bitOfN t₂ m)
      ) else none
    | (_, _) => none

-- 1111 <ₛ 0000
#eval bblastBvSlt (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval termEval (bblastBvSlt (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4)))
-- 1010 <ₛ 1011
#eval bblastBvSlt (val (value.bitvec [true, false, true, false]) (bv 4))
  (val (value.bitvec [true, false, true, true]) (bv 4))
#eval termEval (bblastBvSlt (val (value.bitvec [true, false, true, false]) (bv 4))
  (val (value.bitvec [true, false, true, true]) (bv 4)))
-- 01 <ₛ 10
#eval bblastBvSlt (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2))
#eval termEval (bblastBvSlt (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2)))
-- Using variables
#eval bblastBvSlt (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvSlt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUgt rule
axiom bbBvSlt : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvSlt t₁ t₂) (bblastBvSlt t₁ t₂))


/- -------------------------------
 BV signed less than or equal to
-------------------------------- -/

-- If terms are well-typed, construct their BV Sle application
def mkBvSle : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSle

/-
If terms are well-typed, construct their bit-blasted 
signed less than or equal to comparison
x ≤ₛ y = (x <ₛ y) ∨ (x = y)
-/
def bblastBvSle : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            mkOr (boolListSlt (bitOfN t₁ m) (bitOfN t₂ m)) 
                 (mkAndN (zip (bitOfN t₁ m) (bitOfN t₂ m) mkEq))
      ) else none
    | (_, _) => none

-- 1111 ≤ₛ 0000
#eval bblastBvSle (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval termEval (bblastBvSle (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4)))
-- 1010 ≤ₛ 1010
#eval bblastBvSle (val (value.bitvec [true, false, true, false]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4))
#eval termEval (bblastBvSle (val (value.bitvec [true, false, true, false]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4)))
-- 01 ≤ₛ 10
#eval bblastBvSle (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2))
#eval termEval (bblastBvSle (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2)))
-- Using variables
#eval bblastBvSle (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvSle (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvSle rule
axiom bbBvSle : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvSle t₁ t₂) (bblastBvSle t₁ t₂))


/- ----------------------
 BV signed greater than
----------------------- -/

-- If terms are well-typed, construct their BV Sgt application
def mkBvSgt : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSgt

/-
[x₀, x₁, ... , xₙ] >ₛ [y₀, y₁, ... , yₙ] = 
  (¬x₀ ∧ y₀) ∨ (x₀ = y₀ ∧ ([x₁, ..., xₙ] >ᵤ [y₁, ..., yₙ]))
-/
def boolListSgt : List (Option term) → List (Option term) → Option term
| [h₁], [h₂] => (mkAnd (mkNot h₁) h₂)
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd (mkNot h₁) h₂) (mkAnd (mkEq h₁ h₂) (boolListUgt t₁ t₂)))
| _, _ => none

/-
If terms are well-typed, construct their bit-blasted 
signed greater than comparison
-/
def bblastBvSgt : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListSgt (bitOfN t₁ m) (bitOfN t₂ m)
      ) else none
    | (_, _) => none

-- 0000 >ₛ 1111
#eval bblastBvSgt (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvSgt (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 1011 >ₛ 1010
#eval bblastBvSgt (val (value.bitvec [true, false, true, true]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4))
#eval termEval (bblastBvSgt (val (value.bitvec [true, false, true, true]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4)))
-- 10 >ₛ 01
#eval bblastBvSgt (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2))
#eval termEval (bblastBvSgt (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2)))
-- Using variables
#eval bblastBvSgt (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvSgt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvSgt rule
axiom bbBvSgt : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvSgt t₁ t₂) (bblastBvSgt t₁ t₂))


/- ----------------------------------
 BV signed greater than or equal to
----------------------------------- -/

-- If terms are well-typed, construct their BV Sge application
def mkBvSge : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSge

/-
If terms are well-typed, construct their bit-blasted 
signed greater than or equal to comparison
x ≥ₛ y = (x >ₛ y) ∨ (x = y)
-/
def bblastBvSge : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            mkOr (boolListSgt (bitOfN t₁ m) (bitOfN t₂ m)) 
                 (mkAndN (zip (bitOfN t₁ m) (bitOfN t₂ m) mkEq))
      ) else none
    | (_, _) => none

-- 0000 ≥ₛ 1111
#eval bblastBvSge (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvSge (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 1011 ≥ₛ 1010
#eval bblastBvSge (val (value.bitvec [true, false, true, true]) (bv 4))
  (val (value.bitvec [true, false, true, true]) (bv 4))
#eval termEval (bblastBvSge (val (value.bitvec [true, false, true, true]) (bv 4))
  (val (value.bitvec [true, false, true, true]) (bv 4)))
-- 10 ≥ₛ 01
#eval bblastBvSge (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2))
#eval termEval (bblastBvSge (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2)))
-- Using variables
#eval bblastBvSge (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvSge (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvSge rule
axiom bbBvSge : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvSge t₁ t₂) (bblastBvSge t₁ t₂))


--------------------------------------- Arithmetic Operators ---------------------------------------

/- -----------
 BV addition
----------- -/

-- If terms are well-typed, construct their BV plus application
def mkBvAdd : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvAdd

/-
After reversing the BVs to add:
    [x₀ x₁ ... xₙ] +bv [y₀ y₁ ... yₙ]
-----------------------------------------
[(x₀ ⊕ y₀) ⊕ car₀, ..., (xₙ ⊕ yₙ) ⊕ carₙ]
where car₀ = ⊥
      car_{i+1} = (xᵢ ∧ yᵢ) ∨ ((xᵢ ⊕ yᵢ) ∧ carᵢ)
Then reverse again
-/
def bitAdder : Option term → Option term → Option term → Option term × Option term
| x, y, carry => (mkXor (mkXor x y) carry, 
  mkOr (mkAnd x y) (mkAnd (mkXor x y) carry))
#eval (bitAdder top top top)
#eval termEval (bitAdder top top top).1
#eval termEval (bitAdder top top top).2
def boolListAddAux : Option term → List (Option term) → List (Option term) → List (Option term)
| c, (h₁ :: t₁), (h₂ :: t₂) => (bitAdder h₁ h₂ c).1 :: (boolListAddAux (bitAdder h₁ h₂ c).2 t₁ t₂)
| c, [], [] => []
| _, _, _ => []
def boolListAdd : List (Option term) → List (Option term) → Option term
| l₁, l₂ => mkBbT (List.reverse (boolListAddAux bot l₁ l₂))

-- If terms are well-typed, construct their bit-blasted BV add
def bblastBvAdd : Option term → Option term → Option term :=
  λ ot₁ ot₂ => 
  ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListAdd (bitOfNRev t₁ m) (bitOfNRev t₂ m)
      ) else none
    | (_, _) => none

-- 0000 + 1111
#eval bblastBvAdd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvAdd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 1111 + 1111
#eval bblastBvAdd (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvAdd (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 0101 + 1010
#eval bblastBvAdd (val (value.bitvec [false, true, false, true]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4))
#eval termEval (bblastBvAdd (val (value.bitvec [false, true, false, true]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4)))
-- 1111 + 0001
#eval bblastBvAdd (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, true]) (bv 4))
#eval termEval (bblastBvAdd (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, true]) (bv 4)))
-- Using variables
#eval bblastBvAdd (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvAdd (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvAdd rule
axiom bbBvAdd : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvAdd t₁ t₂) (bblastBvAdd t₁ t₂))


/- -----------
 BV Negation
------------ -/

-- If term is a BV, construct its BV Neg application
def mkBvNeg : Option term → Option term :=
  λ ot => ot >>= λ t => sortOf t >>= λ s =>
  match s with
  | bv n => bvNot n t
  | _ => none 

/- genRevOne n generates the list 
   [(some top) (some bot) ... (some bot)]
   where there are n-1 (some bot) elements -/
def genZeros : Nat → List (Option term)
| 0 => []
| n + 1 => (some bot) :: genZeros n
def genRevOne : Nat → List (Option term) :=
  λ n => (some top) :: genZeros (n - 1)
#eval genZeros 3
#eval genRevOne 4

/-
If term is well-typed, construct its bit-blasted BV neg
-bv x = ((¬bv x) +bv 1)
          OR
bvneg x = bvadd (bvnot x) 1
-/
def bblastBvNeg : Option term → Option term :=
  λ ot => 
  ot >>= λ t => sortOf t >>= λ s => 
    match s with
    |  bv m => boolListAdd (List.map mkNot (bitOfNRev t m)) (genRevOne m)
    | _ => some bot
-- -0000
#eval bblastBvNeg (val (value.bitvec [false, false, false, false]) (bv 4))
#eval termEval (bblastBvNeg (val (value.bitvec [false, false, false, false]) (bv 4)))
-- -0001
#eval bblastBvNeg (val (value.bitvec [false, false, false, true]) (bv 4))
#eval termEval (bblastBvNeg (val (value.bitvec [false, false, false, true]) (bv 4)))
-- -1111
#eval bblastBvNeg (val (value.bitvec [true, true, true, true]) (bv 4))
#eval termEval (bblastBvNeg (val (value.bitvec [true, true, true, true]) (bv 4)))
-- Using variables
#eval bblastBvNeg (const 21 (bv 4))

-- Bit-blasting BvNeg rule
axiom bbBvNeg : ∀ {t : Option term},
  thHolds (mkEq (mkBvNeg t) (bblastBvNeg t))


/- --------------
 BV Subtraction
--------------- -/

-- If terms are well-typed, construct their BV minus application
def mkBvSub : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSub

/-
If term is well-typed, construct its bit-blasted BV sub
x -bv y = +(x, ¬y, 1)
          OR
bvneg x = bvadd (x, bvnot y, 1)
-/
def bblastBvSub : Option term → Option term → Option term :=
  λ ot₁ ot₂ => 
  ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            mkBbT (List.reverse (boolListAddAux 
              top 
              (bitOfNRev t₁ m) 
              ((List.map mkNot (bitOfNRev t₂ m)))))
      ) else none
    | (_, _) => none

-- 1111-0000
#eval bblastBvSub (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval termEval (bblastBvSub (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4)))
-- 0000-0010
#eval bblastBvSub (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [false, false, true, false]) (bv 4))
#eval termEval (bblastBvSub (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [false, false, true, false]) (bv 4)))
-- Using variables
#eval bblastBvSub (const 21 (bv 4)) (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvSub (const 21 (bv 4)) (const 22 (bv 4))
-- Bit-blasting BvNeg rule
axiom bbBvSub : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvSub t₁ t₂) (bblastBvSub t₁ t₂))


---------------------------- BV Length Manipulating Operators ----------------------------

/- -----------
 BV Extraction
------------ -/

-- If terms are well-typed, construct their BV Extraction application
def mkBvExtract : Option term → Option term → Option term → Option term :=
  λ ot oi oj => 
    ot >>= λ t => sortOf t >>= λ s =>
    oi >>= λ i => sortOf i >>= λ si =>
    oj >>= λ j => sortOf i >>= λ sj =>
  match s, si, sj with
  | bv n, intSort, intSort =>
    match i, j with
    | (val (value.integer i₁) intSort), (val (value.integer j₁) intSort) =>
      if (0 ≤ j₁ ∧ j₁ ≤ i₁ ∧ i₁ < n) then
        (bvExtract n (Int.toNat i₁) (Int.toNat j₁) t i j)
      else
        none
    | _, _ => none
  | _, _, _ => none

def removeLastN : List α → Nat → List α
| l, 0 => l
| l, n+1 => removeLastN (List.dropLast l) n

/-
If terms are well-typed, construct their bit-blasted BV extraction
[x₀ ... xₙ]   0 ≤ j ≤ i < n
----------------------------
       [xⱼ ... xᵢ]
-/
def bblastBvExtract : Option term → Option term → Option term → Option term :=
  λ ot oi oj => 
    ot >>= λ t => sortOf t >>= λ s =>
    oi >>= λ i => sortOf i >>= λ si =>
    oj >>= λ j => sortOf i >>= λ sj =>
  match s, si, sj with
  | bv n, intSort, intSort =>
    match i, j with
    | (val (value.integer i₁) intSort), (val (value.integer j₁) intSort) =>
      if (0 ≤ j₁ ∧ j₁ ≤ i₁ ∧ i₁ < n) then 
         mkBbT (removeLastN (List.drop (n - (Int.toNat i₁) - 1) (bitOfN t n)) (Int.toNat j₁))
      else
        none
    | _, _ => none
  | _, _, _ => none
#eval bblastBvExtract (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.integer 3) intSort) (val (value.integer 2) intSort)
#eval bblastBvExtract (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.integer 1) intSort) (val (value.integer 1) intSort)
#eval bblastBvExtract (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.integer 3) intSort) (val (value.integer 0) intSort)
-- Bad call
#eval bblastBvExtract (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.integer 1) intSort) (val (value.integer 2) intSort)
-- Using variables
#eval bblastBvExtract (const 21 (bv 4)) (val (value.integer 2) intSort) 
  (val (value.integer 1) intSort)

-- Bit-blasting BvExtract rule
axiom bbBvExtract : ∀ {t₁ t₂ t₃ : Option term},
  thHolds (mkEq (mkBvExtract t₁ t₂ t₃) (bblastBvExtract t₁ t₂ t₃))


/- ---------------
 BV Concatenation
---------------- -/

-- If terms are well-typed, construct their BV concat application
def mkBvConcat : Option term → Option term → Option term :=
  λ ot₁ ot₂ => ot₁ >>= λ t₁ => sortOf t₁ >>= λ s₁ =>
               ot₂ >>= λ t₂ => sortOf t₂ >>= λ s₂ =>
  match s₁, s₂ with
  | bv m, bv n => bvConcat m n t₁ t₂
  | _, _ => none

/-
If terms are BVs construct their bit-blasted BV concat
[x₀ x₁ ... xₙ] ++ [y₀ y₁ ... yₙ]
---------------------------------
   [y₀ y₁ ... yₙ x₀ x₁ ... xₙ]
-/
def bblastBvConcat : Option term → Option term → Option term :=
  λ ot₁ ot₂ => ot₁ >>= λ t₁ => sortOf t₁ >>= λ s₁ => 
               ot₂ >>= λ t₂ => sortOf t₂ >>= λ s₂ => 
    match s₁, s₂ with
    | bv m, bv n => mkBbT (List.append (bitOfN t₂ n) (bitOfN t₁ m))
    | _, _ => none
-- 0000 ++ 1111
#eval bblastBvConcat (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
-- 11 + 111
#eval bblastBvConcat (val (value.bitvec [true, true]) (bv 2))
  (val (value.bitvec [true, true, true]) (bv 3))
-- 1 + 110
#eval bblastBvConcat (val (value.bitvec [true]) (bv 1))
  (val (value.bitvec [true, true, false]) (bv 3))
-- Using variables
#eval bblastBvConcat (const 21 (bv 2))
  (val (value.bitvec [false, false]) (bv 2))
#eval bblastBvConcat (const 21 (bv 2)) (const 22 (bv 2))

-- Bit-blasting BvConcat rule
axiom bbBvConcat : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvConcat t₁ t₂) (bblastBvAdd t₁ t₂))


/- ---------------
 BV Zero Extend
---------------- -/

-- If terms are well-typed, construct their BV zero extend application
def mkBvZeroExt : Option term → Option term → Option term :=
  λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
             oi >>= λ i => sortOf i >>= λ si =>
  match s, si with
  | bv n, intSort => 
    match i with
    | val (value.integer i₁) intSort => bvZeroExt n (Int.toNat i₁) t i
    | _ => none
  | _, _ => none

/-
If terms are well-typed, construct their bit-blasted BV zero extend
     [x₀ x₁ ... xₙ]    i
-----------------------------
  [0₁ ... 0ᵢ x₀ x₁ ... xₙ]
-/
def bblastZeroExt : Option term → Option term → Option term :=
  λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
             oi >>= λ i => sortOf i >>= λ si =>
  match s, si with
  | bv n, intSort => 
    match i with
    | val (value.integer i₁) intSort => 
      mkBbT (List.append (List.replicate (Int.toNat i₁) (some bot)) (bitOfN t n))
    | _ => none
  | _, _ => none
#eval bblastZeroExt (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.integer 2) intSort)
#eval bblastZeroExt (val (value.bitvec [true, false]) (bv 2))
  (val (value.integer 0) intSort)
-- Using variables
#eval bblastZeroExt (const 21 (bv 4))  (val (value.integer 2) intSort)

-- Bit-blasting BvZeroExt rule
axiom bbBvZeroExt : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvZeroExt t₁ t₂) (bblastZeroExt t₁ t₂))


/- ---------------
 BV Sign Extend
---------------- -/

-- If terms are well-typed, construct their BV sign extend application
def mkBvSignExt : Option term → Option term → Option term :=
  λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
             oi >>= λ i => sortOf i >>= λ si =>
  match s, si with
  | bv n, intSort => 
    match i with
    | val (value.integer i₁) intSort => bvSignExt n (Int.toNat i₁) t i
    | _ => none
  | _, _ => none

def hd : List α → Option α
| h :: t => some h
| [] => none

/-
If terms are well-typed, construct their bit-blasted BV sign extend
     [x₀ x₁ ... xₙ]    i
-----------------------------
  [x₀ ... x₀ x₀ x₁ ... xₙ]
where i x₀'s are prefixed to x
-/
def bblastSignExt : Option term → Option term → Option term :=
  λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
             oi >>= λ i => sortOf i >>= λ si =>
  match s, si with
  | bv n, intSort => 
    match i with
    | val (value.integer i₁) intSort =>
      match hd (bitOfN t n) with
      | some sign => mkBbT (List.append (List.replicate (Int.toNat i₁) sign) (bitOfN t n))
      | none => none
    | _ => none
  | _, _ => none
#eval bblastSignExt (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.integer 2) intSort)
#eval bblastSignExt (val (value.bitvec [false, true, true, true]) (bv 4))
  (val (value.integer 2) intSort)
#eval bblastSignExt (val (value.bitvec [true, false]) (bv 2))
  (val (value.integer 0) intSort)
-- Using variables
#eval bblastSignExt (const 21 (bv 4)) (val (value.integer 2) intSort)

-- Bit-blasting BvSignExt rule
axiom bbBvSignExt : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvSignExt t₁ t₂) (bblastSignExt t₁ t₂))


end term

end proof