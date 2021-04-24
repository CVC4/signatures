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
We represent a BV value as:
MSB ... LSB
(bv 4) representation of decimal 1:
0001 ([false, false, false, true])
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
        match (List.get? (Int.toNat (n - i - 1)) l) with
        | some b => if b then top else bot
        | none => none
    -- or BV can be a var
    | _ => bitOf n t₁ t₂) else none
  | _ => none
| (_, _) => none
#eval mkBitOf (mkValBV [true, false, true, false]) (mkValInt 0)
#eval mkBitOf (mkValBV [true, false, true, false]) (mkValInt 1)
#eval mkBitOf (mkValBV [true, false, true, false]) (mkValInt 4)
#eval mkBitOf (const 21 (bv 4)) (mkValInt 0)
#eval mkBitOf (const 21 (bv 4)) (mkValInt 1)
#eval mkBitOf (const 21 (bv 4)) (mkValInt 4)

/- bitOfN t n
   bit-blasts a BV constant or variable.
   t is the BV term and n is its length.
   bitOfN t n returns a list of length n
   with option terms representing each bit.
-/
def bitOfNAux : term → Nat → List (Option term)
| t, 0 => (mkBitOf t (mkValInt 0)) :: []
| t, (n + 1) => (mkBitOf t (mkValInt (Int.ofNat (n + 1))))
                    :: (bitOfNAux t n)

def bitOfN : term → Nat → List (Option term) :=
  λ t n => bitOfNAux t (n-1)

#eval bitOfN (const 21 (bv 4)) 4
#eval bitOfN (mkValBV [true, true, true, false]) 4
/- The following bad calls create bad bit-blasted terms
   because the nat argument to bitOfN and the length
   of the BV term don't match.-/
#eval bitOfN (const 21 (bv 3)) 4
#eval bitOfN (mkValBV [true, true, true, false]) 3


/- bitOfNRev works like bitOfN but in reverse -/
def bitOfNRevAux : term → Nat → Nat → List (Option term)
| t, 0, _ => []
| t, (n₁+1), n₂ => (mkBitOf t (mkValInt (Int.ofNat (n₂ - n₁ - 1)))) 
                    :: (bitOfNRevAux t n₁ n₂)

def bitOfNRev : term → Nat → List (Option term) :=
  λ t n => bitOfNRevAux t n n

#eval bitOfNRev (const 21 (bv 4)) 4
#eval bitOfNRev (mkValBV [true, true, true, false]) 4
/- The following bad calls create bad bit-blasted terms
   because the nat argument to bitOfN and the length
   of the BV term don't match.-/
#eval bitOfNRev (const 21 (bv 3)) 4
#eval bitOfNRev (mkValBV [true, true, true, false]) 3


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
  [xₙ ... x₁ x₀] = [yₙ ... y₀ y₁]
------------------------------------
    xₙ = yₙ ∧ ... ∧ x₀ = y₀
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
#eval bblastBvEq (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvEq (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 010 = 010
#eval bblastBvEq (mkValBV [false, true, true])
  (mkValBV [false, true, true])
#eval termEval (bblastBvEq (mkValBV [false, true, true])
  (mkValBV [false, true, true]))
-- Using variables
#eval bblastBvEq (const 21 (bv 4))
  (mkValBV [false, false, false, true])
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
  ¬bv [xₙ ... x₁ x₀]
----------------------
  [¬xₙ ...  ¬x₁ ¬x₀]
-/
def bblastBvNot (ot : Option term) : Option term :=
  ot >>= λ t => sortOf t >>= λ s =>
    match s with
    | bv n => mkBbT (List.map mkNot (bitOfN t n))
    | _ => none
-- ¬0000
#eval bblastBvNot (mkValBV [false, false, false, false])
#eval termEval (bblastBvNot (mkValBV [false, false, false, false]))
-- ¬ 1010
#eval bblastBvNot (mkValBV [true, false, true, false])
#eval termEval (bblastBvNot (mkValBV [true, false, true, false]))
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
    [xₙ ... x₁ x₀] ∧bv [yₙ ... y₀ y₁]
-----------------------------------------
    [xₙ ∧ yₙ ... x₁ ∧ y₁  x₀ ∧ y₀]
-/
def bblastBvAnd : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkAnd

-- 0000 ∧ 1111
#eval bblastBvAnd (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvAnd (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0111 ∧ 1101
#eval bblastBvAnd (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true])
#eval termEval (bblastBvAnd (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true]))
-- Using variables
#eval bblastBvAnd (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
   [xₙ ... x₁ x₀] ∨bv [yₙ ... y₀ y₁]
-----------------------------------------
     [xₙ ∨ yₙ ... x₁ ∨ y₁  x₀ ∨ y₀]
-/
def bblastBvOr : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkOr

-- 0000 ∨ 1111
#eval bblastBvOr (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvOr (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0101 ∨ 1010
#eval bblastBvOr (mkValBV [false, true, false, true])
  (mkValBV [true, false, true, false])
#eval termEval (bblastBvOr (mkValBV [false, true, false, true])
  (mkValBV [true, false, true, false]))
-- Using variables
#eval bblastBvOr (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
   [xₙ ... x₁ x₀] ⊕bv [yₙ ... y₀ y₁]
-----------------------------------------
     [xₙ ⊕ yₙ ... x₁ ⊕ y₁  x₀ ⊕ y₀]
-/
def bblastBvXor : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkXor

-- 0000 ⊕ 1111
#eval bblastBvXor (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvXor (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 1111 ⊕ 1111
#eval bblastBvXor (mkValBV [true, true, true, true])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvXor (mkValBV [true, true, true, true])
  (mkValBV [true, true, true, true]))
-- Using variables
#eval bblastBvXor (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
    [xₙ ... x₁ x₀] ¬∧bv [yₙ ... y₀ y₁]
-------------------------------------------
    [xₙ ¬∧ yₙ ... x₁ ¬∧ y₁  x₀ ¬∧ y₀]
-/
def bblastBvNand : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkNand

-- 0000 ¬∧ 1111
#eval bblastBvNand (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvNand (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0111 ¬∧ 1101
#eval bblastBvNand (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true])
#eval termEval (bblastBvNand (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true]))
-- Using variables
#eval bblastBvNand (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
    [xₙ ... x₁ x₀] ¬∨bv [yₙ ... y₀ y₁]
-------------------------------------------
    [xₙ ¬∨ yₙ ... x₁ ¬∨ y₁  x₀ ¬∨ y₀]
-/
def bblastBvNor : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkNor

-- 0000 ¬∨ 1111
#eval bblastBvNor (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvNor (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0111 ¬∨ 1101
#eval bblastBvNor (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true])
#eval termEval (bblastBvNor (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true]))
-- Using variables
#eval bblastBvNor (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
    [xₙ ... x₁ x₀] ¬⊕bv [yₙ ... y₀ y₁]
-------------------------------------------
      [xₙ ↔ yₙ ... x₁ ↔ y₁  x₀ ↔ y₀]
-/
def bblastBvXnor : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkIff

-- 1111 ¬⊕ 1111
#eval bblastBvXnor (mkValBV [true, true, true, true])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvXnor (mkValBV [true, true, true, true])
  (mkValBV [true, true, true, true]))
-- 0111 ¬⊕ 1101
#eval bblastBvXnor (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true])
#eval termEval (bblastBvXnor (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true]))
-- Using variables
#eval bblastBvNor (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
          bvComp [xₙ ... x₁ x₀] [yₙ ... y₀ y₁]
----------------------------------------------------------------
  ite ((xₙ = yₙ) ∧ ... ∧ (x₁ = x₂) ∧ (x₀ = y₀)) [true] [false]
-/
def bblastBvComp : Option term → Option term → Option term :=
  λ ot₁ ot₂ => mkIte (bblastBvEq ot₁ ot₂) (mkBbT [some top]) (mkBbT [some bot])

-- bvComp 0000 1111
#eval bblastBvComp (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvComp (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- bvComp 0010 0010
#eval bblastBvComp (mkValBV [false, false, true, false])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvComp (mkValBV [false, false, true, false])
  (mkValBV [false, false, true, false]))
-- Using variables
#eval bblastBvComp (const 21 (bv 4)) 
  (mkValBV [true, false, false, false])
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
                  [xₙ ... x₁ x₀] <ᵤ [yₙ ... y₀ y₁]
-------------------------------------------------------------------------
    (¬xₙ ∧ yₙ) ∨ ((xₙ ↔ yₙ) ∧ ([x_{n-1} ... x₀] <ᵤ [y_{n-1} ... y₀]))
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
#eval bblastBvUlt (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvUlt (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0010 <ᵤ 0011
#eval bblastBvUlt (mkValBV [false, false, true, false])
  (mkValBV [false, false, true, true])
#eval termEval (bblastBvUlt (mkValBV [false, false, true, false])
  (mkValBV [false, false, true, true]))
-- 10 <ᵤ 01
#eval bblastBvUlt (mkValBV [true, false])
  (mkValBV [false, true])
#eval termEval (bblastBvUlt (mkValBV [true, false])
  (mkValBV [false, true]))
-- Using variables
#eval bblastBvUlt (const 21 (bv 4)) 
  (mkValBV [false, false, false, false])
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
      x ≤ᵤ y 
------------------
(x <ᵤ y) ∨ (x = y)
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
#eval bblastBvUle (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvUle (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0010 ≤ᵤ 0010
#eval bblastBvUle (mkValBV [false, false, true, false])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvUle (mkValBV [false, false, true, false])
  (mkValBV [false, false, true, false]))
-- 10 ≤ᵤ 01
#eval bblastBvUle (mkValBV [true, false])
  (mkValBV [false, true])
#eval termEval (bblastBvUle (mkValBV [true, false])
  (mkValBV [false, true]))
-- Using variables
#eval bblastBvUle (const 21 (bv 4)) 
  (mkValBV [false, false, false, false])
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
                  [xₙ ... x₁ x₀] >ᵤ [yₙ ... y₀ y₁]
-------------------------------------------------------------------------
   (xₙ ∧ ¬yₙ) ∨ ((xₙ ↔ yₙ) ∧ ([x_{n-1} ... x₀] >ᵤ [y_{n-1} ... y₀]))
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
#eval bblastBvUgt (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvUgt (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false]))
-- 0011 >ᵤ 0010
#eval bblastBvUgt (mkValBV [false, false, true, true])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvUgt (mkValBV [false, false, true, true])
  (mkValBV [false, false, true, false]))
-- 01 >ᵤ 10
#eval bblastBvUgt (mkValBV [false, true])
  (mkValBV [true, false])
#eval termEval (bblastBvUgt (mkValBV [false, true])
  (mkValBV [true, false]))
-- Using variables
#eval bblastBvUgt (const 21 (bv 4)) 
  (mkValBV [false, false, false, false])
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
      x ≥ᵤ y
------------------
(x >ᵤ y) ∨ (x = y)
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
#eval bblastBvUge (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvUge (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false]))
-- 0011 ≥ᵤ 0011
#eval bblastBvUge (mkValBV [false, false, true, true])
  (mkValBV [false, false, true, true])
#eval termEval (bblastBvUge (mkValBV [false, false, true, true])
  (mkValBV [false, false, true, true]))
-- 01 ≥ᵤ 10
#eval bblastBvUge (mkValBV [false, true])
  (mkValBV [true, false])
#eval termEval (bblastBvUge (mkValBV [false, true])
  (mkValBV [true, false]))
-- Using variables
#eval bblastBvUge (const 21 (bv 4)) 
  (mkValBV [false, false, false, true])
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
                [xₙ ... x₁ x₀] <ₛ [yₙ ... y₀ y₁]
---------------------------------------------------------------------
  (xₙ ∧ ¬yₙ) ∨ (xₙ ↔ yₙ ∧ ([x_{n-1} ... x₀] <ᵤ [y_{n-1} ... y₀]))
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
#eval bblastBvSlt (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvSlt (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false]))
-- 1010 <ₛ 1011
#eval bblastBvSlt (mkValBV [true, false, true, false])
  (mkValBV [true, false, true, true])
#eval termEval (bblastBvSlt (mkValBV [true, false, true, false])
  (mkValBV [true, false, true, true]))
-- 01 <ₛ 10
#eval bblastBvSlt (mkValBV [false, true])
  (mkValBV [true, false])
#eval termEval (bblastBvSlt (mkValBV [false, true])
  (mkValBV [true, false]))
-- Using variables
#eval bblastBvSlt (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
       x ≤ₛ y
------------------
(x <ₛ y) ∨ (x = y)
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
#eval bblastBvSle (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvSle (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false]))
-- 1010 ≤ₛ 1010
#eval bblastBvSle (mkValBV [true, false, true, false])
  (mkValBV [true, false, true, false])
#eval termEval (bblastBvSle (mkValBV [true, false, true, false])
  (mkValBV [true, false, true, false]))
-- 01 ≤ₛ 10
#eval bblastBvSle (mkValBV [false, true])
  (mkValBV [true, false])
#eval termEval (bblastBvSle (mkValBV [false, true])
  (mkValBV [true, false]))
-- Using variables
#eval bblastBvSle (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
                [xₙ ... x₁ x₀] >ₛ [yₙ ... y₀ y₁]
----------------------------------------------------------------------
  (¬xₙ ∧ yₙ) ∨ (xₙ ↔ yₙ ∧ ([x_{n-1} ... x₀] >ᵤ [y_{n-1} ... y₀]))
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
#eval bblastBvSgt (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvSgt (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 1011 >ₛ 1010
#eval bblastBvSgt (mkValBV [true, false, true, true])
  (mkValBV [true, false, true, false])
#eval termEval (bblastBvSgt (mkValBV [true, false, true, true])
  (mkValBV [true, false, true, false]))
-- 10 >ₛ 01
#eval bblastBvSgt (mkValBV [true, false])
  (mkValBV [false, true])
#eval termEval (bblastBvSgt (mkValBV [true, false])
  (mkValBV [false, true]))
-- Using variables
#eval bblastBvSgt (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
       x ≥ₛ y
------------------
(x >ₛ y) ∨ (x = y)
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
#eval bblastBvSge (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvSge (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 1011 ≥ₛ 1010
#eval bblastBvSge (mkValBV [true, false, true, true])
  (mkValBV [true, false, true, true])
#eval termEval (bblastBvSge (mkValBV [true, false, true, true])
  (mkValBV [true, false, true, true]))
-- 10 ≥ₛ 01
#eval bblastBvSge (mkValBV [true, false])
  (mkValBV [false, true])
#eval termEval (bblastBvSge (mkValBV [true, false])
  (mkValBV [false, true]))
-- Using variables
#eval bblastBvSge (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
#eval bblastBvAdd (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvAdd (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 1111 + 1111
#eval bblastBvAdd (mkValBV [true, true, true, true])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvAdd (mkValBV [true, true, true, true])
  (mkValBV [true, true, true, true]))
-- 0101 + 0010
#eval bblastBvAdd (mkValBV [false, true, false, true])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvAdd (mkValBV [false, true, false, true])
  (mkValBV [false, false, true, false]))
-- 1111 + 0001
#eval bblastBvAdd (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, true])
#eval termEval (bblastBvAdd (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, true]))
-- Using variables
#eval bblastBvAdd (const 21 (bv 4))
  (mkValBV [false, false, false, false])
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
#eval bblastBvNeg (mkValBV [false, false, false, false])
#eval termEval (bblastBvNeg (mkValBV [false, false, false, false]))
-- -0001
#eval bblastBvNeg (mkValBV [false, false, false, true])
#eval termEval (bblastBvNeg (mkValBV [false, false, false, true]))
-- -1111
#eval bblastBvNeg (mkValBV [true, true, true, true])
#eval termEval (bblastBvNeg (mkValBV [true, true, true, true]))
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

-- 1110-0000
#eval bblastBvSub (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvSub (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false]))
-- 0000-0010
#eval bblastBvSub (mkValBV [false, false, false, false])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvSub (mkValBV [false, false, false, false])
  (mkValBV [false, false, true, false]))
-- Using variables
#eval bblastBvSub (const 21 (bv 4)) (mkValBV [false, false, false, false])
#eval bblastBvSub (const 21 (bv 4)) (const 22 (bv 4))
-- Bit-blasting BvNeg rule
axiom bbBvSub : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvSub t₁ t₂) (bblastBvSub t₁ t₂))


--------------------------------------- Shift Operators ---------------------------------------

/- -----------
 BV Left Shift
----------- -/

-- If terms are well-typed, construct their BV left shift application
def mkBvShl : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvShl

/- 
Single left shift
[x₀ ... ]
-/
def leftShiftVal : List Bool → List Bool
| h :: t => t ++ [false]
| [] => []
def leftShift : Option term → Option term :=
  λ ot => ot >>= λ t => sortOf t >>= λ s => 
    match s with 
    | bv n => match t with
              | val (value.bitvec l) _ => val (value.bitvec (leftShiftVal l)) (bv n)
              | _ => mkBbT (List.append (bitOfNAux t (n-2)) [some bot])
    | _ => none
#eval leftShift (mkValBV [true, true, true])
#eval leftShift (const 21 (bv 3))

/-
              a << b
-----------------------------------
ite(b <ᵤ l,
	  (For each s in (0 to log2(l)-1)
      ite(b[s], a << 2^s, a)),
    [00..0]ₗ)
where len(a) = l and [00..0]ₗ is a BV with l 0's
-/

/-   
-- If terms are well-typed, construct their bit-blasted BV left shift
def bblastBvShl : Option term → Option term → Option term :=
  λ ot₁ ot₂ => 
  ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListAdd (bitOfNRev t₁ m) (bitOfNRev t₂ m)
      ) else none
    | (_, _) => none

-- 1001 << 0001
#eval bblastBvShl (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true])
#eval termEval (bblastBvShl (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true]))
-- 1001 << 0100
#eval bblastBvShl (mkValBV [false, true, true, false])
  (mkValBV [false, true, false, false])
#eval termEval (bblastBvShl (mkValBV [false, true, true, false])
  (mkValBV [false, true, false, false]))
-- 1110 << 0000
#eval bblastBvShl (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvShl (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false]))
-- Using variables
#eval bblastBvShl (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvShl (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvShl rule
axiom bbBvShl : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvShl t₁ t₂) (bblastBvShl t₁ t₂))
-/


/- ----------------------
 BV Logical Right Shift
----------------------- -/

-- If terms are well-typed, construct their BV logical right shift application
def mkBvLShr : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvLShr

/-
              a >> b
-----------------------------------
ite(b <ᵤ l,
	  (For each s in (0 to log2(l)-1)
      ite(b[s], a >> 2^s, a)),
    [00..0]ₗ)
where len(a) = l and [00..0]ₗ is a BV with l 0's
-/
-- Single logical right shift
def lRightShiftVal : List Bool → List Bool
| h :: t => false :: h :: (List.dropLast t)
| [] => []
-- Need a modified bitOfN for right shifts
def bitOfNRShAux : term → Nat → List (Option term)
| t, 0 => []
| t, (n + 1) => (mkBitOf t (mkValInt (Int.ofNat (n + 1))))
                    :: (bitOfNRShAux t n)
#eval bitOfNRShAux (const 21 (bv 4)) 3
def lRightShift : Option term → Option term :=
  λ ot => ot >>= λ t => sortOf t >>= λ s => 
    match s with 
    | bv n => match t with
              | val (value.bitvec l) _ => val (value.bitvec (lRightShiftVal l)) (bv n)
              | _ => mkBbT (some bot :: (bitOfNRShAux t (n-1)))
    | _ => none
#eval lRightShift (mkValBV [true, true, true])
#eval lRightShift (const 21 (bv 3))

/-   
-- If terms are well-typed, construct their bit-blasted BV logical right shift
def bblastBvLShr : Option term → Option term → Option term :=
  λ ot₁ ot₂ => 
  ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListAdd (bitOfNRev t₁ m) (bitOfNRev t₂ m)
      ) else none
    | (_, _) => none

-- 1001 >> 0001
#eval bblastBvLShr (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true])
#eval termEval (bblastBvLShr (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true]))
-- 1001 >> 0100
#eval bblastBvLShr (mkValBV [false, true, true, false])
  (mkValBV [false, true, false, false])
#eval termEval (bblastBvLShr (mkValBV [false, true, true, false])
  (mkValBV [false, true, false, false]))
-- 1110 >> 0000
#eval bblastBvLShr (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvLShr (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false]))
-- Using variables
#eval bblastBvLShr (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvLShr (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvLShr rule
axiom bbBvLShr : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvLShr t₁ t₂) (bblastBvLShr t₁ t₂))
-/


/- ------------------------
 BV Arithmetic Right Shift
------------------------- -/

-- If terms are well-typed, construct their BV logical right shift application
def mkBvAShr : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvAShr

/-
              a >>ₐ b
-----------------------------------
ite(b <ᵤ l,
	  (For each s in (0 to log2(l)-1)
      ite(b[s], a >>ₐ 2^s, a)),
    [00..0]ₗ)
where len(a) = l and [00..0]ₗ is a BV with l 0's
-/
-- Single arithmetic right shift
def aRightShiftVal : List Bool → Bool → List Bool
| h :: t, sign => sign :: h :: (List.dropLast t)
| [], sign  => []
-- Need a bool list head function (that defaults to false)
def head : List Bool → Bool 
| h :: t => h
| [] => false
def aRightShift : Option term → Option term :=
  λ ot => ot >>= λ t => sortOf t >>= λ s => 
    match s with 
    | bv n => match t with
              | val (value.bitvec l) _ => val (value.bitvec (aRightShiftVal l (head l))) (bv n)
              | _ => mkBbT ((mkBitOf t (mkValInt (Int.ofNat (n-1)))) :: 
                            (bitOfNRShAux t (n-1)))
    | _ => none
#eval aRightShift (mkValBV [true, false, true])
#eval aRightShift (mkValBV [false, true, true])
#eval aRightShift (const 21 (bv 3))

/-   
-- If terms are well-typed, construct their bit-blasted BV arithmetic right shift
def bblastBvAShr : Option term → Option term → Option term :=
  λ ot₁ ot₂ => 
  ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListAdd (bitOfNRev t₁ m) (bitOfNRev t₂ m)
      ) else none
    | (_, _) => none

-- 1001 >>ₐ 0001
#eval bblastBvAShr (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true])
#eval termEval (bblastBvAShr (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true]))
-- 1001 >>ₐ 0100
#eval bblastBvAShr (mkValBV [false, true, true, false])
  (mkValBV [false, true, false, false])
#eval termEval (bblastBvAShr (mkValBV [false, true, true, false])
  (mkValBV [false, true, false, false]))
-- 1110 >>ₐ 0000
#eval bblastBvAShr (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvAShr (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false]))
-- 0101 >>ₐ 0010
#eval bblastBvAShr (mkValBV [false, true, false, true])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvAShr (mkValBV [false, true, false, true])
  (mkValBV [false, false, true, false]))
-- Using variables
#eval bblastBvAShr (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvAShr (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvAShr rule
axiom bbBvAShr : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvAShr t₁ t₂) (bblastBvAShr t₁ t₂))
-/


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
[xₙ ... x₀]   0 ≤ j ≤ i < n
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
#eval bblastBvExtract (mkValBV [false, false, true, false])
  (mkValInt 3) (mkValInt 2)
#eval bblastBvExtract (mkValBV [false, false, true, false])
  (mkValInt 1) (mkValInt 1)
#eval bblastBvExtract (mkValBV [false, false, true, false])
  (mkValInt 3) (mkValInt 0)
-- Bad call
#eval bblastBvExtract (mkValBV [false, false, true, false])
  (mkValInt 1) (mkValInt 2)
-- Using variables
#eval bblastBvExtract (const 21 (bv 4)) (mkValInt 2) 
  (mkValInt 1)

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
[xₙ ... x₁ x₀] ++ [yₙ ... y₁ y₀]
---------------------------------
   [xₙ ... x₁ x₀ yₙ ... y₁ y₀]
-/
def bblastBvConcat : Option term → Option term → Option term :=
  λ ot₁ ot₂ => ot₁ >>= λ t₁ => sortOf t₁ >>= λ s₁ => 
               ot₂ >>= λ t₂ => sortOf t₂ >>= λ s₂ => 
    match s₁, s₂ with
    | bv m, bv n => mkBbT (List.append (bitOfN t₁ m) (bitOfN t₂ n))
    | _, _ => none
-- 0000 ++ 1111
#eval bblastBvConcat (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
-- 11 + 111
#eval bblastBvConcat (mkValBV [true, true])
  (mkValBV [true, true, true])
-- 1 + 110
#eval bblastBvConcat (mkValBV [true])
  (mkValBV [true, true, false])
-- Using variables
#eval bblastBvConcat (const 21 (bv 2))
  (mkValBV [false, false])
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
     [xₙ ... x₁ x₀]    i
-----------------------------
  [0₁ ... 0ᵢ xₙ ... x₁ x₀]
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
#eval bblastZeroExt (mkValBV [true, true, true, true])
  (mkValInt 2)
#eval bblastZeroExt (mkValBV [true, false])
  (mkValInt 0)
-- Using variables
#eval bblastZeroExt (const 21 (bv 4))  (mkValInt 2)

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
     [xₙ ... x₁ x₀]   i
-----------------------------
  [xₙ ... xₙ xₙ ... x₁ x₀]
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
#eval bblastSignExt (mkValBV [true, true, true, false])
  (mkValInt 2)
#eval bblastSignExt (mkValBV [false, true, true, true])
  (mkValInt 2)
#eval bblastSignExt (mkValBV [true, false])
  (mkValInt 0)
-- Using variables
#eval bblastSignExt (const 21 (bv 4)) (mkValInt 2)

-- Bit-blasting BvSignExt rule
axiom bbBvSignExt : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvSignExt t₁ t₂) (bblastSignExt t₁ t₂))


/- ----------
 BV Repeat
----------- -/

-- If terms are well-typed, construct their BV repeat application
def mkBvRepeat : Option term → Option term → Option term :=
  λ oi ot => oi >>= λ i => sortOf i >>= λ si =>
             ot >>= λ t => sortOf t >>= λ s =>
  match si, s with
  | intSort, bv n => 
    match i with
    | val (value.integer i₁) intSort => bvRepeat n (Int.toNat i₁) i t
    | _ => none
  | _, _ => none

def repeatList : Nat → List α → List α
| (n+1), l => List.append l (repeatList n l)
| 0, l => []
/-
If terms are well-typed, construct their bit-blasted BV repeat
            i    [xₙ ... x₁ x₀]
------------------------------------------
  [xₙ ... x₁ x₀ xₙ ... x₁ x₀ xₙ ... x₁ x₀]
where x₀ ... xₙ is repeated i times
-/
def bblastRepeat : Option term → Option term → Option term :=
  λ oi ot => oi >>= λ i => sortOf i >>= λ si =>
             ot >>= λ t => sortOf t >>= λ s =>
  match si, s with
  | intSort, bv n => 
    match i with
    | val (value.integer i₁) intSort =>
      if (i₁ < 0) then none else
        mkBbT (repeatList (Int.toNat i₁) (bitOfN t n))
    | _ => none
  | _, _ => none

#eval bblastRepeat (mkValInt 2) 
  (mkValBV [true, true, true, true])
#eval bblastRepeat (mkValInt (-1))
  (mkValBV [true, true, true, true])
#eval bblastRepeat (mkValInt 7) 
  (mkValBV [true, false])
-- Using variables
#eval bblastRepeat (mkValInt 2) (const 21 (bv 2))

-- Bit-blasting BvRepeat rule
axiom bbBvRepeat : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvRepeat t₁ t₂) (bblastRepeat t₁ t₂))


end term

end proof