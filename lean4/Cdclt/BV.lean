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


--------------------------------------- Bit Of ---------------------------------------
/- mkBitOf bv n, returns the nth element
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


--------------------------------------- Bitwise Operators ---------------------------------------

/-
mkBbT n l
Construct a (bv n) term that is a bbT of the bools 
in l
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

-- For BVAnd and BVOr
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

-- If terms are well-typed, construct a BV Eq application
-- of them
def mkBvEq : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvEq

/-
bblastBvEq ot₁ ot₂
If ot₁ and ot₂ are BVs of the same length,
then return a boolean term that represents
the bit-blasted equality of ot₁ and ot₂

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
      ) else some top
    | (_, _) => some bot
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


/- -----------
 BV not
----------- -/

-- If term is a BV, construct a BV Not application
def mkBvNot : Option term → Option term :=
  λ ot => ot >>= λ t => sortOf t >>= λ s =>
  match s with
  | bv n => bvNot n t
  | _ => none 

/-
If term is a BV, construct a bit-blasted BV Not
¬bv [x₀, x₁, ... , xₙ]
----------------------
 [¬x₀, ¬x₁, ... , ¬x]
-/
def bblastBvNot (ot : Option term) : Option term :=
  ot >>= λ t => sortOf t >>= λ s =>
    match s with
    | bv n => mkBbT (List.map mkNot (bitOfN t n))
    | _ => none
#eval bblastBvNot (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvNot (const 21 (bv 4))

-- Bit-blasting BvNot rule
axiom bbBvNot : ∀ {t : Option term},
  thHolds (mkEq (mkBvNot t) (bblastBvNot t))


/- -----------
 BV and
----------- -/

-- If terms are well-typed, construct a BV And application
-- of them
def mkBvAnd : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvAnd

/-
If terms are well-typed, construct a bit-blasted BV and
of them
[x₀ x₁ ... xₙ] ∧bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ∧ y₀, x₁ ∧ x₂, ... xₙ ∧ yₙ]
-/
def bblastBvAnd : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkAnd

#eval bblastBvAnd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvAnd rule
axiom bbBvAnd : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvAnd t₁ t₂) (bblastBvAnd t₁ t₂))


/- -----------
 BV or
----------- -/

-- If terms are well-typed, construct a BV Or application
-- of them
def mkBvOr : Option term → Option term → Option term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvOr

/-
If terms are well-typed, construct a bit-blasted BV and
of them
[x₀ x₁ ... xₙ] ∨bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ∨ y₀, x₁ ∨ x₂, ... xₙ ∨ yₙ]
-/
def bblastBvOr : Option term → Option term → Option term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkOr

#eval bblastBvOr (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvOr (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvOr (const 21 (bv 4)) (const 22 (bv 4))
#eval mkBbT (bitOfN (val (value.bitvec [true, true, true, true]) (bv 4)) 4)

-- Bit-blasting BvOr rule
axiom bbBvOr : ∀ {t₁ t₂ : Option term},
  thHolds (mkEq (mkBvOr t₁ t₂) (bblastBvOr t₁ t₂))


--------------------------------------- Comparison Operators ---------------------------------------
/-
Endian-ness:
We assume that a BV is represented as:
MSB ... LSB
(bv 4) representation of decimal 1:
0001
-/

/- -------------------
 BV unsigned less than
--------------------- -/

-- If terms are well-typed, construct a BV Ult application
-- of them
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
bblastBvUlt ot₁ ot₂
If ot₁ and ot₂ are BVs of the same length, 
then return a boolean term that represents 
ot₁ <ᵤ ot₂
-/
def bblastBvUlt : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListUlt (bitOfN t₁ m) (bitOfN t₂ m)
      ) else some top
    | (_, _) => some bot

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


/- ----------------------
 BV unsigned greater than
----------------------- -/

-- If terms are well-typed, construct a BV Ugt application
-- of them
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
bblastBvUgt ot₁ ot₂
If ot₁ and ot₂ are BVs of the same length, 
then return a boolean term that represents 
ot₁ >ᵤ ot₂
-/
def bblastBvUgt : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListUgt (bitOfN t₁ m) (bitOfN t₂ m)
      ) else some top
    | (_, _) => some bot

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


/- ----------------------
 BV signed less than
----------------------- -/

-- If terms are well-typed, construct a BV Slt application
-- of them
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
bblastBvSlt ot₁ ot₂
If ot₁ and ot₂ are BVs of the same length, 
then return a boolean term that represents 
ot₁ <ₛ ot₂
-/
def bblastBvSlt : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListSlt (bitOfN t₁ m) (bitOfN t₂ m)
      ) else some top
    | (_, _) => some bot

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


/- ----------------------
 BV signed greater than
----------------------- -/

-- If terms are well-typed, construct a BV Sgt application
-- of them
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
bblastBvSgt ot₁ ot₂
If ot₁ and ot₂ are BVs of the same length, 
then return a boolean term that represents 
ot₁ <ₛ ot₂
-/
def bblastBvSgt : Option term → Option term → Option term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ => 
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) => 
      if (m = n) then (
            boolListSgt (bitOfN t₁ m) (bitOfN t₂ m)
      ) else some top
    | (_, _) => some bot

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


end term

end proof