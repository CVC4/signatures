import Cdclt.Term
import Cdclt.Boolean
import Cdclt.TermEval

open proof
open proof.sort proof.Term
open rules

namespace proof

namespace Term

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
def mkBitOf : OptionM Term → OptionM Term → OptionM Term :=
λ ot₁ ot₂ =>
  ot₁ >>= λ t₁ => ot₂ >>= λ t₂ =>
  sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
match (s₁, s₂) with
| (bv n, intSort) =>
  match t₂ with
  -- integer index has to be an in-range value
  | val (Value.integer i) _ => if (i >= 0 ∧ i < n) then
    (match t₁ with
    -- BV can be a constant
    | val (Value.bitvec l) _ =>
        match (List.get? (Int.toNat i) l) with
        | some b => if b then top else bot
        | none => none
    -- or BV can be a var
    | _ => bitOf n t₁ t₂) else none
  | _ => none
| (_, _) => none
#check mkBitOf (val (Value.bitvec [true, false, true, false]) (bv 4)) (val (Value.integer 0) intSort)
#check mkBitOf (val (Value.bitvec [true, false, true, false]) (bv 4)) (val (Value.integer 1) intSort)
#check mkBitOf (val (Value.bitvec [true, false, true, false]) (bv 4)) (val (Value.integer 4) intSort)
#check mkBitOf (const (mkName "x") (bv 4)) (val (Value.integer 0) intSort)
#check mkBitOf (const (mkName "x") (bv 4)) (val (Value.integer 1) intSort)
#check mkBitOf (const (mkName "x") (bv 4)) (val (Value.integer 4) intSort)

/- bitOfN t n
   bit-blasts a BV constant or variable.
   t is the BV Term and n is its length.
   bitOfN t n returns a list of length n
   with option Terms representing each bit.
-/
def bitOfNAux : Term → Nat → Nat → List (OptionM Term)
| t, 0, _ => []
| t, (n₁+1), n₂ => (mkBitOf t (val (Value.integer (Int.ofNat (n₂ - n₁ - 1))) intSort))
                    :: (bitOfNAux t n₁ n₂)

def bitOfN : Term → Nat → List (OptionM Term) :=
  λ t n => bitOfNAux t n n

#check bitOfN (const (mkName "x") (bv 4)) 4
#check bitOfN (val (Value.bitvec [true, true, true, false]) (bv 4)) 4
/- The following bad calls create bad bit-blasted Terms
   because the nat argument to bitOfN and the length
   of the BV Term don't match.-/
#check bitOfN (const (mkName "x") (bv 3)) 4
#check bitOfN (val (Value.bitvec [true, true, true, false]) (bv 4)) 3


/- bitOfNRev works like bitOfN but in reverse -/
def bitOfNRevAux : Term → Nat → List (OptionM Term)
| t, 0 => (mkBitOf t (val (Value.integer (Int.ofNat 0)) intSort)) :: []
| t, (n + 1) => (mkBitOf t (val (Value.integer (Int.ofNat (n + 1))) intSort))
                    :: (bitOfNRevAux t n)

def bitOfNRev : Term → Nat → List (OptionM Term) :=
  λ t n => bitOfNRevAux t (n-1)

#check bitOfNRev (const (mkName "x") (bv 4)) 4
#check bitOfNRev (val (Value.bitvec [true, true, true, false]) (bv 4)) 4
/- The following bad calls create bad bit-blasted Terms
   because the nat argument to bitOfN and the length
   of the BV Term don't match.-/
#check bitOfNRev (const (mkName "x") (bv 3)) 4
#check bitOfNRev (val (Value.bitvec [true, true, true, false]) (bv 4)) 3


--------------------------------------- Bitwise Operators ---------------------------------------

/-
mkBbT l
Construct a BV Term that is a bbT (bit-blasted Term)
of the bools in l
-/
@[matchPattern] def mkBbT (l : List (OptionM Term)) : OptionM Term :=
  mkAppN (bbT (List.length l)) l

#check mkBbT ([some top, some top, some top, some top])

/-
checkBinaryBV ot₁ ot₂ constr
If ot₁ and ot₂ are BVs of the same length, then
construct a bitwise op of (constr ot₁ ot₂)
-/
def checkBinaryBV : OptionM Term → OptionM Term →
  (Nat → Term → Term → Term) → OptionM Term :=
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
and returns an OptionM List of OptionM Terms that
has the bitwise application of const to the
respective elements of ot₁ and ot₂
-/
def bblastBvBitwise (ot₁ ot₂ : OptionM Term)
 (constructor : OptionM Term → OptionM Term → OptionM Term) : OptionM Term :=
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

-- If Terms are well-typed, construct their BV Eq application
def mkBvEq : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvEq

/-
If Terms are well-typed, construct their bit-blasted BV eq
[x₀, x₁, ... , xₙ] = [y₀, y₁, ... , yₙ]
---------------------------------------
       x₀ = y₀ ∧ ... ∧ xₙ = yₙ
-/
def bblastBvEq : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ =>
    ot₁ >>= λ t₁ => ot₂ >>= λ t₂ =>
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    | (bv m, bv n) =>
      if (m = n) then (
            mkAndN (zip (bitOfN t₁ m) (bitOfN t₂ m) mkEq)
      ) else some top
    | (_, _) => some bot

-- 0000 = 1111
#check bblastBvEq (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4))
#check termEval (bblastBvEq (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4)))
-- #check OptionMTermToString (termEval (bblastBvEq (val (Value.bitvec [false, false, false, false]) (bv 4))
--  (val (Value.bitvec [true, true, true, true]) (bv 4))))
-- 010 = 010
-- #check bblastBvEq (val (Value.bitvec [false, true, false]) (bv 3))
--   (val (Value.bitvec [false, true, false]) (bv 3))
--
-- check (bblastBvEq (val (Value.bitvec [false, true, false]) (bv 3))
--                   (val (Value.bitvec [false, true, false]) (bv 3)))
--
-- #check OptionMTermToString
--   (termEval (bblastBvEq (val (Value.bitvec [false, true, false]) (bv 3))
--   (val (Value.bitvec [false, true, false]) (bv 3))))

-- Using variables
#check bblastBvEq (const (mkName "x") (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4))
#check bblastBvEq (const (mkName "x") (bv 4)) (const (mkName "y") (bv 4))

-- #check OptionMTermToString (bblastBvEq (const (mkName "x") (bv 4)) (const (mkName "y") (bv 4)))

-- Bit-blasting BvEq rule
axiom bbBvEq : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvEq t₁ t₂) (bblastBvEq t₁ t₂))


/- ------
 BV not
------- -/

-- If Term is a BV, construct its BV Not application
def mkBvNot : OptionM Term → OptionM Term :=
  λ ot => ot >>= λ t => sortOf t >>= λ s =>
  match s with
  | bv n => bvNot n t
  | _ => none

/-
If Term is a BV, construct its bit-blasted BV not
¬bv [x₀, x₁, ... , xₙ]
----------------------
 [¬x₀, ¬x₁, ... , ¬x]
-/
def bblastBvNot (ot : OptionM Term) : OptionM Term :=
  ot >>= λ t => sortOf t >>= λ s =>
    match s with
    | bv n => mkBbT (List.map mkNot (bitOfN t n))
    | _ => none
#check bblastBvNot (val (Value.bitvec [false, false, false, false]) (bv 4))
#check bblastBvNot (const (mkName "x") (bv 4))

-- Bit-blasting BvNot rule
axiom bbBvNot : ∀ {t : OptionM Term},
  thHolds (mkEq (mkBvNot t) (bblastBvNot t))


/- -------
 BV and
-------- -/

-- If Terms are well-typed, construct their BV And application
def mkBvAnd : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvAnd

/-
If Terms are well-typed, construct their bit-blasted BV and
[x₀ x₁ ... xₙ] ∧bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ∧ y₀, x₁ ∧ x₂, ... xₙ ∧ yₙ]
-/
def bblastBvAnd : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkAnd

#check bblastBvAnd (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4))
#check bblastBvAnd (const (mkName "x") (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4))
#check bblastBvAnd (const (mkName "x") (bv 4)) (const (mkName "y") (bv 4))

-- Bit-blasting BvAnd rule
axiom bbBvAnd : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvAnd t₁ t₂) (bblastBvAnd t₁ t₂))


/- -----
 BV or
----- -/

-- If Terms are well-typed, construct their BV Or application
def mkBvOr : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvOr

/-
If Terms are well-typed, construct their bit-blasted BV or
[x₀ x₁ ... xₙ] ∨bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ∨ y₀, x₁ ∨ x₂, ... xₙ ∨ yₙ]
-/
def bblastBvOr : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkOr

#check bblastBvOr (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4))
#check bblastBvOr (const (mkName "x") (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4))
#check bblastBvOr (const (mkName "x") (bv 4)) (const (mkName "y") (bv 4))
#check mkBbT (bitOfN (val (Value.bitvec [true, true, true, true]) (bv 4)) 4)

-- Bit-blasting BvOr rule
axiom bbBvOr : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvOr t₁ t₂) (bblastBvOr t₁ t₂))


--------------------------------------- Comparison Operators ---------------------------------------

/- -------------------
 BV unsigned less than
--------------------- -/

-- If Terms are well-typed, construct their BV Ult application
def mkBvUlt : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUlt

/-
[x₀, x₁, ... , xₙ] <ᵤ [y₀, y₁, ... , yₙ] =
  (¬x₀ ∧ y₀) ∨ ((x₀ ↔ y₀) ∧ ([x₁, ... , xₙ] <ᵤ [y₁, ... , yₙ]))
-/
def boolListUlt : List (OptionM Term) → List (OptionM Term) → OptionM Term
| [h₁], [h₂] => mkAnd (mkNot h₁) h₂
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd (mkNot h₁) h₂) (mkAnd (mkEq h₁ h₂) (boolListUlt t₁ t₂)))
| _, _ => none

/-
If Terms are well-typed, construct their bit-blasted
unsigned less than comparison
-/
def bblastBvUlt : OptionM Term → OptionM Term → OptionM Term :=
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
#check bblastBvUlt (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4))
#check termEval (bblastBvUlt (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4)))
-- 0010 <ᵤ 0011
#check bblastBvUlt (val (Value.bitvec [false, false, true, false]) (bv 4))
  (val (Value.bitvec [false, false, true, true]) (bv 4))
#check termEval (bblastBvUlt (val (Value.bitvec [false, false, true, false]) (bv 4))
  (val (Value.bitvec [false, false, true, true]) (bv 4)))
-- 10 <ᵤ 01
#check bblastBvUlt (val (Value.bitvec [true, false]) (bv 2))
  (val (Value.bitvec [false, true]) (bv 2))
#check termEval (bblastBvUlt (val (Value.bitvec [true, false]) (bv 2))
  (val (Value.bitvec [false, true]) (bv 2)))
-- Using variables
#check bblastBvUlt (const (mkName "x") (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4))
#check bblastBvUlt (const (mkName "x") (bv 4)) (const (mkName "y") (bv 4))

-- Bit-blasting BvUlt rule
axiom bbBvUlt : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvUlt t₁ t₂) (bblastBvUlt t₁ t₂))


/- ----------------------
 BV unsigned greater than
----------------------- -/

-- If Terms are well-typed, construct their BV Ugt application
def mkBvUgt : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUgt

/-
[x₀, x₁, ... , xₙ] >ᵤ [y₀, y₁, ... , yₙ] =
  (x₀ ∧ ¬y₀) ∨ ((x₀ ↔ y₀) ∧ ([x₁, ... , xₙ] >ᵤ [y₁, ... , yₙ]))
-/
def boolListUgt : List (OptionM Term) → List (OptionM Term) → OptionM Term
| [h₁], [h₂] => mkAnd h₁ (mkNot h₂)
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd h₁ (mkNot h₂)) (mkAnd (mkEq h₁ h₂) (boolListUgt t₁ t₂)))
| _, _ => none

/-
If Terms are well-typed, construct their bit-blasted
unsigned greater than comparison
-/
def bblastBvUgt : OptionM Term → OptionM Term → OptionM Term :=
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
#check bblastBvUgt (val (Value.bitvec [true, true, true, true]) (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4))
#check termEval (bblastBvUgt (val (Value.bitvec [true, true, true, true]) (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4)))
-- 0011 >ᵤ 0010
#check bblastBvUgt (val (Value.bitvec [false, false, true, true]) (bv 4))
  (val (Value.bitvec [false, false, true, false]) (bv 4))
#check termEval (bblastBvUgt (val (Value.bitvec [false, false, true, true]) (bv 4))
  (val (Value.bitvec [false, false, true, false]) (bv 4)))
-- 01 >ᵤ 10
#check bblastBvUgt (val (Value.bitvec [false, true]) (bv 2))
  (val (Value.bitvec [true, false]) (bv 2))
#check termEval (bblastBvUgt (val (Value.bitvec [false, true]) (bv 2))
  (val (Value.bitvec [true, false]) (bv 2)))
-- Using variables
#check bblastBvUgt (const (mkName "x") (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4))
#check bblastBvUgt (const (mkName "x") (bv 4)) (const (mkName "y") (bv 4))

-- Bit-blasting BvUgt rule
axiom bbBvUgt : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvUgt t₁ t₂) (bblastBvUgt t₁ t₂))


/- -------------------
 BV signed less than
------------------- -/

-- If Terms are well-typed, construct their BV Slt application
def mkBvSlt : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSlt

/-
[x₀, x₁, ... , xₙ] <ₛ [y₀, y₁, ... , yₙ] =
  (x₀ ∧ ¬y₀) ∨ (x₀ = y₀ ∧ ([x₁, ..., xₙ] <ᵤ [y₁, ..., yₙ]))
-/
def boolListSlt : List (OptionM Term) → List (OptionM Term) → OptionM Term
| [h₁], [h₂] => (mkAnd h₁ (mkNot h₂))
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd h₁ (mkNot h₂)) (mkAnd (mkEq h₁ h₂) (boolListUlt t₁ t₂)))
| _, _ => none

/-
If Terms are well-typed, construct their bit-blasted
signed less than comparison
-/
def bblastBvSlt : OptionM Term → OptionM Term → OptionM Term :=
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
#check bblastBvSlt (val (Value.bitvec [true, true, true, true]) (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4))
#check termEval (bblastBvSlt (val (Value.bitvec [true, true, true, true]) (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4)))
-- 1010 <ₛ 1011
#check bblastBvSlt (val (Value.bitvec [true, false, true, false]) (bv 4))
  (val (Value.bitvec [true, false, true, true]) (bv 4))
#check termEval (bblastBvSlt (val (Value.bitvec [true, false, true, false]) (bv 4))
  (val (Value.bitvec [true, false, true, true]) (bv 4)))
-- 01 <ₛ 10
#check bblastBvSlt (val (Value.bitvec [false, true]) (bv 2))
  (val (Value.bitvec [true, false]) (bv 2))
#check termEval (bblastBvSlt (val (Value.bitvec [false, true]) (bv 2))
  (val (Value.bitvec [true, false]) (bv 2)))
-- Using variables
#check bblastBvSlt (const (mkName "x") (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4))
#check bblastBvSlt (const (mkName "x") (bv 4)) (const (mkName "y") (bv 4))

-- Bit-blasting BvUgt rule
axiom bbBvSlt : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvSlt t₁ t₂) (bblastBvSlt t₁ t₂))


/- ----------------------
 BV signed greater than
----------------------- -/

-- If Terms are well-typed, construct their BV Sgt application
def mkBvSgt : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSgt

/-
[x₀, x₁, ... , xₙ] >ₛ [y₀, y₁, ... , yₙ] =
  (¬x₀ ∧ y₀) ∨ (x₀ = y₀ ∧ ([x₁, ..., xₙ] >ᵤ [y₁, ..., yₙ]))
-/
def boolListSgt : List (OptionM Term) → List (OptionM Term) → OptionM Term
| [h₁], [h₂] => (mkAnd (mkNot h₁) h₂)
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd (mkNot h₁) h₂) (mkAnd (mkEq h₁ h₂) (boolListUgt t₁ t₂)))
| _, _ => none

/-
If Terms are well-typed, construct their bit-blasted
signed greater than comparison
-/
def bblastBvSgt : OptionM Term → OptionM Term → OptionM Term :=
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
#check bblastBvSgt (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4))
#check termEval (bblastBvSgt (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4)))
-- 1011 >ₛ 1010
#check bblastBvSgt (val (Value.bitvec [true, false, true, true]) (bv 4))
  (val (Value.bitvec [true, false, true, false]) (bv 4))
#check termEval (bblastBvSgt (val (Value.bitvec [true, false, true, true]) (bv 4))
  (val (Value.bitvec [true, false, true, false]) (bv 4)))
-- 10 >ₛ 01
#check bblastBvSgt (val (Value.bitvec [true, false]) (bv 2))
  (val (Value.bitvec [false, true]) (bv 2))
#check termEval (bblastBvSgt (val (Value.bitvec [true, false]) (bv 2))
  (val (Value.bitvec [false, true]) (bv 2)))
-- Using variables
#check bblastBvSgt (const (mkName "x") (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4))
#check bblastBvSgt (const (mkName "x") (bv 4)) (const (mkName "y") (bv 4))

-- Bit-blasting BvSgt rule
axiom bbBvSgt : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvSgt t₁ t₂) (bblastBvSgt t₁ t₂))


--------------------------------------- Arithmetic Operators ---------------------------------------

/- -----------
 BV addition
----------- -/

-- If Terms are well-typed, construct their BV plus application
def mkBvAdd : OptionM Term → OptionM Term → OptionM Term :=
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
def bitAdder : OptionM Term → OptionM Term → OptionM Term → OptionM Term × OptionM Term
| x, y, carry => (mkXor (mkXor x y) carry,
  mkOr (mkAnd x y) (mkAnd (mkXor x y) carry))
#check (bitAdder top top top)
#check termEval (bitAdder top top top).1
#check termEval (bitAdder top top top).2
def boolListAddAux : OptionM Term → List (OptionM Term) → List (OptionM Term) → List (OptionM Term)
| c, (h₁ :: t₁), (h₂ :: t₂) => (bitAdder h₁ h₂ c).1 :: (boolListAddAux (bitAdder h₁ h₂ c).2 t₁ t₂)
| c, [], [] => []
| _, _, _ => []
def boolListAdd : List (OptionM Term) → List (OptionM Term) → OptionM Term
| l₁, l₂ => mkBbT (List.reverse (boolListAddAux bot l₁ l₂))

-- If Terms are well-typed, construct their bit-blasted BV add
def bblastBvAdd : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ =>
  ot₁ >>= λ t₁ => ot₂ >>= λ t₂ =>
    sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
    match (s₁, s₂) with
    |  (bv m, bv n) =>
      if (m = n) then (
            boolListAdd (bitOfNRev t₁ m) (bitOfNRev t₂ m)
      ) else some top
    | (_, _) => some bot

-- 0000 + 1111
#check bblastBvAdd (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4))
#check termEval (bblastBvAdd (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4)))
-- 1111 + 1111
#check bblastBvAdd (val (Value.bitvec [true, true, true, true]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4))
#check termEval (bblastBvAdd (val (Value.bitvec [true, true, true, true]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4)))
-- 0101 + 1010
#check bblastBvAdd (val (Value.bitvec [false, true, false, true]) (bv 4))
  (val (Value.bitvec [true, false, true, false]) (bv 4))
#check termEval (bblastBvAdd (val (Value.bitvec [false, true, false, true]) (bv 4))
  (val (Value.bitvec [true, false, true, false]) (bv 4)))
-- 1111 + 0001
#check bblastBvAdd (val (Value.bitvec [true, true, true, true]) (bv 4))
  (val (Value.bitvec [false, false, false, true]) (bv 4))
#check termEval (bblastBvAdd (val (Value.bitvec [true, true, true, true]) (bv 4))
  (val (Value.bitvec [false, false, false, true]) (bv 4)))
-- Using variables
#check bblastBvAdd (const (mkName "x") (bv 4))
  (val (Value.bitvec [false, false, false, false]) (bv 4))
#check bblastBvAdd (const (mkName "x") (bv 4)) (const (mkName "y") (bv 4))

-- Bit-blasting BvAdd rule
axiom bbBvAdd : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvAdd t₁ t₂) (bblastBvAdd t₁ t₂))


/- -----------
 BV Negation
------------ -/

-- If Term is a BV, construct its BV Neg application
def mkBvNeg : OptionM Term → OptionM Term :=
  λ ot => ot >>= λ t => sortOf t >>= λ s =>
  match s with
  | bv n => bvNot n t
  | _ => none

/- genRevOne n generates the list
   [(some top) (some bot) ... (some bot)]
   where there are n-1 (some bot) elements -/
def genZeros : Nat → List (OptionM Term)
| 0 => []
| n + 1 => (some bot) :: genZeros n
def genRevOne : Nat → List (OptionM Term) :=
  λ n => (some top) :: genZeros (n - 1)
#check genZeros 3
#check genRevOne 4

/-
If Term is well-typed, construct its bit-blasted BV neg
-bv x = ((¬bv x) +bv 1)
          OR
bvneg x = bvadd (bvnot x) 1
-/
def bblastBvNeg : OptionM Term → OptionM Term :=
  λ ot =>
  ot >>= λ t => sortOf t >>= λ s =>
    match s with
    |  bv m => boolListAdd (List.map mkNot (bitOfNRev t m)) (genRevOne m)
    | _ => some bot
-- -0000
#check bblastBvNeg (val (Value.bitvec [false, false, false, false]) (bv 4))
#check termEval (bblastBvNeg (val (Value.bitvec [false, false, false, false]) (bv 4)))
-- -0001
#check bblastBvNeg (val (Value.bitvec [false, false, false, true]) (bv 4))
#check termEval (bblastBvNeg (val (Value.bitvec [false, false, false, true]) (bv 4)))
-- -1111
#check bblastBvNeg (val (Value.bitvec [true, true, true, true]) (bv 4))
#check termEval (bblastBvNeg (val (Value.bitvec [true, true, true, true]) (bv 4)))
-- Using variables
#check bblastBvNeg (const (mkName "x") (bv 4))

-- Bit-blasting BvNeg rule
axiom bbBvNeg : ∀ {t : OptionM Term},
  thHolds (mkEq (mkBvNeg t) (bblastBvNeg t))


---------------------------- BV Length Manipulating Operators ----------------------------

/- -----------
 BV Extraction
------------ -/

-- If Terms are well-typed, construct their BV Extraction application
def mkBvExtract : OptionM Term → OptionM Term → OptionM Term → OptionM Term :=
  λ ot oi oj =>
    ot >>= λ t => sortOf t >>= λ s =>
    oi >>= λ i => sortOf i >>= λ si =>
    oj >>= λ j => sortOf i >>= λ sj =>
  match s, si, sj with
  | bv n, intSort, intSort =>
    match i, j with
    | (val (Value.integer i₁) intSort), (val (Value.integer j₁) intSort) =>
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
If Terms are well-typed, construct their bit-blasted BV extraction
[x₀ ... xₙ]   0 ≤ j ≤ i < n
----------------------------
       [xⱼ ... xᵢ]
-/
def bblastBvExtract : OptionM Term → OptionM Term → OptionM Term → OptionM Term :=
  λ ot oi oj =>
    ot >>= λ t => sortOf t >>= λ s =>
    oi >>= λ i => sortOf i >>= λ si =>
    oj >>= λ j => sortOf i >>= λ sj =>
  match s, si, sj with
  | bv n, intSort, intSort =>
    match i, j with
    | (val (Value.integer i₁) intSort), (val (Value.integer j₁) intSort) =>
      if (0 ≤ j₁ ∧ j₁ ≤ i₁ ∧ i₁ < n) then
         mkBbT (removeLastN (List.drop (n - (Int.toNat i₁) - 1) (bitOfN t n)) (Int.toNat j₁))
      else
        none
    | _, _ => none
  | _, _, _ => none
#check bblastBvExtract (val (Value.bitvec [false, false, true, false]) (bv 4))
  (val (Value.integer 3) intSort) (val (Value.integer 2) intSort)
#check bblastBvExtract (val (Value.bitvec [false, false, true, false]) (bv 4))
  (val (Value.integer 1) intSort) (val (Value.integer 1) intSort)
#check bblastBvExtract (val (Value.bitvec [false, false, true, false]) (bv 4))
  (val (Value.integer 3) intSort) (val (Value.integer 0) intSort)
-- Bad call
#check bblastBvExtract (val (Value.bitvec [false, false, true, false]) (bv 4))
  (val (Value.integer 1) intSort) (val (Value.integer 2) intSort)
-- Using variables
#check bblastBvExtract (const (mkName "x") (bv 4)) (val (Value.integer 2) intSort)
  (val (Value.integer 1) intSort)

-- Bit-blasting BvExtract rule
axiom bbBvExtract : ∀ {t₁ t₂ t₃ : OptionM Term},
  thHolds (mkEq (mkBvExtract t₁ t₂ t₃) (bblastBvExtract t₁ t₂ t₃))


/- ---------------
 BV Concatenation
---------------- -/

-- If Terms are well-typed, construct their BV concat application
def mkBvConcat : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => ot₁ >>= λ t₁ => sortOf t₁ >>= λ s₁ =>
               ot₂ >>= λ t₂ => sortOf t₂ >>= λ s₂ =>
  match s₁, s₂ with
  | bv m, bv n => bvConcat m n t₁ t₂
  | _, _ => none

/-
If Terms are BVs construct their bit-blasted BV concat
[x₀ x₁ ... xₙ] ++ [y₀ y₁ ... yₙ]
---------------------------------
   [y₀ y₁ ... yₙ x₀ x₁ ... xₙ]
-/
def bblastBvConcat : OptionM Term → OptionM Term → OptionM Term :=
  λ ot₁ ot₂ => ot₁ >>= λ t₁ => sortOf t₁ >>= λ s₁ =>
               ot₂ >>= λ t₂ => sortOf t₂ >>= λ s₂ =>
    match s₁, s₂ with
    | bv m, bv n => mkBbT (List.append (bitOfN t₂ n) (bitOfN t₁ m))
    | _, _ => none
-- 0000 ++ 1111
#check bblastBvConcat (val (Value.bitvec [false, false, false, false]) (bv 4))
  (val (Value.bitvec [true, true, true, true]) (bv 4))
-- 11 + 111
#check bblastBvConcat (val (Value.bitvec [true, true]) (bv 2))
  (val (Value.bitvec [true, true, true]) (bv 3))
-- 1 + 110
#check bblastBvConcat (val (Value.bitvec [true]) (bv 1))
  (val (Value.bitvec [true, true, false]) (bv 3))
-- Using variables
#check bblastBvConcat (const (mkName "x") (bv 2))
  (val (Value.bitvec [false, false]) (bv 2))
#check bblastBvConcat (const (mkName "x") (bv 2)) (const (mkName "y") (bv 2))

-- Bit-blasting BvConcat rule
axiom bbBvConcat : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvConcat t₁ t₂) (bblastBvAdd t₁ t₂))


/- ---------------
 BV Zero Extend
---------------- -/

-- If Terms are well-typed, construct their BV zero extend application
def mkBvZeroExt : OptionM Term → OptionM Term → OptionM Term :=
  λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
             oi >>= λ i => sortOf i >>= λ si =>
  match s, si with
  | bv n, intSort =>
    match i with
    | val (Value.integer i₁) intSort => bvZeroExt n (Int.toNat i₁) t i
    | _ => none
  | _, _ => none

/-
If Terms are well-typed, construct their bit-blasted BV zero extend
     [x₀ x₁ ... xₙ]    i
-----------------------------
  [0₁ ... 0ᵢ x₀ x₁ ... xₙ]
-/
def bblastZeroExt : OptionM Term → OptionM Term → OptionM Term :=
  λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
             oi >>= λ i => sortOf i >>= λ si =>
  match s, si with
  | bv n, intSort =>
    match i with
    | val (Value.integer i₁) intSort =>
      mkBbT (List.append (List.replicate (Int.toNat i₁) (some bot)) (bitOfN t n))
    | _ => none
  | _, _ => none
#check bblastZeroExt (val (Value.bitvec [true, true, true, true]) (bv 4))
  (val (Value.integer 2) intSort)
#check bblastZeroExt (val (Value.bitvec [true, false]) (bv 2))
  (val (Value.integer 0) intSort)
-- Using variables
#check bblastZeroExt (const (mkName "x") (bv 4))  (val (Value.integer 2) intSort)

-- Bit-blasting BvZeroExt rule
axiom bbBvZeroExt : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvZeroExt t₁ t₂) (bblastZeroExt t₁ t₂))


/- ---------------
 BV Sign Extend
---------------- -/

-- If Terms are well-typed, construct their BV sign extend application
def mkBvSignExt : OptionM Term → OptionM Term → OptionM Term :=
  λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
             oi >>= λ i => sortOf i >>= λ si =>
  match s, si with
  | bv n, intSort =>
    match i with
    | val (Value.integer i₁) intSort => bvSignExt n (Int.toNat i₁) t i
    | _ => none
  | _, _ => none

def hd : List α → OptionM α
| h :: t => some h
| [] => none

/-
If Terms are well-typed, construct their bit-blasted BV sign extend
     [x₀ x₁ ... xₙ]    i
-----------------------------
  [x₀ ... x₀ x₀ x₁ ... xₙ]
where i x₀'s are prefixed to x
-/
def bblastSignExt : OptionM Term → OptionM Term → OptionM Term :=
  λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
             oi >>= λ i => sortOf i >>= λ si =>
  match s, si with
  | bv n, intSort =>
    match i with
    | val (Value.integer i₁) intSort =>
      match hd (bitOfN t n) with
      | some sign => mkBbT (List.append (List.replicate (Int.toNat i₁) sign) (bitOfN t n))
      | none => none
    | _ => none
  | _, _ => none
#check bblastSignExt (val (Value.bitvec [true, true, true, true]) (bv 4))
  (val (Value.integer 2) intSort)
#check bblastSignExt (val (Value.bitvec [false, true, true, true]) (bv 4))
  (val (Value.integer 2) intSort)
#check bblastSignExt (val (Value.bitvec [true, false]) (bv 2))
  (val (Value.integer 0) intSort)
-- Using variables
#check bblastSignExt (const (mkName "x") (bv 4)) (val (Value.integer 2) intSort)

-- Bit-blasting BvSignExt rule
axiom bbBvSignExt : ∀ {t₁ t₂ : OptionM Term},
  thHolds (mkEq (mkBvSignExt t₁ t₂) (bblastSignExt t₁ t₂))

end Term

end proof
