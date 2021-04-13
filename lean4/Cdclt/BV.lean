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
def mkBitOf : Option Term → Option Term → Option Term :=
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
   t is the BV Term and n is its length.
   bitOfN t n returns a list of length n
   with option Terms representing each bit.
-/
def bitOfNAux : Term → Nat → Nat → List (Option Term)
| t, 0, _ => []
| t, (n₁+1), n₂ => (mkBitOf t (val (value.integer (Int.ofNat (n₂ - n₁ - 1))) intSort))
                    :: (bitOfNAux t n₁ n₂)

def bitOfN : Term → Nat → List (Option Term) :=
  λ t n => bitOfNAux t n n

#eval bitOfN (const 21 (bv 4)) 4
#eval bitOfN (val (value.bitvec [true, true, true, false]) (bv 4)) 4
/- The following bad calls create bad bit-blasted Terms
   because the nat argument to bitOfN and the length
   of the BV Term don't match.-/
#eval bitOfN (const 21 (bv 3)) 4
#eval bitOfN (val (value.bitvec [true, true, true, false]) (bv 4)) 3


/- bitOfNRev works like bitOfN but in reverse -/
def bitOfNRevAux : Term → Nat → List (Option Term)
| t, 0 => (mkBitOf t (val (value.integer (Int.ofNat 0)) intSort)) :: []
| t, (n + 1) => (mkBitOf t (val (value.integer (Int.ofNat (n + 1))) intSort))
                    :: (bitOfNRevAux t n)

def bitOfNRev : Term → Nat → List (Option Term) :=
  λ t n => bitOfNRevAux t (n-1)

#eval bitOfNRev (const 21 (bv 4)) 4
#eval bitOfNRev (val (value.bitvec [true, true, true, false]) (bv 4)) 4
/- The following bad calls create bad bit-blasted Terms
   because the nat argument to bitOfN and the length
   of the BV Term don't match.-/
#eval bitOfNRev (const 21 (bv 3)) 4
#eval bitOfNRev (val (value.bitvec [true, true, true, false]) (bv 4)) 3


--------------------------------------- Bitwise Operators ---------------------------------------

/-
mkBbT l
Construct a BV Term that is a bbT (bit-blasted Term)
of the bools in l
-/
@[matchPattern] def mkBbT (l : List (Option Term)) : Option Term :=
  mkAppN (bbT (List.length l)) l

#eval mkBbT ([some top, some top, some top, some top])

/-
checkBinaryBV ot₁ ot₂ constr
If ot₁ and ot₂ are BVs of the same length, then
construct a bitwise op of (constr ot₁ ot₂)
-/
def checkBinaryBV : Option Term → Option Term →
  (Nat → Term → Term → Term) → Option Term :=
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
and returns an Option List of Option Terms that
has the bitwise application of const to the
respective elements of ot₁ and ot₂
-/
def bblastBvBitwise (ot₁ ot₂ : Option Term)
 (constructor : Option Term → Option Term → Option Term) : Option Term :=
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
def mkBvEq : Option Term → Option Term → Option Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvEq

/-
If Terms are well-typed, construct their bit-blasted BV eq
[x₀, x₁, ... , xₙ] = [y₀, y₁, ... , yₙ]
---------------------------------------
       x₀ = y₀ ∧ ... ∧ xₙ = yₙ
-/
def bblastBvEq : Option Term → Option Term → Option Term :=
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
#eval TermEval (bblastBvEq (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 010 = 010
#eval bblastBvEq (val (value.bitvec [false, true, false]) (bv 3))
  (val (value.bitvec [false, true, false]) (bv 3))
#eval TermEval (bblastBvEq (val (value.bitvec [false, true, false]) (bv 3))
  (val (value.bitvec [false, true, false]) (bv 3)))
-- Using variables
#eval bblastBvEq (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvEq (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvEq rule
axiom bbBvEq : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvEq t₁ t₂) (bblastBvEq t₁ t₂))


/- ------
 BV not
------- -/

-- If Term is a BV, construct its BV Not application
def mkBvNot : Option Term → Option Term :=
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
def bblastBvNot (ot : Option Term) : Option Term :=
  ot >>= λ t => sortOf t >>= λ s =>
    match s with
    | bv n => mkBbT (List.map mkNot (bitOfN t n))
    | _ => none
#eval bblastBvNot (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvNot (const 21 (bv 4))

-- Bit-blasting BvNot rule
axiom bbBvNot : ∀ {t : Option Term},
  thHolds (mkEq (mkBvNot t) (bblastBvNot t))


/- -------
 BV and
-------- -/

-- If Terms are well-typed, construct their BV And application
def mkBvAnd : Option Term → Option Term → Option Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvAnd

/-
If Terms are well-typed, construct their bit-blasted BV and
[x₀ x₁ ... xₙ] ∧bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ∧ y₀, x₁ ∧ x₂, ... xₙ ∧ yₙ]
-/
def bblastBvAnd : Option Term → Option Term → Option Term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkAnd

#eval bblastBvAnd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvAnd rule
axiom bbBvAnd : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvAnd t₁ t₂) (bblastBvAnd t₁ t₂))


/- -----
 BV or
----- -/

-- If Terms are well-typed, construct their BV Or application
def mkBvOr : Option Term → Option Term → Option Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvOr

/-
If Terms are well-typed, construct their bit-blasted BV or
[x₀ x₁ ... xₙ] ∨bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ∨ y₀, x₁ ∨ x₂, ... xₙ ∨ yₙ]
-/
def bblastBvOr : Option Term → Option Term → Option Term :=
  λ ot₁ ot₂ => bblastBvBitwise ot₁ ot₂ mkOr

#eval bblastBvOr (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvOr (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvOr (const 21 (bv 4)) (const 22 (bv 4))
#eval mkBbT (bitOfN (val (value.bitvec [true, true, true, true]) (bv 4)) 4)

-- Bit-blasting BvOr rule
axiom bbBvOr : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvOr t₁ t₂) (bblastBvOr t₁ t₂))


--------------------------------------- Comparison Operators ---------------------------------------

/- -------------------
 BV unsigned less than
--------------------- -/

-- If Terms are well-typed, construct their BV Ult application
def mkBvUlt : Option Term → Option Term → Option Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUlt

/-
[x₀, x₁, ... , xₙ] <ᵤ [y₀, y₁, ... , yₙ] =
  (¬x₀ ∧ y₀) ∨ ((x₀ ↔ y₀) ∧ ([x₁, ... , xₙ] <ᵤ [y₁, ... , yₙ]))
-/
def boolListUlt : List (Option Term) → List (Option Term) → Option Term
| [h₁], [h₂] => mkAnd (mkNot h₁) h₂
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd (mkNot h₁) h₂) (mkAnd (mkEq h₁ h₂) (boolListUlt t₁ t₂)))
| _, _ => none

/-
If Terms are well-typed, construct their bit-blasted
unsigned less than comparison
-/
def bblastBvUlt : Option Term → Option Term → Option Term :=
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
#eval TermEval (bblastBvUlt (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 0010 <ᵤ 0011
#eval bblastBvUlt (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.bitvec [false, false, true, true]) (bv 4))
#eval TermEval (bblastBvUlt (val (value.bitvec [false, false, true, false]) (bv 4))
  (val (value.bitvec [false, false, true, true]) (bv 4)))
-- 10 <ᵤ 01
#eval bblastBvUlt (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2))
#eval TermEval (bblastBvUlt (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2)))
-- Using variables
#eval bblastBvUlt (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvUlt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUlt rule
axiom bbBvUlt : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvUlt t₁ t₂) (bblastBvUlt t₁ t₂))


/- ----------------------
 BV unsigned greater than
----------------------- -/

-- If Terms are well-typed, construct their BV Ugt application
def mkBvUgt : Option Term → Option Term → Option Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUgt

/-
[x₀, x₁, ... , xₙ] >ᵤ [y₀, y₁, ... , yₙ] =
  (x₀ ∧ ¬y₀) ∨ ((x₀ ↔ y₀) ∧ ([x₁, ... , xₙ] >ᵤ [y₁, ... , yₙ]))
-/
def boolListUgt : List (Option Term) → List (Option Term) → Option Term
| [h₁], [h₂] => mkAnd h₁ (mkNot h₂)
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd h₁ (mkNot h₂)) (mkAnd (mkEq h₁ h₂) (boolListUgt t₁ t₂)))
| _, _ => none

/-
If Terms are well-typed, construct their bit-blasted
unsigned greater than comparison
-/
def bblastBvUgt : Option Term → Option Term → Option Term :=
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
#eval TermEval (bblastBvUgt (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4)))
-- 0011 >ᵤ 0010
#eval bblastBvUgt (val (value.bitvec [false, false, true, true]) (bv 4))
  (val (value.bitvec [false, false, true, false]) (bv 4))
#eval TermEval (bblastBvUgt (val (value.bitvec [false, false, true, true]) (bv 4))
  (val (value.bitvec [false, false, true, false]) (bv 4)))
-- 01 >ᵤ 10
#eval bblastBvUgt (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2))
#eval TermEval (bblastBvUgt (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2)))
-- Using variables
#eval bblastBvUgt (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvUgt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUgt rule
axiom bbBvUgt : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvUgt t₁ t₂) (bblastBvUgt t₁ t₂))


/- -------------------
 BV signed less than
------------------- -/

-- If Terms are well-typed, construct their BV Slt application
def mkBvSlt : Option Term → Option Term → Option Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSlt

/-
[x₀, x₁, ... , xₙ] <ₛ [y₀, y₁, ... , yₙ] =
  (x₀ ∧ ¬y₀) ∨ (x₀ = y₀ ∧ ([x₁, ..., xₙ] <ᵤ [y₁, ..., yₙ]))
-/
def boolListSlt : List (Option Term) → List (Option Term) → Option Term
| [h₁], [h₂] => (mkAnd h₁ (mkNot h₂))
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd h₁ (mkNot h₂)) (mkAnd (mkEq h₁ h₂) (boolListUlt t₁ t₂)))
| _, _ => none

/-
If Terms are well-typed, construct their bit-blasted
signed less than comparison
-/
def bblastBvSlt : Option Term → Option Term → Option Term :=
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
#eval TermEval (bblastBvSlt (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4)))
-- 1010 <ₛ 1011
#eval bblastBvSlt (val (value.bitvec [true, false, true, false]) (bv 4))
  (val (value.bitvec [true, false, true, true]) (bv 4))
#eval TermEval (bblastBvSlt (val (value.bitvec [true, false, true, false]) (bv 4))
  (val (value.bitvec [true, false, true, true]) (bv 4)))
-- 01 <ₛ 10
#eval bblastBvSlt (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2))
#eval TermEval (bblastBvSlt (val (value.bitvec [false, true]) (bv 2))
  (val (value.bitvec [true, false]) (bv 2)))
-- Using variables
#eval bblastBvSlt (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvSlt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUgt rule
axiom bbBvSlt : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvSlt t₁ t₂) (bblastBvSlt t₁ t₂))


/- ----------------------
 BV signed greater than
----------------------- -/

-- If Terms are well-typed, construct their BV Sgt application
def mkBvSgt : Option Term → Option Term → Option Term :=
  λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSgt

/-
[x₀, x₁, ... , xₙ] >ₛ [y₀, y₁, ... , yₙ] =
  (¬x₀ ∧ y₀) ∨ (x₀ = y₀ ∧ ([x₁, ..., xₙ] >ᵤ [y₁, ..., yₙ]))
-/
def boolListSgt : List (Option Term) → List (Option Term) → Option Term
| [h₁], [h₂] => (mkAnd (mkNot h₁) h₂)
| (h₁ :: t₁), (h₂ :: t₂) => (mkOr (mkAnd (mkNot h₁) h₂) (mkAnd (mkEq h₁ h₂) (boolListUgt t₁ t₂)))
| _, _ => none

/-
If Terms are well-typed, construct their bit-blasted
signed greater than comparison
-/
def bblastBvSgt : Option Term → Option Term → Option Term :=
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
#eval TermEval (bblastBvSgt (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 1011 >ₛ 1010
#eval bblastBvSgt (val (value.bitvec [true, false, true, true]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4))
#eval TermEval (bblastBvSgt (val (value.bitvec [true, false, true, true]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4)))
-- 10 >ₛ 01
#eval bblastBvSgt (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2))
#eval TermEval (bblastBvSgt (val (value.bitvec [true, false]) (bv 2))
  (val (value.bitvec [false, true]) (bv 2)))
-- Using variables
#eval bblastBvSgt (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvSgt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvSgt rule
axiom bbBvSgt : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvSgt t₁ t₂) (bblastBvSgt t₁ t₂))


--------------------------------------- Arithmetic Operators ---------------------------------------

/- -----------
 BV addition
----------- -/

-- If Terms are well-typed, construct their BV plus application
def mkBvAdd : Option Term → Option Term → Option Term :=
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
def bitAdder : Option Term → Option Term → Option Term → Option Term × Option Term
| x, y, carry => (mkXor (mkXor x y) carry,
  mkOr (mkAnd x y) (mkAnd (mkXor x y) carry))
#eval (bitAdder top top top)
#eval TermEval (bitAdder top top top).1
#eval TermEval (bitAdder top top top).2
def boolListAddAux : Option Term → List (Option Term) → List (Option Term) → List (Option Term)
| c, (h₁ :: t₁), (h₂ :: t₂) => (bitAdder h₁ h₂ c).1 :: (boolListAddAux (bitAdder h₁ h₂ c).2 t₁ t₂)
| c, [], [] => []
| _, _, _ => []
def boolListAdd : List (Option Term) → List (Option Term) → Option Term
| l₁, l₂ => mkBbT (List.reverse (boolListAddAux bot l₁ l₂))

-- If Terms are well-typed, construct their bit-blasted BV add
def bblastBvAdd : Option Term → Option Term → Option Term :=
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
#eval bblastBvAdd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval TermEval (bblastBvAdd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 1111 + 1111
#eval bblastBvAdd (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval TermEval (bblastBvAdd (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4)))
-- 0101 + 1010
#eval bblastBvAdd (val (value.bitvec [false, true, false, true]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4))
#eval TermEval (bblastBvAdd (val (value.bitvec [false, true, false, true]) (bv 4))
  (val (value.bitvec [true, false, true, false]) (bv 4)))
-- 1111 + 0001
#eval bblastBvAdd (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, true]) (bv 4))
#eval TermEval (bblastBvAdd (val (value.bitvec [true, true, true, true]) (bv 4))
  (val (value.bitvec [false, false, false, true]) (bv 4)))
-- Using variables
#eval bblastBvAdd (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvAdd (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvAdd rule
axiom bbBvAdd : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvAdd t₁ t₂) (bblastBvAdd t₁ t₂))


/- -----------
 BV Negation
------------ -/

-- If Term is a BV, construct its BV Neg application
def mkBvNeg : Option Term → Option Term :=
  λ ot => ot >>= λ t => sortOf t >>= λ s =>
  match s with
  | bv n => bvNot n t
  | _ => none

/- genRevOne n generates the list
   [(some top) (some bot) ... (some bot)]
   where there are n-1 (some bot) elements -/
def genZeros : Nat → List (Option Term)
| 0 => []
| n + 1 => (some bot) :: genZeros n
def genRevOne : Nat → List (Option Term) :=
  λ n => (some top) :: genZeros (n - 1)
#eval genZeros 3
#eval genRevOne 4

/-
If Term is well-typed, construct its bit-blasted BV neg
-bv x = ((¬bv x) +bv 1)
          OR
bvneg x = bvadd (bvnot x) 1
-/
def bblastBvNeg : Option Term → Option Term :=
  λ ot =>
  ot >>= λ t => sortOf t >>= λ s =>
    match s with
    |  bv m => boolListAdd (List.map mkNot (bitOfNRev t m)) (genRevOne m)
    | _ => some bot
-- -0000
#eval bblastBvNeg (val (value.bitvec [false, false, false, false]) (bv 4))
#eval TermEval (bblastBvNeg (val (value.bitvec [false, false, false, false]) (bv 4)))
-- -0001
#eval bblastBvNeg (val (value.bitvec [false, false, false, true]) (bv 4))
#eval TermEval (bblastBvNeg (val (value.bitvec [false, false, false, true]) (bv 4)))
-- -1111
#eval bblastBvNeg (val (value.bitvec [true, true, true, true]) (bv 4))
#eval TermEval (bblastBvNeg (val (value.bitvec [true, true, true, true]) (bv 4)))
-- Using variables
#eval bblastBvNeg (const 21 (bv 4))

-- Bit-blasting BvNeg rule
axiom bbBvNeg : ∀ {t : Option Term},
  thHolds (mkEq (mkBvNeg t) (bblastBvNeg t))


---------------------------- BV Length Manipulating Operators ----------------------------

/- -----------
 BV Extraction
------------ -/

-- If Terms are well-typed, construct their BV Extraction application
def mkBvExtract : Option Term → Option Term → Option Term → Option Term :=
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
If Terms are well-typed, construct their bit-blasted BV extraction
[x₀ ... xₙ]   0 ≤ j ≤ i < n
----------------------------
       [xⱼ ... xᵢ]
-/
def bblastBvExtract : Option Term → Option Term → Option Term → Option Term :=
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
axiom bbBvExtract : ∀ {t₁ t₂ t₃ : Option Term},
  thHolds (mkEq (mkBvExtract t₁ t₂ t₃) (bblastBvExtract t₁ t₂ t₃))


/- ---------------
 BV Concatenation
---------------- -/

-- If Terms are well-typed, construct their BV concat application
def mkBvConcat : Option Term → Option Term → Option Term :=
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
def bblastBvConcat : Option Term → Option Term → Option Term :=
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
axiom bbBvConcat : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvConcat t₁ t₂) (bblastBvAdd t₁ t₂))


/- ---------------
 BV Zero Extend
---------------- -/

-- If Terms are well-typed, construct their BV zero extend application
def mkBvZeroExt : Option Term → Option Term → Option Term :=
  λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
             oi >>= λ i => sortOf i >>= λ si =>
  match s, si with
  | bv n, intSort =>
    match i with
    | val (value.integer i₁) intSort => bvZeroExt n (Int.toNat i₁) t i
    | _ => none
  | _, _ => none

/-
If Terms are well-typed, construct their bit-blasted BV zero extend
     [x₀ x₁ ... xₙ]    i
-----------------------------
  [0₁ ... 0ᵢ x₀ x₁ ... xₙ]
-/
def bblastZeroExt : Option Term → Option Term → Option Term :=
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
axiom bbBvZeroExt : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvZeroExt t₁ t₂) (bblastZeroExt t₁ t₂))


/- ---------------
 BV Sign Extend
---------------- -/

-- If Terms are well-typed, construct their BV sign extend application
def mkBvSignExt : Option Term → Option Term → Option Term :=
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
If Terms are well-typed, construct their bit-blasted BV sign extend
     [x₀ x₁ ... xₙ]    i
-----------------------------
  [x₀ ... x₀ x₀ x₁ ... xₙ]
where i x₀'s are prefixed to x
-/
def bblastSignExt : Option Term → Option Term → Option Term :=
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
axiom bbBvSignExt : ∀ {t₁ t₂ : Option Term},
  thHolds (mkEq (mkBvSignExt t₁ t₂) (bblastSignExt t₁ t₂))


end Term

end proof
