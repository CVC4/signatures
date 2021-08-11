import Cdclt.Term
import Cdclt.Boolean
import Cdclt.TermEval

open proof
open proof.sort proof.term
open rules

namespace bvRules

/-
Endian-ness:
We represent a BV value as:
MSB ... LSB
(bv 4) representation of decimal 1:
0001 ([false, false, false, true])
-/

--------------------------------------- Aux Functions ------------------------------------

-- Nat to BV
def pad : List Bool → Nat → List Bool
| l, 0 => l
| l, (n+1) => false :: (pad l n)

partial def nat2BVAux : Nat → List Bool
| 0 => []
| n => List.append (nat2BVAux (n/2)) [if (n % 2 = 1) then true else false]

def nat2BV (n size : Nat) : term :=
  let res := (nat2BVAux n)
  if (List.length res ≤ size) then
    mkValBV (pad res (size - (List.length res)))
  else undef

#eval nat2BV 4 4

-- log 2
partial def log2 : Nat → Nat
| 0 => 0
| 1 => 0
| n => log2 (n/2) + 1

def mkZero (n : Nat) : term :=
  mkValBV (List.replicate n false)

def mkOnes (n : Nat) : term :=
  mkValBV (List.replicate n true)

--------------------------------------- Bit Of ---------------------------------------

/- mkBitOf bv n returns the nth element
   of bv if it exists; none otherwise -/
def mkBitOf : OptionM term → OptionM term → OptionM term :=
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
    | _ => bitOf t₁ t₂) else none
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
def bitOfListAux : Nat → term →  Nat → List term
| n, t, 0 => bitOf t (mkValInt (Int.ofNat (n - 1))) :: []
| n, t, (i + 1) => if i+1 >= n then [] else
                   (bitOf t (mkValInt
                                (Int.ofNat (n - (i + 1) - 1)))
                   ) :: (bitOfListAux n t i)

def bitOfList (n : Nat) (t : term) : List term :=  bitOfListAux n t (n-1)

#eval bitOfList 4 (const 21 (bv 4))
#eval bitOfList 4 (mkValBV [true, true, true, false])
/- The following bad calls create bad bit-blasted terms
   because the nat argument to bitOfList and the length
   of the BV term don't match.-/
-- #eval bitOfList (const 21 (bv 3)) 4
-- #eval bitOfList (mkValBV [true, true, true, false]) 3


/- bitOfNRev works like bitOfN but in reverse -/
def bitOfListRevAux : Nat → term → Nat → List term
| n, t, 0 => bitOf t (mkValInt (Int.ofNat 0)) :: []
| n, t, (i + 1) => if i+1 >= n then [] else
                   (bitOf t (mkValInt
                                (Int.ofNat (i + 1)))
                   ) :: (bitOfListRevAux n t i)

def bitOfListRev (n : Nat) (t: term) : List term := bitOfListRevAux n t (n-1)

#eval bitOfListRev 4 (const 21 (bv 4))
#eval bitOfListRev 4 (mkValBV [true, true, true, false])
/- The following bad calls create bad bit-blasted terms
   because the nat argument to bitOfList and the length
   of the BV term don't match.-/
-- #eval bitOfListRev (const 21 (bv 3)) 4
-- #eval bitOfListRev (mkValBV [true, true, true, false]) 3

/- bitOfN t n
   bit-blasts a BV constant or variable.
   t is the BV term and n is its length.
   bitOfN t n returns a list of length n
   with option terms representing each bit.
-/

def bbTtoListAux : Nat → term →  Nat → List term
| n, (bbT • t), 0 => [t]
| n, (t₁ • t₂), (i + 1) => List.concat (bbTtoListAux n t₁ i) t₂
| _, _, _ => []

def bbTtoList (n : Nat) (t : term) : List term :=  bbTtoListAux n t (n-1)

--------------------------------------- Bitwise Operators ---------------------------------------

/-
mkBbT l
Construct a BV term that is a bbT (bit-blasted term)
of the bools in l
-/
@[matchPattern] def mkBbT (l : List term) : term :=
  appN bbT l

#eval mkBbT ([top, top, top, top])

/-
checkBinaryBV ot₁ ot₂ constr
If ot₁ and ot₂ are BVs of the same length, then
construct a bitwise op of (constr ot₁ ot₂)
-/
def checkBinaryBV : OptionM term → OptionM term →
  (Nat → term → term → term) → OptionM term :=
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
and returns an OptionM List of OptionM terms that
has the bitwise application of const to the
respective elements of ot₁ and ot₂
-/
def bblastBvBitwise (n : Nat) (t₁ t₂ : term)
                    (constructor : term → term → term) : term :=
    mkBbT (zip (bbTtoList n t₁) (bbTtoList n t₂) constructor)

/- ------------------------
 BV values and variables
--------------------------- -/

---- Values
def bblastBvVal : term → term
| val (value.bitvec l) (bv n) => mkBbTVal bbT l
| _ => undef

#eval bblastBvVal (mkValBV [true, false, true])

axiom bbBvVal : ∀ {t : term},
  thHolds (eq t (bblastBvVal t))

#check (bbBvVal : thHolds (eq (mkValBV [true, false, true]) (bbT • top • bot • top)))

---- Variables
def bblastBvVar (n : Nat) (t : term) : term := mkBbTVar n n bbT t

#eval bblastBvVar 2 (mkValBV [true, false])

axiom bbBvVar : ∀ {t : term} (n : Nat),
  thHolds (eq t (bblastBvVar n t))

def tbv := const 1001 (bv 2)
#check (bbBvVar 2 : thHolds (eq tbv (bbT • (bitOf tbv (mkValInt 0)) • (bitOf tbv (mkValInt 1)))))

/- -----------
 BV equality
----------- -/

-- If terms are well-typed, construct their BV Eq application
-- def mkBvEq : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ eq

/-
If terms are well-typed, construct their bit-blasted BV eq
  [xₙ ... x₁ x₀] = [yₙ ... y₀ y₁]
------------------------------------
    xₙ = yₙ ∧ ... ∧ x₀ = y₀
-/
def bblastBvEq (n : Nat) (t₁ t₂ : term) : term :=
  andN (zip (bbTtoList n t₁) (bbTtoList n t₂) eq)

-- 0000 = 1111
#eval bblastBvEq 4
                 (bblastBvVal $ mkValBV [false, false, false, false])
                 (bblastBvVal $ mkValBV [true, true, true, true])

#eval termEval (bblastBvEq 4 (bblastBvVal $ mkValBV [false, false, false, false]) (bblastBvVal $ mkValBV [true, true, true, true]))

-- 010 = 010
#eval bblastBvEq 3 (bblastBvVal $ mkValBV [false, true, true])
  (bblastBvVal $ mkValBV [false, true, true])
#eval termEval (bblastBvEq 3 (bblastBvVal $ mkValBV [false, true, true])
  (bblastBvVal $ mkValBV [false, true, true]))
-- Using variables
#eval bblastBvEq 4 (bblastBvVar 4 (const 21 (bv 4)))
  (bblastBvVal $ mkValBV [false, false, false, true])
#eval bblastBvEq 4 (bblastBvVar 4 (const 21 (bv 4))) (bblastBvVar 4 (const 22 (bv 4)))

-- Bit-blasting BvEq rule
axiom bbBvEq : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (eq t₁ t₂) (bblastBvEq n t₁ t₂))

def eqSimp : term → term → term
| top, t₂ => t₂
| bot, t₂ => not t₂
| t₁, top => t₁
| t₁, bot => not t₁
| t₁, t₂ => (eq t₁ t₂)

def bblastBvEqVal (n : Nat) (t₁ t₂ : term) : term :=
  andN (zip (bbTtoList n t₁) (bbTtoList n t₂) eqSimp)

#eval bblastBvEqVal 4 (bblastBvVar 4 (const 21 (bv 4)))
  (bblastBvVal $ mkValBV [false, false, false, true])

axiom bbBvEqVal : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (eq t₁ t₂) (bblastBvEqVal n t₁ t₂))

/-------
 BV not
------- -/

-- If term is a BV, construct its BV Not application
def mkBvNot : OptionM term → OptionM term :=
  λ ot => ot >>= λ t => sortOf t >>= λ s =>
  match s with
  | bv n => bvNot t
  | _ => none

/-
If term is a BV, construct its bit-blasted BV not
  ¬bv [xₙ ... x₁ x₀]
----------------------
  [¬xₙ ...  ¬x₁ ¬x₀]
-/
def bblastBvNot (n : Nat) (t : term) : term := mkBbT (List.map bvNot (bitOfList n t))

-- ¬0000
#eval bblastBvNot 4 (mkValBV [false, false, false, false])
#eval termEval (bblastBvNot 4 (mkValBV [false, false, false, false]))
-- ¬ 1010
#eval bblastBvNot 4 (mkValBV [true, false, true, false])
#eval termEval (bblastBvNot 4 (mkValBV [true, false, true, false]))
-- Using variables
#eval bblastBvNot 4 (const 21 (bv 4))

-- Bit-blasting BvNot rule
axiom bbBvNot : ∀ {t : term} (n : Nat),
  thHolds (eq (bvNot t) (bblastBvNot n t))


/- -------
 BV and
-------- -/

-- If terms are well-typed, construct their BV And application
-- def mkBvAnd : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvAnd

/-
If terms are well-typed, construct their bit-blasted BV and
    [xₙ ... x₁ x₀] ∧bv [yₙ ... y₀ y₁]
-----------------------------------------
    [xₙ ∧ yₙ ... x₁ ∧ y₁  x₀ ∧ y₀]
-/
def bblastBvAnd (n : Nat) (t₁ t₂ : term) : term := bblastBvBitwise n t₁ t₂ and

-- 0000 ∧ 1111
#eval bblastBvAnd 4 (bblastBvVal $ mkValBV [false, false, false, false])
  (bblastBvVal $ mkValBV [true, true, true, true])
#eval termEval (bblastBvAnd 4 (bblastBvVal $ mkValBV [false, false, false, false])
  (bblastBvVal $ mkValBV [true, true, true, true]))
-- 0111 ∧ 1101
#eval bblastBvAnd 4 (bblastBvVal $ mkValBV [false, true, true, true])
  (bblastBvVal $ mkValBV [true, true, false, true])
#eval termEval (bblastBvAnd 4 (bblastBvVal $ mkValBV [false, true, true, true])
  (bblastBvVal $ mkValBV [true, true, false, true]))
-- Using variables
#eval bblastBvAnd 4 (bblastBvVar 4 (const 21 (bv 4)))
  (bblastBvVal $ mkValBV [false, false, false, false])
#eval bblastBvAnd 4 (bblastBvVar 4 (const 21 (bv 4))) (bblastBvVar 4 (const 22 (bv 4)))

-- Bit-blasting BvAnd rule
axiom bbBvAnd : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvAnd t₁ t₂) (bblastBvAnd n t₁ t₂))

def andSimp : term → term → term
| top, t₂ => t₂
| bot, t₂ => bot
| t₁, top => t₁
| t₁, bot => bot
| t₁, t₂ => (and t₁ t₂)

def bblastBvAndVal (n : Nat) (t₁ t₂ : term) : term :=
  bblastBvBitwise n t₁ t₂ andSimp

#eval bblastBvAndVal 4 (bblastBvVar 4 (const 21 (bv 4)))
  (bblastBvVal $ mkValBV [false, false, false, true])

axiom bbBvAndVal : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvAnd t₁ t₂) (bblastBvAndVal n t₁ t₂))

/------
 BV or
----- -/

-- If terms are well-typed, construct their BV Or application
-- def mkBvOr : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvOr

/-
If terms are well-typed, construct their bit-blasted BV or
   [xₙ ... x₁ x₀] ∨bv [yₙ ... y₀ y₁]
-----------------------------------------
     [xₙ ∨ yₙ ... x₁ ∨ y₁  x₀ ∨ y₀]
-/
def bblastBvOr (n : Nat) (t₁ t₂ : term) : term :=
  bblastBvBitwise n t₁ t₂ bvOr

-- 0000 ∨ 1111
#eval bblastBvOr 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvOr 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0101 ∨ 1010
#eval bblastBvOr 4 (mkValBV [false, true, false, true])
  (mkValBV [true, false, true, false])
#eval termEval (bblastBvOr 4 (mkValBV [false, true, false, true])
  (mkValBV [true, false, true, false]))
-- Using variables
#eval bblastBvOr 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvOr 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvOr rule
axiom bbBvOr : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvOr t₁ t₂) (bblastBvOr n t₁ t₂))


/- ------
 BV Xor
------ -/

-- If terms are well-typed, construct their BV Xor application
-- def mkBvXor : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvXor

/-
If terms are well-typed, construct their bit-blasted BV xor
   [xₙ ... x₁ x₀] ⊕bv [yₙ ... y₀ y₁]
-----------------------------------------
     [xₙ ⊕ yₙ ... x₁ ⊕ y₁  x₀ ⊕ y₀]
-/
def bblastBvXor (n : Nat) (t₁ t₂ : term) : term :=
  bblastBvBitwise n t₁ t₂ bvXor

-- 0000 ⊕ 1111
#eval bblastBvXor 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvXor 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 1111 ⊕ 1111
#eval bblastBvXor 4 (mkValBV [true, true, true, true])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvXor 4 (mkValBV [true, true, true, true])
  (mkValBV [true, true, true, true]))
-- Using variables
#eval bblastBvXor 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvXor 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvXor rule
axiom bbBvXor : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvXor t₁ t₂) (bblastBvXor n t₁ t₂))


/- -------
 BV Nand
------- -/

-- If terms are well-typed, construct their BV Nand application
-- def mkBvNand : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvNand

/-
If terms are well-typed, construct their bit-blasted BV Nand
    [xₙ ... x₁ x₀] ¬∧bv [yₙ ... y₀ y₁]
-------------------------------------------
    [xₙ ¬∧ yₙ ... x₁ ¬∧ y₁  x₀ ¬∧ y₀]
-/
def bblastBvNand (n : Nat) (t₁ t₂ : term) : term :=
  bblastBvBitwise n t₁ t₂ bvNand

-- 0000 ¬∧ 1111
#eval bblastBvNand 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvNand 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0111 ¬∧ 1101
#eval bblastBvNand 4 (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true])
#eval termEval (bblastBvNand 4 (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true]))
-- Using variables
#eval bblastBvNand 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvNand 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvNand rule
axiom bbBvNand : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvNand t₁ t₂) (bblastBvNand n t₁ t₂))


/- -------
 BV Nor
------- -/

-- If terms are well-typed, construct their BV Nor application
-- def mkBvNor : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvNor

/-
If terms are well-typed, construct their bit-blasted BV Nand
    [xₙ ... x₁ x₀] ¬∨bv [yₙ ... y₀ y₁]
-------------------------------------------
    [xₙ ¬∨ yₙ ... x₁ ¬∨ y₁  x₀ ¬∨ y₀]
-/
def bblastBvNor (n : Nat) (t₁ t₂ : term) : term :=
  bblastBvBitwise n t₁ t₂ bvNor

-- 0000 ¬∨ 1111
#eval bblastBvNor 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvNor 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0111 ¬∨ 1101
#eval bblastBvNor 4 (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true])
#eval termEval (bblastBvNor 4 (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true]))
-- Using variables
#eval bblastBvNor 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvNor 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvNor rule
axiom bbBvNor : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvNor t₁ t₂) (bblastBvNor n t₁ t₂))


/- -------
 BV Xnor
------- -/

-- If terms are well-typed, construct their BV Xnor application
-- def mkBvXnor : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvXnor

/-
If terms are well-typed, construct their bit-blasted BV Nand
    [xₙ ... x₁ x₀] ¬⊕bv [yₙ ... y₀ y₁]
-------------------------------------------
      [xₙ ↔ yₙ ... x₁ ↔ y₁  x₀ ↔ y₀]
-/
def bblastBvXnor (n : Nat) (t₁ t₂ : term) : term :=
  bblastBvBitwise n t₁ t₂ eq

-- 1111 ¬⊕ 1111
#eval bblastBvXnor 4 (mkValBV [true, true, true, true])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvXnor 4 (mkValBV [true, true, true, true])
  (mkValBV [true, true, true, true]))
-- 0111 ¬⊕ 1101
#eval bblastBvXnor 4 (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true])
#eval termEval (bblastBvXnor 4 (mkValBV [false, true, true, true])
  (mkValBV [true, true, false, true]))
-- Using variables
#eval bblastBvXnor 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvXnor 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvNor rule
axiom bbBvXnor : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvXnor t₁ t₂) (bblastBvXnor n t₁ t₂))


--------------------------------------- Comparison Operators ---------------------------------------

/- ------
BV Comp
------ -/

-- If terms are well-typed, construct their BV Comp application
-- def mkBvComp : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvComp

/-
If terms are well-typed, construct their bit-blasted
bv comp
          bvComp [xₙ ... x₁ x₀] [yₙ ... y₀ y₁]
----------------------------------------------------------------
  ite ((xₙ = yₙ) ∧ ... ∧ (x₁ = x₂) ∧ (x₀ = y₀)) [true] [false]
-/
def bblastBvComp (n : Nat) (t₁ t₂ : term) : term :=
  fIte (bblastBvEq n t₁ t₂) (mkBbT [top]) (mkBbT [bot])

-- bvComp 0000 1111
#eval bblastBvComp 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvComp 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- bvComp 0010 0010
#eval bblastBvComp 4 (mkValBV [false, false, true, false])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvComp 4 (mkValBV [false, false, true, false])
  (mkValBV [false, false, true, false]))
-- Using variables
#eval bblastBvComp 4 (const 21 (bv 4))
  (mkValBV [true, false, false, false])
#eval bblastBvComp 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvComp rule
axiom bbBvComp : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvComp t₁ t₂) (bblastBvComp n t₁ t₂))


/- -------------------
 BV unsigned less than
--------------------- -/

-- If terms are well-typed, construct their BV Ult application
-- def mkBvUlt : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUlt

/-
                  [x₀ ... xₙ] <ᵤ [y₀ ... yₙ]
-------------------------------------------------------------------------
    (¬xₙ ∧ yₙ) ∨ ((xₙ ↔ yₙ) ∧ ([x_{n-1} ... x₀] <ᵤ [y_{n-1} ... y₀]))
-/
def bblastBvUltAux : List term → List term → term → term
| [], [], acc => acc
| (h₁ :: tl₁), (h₂ :: tl₂), acc =>
      bblastBvUltAux tl₁ tl₂ (or (and (eq h₂ h₁) acc) (and (not h₁) h₂))
| _, _, _ => undef

/-
If terms are well-typed, construct their bit-blasted
unsigned less than comparison
-/
def bblastBvUlt (n : Nat) (t₁ t₂ : term) : term :=
  let l₁ := (bbTtoList n t₁)
  let l₂ := (bbTtoList n t₂)
  match l₁, l₂ with
  | h₁::tl₁, h₂::tl₂ => bblastBvUltAux tl₁ tl₂ (and (not h₁) h₂)
  | _, _ => undef

-- 01 <ᵤ 10
#eval bblastBvUlt 2 (bblastBvVal $ mkValBV [true, false])
  (bblastBvVal $ mkValBV [false, true])

-- 0000 <ᵤ 1111
#eval bblastBvUlt 4 (bblastBvVal $ mkValBV [false, false, false, false])
  (bblastBvVal $ mkValBV [true, true, true, true])
#eval termEval (bblastBvUlt 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0010 <ᵤ 0011
#eval bblastBvUlt 4 (bblastBvVal $ mkValBV [false, true, false, false])
  (bblastBvVal $ mkValBV [true, true, false, false])
#eval termEval (bblastBvUlt 4 (mkValBV [false, true, false, false])
  (mkValBV [true, true, false, false]))

#eval termEval (bblastBvUlt 4 (bblastBvVal $ mkValBV [true, false])
  (bblastBvVal $ mkValBV [false, true]))
-- Using variables
#eval bblastBvVar 4 $ const 1001 (bv 4)
#eval bbTtoList 4 $ bblastBvVar 4 $ const 1001 (bv 4)
#eval bblastBvVal $ mkValBV [false, false, false, false]

#eval bblastBvUlt 4 (bblastBvVar 4 $ const 1001 (bv 4))
  (bblastBvVal $ mkValBV [false, false, false, false])

#eval bblastBvUlt 4 (const 21 (bv 4)) (const 1002 (bv 4))

-- Bit-blasting BvUlt rule
axiom bbBvUlt : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvUlt t₁ t₂) (bblastBvUlt n t₁ t₂))

def boolListUltVal : List term → List term → term → term
| [], [], acc => acc
| (h₁ :: tl₁), (bot :: tl₂), bot =>
      boolListUltVal tl₁ tl₂ bot
| (h₁ :: tl₁), (top :: tl₂), bot =>
      boolListUltVal tl₁ tl₂ (not h₁)
| (bot :: tl₁), (h₂ :: tl₂), bot =>
      boolListUltVal tl₁ tl₂ h₂
| (top :: tl₁), (h₂ :: tl₂), bot =>
      boolListUltVal tl₁ tl₂ bot
| (h₁ :: tl₁), (bot :: tl₂), acc =>
      boolListUltVal tl₁ tl₂ (and (not h₁) acc)
| (h₁ :: tl₁), (top :: tl₂), acc =>
      boolListUltVal tl₁ tl₂ (or (and h₁ acc) (not h₁))
| (bot :: tl₁), (h₂ :: tl₂), acc =>
      boolListUltVal tl₁ tl₂ (or (and (not h₂) acc) h₂)
| (top :: tl₁), (h₂ :: tl₂), acc =>
      boolListUltVal tl₁ tl₂ (and h₂ acc)
-- | (h₁ :: tl₁), (h₂ :: tl₂), acc =>
--       boolListUlt tl₁ tl₂ (or (and (eq h₂ h₁) acc) (and (not h₁) h₂))
| _, _, _ => undef

/-
If terms are well-typed, construct their bit-blasted
unsigned less than comparison
-/
def bblastBvUltVal (n : Nat) (t₁ t₂ : term) : term :=
  let l₁ := (bbTtoList n t₁)
  let l₂ := (bbTtoList n t₂)
  match l₁, l₂ with
  | h₁::tl₁, bot::tl₂ => boolListUltVal tl₁ tl₂ bot
  | h₁::tl₁, top::tl₂ => boolListUltVal tl₁ tl₂ (not h₁)
  | bot::tl₁, h₂::tl₂ => boolListUltVal tl₁ tl₂ h₂
  | top::tl₁, h₂::tl₂ => boolListUltVal tl₁ tl₂ bot
  | _, _ => undef

axiom bbBvUltVal : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvUlt t₁ t₂) (bblastBvUltVal n t₁ t₂))


/- -----------------------------------
 BV unsigned less than or equal to
----------------------------------- -/

-- If terms are well-typed, construct their BV Ule application
-- def mkBvUle : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUle

/-
If terms are well-typed, construct their bit-blasted
unsigned less than or equal to comparison
      x ≤ᵤ y
------------------
(x <ᵤ y) ∨ (x = y)

def bblastBvUle (n : Nat) (t₁ t₂ : term) : term :=
  let bitOfLt₁ := (bitOfList n t₁)
  let bitOfLt₂ := (bitOfList n t₂)
  term.or (boolListUlt bitOfLt₁ bitOfLt₂) (andN (zip bitOfLt₁ bitOfLt₂ eq))

-- 0000 ≤ᵤ 1111
#eval bblastBvUle 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvUle 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 0010 ≤ᵤ 0010
#eval bblastBvUle 4 (mkValBV [false, false, true, false])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvUle 4 (mkValBV [false, false, true, false])
  (mkValBV [false, false, true, false]))
-- 10 ≤ᵤ 01
#eval bblastBvUle 4 (mkValBV [true, false])
  (mkValBV [false, true])
#eval termEval (bblastBvUle 4 (mkValBV [true, false])
  (mkValBV [false, true]))
-- Using variables
#eval bblastBvUle 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvUle 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUle rule
axiom bbBvUle : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvUle t₁ t₂) (bblastBvUle n t₁ t₂))
-/

/- ----------------------
 BV unsigned greater than
----------------------- -/

-- If terms are well-typed, construct their BV Ugt application
-- def mkBvUgt : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUgt

/-
                  [xₙ ... x₁ x₀] >ᵤ [yₙ ... y₀ y₁]
-------------------------------------------------------------------------
   (xₙ ∧ ¬yₙ) ∨ ((xₙ ↔ yₙ) ∧ ([x_{n-1} ... x₀] >ᵤ [y_{n-1} ... y₀]))
-/
def boolListUgt : List term → List term → term
| [h₁], [h₂] => and h₁ (not h₂)
| (h₁ :: t₁), (h₂ :: t₂) => (or (and h₁ (not h₂)) (and (eq h₁ h₂) (boolListUgt t₁ t₂)))
| _, _ => undef

/-
If terms are well-typed, construct their bit-blasted
unsigned greater than comparison
-/
def bblastBvUgt (n : Nat) (t₁ t₂ : term) : term :=
  boolListUgt (bitOfList n t₁) (bitOfList n t₂)

-- 1111 >ᵤ 0000
#eval bblastBvUgt 4 (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvUgt 4 (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false]))
-- 0011 >ᵤ 0010
#eval bblastBvUgt 4 (mkValBV [false, false, true, true])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvUgt 4 (mkValBV [false, false, true, true])
  (mkValBV [false, false, true, false]))
-- 01 >ᵤ 10
#eval bblastBvUgt 4 (mkValBV [false, true])
  (mkValBV [true, false])
#eval termEval (bblastBvUgt 4 (mkValBV [false, true])
  (mkValBV [true, false]))
-- Using variables
#eval bblastBvUgt 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvUgt 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUgt rule
axiom bbBvUgt : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvUgt t₁ t₂) (bblastBvUgt n t₁ t₂))


/- ------------------------------------
 BV unsigned greater than pr equal to
------------------------------------- -/

-- If terms are well-typed, construct their BV Uge application
-- def mkBvUge : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvUge

/-
If terms are well-typed, construct their bit-blasted
unsigned greater than or equal to comparison
      x ≥ᵤ y
------------------
(x >ᵤ y) ∨ (x = y)
-/
def bblastBvUge (n : Nat) (t₁ t₂ : term) : term :=
  or (boolListUgt (bitOfList n t₁) (bitOfList n t₂))
     (andN (zip (bitOfList n t₁) (bitOfList n t₂) eq))


-- 1111 ≥ᵤ 0000
#eval bblastBvUge 4 (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvUge 4 (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false]))
-- 0011 ≥ᵤ 0011
#eval bblastBvUge 4 (mkValBV [false, false, true, true])
  (mkValBV [false, false, true, true])
#eval termEval (bblastBvUge 4 (mkValBV [false, false, true, true])
  (mkValBV [false, false, true, true]))
-- 01 ≥ᵤ 10
#eval bblastBvUge 4 (mkValBV [false, true])
  (mkValBV [true, false])
#eval termEval (bblastBvUge 4 (mkValBV [false, true])
  (mkValBV [true, false]))
-- Using variables
#eval bblastBvUge 4 (const 21 (bv 4))
  (mkValBV [false, false, false, true])
#eval bblastBvUge 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUge rule
axiom bbBvUge : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvUge t₁ t₂) (bblastBvUge n t₁ t₂))


/- -------------------
 BV signed less than
------------------- -/

-- If terms are well-typed, construct their BV Slt application
-- def mkBvSlt : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSlt

/-
                [xₙ ... x₁ x₀] <ₛ [yₙ ... y₀ y₁]
---------------------------------------------------------------------
  (xₙ ∧ ¬yₙ) ∨ (xₙ ↔ yₙ ∧ ([x_{n-1} ... x₀] <ᵤ [y_{n-1} ... y₀]))

def boolListSlt : List term → List term → term
| [h₁], [h₂] => (and h₁ (not h₂))
| (h₁ :: t₁), (h₂ :: t₂) => (term.or (and h₁ (not h₂)) (term.and (eq h₁ h₂) (boolListUlt t₁ t₂)))
| _, _ => undef

/-
If terms are well-typed, construct their bit-blasted
signed less than comparison
-/
def bblastBvSlt (n : Nat) (t₁ t₂ : term) : term :=
  boolListSlt (bitOfList n t₁) (bitOfList n t₂)

-- 1111 <ₛ 0000
#eval bblastBvSlt 4 (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvSlt 4 (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false]))
-- 1010 <ₛ 1011
#eval bblastBvSlt 4 (mkValBV [true, false, true, false])
  (mkValBV [true, false, true, true])
#eval termEval (bblastBvSlt 4 (mkValBV [true, false, true, false])
  (mkValBV [true, false, true, true]))
-- 01 <ₛ 10
#eval bblastBvSlt 4 (mkValBV [false, true])
  (mkValBV [true, false])
#eval termEval (bblastBvSlt 4 (mkValBV [false, true])
  (mkValBV [true, false]))
-- Using variables
#eval bblastBvSlt 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvSlt 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUgt rule
axiom bbBvSlt : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvSlt t₁ t₂) (bblastBvSlt n t₁ t₂))
-/

/- -------------------------------
 BV signed less than or equal to
-------------------------------- -/

-- If terms are well-typed, construct their BV Sle application
-- def mkBvSle : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSle

/-
If terms are well-typed, construct their bit-blasted
signed less than or equal to comparison
       x ≤ₛ y
------------------
(x <ₛ y) ∨ (x = y)

def bblastBvSle (n : Nat) (t₁ t₂ : term) : term :=
  or (boolListSlt (bitOfList n t₁) (bitOfList n t₂))
     (andN (zip (bitOfList n t₁) (bitOfList n t₂) eq))

-- 1111 ≤ₛ 0000
#eval bblastBvSle 4 (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvSle 4 (mkValBV [true, true, true, true])
  (mkValBV [false, false, false, false]))
-- 1010 ≤ₛ 1010
#eval bblastBvSle 4 (mkValBV [true, false, true, false])
  (mkValBV [true, false, true, false])
#eval termEval (bblastBvSle 4 (mkValBV [true, false, true, false])
  (mkValBV [true, false, true, false]))
-- 01 ≤ₛ 10
#eval bblastBvSle 4 (mkValBV [false, true])
  (mkValBV [true, false])
#eval termEval (bblastBvSle 4 (mkValBV [false, true])
  (mkValBV [true, false]))
-- Using variables
#eval bblastBvSle 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvSle 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvSle rule
axiom bbBvSle : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvSle t₁ t₂) (bblastBvSle n t₁ t₂))
-/

/- ----------------------
 BV signed greater than
----------------------- -/

-- If terms are well-typed, construct their BV Sgt application
-- def mkBvSgt : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSgt

/-
                [xₙ ... x₁ x₀] >ₛ [yₙ ... y₀ y₁]
----------------------------------------------------------------------
  (¬xₙ ∧ yₙ) ∨ (xₙ ↔ yₙ ∧ ([x_{n-1} ... x₀] >ᵤ [y_{n-1} ... y₀]))
-/
def boolListSgt : List term → List term → term
| [h₁], [h₂] => (and (not h₁) h₂)
| (h₁ :: t₁), (h₂ :: t₂) => (or (and (not h₁) h₂) (and (eq h₁ h₂) (boolListUgt t₁ t₂)))
| _, _ => undef

/-
If terms are well-typed, construct their bit-blasted
signed greater than comparison
-/
def bblastBvSgt (n : Nat) (t₁ t₂ : term) : term :=
  boolListSgt (bitOfList n t₁) (bitOfList n t₂)

-- 0000 >ₛ 1111
#eval bblastBvSgt 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvSgt 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 1011 >ₛ 1010
#eval bblastBvSgt 4 (mkValBV [true, false, true, true])
  (mkValBV [true, false, true, false])
#eval termEval (bblastBvSgt 4 (mkValBV [true, false, true, true])
  (mkValBV [true, false, true, false]))
-- 10 >ₛ 01
#eval bblastBvSgt 4 (mkValBV [true, false])
  (mkValBV [false, true])
#eval termEval (bblastBvSgt 4 (mkValBV [true, false])
  (mkValBV [false, true]))
-- Using variables
#eval bblastBvSgt 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvSgt 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvSgt rule
axiom bbBvSgt : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvSgt t₁ t₂) (bblastBvSgt n t₁ t₂))


/- ----------------------------------
 BV signed greater than or equal to
----------------------------------- -/

-- If terms are well-typed, construct their BV Sge application
-- def mkBvSge : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSge

/-
If terms are well-typed, construct their bit-blasted
signed greater than or equal to comparison
       x ≥ₛ y
------------------
(x >ₛ y) ∨ (x = y)
-/
def bblastBvSge (n : Nat) (t₁ t₂ : term) : term :=
  or (boolListSgt (bitOfList n t₁) (bitOfList n t₂))
     (andN (zip (bitOfList n t₁) (bitOfList n t₂) eq))

-- 0000 ≥ₛ 1111
#eval bblastBvSge 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true])
#eval termEval (bblastBvSge 4 (mkValBV [false, false, false, false])
  (mkValBV [true, true, true, true]))
-- 1011 ≥ₛ 1010
#eval bblastBvSge 4 (mkValBV [true, false, true, true])
  (mkValBV [true, false, true, true])
#eval termEval (bblastBvSge 4 (mkValBV [true, false, true, true])
  (mkValBV [true, false, true, true]))
-- 10 ≥ₛ 01
#eval bblastBvSge 4 (mkValBV [true, false])
  (mkValBV [false, true])
#eval termEval (bblastBvSge 4 (mkValBV [true, false])
  (mkValBV [false, true]))
-- Using variables
#eval bblastBvSge 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvSge 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvSge rule
axiom bbBvSge : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvSge t₁ t₂) (bblastBvSge n t₁ t₂))


--------------------------------------- Arithmetic Operators ---------------------------------------

/- -----------
 BV addition
----------- -/

-- If terms are well-typed, construct their BV plus application
-- def mkBvAdd : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvAdd

/-
After reversing the BVs to add:
    [x₀ x₁ ... xₙ] +bv [y₀ y₁ ... yₙ]
-----------------------------------------
[(x₀ ⊕ y₀) ⊕ car₀, ..., (xₙ ⊕ yₙ) ⊕ carₙ]
where car₀ = ⊥
      car_{i+1} = (xᵢ ∧ yᵢ) ∨ ((xᵢ ⊕ yᵢ) ∧ carᵢ)
Then reverse again
-/
def bitAdder : term → term → term → term × term
| x, y, carry => (xor (xor x y) carry,
  or (and x y) (and (xor x y) carry))

#eval (bitAdder top top top)
#eval termEval (bitAdder top top top).1
#eval termEval (bitAdder top top top).2

def boolListAddAux : term → List term → List term → List term
| c, (h₁ :: t₁), (h₂ :: t₂) => (bitAdder h₁ h₂ c).1 :: (boolListAddAux (bitAdder h₁ h₂ c).2 t₁ t₂)
| c, [], [] => []
| _, _, _ => []

def boolListAdd (l₁ l₂ : List term) : term :=
  mkBbT (boolListAddAux bot l₁ l₂)

-- If terms are well-typed, construct their bit-blasted BV add
def bblastBvAdd (n : Nat) (t₁ t₂ : term) : term :=
  boolListAdd (bbTtoList n t₁) (bbTtoList n t₂)

-- 0000 + 1111
#eval bblastBvAdd 4 (bblastBvVal $ mkValBV [false, false, false, false])
  (bblastBvVal $ mkValBV [true, true, true, true])
#eval termEval (bblastBvAdd 4 (bblastBvVal $ mkValBV [false, false, false, false])
  (bblastBvVal $ mkValBV [true, true, true, true]))
-- 1111 + 1111
#eval bblastBvAdd 4 (bblastBvVal $ mkValBV [true, true, true, true])
  (bblastBvVal $ mkValBV [true, true, true, true])
#eval termEval (bblastBvAdd 4 (bblastBvVal $ mkValBV [true, true, true, true])
  (bblastBvVal $ mkValBV [true, true, true, true]))
-- 0101 + 0010
#eval bblastBvAdd 4 (bblastBvVal $ mkValBV [false, true, false, false])
  (bblastBvVal $ mkValBV [true, false, true, false])
#eval termEval (bblastBvAdd 4 (bblastBvVal $ mkValBV [false, true, false, false])
  (bblastBvVal $ mkValBV [true, false, true, false]))
-- 1111 + 0001
#eval bblastBvAdd 4 (bblastBvVal $ mkValBV [true, true, true, true])
  (bblastBvVal $ mkValBV [false, false, false, true])
#eval termEval (bblastBvAdd 4 (bblastBvVal $ mkValBV [true, true, true, true])
  (bblastBvVal $ mkValBV [false, false, false, true]))
-- Using variables
#eval bblastBvAdd 4 (bblastBvVar 4 (const 21 (bv 4)))
  (bblastBvVal $ mkValBV [false, false, false, false])
#eval bblastBvAdd 4 ( bblastBvVar 4 (const 21 (bv 4))) (bblastBvVar 4 (const 22 (bv 4)))

-- Bit-blasting BvAdd rule
axiom bbBvAdd : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvAdd t₁ t₂) (bblastBvAdd n t₁ t₂))

/- -----------
 BV Negation
------------ -/

-- If term is a BV, construct its BV Neg application
-- def mkBvNeg : OptionM term → OptionM term :=
--   λ ot => ot >>= λ t => sortOf t >>= λ s =>
--   match s with
--   | bv n => bvNot n t
--   | _ => none

/- genRevOne n generates the list
   [(some top) (some bot) ... (some bot)]
   where there are n-1 (some bot) elements -/
def genZeros : Nat → List term
| 0 => []
| n + 1 => bot :: genZeros n

def genRevOne : Nat → List term :=
  λ n => top :: genZeros (n - 1)

#eval genZeros 3
#eval genRevOne 4

/-
If term is well-typed, construct its bit-blasted BV neg
-bv x = ((¬bv x) +bv 1)
          OR
bvneg x = bvadd (bvnot x) 1
-/
def bblastBvNeg (n : Nat) (t : term) : term :=
  boolListAdd (List.map term.not (bitOfListRev n t)) (genRevOne n)

-- -0000
#eval bblastBvNeg 4 (mkValBV [false, false, false, false])
#eval termEval (bblastBvNeg 4 (mkValBV [false, false, false, false]))
-- -0001
#eval bblastBvNeg 4 (mkValBV [false, false, false, true])
#eval termEval (bblastBvNeg 4 (mkValBV [false, false, false, true]))
-- -1111
#eval bblastBvNeg 4 (mkValBV [true, true, true, true])
#eval termEval (bblastBvNeg 4 (mkValBV [true, true, true, true]))
-- Using variables
#eval bblastBvNeg 4 (const 21 (bv 4))

-- Bit-blasting BvNeg rule
axiom bbBvNeg : ∀ {t : term} (n : Nat),
  thHolds (eq (bvNeg t) (bblastBvNeg n t))


/- --------------
 BV Subtraction
--------------- -/

-- If terms are well-typed, construct their BV minus application
-- def mkBvSub : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvSub

/-
If term is well-typed, construct its bit-blasted BV sub
x -bv y = +(x, ¬y, 1)
          OR
bvneg x = bvadd (x, bvnot y, 1)
-/
def bblastBvSub (n : Nat) (t₁ t₂ : term) : term :=
  mkBbT (List.reverse (boolListAddAux
    top
    (bitOfListRev n t₁)
    ((List.map term.not (bitOfListRev n t₂)))))

-- 1110-0000
#eval bblastBvSub 4 (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvSub 4 (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false]))
-- 0000-0010
#eval bblastBvSub 4 (mkValBV [false, false, false, false])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvSub 4 (mkValBV [false, false, false, false])
  (mkValBV [false, false, true, false]))
-- Using variables
#eval bblastBvSub 4 (const 21 (bv 4)) (mkValBV [false, false, false, false])
#eval bblastBvSub 4 (const 21 (bv 4)) (const 22 (bv 4))
-- Bit-blasting BvNeg rule
axiom bbBvSub : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvSub t₁ t₂) (bblastBvSub n t₁ t₂))


--------------------------------------- Shift Operators ---------------------------------------

/- -----------
 BV Left Shift
----------- -/

-- If terms are well-typed, construct their BV left shift application
-- def mkBvShl : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvShl

/-
Single left shift:
[xₙ ... x₀] → [x_{n-1} ... x₀ 0]
-/
def leftShiftVal : List Bool → List Bool
| h :: t => t ++ [false]
| [] => []

def leftShift (n : Nat) (t : term) : term :=
  mkBbT (List.append (bitOfListAux n t (n-2)) [bot])

#eval leftShift 3 (mkValBV [true, true, true])
#eval leftShift 3 (const 21 (bv 3))

-- n left shifts
def leftShiftNAux : Nat → Nat → term → term
| _, 0, t => t
| n, (i + 1), t => leftShiftNAux n i (leftShift n t)

def leftShiftN (n : Nat) (t : term) (i : Nat) : term :=
  leftShiftNAux n i t

/-
bvLeftShift n a b
for b[n] → b[0],
  if b[i], then a << 2^i
n is expected to be log2(len(b))
-/
def bvLeftShift : Nat → Nat → term → term → term
| n, 0, a, b => fIte (eq (bitOf b (mkValInt 0)) top) (leftShift n a) a
| n, (i + 1), a, b =>
                  let res := (bvLeftShift n i a b)
                  (fIte (eq (bitOf b (mkValInt (Int.ofNat (n+1)))) top)
                              (leftShiftN n res (2^(i+1))) res)

#eval termEval (bvLeftShift 3 2 (mkValBV [false, false, true]) (mkValBV [false, false,
 true]))

/-
If terms are well-typed, construct their bit-blasted BV left shift
              a << b
-----------------------------------
ite(b <ᵤ l,
    (For each s in (0 to log2(l)-1)
      ite(b[s], a << 2^s, a)),
    [00..0]ₗ)
where len(a) = l and [00..0]ₗ is a BV with l 0's


def bblastBvShl (n : Nat) (t₁ t₂ : term) : term :=
  fIte (boolListUlt (bitOfList n t₂) (bitOfList n (nat2BV n n)))
    (bvLeftShift n ((log2 n) - 1) t₁ t₂)
    (mkZero n)

-- 1001 << 0001
#eval bblastBvShl 4 (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true])
#eval termEval (bblastBvShl 4 (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true]))
-- 1001 << 0100
#eval bblastBvShl 4 (mkValBV [false, true, true, false])
  (mkValBV [false, true, false, false])
#eval termEval (bblastBvShl 4 (mkValBV [false, true, true, false])
  (mkValBV [false, true, false, false]))
-- 1110 << 0000
#eval bblastBvShl 4 (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvShl 4 (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false]))
-- Using variables
#eval bblastBvShl 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvShl 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvShl rule
axiom bbBvShl : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvShl t₁ t₂) (bblastBvShl n t₁ t₂))
-/

/- ----------------------
 BV Logical Right Shift
----------------------- -/

-- If terms are well-typed, construct their BV logical right shift application
-- def mkBvLShr : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvLShr

-- Single logical right shift
def lRightShiftVal : List Bool → List Bool
| h :: t => false :: h :: (List.dropLast t)
| [] => []

-- Need a modified bitOfN for right shifts
def bitOfListRShAux : Nat → term → Nat → List term
| n, t, 0 => []
| n, t, (i + 1) => (bitOf t (mkValInt (Int.ofNat (i + 1))))
                    :: (bitOfListRShAux n t i)

#eval bitOfListRShAux 4 (const 21 (bv 4)) 3

def lRightShift (n : Nat) (t : term) : term :=
  mkBbT (bot :: (bitOfListRShAux n t (n-1)))

#eval lRightShift 3 (mkValBV [true, true, true])
#eval lRightShift 3 (const 21 (bv 3))

-- n right shifts
def lRightShiftNAux : Nat → Nat → term → term
| n, 0, t => t
| n, (i + 1), t => lRightShiftNAux n i (lRightShift n t)

def lRightShiftN (n : Nat) (t : term) (i : Nat) : term :=
  lRightShiftNAux n i t

/-
bvLRightShift n a b
for b[n] → b[0],
  if b[i], then a >> 2^i
n is expected to be log2(len(b))
-/
def bvLRightShift : Nat → Nat → term → term → term
| n, 0, a, b => fIte (eq (bitOf b (mkValInt 0)) top) (lRightShift n a) a
| n, (i + 1), a, b =>
                  let res := (bvLRightShift n i a b)
                  (fIte (eq (bitOf b (mkValInt (Int.ofNat (i+1)))) top)
                              (lRightShiftN n res (2^(i+1))) res)

/-
If terms are well-typed, construct their bit-blasted BV logical right shift
              a >> b
-----------------------------------
ite(b <ᵤ l,
    (For each s in (0 to log2(l)-1)
      ite(b[s], a >> 2^s, a)),
    [00..0]ₗ)
where len(a) = l and [00..0]ₗ is a BV with l 0's

def bblastBvLShr (n : Nat) (t₁ t₂ : term) : term :=
  fIte (boolListUlt (bitOfList n t₂) (bitOfList n (nat2BV n n)))
    (bvLRightShift n ((log2 n) - 1) t₁ t₂)
    (mkZero n)

-- 1001 >> 0001
#eval bblastBvLShr 4 (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true])
#eval termEval (bblastBvLShr 4 (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true]))
-- 1001 >> 0100
#eval bblastBvLShr 4 (mkValBV [false, true, true, false])
  (mkValBV [false, true, false, false])
#eval termEval (bblastBvLShr 4 (mkValBV [false, true, true, false])
  (mkValBV [false, true, false, false]))
-- 1110 >> 0000
#eval bblastBvLShr 4 (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvLShr 4 (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false]))
-- Using variables
#eval bblastBvLShr 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvLShr 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvLShr rule
axiom bbBvLShr : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvLShr t₁ t₂) (bblastBvLShr n t₁ t₂))
-/

/- ------------------------
 BV Arithmetic Right Shift
------------------------- -/

-- If terms are well-typed, construct their BV logical right shift application
-- def mkBvAShr : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => checkBinaryBV ot₁ ot₂ bvAShr

-- Single arithmetic right shift
def aRightShiftVal : List Bool → Bool → List Bool
| h :: t, sign => sign :: h :: (List.dropLast t)
| [], sign  => []

-- Need a bool list head function (that defaults to false)
def head : List Bool → Bool
| h :: t => h
| [] => false

def sign (n : Nat) (t : term) : term :=
  (bitOf t (mkValInt (Int.ofNat (n-1))))

def aRightShift  (n : Nat) (t : term) : term :=
  mkBbT ((sign n t) ::
         (bitOfListRShAux n t (n-1)))

#eval aRightShift 3 (mkValBV [true, false, true])
#eval aRightShift 3 (mkValBV [false, true, true])
#eval aRightShift 3 (const 21 (bv 3))

-- n right shifts
def aRightShiftNAux : Nat → Nat → term → term
| n, 0, t => t
| n, (i + 1), t => aRightShiftNAux n i (aRightShift n t)

def aRightShiftN (n : Nat) (t : term) (i : Nat) : term :=
  aRightShiftNAux n i t

/-
bvARightShift n a b
for b[n] → b[0],
  if b[i], then a >>ₐ 2^i
n is expected to be log2(len(b))
-/
def bvARightShift : Nat → Nat → term → term → term
| n, 0, a, b => fIte (eq (bitOf b (mkValInt 0)) top) (aRightShift n a) a
| n, (i + 1), a, b =>
                  let res := (bvARightShift n i a b)
                  (fIte (eq (bitOf b (mkValInt (Int.ofNat (i+1)))) top)
                              (aRightShiftN n res (2^(i+1))) res)

/-
If terms are well-typed, construct their bit-blasted BV arithmetic right shift
              a >>ₐ b
-----------------------------------
ite(b <ᵤ l,
    (For each s in (0 to log2(l)-1)
      ite(b[s], a >>ₐ 2^s, a)),
    [00..0]ₗ)
where len(a) = l and [00..0]ₗ is a BV with l 0's

def bblastBvAShr (n : Nat) (t₁ t₂ : term) : term :=
  fIte (boolListUlt (bitOfList n t₂) (bitOfList n (nat2BV n n)))
    (bvARightShift n ((log2 n) - 1) t₁ t₂)
    (fIte (sign n t₁) (mkOnes n) (mkZero n))

-- 1001 >>ₐ 0001
#eval bblastBvAShr 4 (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true])
#eval termEval (bblastBvAShr 4 (mkValBV [true, false, false, true])
  (mkValBV [false, false, false, true]))
-- 1001 >>ₐ 0100
#eval bblastBvAShr 4 (mkValBV [true, false, false, true])
  (mkValBV [false, true, false, false])
#eval termEval (bblastBvAShr 4 (mkValBV [true, false, false, true])
  (mkValBV [false, true, false, false]))
-- 1110 >>ₐ 0000
#eval bblastBvAShr 4 (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false])
#eval termEval (bblastBvAShr 4 (mkValBV [true, true, true, false])
  (mkValBV [false, false, false, false]))
-- 0101 >>ₐ 0010
#eval bblastBvAShr 4 (mkValBV [false, true, false, true])
  (mkValBV [false, false, true, false])
#eval termEval (bblastBvAShr 4 (mkValBV [false, true, false, true])
  (mkValBV [false, false, true, false]))
-- Using variables
#eval bblastBvAShr 4 (const 21 (bv 4))
  (mkValBV [false, false, false, false])
#eval bblastBvAShr 4 (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvAShr rule
axiom bbBvAShr : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvAShr t₁ t₂) (bblastBvAShr n t₁ t₂))
-/

---------------------------- BV Length Manipulating Operators ----------------------------

/- -----------
 BV Extraction
------------ -/

-- If terms are well-typed, construct their BV Extraction application
-- def mkBvExtract : OptionM term → OptionM term → OptionM term → OptionM term :=
--   λ ot oi oj =>
--     ot >>= λ t => sortOf t >>= λ s =>
--     oi >>= λ i => sortOf i >>= λ si =>
--     oj >>= λ j => sortOf i >>= λ sj =>
--   match s, si, sj with
--   | bv n, intSort, intSort =>
--     match i, j with
--     | (val (value.integer i₁) intSort), (val (value.integer j₁) intSort) =>
--       if (0 ≤ j₁ ∧ j₁ ≤ i₁ ∧ i₁ < n) then
--         (bvExtract n (Int.toNat i₁) (Int.toNat j₁) t i j)
--       else
--         none
--     | _, _ => none
--   | _, _, _ => none

def removeLastN : List α → Nat → List α
| l, 0 => l
| l, n+1 => removeLastN (List.dropLast l) n

/-
If terms are well-typed, construct their bit-blasted BV extraction
[x₀ ... xₙ]   0 ≤ j ≤ i < n
----------------------------
       [xⱼ ... xᵢ]
-/
def bblastBvExtract (n : Nat) (t i j : term) : term :=
    match i, j with
    | (val (value.integer i₁) _), (val (value.integer j₁) _) =>
         mkBbT (List.drop (Int.toNat j₁) (removeLastN (bbTtoList n t) (n - (Int.toNat i₁) - 1)))
    | _, _ => undef

#eval bblastBvExtract 4 (bblastBvVal $ mkValBV [false, false, true, false])
  (mkValInt 3) (mkValInt 2)
#eval bblastBvExtract 4 (bblastBvVal $ mkValBV [false, false, true, false])
  (mkValInt 2) (mkValInt 2)
#eval bblastBvExtract 4 (bblastBvVal $ mkValBV [false, false, true, false])
  (mkValInt 3) (mkValInt 0)
-- Bad call
#eval bblastBvExtract 4 (bblastBvVal $ mkValBV [false, false, true, false])
  (mkValInt 1) (mkValInt 2)
-- Using variables
#eval bblastBvExtract 4 (bblastBvVar 4 (const 21 (bv 4))) (mkValInt 2)
  (mkValInt 1)

-- Bit-blasting BvExtract rule
axiom bbBvExtract : ∀ {t i j : term} (n : Nat),
  thHolds (eq (bvExtract t i j) (bblastBvExtract n t i j))


/----------------
 BV Concatenation
---------------- -/

-- If terms are well-typed, construct their BV concat application
-- def mkBvConcat : OptionM term → OptionM term → OptionM term :=
--   λ ot₁ ot₂ => ot₁ >>= λ t₁ => sortOf t₁ >>= λ s₁ =>
--                ot₂ >>= λ t₂ => sortOf t₂ >>= λ s₂ =>
--   match s₁, s₂ with
--   | bv m, bv n => bvConcat m n t₁ t₂
--   | _, _ => none

/-
If terms are BVs construct their bit-blasted BV concat
[xₙ ... x₁ x₀] ++ [yₙ ... y₁ y₀]
---------------------------------
   [xₙ ... x₁ x₀ yₙ ... y₁ y₀]
-/
def bblastBvConcat (n₁ n₂ : Nat) (t₁ t₂ : term) : term :=
  mkBbT (List.append (bbTtoList n₂ t₂) (bbTtoList n₁ t₁))

-- 0000 ++ 1111
#eval bblastBvConcat 4 4 (bblastBvVal $ mkValBV [false, false, false, false])
  (bblastBvVal $ mkValBV [true, true, true, true])
-- 11 + 111
#eval bblastBvConcat 2 3 (bblastBvVal $ mkValBV [true, true])
  (bblastBvVal $ mkValBV [true, true, true])
-- 1 + 011
#eval bblastBvConcat 1 3 (bblastBvVal $ mkValBV [true])
  (bblastBvVal $ mkValBV [true, true, false])
-- Using variables
#eval bblastBvConcat 2 2 (bblastBvVar 2 (const 21 (bv 2)))
  (bblastBvVal $ mkValBV [false, false])
#eval bblastBvConcat 2 2 (bblastBvVar 2 (const 21 (bv 2))) (bblastBvVar 2 (const 22 (bv 2)))

-- Bit-blasting BvConcat rule
axiom bbBvConcat : ∀ {t₁ t₂ : term} (n₁ n₂ : Nat),
  thHolds (eq (bvConcat t₁ t₂) (bblastBvConcat n₁ n₂ t₁ t₂))

/- ---------------
 BV Zero Extend
---------------- -/

-- If terms are well-typed, construct their BV zero extend application
-- def mkBvZeroExt : OptionM term → OptionM term → OptionM term :=
--   λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
--              oi >>= λ i => sortOf i >>= λ si =>
--   match s, si with
--   | bv n, intSort =>
--     match i with
--     | val (value.integer i₁) intSort => bvZeroExt n (Int.toNat i₁) t i
--     | _ => none
--   | _, _ => none

/-
If terms are well-typed, construct their bit-blasted BV zero extend
     [xₙ ... x₁ x₀]    i
-----------------------------
  [0₁ ... 0ᵢ xₙ ... x₁ x₀]
-/
def bblastZeroExt (n : Nat) (t i : term) : term :=
    match i with
    | val (value.integer i₁) intSort =>
      mkBbT (List.append (List.replicate (Int.toNat i₁) bot) (bitOfList n t))
    | _ => undef

#eval bblastZeroExt 4 (mkValBV [true, true, true, true])
  (mkValInt 2)
#eval bblastZeroExt 2 (mkValBV [true, false])
  (mkValInt 0)

-- Using variables
#eval bblastZeroExt 4 (const 21 (bv 4)) (mkValInt 2)

-- Bit-blasting BvZeroExt rule
axiom bbBvZeroExt : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvZeroExt t₁ t₂) (bblastZeroExt n t₁ t₂))


/- ---------------
 BV Sign Extend
---------------- -/

-- If terms are well-typed, construct their BV sign extend application
-- def mkBvSignExt : OptionM term → OptionM term → OptionM term :=
--   λ ot oi => ot >>= λ t => sortOf t >>= λ s =>
--              oi >>= λ i => sortOf i >>= λ si =>
--   match s, si with
--   | bv n, intSort =>
--     match i with
--     | val (value.integer i₁) intSort => bvSignExt n (Int.toNat i₁) t i
--     | _ => none
--   | _, _ => none

def hd : List term → term
| h :: t => h
| [] => undef

/-
If terms are well-typed, construct their bit-blasted BV sign extend
     [xₙ ... x₁ x₀]   i
-----------------------------
  [xₙ ... xₙ xₙ ... x₁ x₀]
where i x₀'s are prefixed to x
-/
def bblastSignExt (n : Nat) (t i : term) : term :=
    match i with
    | val (value.integer i₁) intSort =>
      match hd (bitOfList n t) with
      | term.undef => undef
      | sign => mkBbT (List.append (List.replicate (Int.toNat i₁) sign) (bitOfList n t))
    | _ => undef

#eval bblastSignExt 4 (mkValBV [true, true, true, false])
  (mkValInt 2)
#eval bblastSignExt 4 (mkValBV [false, true, true, true])
  (mkValInt 2)
#eval bblastSignExt 2 (mkValBV [true, false])
  (mkValInt 0)
-- Using variables
#eval bblastSignExt 4 (const 21 (bv 4)) (mkValInt 2)

-- Bit-blasting BvSignExt rule
axiom bbBvSignExt : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvSignExt t₁ t₂) (bblastSignExt n t₁ t₂))


/- ----------
 BV Repeat
----------- -/

-- If terms are well-typed, construct their BV repeat application
-- def mkBvRepeat : OptionM term → OptionM term → OptionM term :=
--   λ oi ot => oi >>= λ i => sortOf i >>= λ si =>
--              ot >>= λ t => sortOf t >>= λ s =>
--   match si, s with
--   | intSort, bv n =>
--     match i with
--     | val (value.integer i₁) intSort => bvRepeat n (Int.toNat i₁) i t
--     | _ => none
--   | _, _ => none

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
def bblastRepeat (n : Nat) (i t : term) : term :=
    match i with
    | val (value.integer i₁) _ =>
        mkBbT (repeatList (Int.toNat i₁) (bitOfList n t))
    | _ => undef

#eval bblastRepeat 4 (mkValInt 2)
  (mkValBV [true, true, true, true])
#eval bblastRepeat 4 (mkValInt (-1))
  (mkValBV [true, true, true, true])
#eval bblastRepeat 2 (mkValInt 7)
  (mkValBV [true, false])
-- Using variables
#eval bblastRepeat 2 (mkValInt 2) (const 21 (bv 2))

-- Bit-blasting BvRepeat rule
axiom bbBvRepeat : ∀ {t₁ t₂ : term} (n : Nat),
  thHolds (eq (bvRepeat t₁ t₂) (bblastRepeat n t₁ t₂))

end bvRules
