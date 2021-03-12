import term
import aux
import cdclt

open proof
open proof.sort proof.term
open rules

namespace proof

namespace term

-- For equation compiler related debugging:
--set_option trace.eqn_compiler.elim_match true


-- bit-vector sort definition
@[pattern] def bvsort := sort.bv


/--------------------------------------- Bit Of ---------------------------------------/

/- mkBitOf bv n, returns the nth element
   of bv if it exists; none otherwise -/
def mkBitOf : option term → option term → option term :=
λ ot₁ ot₂, do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortOf t₁, s₂ ← sortOf t₂,
match (s₁, s₂) with
| (bv n, intsort) :=
  match t₂ with
  -- integer index has to be an in-range value
  | val (value.integer i) _ := if (i >= 0 ∧ i < n) then
    (match t₁ with
    -- BV can be a constant
    | val (value.bitvec l) _ :=
        match (list.nth l (int.to_nat i)) with
        | some b := if b then top else bot
        | none := none
        end
    -- or BV can be a var
    | _ := bitOf n t₁ t₂
    end) else none
  | _ := none
  end
| (_, _) := none
end
#eval mkBitOf (val (value.bitvec [true, false, true, false]) (bv 4)) (val (value.integer 0) intsort)
#eval mkBitOf (val (value.bitvec [true, false, true, false]) (bv 4)) (val (value.integer 1) intsort)
#eval mkBitOf (val (value.bitvec [true, false, true, false]) (bv 4)) (val (value.integer 4) intsort)
#eval mkBitOf (const 21 (bv 4)) (val (value.integer 0) intsort)
#eval mkBitOf (const 21 (bv 4)) (val (value.integer 1) intsort)
#eval mkBitOf (const 21 (bv 4)) (val (value.integer 4) intsort)

/- bitOfN t n
   bit-blasts a BV constant or variable.
   t is the BV term and n is its length.
   bitOfN t n returns a list of length n
   with option terms representing each bit.
-/
def bitOfNAux : term → ℕ → ℕ → list (option term)
| t 0 _ := []
| t (n₁+1) n₂ := (mkBitOf t (val (value.integer (n₂ - n₁ - 1)) intsort)) :: (bitOfNAux t n₁ n₂)
def bitOfN : term → ℕ → list (option term) :=
  λ t n, bitOfNAux t n n

#eval bitOfN (const 21 (bv 4)) 4
#eval bitOfN (val (value.bitvec [true, true, true, false]) (bv 4)) 4
/- The following bad calls create bad bit-blasted terms
   because the nat argument to bitOfN and the length
   of the BV term don't match.-/
#eval bitOfN (const 21 (bv 3)) 4
#eval bitOfN (val (value.bitvec [true, true, true, false]) (bv 4)) 3


/--------------------------------------- Bitwise Operators ---------------------------------------/

/-
mkBbT n l
Construct a (bv n) term that is a bbT of the bools 
in l
-/
@[pattern] def mkBbT (l : list (option term)) : option term :=
  mkAppN (bbT (list.length l)) l
#eval mkBbT ([some top, some top, some top, some top])

/-
checkBinaryBV ot₁ ot₂ constr
If ot₁ and ot₂ are BVs of the same length, then
construct a bitwise op of (constr ot₁ ot₂)
-/
def checkBinaryBV : option term → option term →
  (ℕ → term → term → term) → option term :=
  λ ot₁ ot₂ constr,
  do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortOf t₁, s₂ ← sortOf t₂,
  match (s₁, s₂) with
  | (bv m, bv n) := if (m = n) then (constr m t₁ t₂) else none
  | (_, _) := none
  end

-- For BVAnd and BVOr
/-
bblastBvBitwise ot₁ ot₂ const
checks that ot₁ and ot₂ are BVs of the same length
and returns an option list of option terms that
has the bitwise application of const to the
respective elements of ot₁ and ot₂
-/
def bblastBvBitwise (ot₁ ot₂ : option term)
 (constructor : option term → option term → option term) : option term :=
    do t₁ : term ← ot₁, t₂ : term ← ot₂, s₁ : sort ← sortOf ot₁, s₂ : sort ← sortOf ot₂,
      match (s₁, s₂) with
      |  (bv m, bv n) :=
          if (m = n) then
            let l₁ := bitOfN t₁ m,
                l₂ := bitOfN t₂ m in
                  mkBbT (zip l₁ l₂ constructor)
          else none
      | (_, _) := none
      end


/------------
 BV equality
------------/

-- If terms are well-typed, construct a BV Eq application
-- of them
def mkBvEq : option term → option term → option term :=
  λ ot₁ ot₂, checkBinaryBV ot₁ ot₂ bvEq

/-
bblastBvEq ot₁ ot₂
If ot₁ and ot₂ are BVs of the same length,
then return a boolean term that represents
the bit-blasted equality of ot₁ and ot₂

[x₀, x₁, ... , xₙ] = [y₀, y₁, ... , yₙ]
---------------------------------------
       x₀ = y₀ ∧ ... ∧ xₙ = yₙ
-/
def bblastBvEq : option term → option term → option term :=
  λ ot₁ ot₂,
    do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortOf t₁, s₂ ← sortOf t₂,
    match (s₁, s₂) with
    |  (bv m, bv n) :=
      if (m = n) then (
        let l₁ := bitOfN t₁ m,
            l₂ := bitOfN t₂ m in
            mkAndN (zip l₁ l₂ mkEq)
      ) else some top
    | (_, _) := some bot
    end

#eval bblastBvEq (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvEq (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvEq (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvEq rule
constant bbBvEq {t₁ t₂ : option term} :
  thHolds (mkEq (mkBvEq t₁ t₂) (bblastBvEq t₁ t₂))


/------------
 BV not
------------/

-- If term is a BV, construct a BV Not application
def mkBvNot : option term → option term :=
  λ ot, do t ← ot, s ← sortOf t,
  match s with
  | bv n := bvNot n t
  | _ := none
  end

/-
If term is a BV, construct a bit-blasted BV Not
¬bv [x₀, x₁, ... , xₙ]
----------------------
 [¬x₀, ¬x₁, ... , ¬x]
-/
def bblastBvNot (ot : option term) : option term :=
  do t ← ot, s ← sortOf t,
    match s with
    | bv n := let l := bitOfN t n in mkBbT (list.map mkNot l)
    | _ := none
    end

#eval bblastBvNot (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvNot (const 21 (bv 4))

-- Bit-blasting BvNot rule
constant bbBvNot {t : option term} :
  thHolds (mkEq (mkBvNot t) (bblastBvNot t))


/------------
 BV and
------------/

-- If terms are well-typed, construct a BV And application
-- of them
def mkBvAnd : option term → option term → option term :=
  λ ot₁ ot₂, checkBinaryBV ot₁ ot₂ bvAnd

/-
If terms are well-typed, construct a bit-blasted BV and
of them
[x₀ x₁ ... xₙ] ∧bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ∧ y₀, x₁ ∧ x₂, ... xₙ ∧ yₙ]
-/
def bblastBvAnd : option term → option term → option term :=
  λ ot₁ ot₂, bblastBvBitwise ot₁ ot₂ mkAnd

#eval bblastBvAnd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvAnd rule
constant bbBvAnd {t₁ t₂ : option term}:
  thHolds (mkEq (mkBvAnd t₁ t₂) (bblastBvAnd t₁ t₂))


/------------
 BV or
------------/

-- If terms are well-typed, construct a BV Or application
-- of them
def mkBvOr : option term → option term → option term :=
  λ ot₁ ot₂, checkBinaryBV ot₁ ot₂ bvOr

/-
If terms are well-typed, construct a bit-blasted BV and
of them
[x₀ x₁ ... xₙ] ∨bv [y₀ y₁ ... yₙ]
---------------------------------
 [x₀ ∨ y₀, x₁ ∨ x₂, ... xₙ ∨ yₙ]
-/
def bblastBvOr : option term → option term → option term :=
  λ ot₁ ot₂, bblastBvBitwise ot₁ ot₂ mkOr

#eval bblastBvOr (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvOr (const 21 (bv 4))
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvOr (const 21 (bv 4)) (const 22 (bv 4))
#eval mkBbT (bitOfN (val (value.bitvec [true, true, true, true]) (bv 4)) 4)

-- Bit-blasting BvOr rule
constant bbBvOr {t₁ t₂ : option term} :
  thHolds (mkEq (mkBvOr t₁ t₂) (bblastBvOr t₁ t₂))

/--------------------------------------- Comparison Operators ---------------------------------------/

/- -------------------
 BV unsigned less than
----------------------/

-- If terms are well-typed, construct a BV Ult application
-- of them
def mkBvUlt : option term → option term → option term :=
  λ ot₁ ot₂, checkBinaryBV ot₁ ot₂ bvUlt

/-
If we reverse l₁ and l₂ in bblastBvUlt
[x₀, x₁, ... , xₙ] <ᵤ [y₀, y₁, ... , yₙ] iff resₙ
where res₀ = ¬x₀ ∧ y₀
      resᵢ = ((xᵢ ↔ yᵢ) ∧ res_{i-1}) ∨ (¬xᵢ ∧ yᵢ)
def boolListUlt : list (option term) → list (option term) → option term
| [h₁] [h₂] := mkAnd (mkNot h₁) h₂
| (h₁ :: t₁) (h₂ :: t₂) := (mkOr (mkAnd (mkEq h₁ h₂) (boolListUlt t₁ t₂)) (mkAnd (mkNot h₁) h₂))
| _ _ := none
-/

/-
[x₀, x₁, ... , xₙ] <ᵤ [y₀, y₁, ... , yₙ] = 
  (¬x₀ ∧ y₀) ∨ ((x₀ ↔ y₀) ∧ ([x₁, ... , xₙ] <ᵤ [y₁, ... , yₙ]))
-/
def boolListUlt : list (option term) → list (option term) → option term
| [h₁] [h₂] := mkAnd (mkNot h₁) h₂
| (h₁ :: t₁) (h₂ :: t₂) := (mkOr (mkAnd (mkNot h₁) h₂) (mkAnd (mkEq h₁ h₂) (boolListUlt t₁ t₂)) )
| _ _ := none

/-
bblastBvUlt ot₁ ot₂
If ot₁ and ot₂ are BVs of the same length, 
then return a boolean term that represents 
ot₁ <ᵤ ot₂
-/
def bblastBvUlt : option term → option term → option term :=
  λ ot₁ ot₂,
    do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortOf t₁, s₂ ← sortOf t₂,
    match (s₁, s₂) with
    |  (bv m, bv n) := 
      if (m = n) then (
        let l₁ := bitOfN t₁ m,
            l₂ := bitOfN t₂ m in
            boolListUlt l₁ l₂
      ) else some top
    | (_, _) := some bot
    end

#eval bblastBvUlt (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvUlt (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvUlt (const 21 (bv 4)) (const 22 (bv 4))

-- Bit-blasting BvUlt rule
constant bbBvUlt {t₁ t₂ : option term} : 
  thHolds (mkEq (mkBvUlt t₁ t₂) (bblastBvUlt t₁ t₂))


end term

end proof
