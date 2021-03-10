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
checkBinaryBV ot₁ ot₂ const
If ot₁ and ot₂ are BVs of the same length, then 
construct a bitwise op of (const ot₁ ot₂)
-/
def checkBinaryBV : option term → option term → 
  (ℕ → term → term → term) → option term :=
  λ ot₁ ot₂ const, 
  do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortOf t₁, s₂ ← sortOf t₂,
  match (s₁, s₂) with
  | (bv m, bv n) := if (m = n) then (const m t₁ t₂) else none
  | (_, _) := none
  end

--For bv and and bv or
/-
def bblastBVBitwise : option term → option term → 
  (option term → option term → option term ) → option term :=
  λ ot₁ ot₂ const,
    do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortOf t₁, s₂ ← sortOf t₂,
    match (s₁, s₂) with
    |  (bv m, bv n) := 
      if (m = n) then (
        let l₁ := bitOfN t₁ m,
            l₂ := bitOfN t₂ m in
             val (value.bitvec (zip l₁ l₂ const)) (bv m)
      ) else some top
    | (_, _) := some bot
    end
-/
-- BV equality

-- If terms are well-typed, construct a BV Eq application
-- of them
def mkBvEq : option term → option term → option term :=
  λ ot₁ ot₂, checkBinaryBV ot₁ ot₂ bvEq

/-
bblastBvEq ot₁ ot₂
If ot₁ and ot₂ are BVs of the same length, 
then return a boolean term that represents 
the bit-blasted equality of ot₁ and ot₂

[x₀ x₁ ... xₙ] = [y₀ y₁ ... yₙ]
-------------------------------
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


-- BV And

-- If terms are well-typed, construct a BV And application
-- of them
def mkBvAnd : option term → option term → option term :=
  λ ot₁ ot₂, checkBinaryBV ot₁ ot₂ bvAnd

-- If terms are well-typed, construct a bit-blasted BV and
-- of them
/-
def bblastBvAnd : option term → option term → option term :=
  λ ot₁ ot₂, bblastBVBitwise ot₁ ot₂ mkAnd

#eval bblastBvAnd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4)) (const 22 (bv 4))
-/

-- BV Or

-- If terms are well-typed, construct a BV Or application
-- of them
def mkBvOr : option term → option term → option term :=
  λ ot₁ ot₂, checkBinaryBV ot₁ ot₂ bvOr
/-
-- If terms are well-typed, construct a bit-blasted BV and
-- of them
def bblastBvOr : option term → option term → option term :=
  λ ot₁ ot₂, bblastBVBitwise ot₁ ot₂ mkOr

#eval bblastBvOr (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvOr (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvOr (const 21 (bv 4)) (const 22 (bv 4))
-/
end term

end proof

constant cnfBvEq {t₁ t₂ : option term} : 
  holds [mkNot (proof.term.mkBvEq t₁ t₂), (proof.term.bblastBvEq t₁ t₂)]
/-
constant cnfBvAnd {t₁ t₂ : option term} : 
  holds [mkNot (proof.term.mkBvAnd t₁ t₂), (proof.term.bblastBvAnd t₁ t₂)]

constant cnfBvOr {t₁ t₂ : option term} : 
  holds [mkNot (proof.term.mkBvOr t₁ t₂), (proof.term.bblastBvOr t₁ t₂)]
-/