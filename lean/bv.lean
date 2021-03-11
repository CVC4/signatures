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

@[pattern] def mkBbT (n : ℕ) (l : option (list (option term))) : option term := 
  match l with
  | some l :=  mkAppN (bbT n) l
  | none := none
  end
#eval mkBbT 4 (some [some top, some top, some top, some top])

def checkBinaryBV : option term → option term → 
  (ℕ → term → term → term) → option term :=
  λ ot₁ ot₂ const, 
  do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortOf t₁, s₂ ← sortOf t₂,
  match (s₁, s₂) with
  | (bv m, bv n) := if (m = n) then (const m t₁ t₂) else none
  | (_, _) := none
  end

-- For BVAnd and BVOR
/- 
bblastBvBitwise ot₁ ot₂ const
checks that ot₁ and ot₂ are BVs of the same length
and returns an option list of option terms that 
has the bitwise application of const to the 
respective elements of ot₁ and ot₂
-/
def bblastBvBitwise : option term → option term → 
  (option term → option term → option term ) → option (list (option term)) :=
  λ ot₁ ot₂ const,
    do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortOf t₁, s₂ ← sortOf t₂,
    match (s₁, s₂) with
    |  (bv m, bv n) := 
      if (m = n) then (
        let l₁ := bitOfN t₁ m,
            l₂ := bitOfN t₂ m in
             some (zip l₁ l₂ const)
      ) else none
    | (_, _) := none
    end


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


-- BV Not

-- If term is a BV, construct a BV Not application
def mkBvNot : option term → option term :=
  λ ot, do t ← ot, s ← sortOf t,
  match s with
  | bv n := bvNot n t
  | _ := none
  end

-- If term is a BV, construct a bit-blasted BV Not
def bblastBvNot : option term → option (list (option term)) :=
  λ ot, do t ← ot, s ← sortOf t,
    match s with
    |  bv n := let l := bitOfN t n in
             some (list.map mkNot l)
    | _ := none
    end

#eval bblastBvNot (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvNot (const 21 (bv 4)) 


-- BV And

-- If terms are well-typed, construct a BV And application
-- of them
def mkBvAnd : option term → option term → option term :=
  λ ot₁ ot₂, checkBinaryBV ot₁ ot₂ bvAnd

-- If terms are well-typed, construct a bit-blasted BV and
-- of them
def bblastBvAnd : option term → option term → option (list (option term)) :=
  λ ot₁ ot₂, bblastBvBitwise ot₁ ot₂ mkAnd

#eval bblastBvAnd (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvAnd (const 21 (bv 4)) (const 22 (bv 4))


-- BV Or

-- If terms are well-typed, construct a BV Or application
-- of them
def mkBvOr : option term → option term → option term :=
  λ ot₁ ot₂, checkBinaryBV ot₁ ot₂ bvOr

-- If terms are well-typed, construct a bit-blasted BV and
-- of them
def bblastBvOr : option term → option term → option (list (option term)) :=
  λ ot₁ ot₂, bblastBvBitwise ot₁ ot₂ mkOr

#eval bblastBvOr (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvOr (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvOr (const 21 (bv 4)) (const 22 (bv 4))
#eval mkBbT 4 (bblastBvOr (const 21 (bv 4)) (const 22 (bv 4)))


-- BV unsigned less than

-- If terms are well-typed, construct a BV Eq application
-- of them
def mkBvUlt : option term → option term → option term :=
  λ ot₁ ot₂, checkBinaryBV ot₁ ot₂ bvUlt

/-
bblastBvEq ot₁ ot₂
If ot₁ and ot₂ are BVs of the same length, 
then return a boolean term that represents 
the bit-blasted equality of ot₁ and ot₂

[x₀ x₁ ... xₙ] = [y₀ y₁ ... yₙ]
-------------------------------
    x₀ = y₀ ∧ ... ∧ xₙ = yₙ
-/
def boolListUlt : list (option term) → list (option term) → option term
| [h₁] [h₂] := mkAnd (mkNot h₁) h₂
| (h₁ :: t₁) (h₂ :: t₂) := (mkOr (mkAnd (mkEq h₁ h₂) (boolListUlt t₁ t₂)) (mkAnd (mkNot h₁) h₂))
| _ _ := none

def bblastBvUlt : option term → option term → option term :=
  λ ot₁ ot₂,
    do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortOf t₁, s₂ ← sortOf t₂,
    match (s₁, s₂) with
    |  (bv m, bv n) := 
      if (m = n) then (
        let l₁ := list.reverse (bitOfN t₁ m),
            l₂ := list.reverse (bitOfN t₂ m) in
            boolListUlt l₁ l₂
      ) else some top
    | (_, _) := some bot
    end

#eval bblastBvUlt (val (value.bitvec [false, false, false, false]) (bv 4))
  (val (value.bitvec [true, true, true, true]) (bv 4))
#eval bblastBvUlt (const 21 (bv 4)) 
  (val (value.bitvec [false, false, false, false]) (bv 4))
#eval bblastBvUlt (const 21 (bv 4)) (const 22 (bv 4))

end term

end proof

constant cnfBvEq {t₁ t₂ : option term} : 
  holds [mkNot (proof.term.mkBvEq t₁ t₂), (proof.term.bblastBvEq t₁ t₂)]

constant cnfBvUlt {t₁ t₂ : option term} : 
  holds [mkNot (proof.term.mkBvEq t₁ t₂), (proof.term.bblastBvUlt t₁ t₂)]

constant cnfBvNot {t : option term} (n : ℕ) :
  holds [mkNot (proof.term.mkBvNot t), (proof.term.mkBbT n (proof.term.bblastBvNot t))]

constant cnfBvOr {t₁ t₂ : option term} (n : ℕ): 
  holds [mkNot (proof.term.mkBvOr t₁ t₂), (proof.term.mkBbT n (proof.term.bblastBvOr t₁ t₂))]

constant cnfBvAnd {t₁ t₂ : option term} (n : ℕ): 
  holds [mkNot (proof.term.mkBvOr t₁ t₂), (proof.term.mkBbT n (proof.term.bblastBvAnd t₁ t₂))]