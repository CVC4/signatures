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

-- sort definition
@[pattern] def bvsort := sort.bv

-- Check that both terms have the same BV type
@[simp] def mkBvEq : option term → option term → option term :=
  λ ot₁ ot₂, 
  do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortOf t₁, s₂ ← sortOf t₂,
  match (s₁, s₂) with
  | (bv m, bv n) := if (m = n) then (bvEq m t₁ t₂) else none
  | (_, _) := none
  end

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

/-
def mkBitOf : term → ℕ → option term :=
λ t m, do s ← sortOf t, 
match s with
| bv n := if (m < n) then
  (match t with
  | val (value.bitvec l) s := 
    (match (list.nth l m) with
    | some b := if b then top else bot
    | none := none
    end)
  | _ := bitOf n t (val (value.integer m) (bv n))
  end) else none
| _ := none
end-/
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

/-
Given option terms t₁ and t₂ of type (bv n), 
bblastBvEq t₁ t₂ returns an option term representing 
the bit-blasted version of their equality, which is a 
conjunction of the equality of their corresponding bits.
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

#eval (bitOfN (val (value.bitvec [false, false, false, false]) (bv 4)) 4)
#eval (bitOfN (const 21 (bv 4)) 4)
#eval sortOf (bitOf 4 (const 21 (bv 4)) (val (value.integer 0) intsort))
#eval sortOf (bitOf 4 (val (value.bitvec [false, false, false, false]) (bv 4))
             (val (value.integer 0) intsort))
#eval zip (bitOfN (const 21 (bv 4)) 4)
          (bitOfN (val (value.bitvec [false, false, false, false]) (bv 4)) 4)
          mkEq
#eval bblastBvEq (const 21 (bv 4)) (const 22 (bv 4))

/-
@[pattern] def mkBvNot : ℕ → term → term := 
  λ (n : ℕ), 
  toUnary $ cstr bvNotNum (arrow (bvsort n) (bvsort n))

def bvNot : list bool → list bool := 
  λ b, list.map bnot b

def bvAnd : list bool → list bool → list bool := 
  λ b1 b2, if (list.length b1 = list.length b2) then (list.map₂ band b1 b2) else []

def bvOr : list bool → list bool → list bool :=
  λ b1 b2, if (list.length b1 = list.length b2) then (list.map₂ bor b1 b2) else []
  
def mkBvNot2 : option term → option term :=
  flip option.bind $
    λ t, do s ← sortOf t, 
    match s with
    | bv n := 
      match t with
      | val (value.bitvec b) s := some (val (value.bitvec (bvNot b)) s)
      | _ := none
      end
    | _ := none
    end

inductive bblast_term : Type
| bvconst : ℕ → list term → term → bblast_term 
| ill_formed : bblast_term

def check_bv_const : list term → list bool → bool
  | (bot :: t1) (false :: t2) := check_bv_const t1 t2
  | (top :: t1) (true :: t2) := check_bv_const t1 t2
  | _ _ := false

@[pattern] def mk_bvconst : ℕ → list term → term → bblast_term :=
  λ (n : ℕ) (f : list term) (b : term), 
  match (f,b) with 
    | (fl,  val (value.bitvec bl) s) := 
      if check_bv_const fl bl then 
        bblast_term.bvconst n f b
      else 
        bblast_term.ill_formed
  | _ := bblast_term.ill_formed
  end

constant bvconst {n : ℕ} {l : list term} {t : term} {b : bblast_term}
-/

/-
/-
mkRevBitsConst n t m

Precondition: t is a BV variable (const p (bv n), for some p).

t is a BV variable of length n, m is the number of bits we want to 
represent - this is usually the length of the BV. 
Function outputs (in reverse) a list of option terms that represent 
each bit of t (bit-blasting). 
We need n because bitOf requires the length of the BV as input.
A call to mkRevBitsConst has n = m = length of BV. This isn't 
redundant, because recursive calls reduce m.
-/
def mkRevBitsConst : ℕ → term → ℕ → list (option term)
| n t 0 := []
| n t (m + 1) := (bitOf n t (val (value.integer m) intsort)) :: mkRevBitsConst n t m
-- by default, the order is reversed
#eval (mkRevBitsConst 4 (const 21 (bv 4)) 4)
-- this is the right order of bits
#eval list.reverse (mkRevBitsConst 4 (const 21 (bv 4)) 4)
-- This isn't intended to be used with constants. mkBitsVal is more appropriate for those
#eval (mkRevBitsConst 4 (val (value.bitvec [true, true, true, true]) (bv 4)) 4)
-- Since the last argument is 3, we only get 3 bits from the BV. This 
-- function isn't intended to be used like this
#eval (mkRevBitsConst 4 (const 21 (bv 4)) 3)
-- This will type bitOf as (bv 3 → intsort → boolsort), an ill-typed term
#eval (mkRevBitsConst 3 (const 21 (bv 4)) 4)

/-
mkBitsVal t

Precondition: t is a BV constant (val (value.bitvector l) (bv n), for some n).

Function outputs a list of Boolean terms representing the bits of t if 
t is a BV constant, and an empty list otherwise.
-/
def mkBitsVal : term → list (option term)
| (val (value.bitvec (h :: t)) s) := 
  if h then 
    (some top) :: mkBitsVal (val (value.bitvec t) s)
  else
    (some bot) :: mkBitsVal (val (value.bitvec t) s)
| (val (value.bitvec []) s) := []
| _ := []
#eval mkBitsVal (val (value.bitvec [true, true, false, false]) (bv 4))
-- Precondition isn't met, so it returns an empty list
#eval mkBitsVal (const 21 (bv 4))

/-
bitOfN n t
t is a BV term of type (bv n). We have to explicitly 
provide n to bitOfN because its not able to infer it from t, 
using sortOf. See the commented version above for the issue.

If t is a BV const, bitOfN returns a list of Boolean option 
terms representing its bits.
If t is a BV var, bitOfN returns a list of variables 
representing each bit of t.
Otherwise, it retursn an empty list.
-/
def bitOfN : ℕ → term → list (option term) :=
λ n t, 
match t with 
| (val (value.bitvec l) s) := 
  if (s = bv n) then 
    mkBitsVal (val (value.bitvec l) s)
  else
    []
| const p s := 
  if (s = bv n) then 
    let l := (mkRevBitsConst n t n) in list.reverse l
  else
    []
| _ := []
end
#eval bitOfN 4 (const 21 (bv 4))
#eval bitOfN 4 (val (value.bitvec [true, true, true, false]) (bv 4))
-- The following bad calls create empty lists
#eval bitOfN 4 (const 21 (bv 3))
#eval bitOfN 3 (val (value.bitvec [true, true, true, false]) (bv 4))
-/
end term

end proof

constant bblastBvEq {t₁ t₂ : option term} : 
  holds [mkNot (proof.term.mkBvEq t₁ t₂), (proof.term.bblastBvEq t₁ t₂)]