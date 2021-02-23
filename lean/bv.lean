import term
import aux
import cdclt 

open proof
open proof.sort proof.term
open rules

namespace proof

section
@[pattern] def bvBitOfNum : ℕ := forall_num + 1
@[pattern] def bvEqNum : ℕ := bvBitOfNum + 1
@[pattern] def bvNotNum : ℕ := bvEqNum + 1
@[pattern] def bvAndNum : ℕ := bvNotNum + 1
@[pattern] def bvOrNum : ℕ := bvAndNum + 1
end

namespace term

-- For equation compiler related debugging:
--set_option trace.eqn_compiler.elim_match true

-- sort definition
@[pattern] def bvsort := sort.bv

-- term definitions
@[pattern] def bitOf : ℕ → term → term → term := λ n, toBinary $ cstr bvBitOfNum (bv n)
@[pattern] def bvEq : ℕ → term → term → term := λ n, toBinary $ cstr bvEqNum (bv n)

-- Check that both terms have the same BV type
@[simp] def mkBvEq : option term → option term → option term :=
  λ ot₁ ot₂, 
  do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortof t₁, s₂ ← sortof t₂,
  match (s₁, s₂) with
  | (bv m, bv n) := if (m = n) then (bvEq m t₁ t₂) else none
  | (_, _) := none
  end

/- mkBitOf bv n, returns the nth element
   of bv if it exists; none otherwise -/
-- We don't use this yet, but it should 
-- prove useful
def mkBitOf : term → ℕ → option term :=
λ t m, do s ← sortof t, 
match s with
| bv n := if (m < n) then
  (match t with
  | val (value.bitvec l) s := 
    (match (list.nth l m) with
    | some b := if b then some top else some bot
    | none := none
    end)
  | const p s := bitOf n t (val (value.integer m) (bv n))
  | _ := none
  end) else none
| _ := none
end

/-
-- This would've been the way to go to built 
-- BV term equalities but the equation compiler
-- can't see that recursion will terminate
def bitOfN : term → ℕ → ℕ → list (option term)
| t n₁ n₂ := if n₁ < n₂ then 
              (mkBitOf t n₁) :: (bitOfN  t (n₁ + 1) n₂)
             else
              []
-/

/-
mkRevBitsConst n t m

Precondition: t is a BV variable (const p (bv n), for some p).

n is the length of the BV variable, t the BV variable, m is 
the successor of the index of t we want to represent. 
Function outputs (in reverse) a list of option terms that represent 
each bit of t (bit-blasting). 

So, for term x of type bv 4, (mkRevBitsConst 4 x 4) returns
[(some x₃) (some x₂) (some x₁) (some x₀)] where 
xᵢ is a fresh variable representing x[i].
-/
def mkRevBitsConst : ℕ → term → ℕ → list (option term)
| n t 0 := []
| n t (m + 1) := (bitOf n t (val (value.integer m) (bv n))) :: mkRevBitsConst n t m

/-
mkBitsVal t

Precondition: t is a BV constant (val (value.bitvector l) (bv n), for some n).

Function outputs a list of Boolean terms representing the bits of t.

So for x = [true true false false], (mkBitsVal x) returns
[(some top) (some top) (some bot) (some bot)].
-/
def mkBitsVal : term → list (option term)
| (val (value.bitvec (h :: t)) s) := 
  if h then 
    (some top) :: mkBitsVal (val (value.bitvec t) s)
  else
    (some bot) :: mkBitsVal (val (value.bitvec t) s)
| (val (value.bitvec []) s) := []
| _ := []

/-
def bitOfN : term → list (option term) :=
λ t, do s ← sortof t,
match s with
| bv n := (match t with 
          | (val (value.bitvec l) s₁) := mkBitsVal (val (value.bitvec l) s₁)
          | const p s₁ := let l := (mkRevBitsConst n t (n-1)) in list.reverse l
          | _ := []
          end)
| _ := []
end
-/

/-
bitOfN n t
t is a BV term of type (bv n). We have to explicitly 
provide n to bitOfN because its not able to infer it from t, 
using sortof. See the commented version above for the issue.

If t is a BV const, bitOfN returns a list of Boolean option 
terms representing its bits.
If t is a BV var, bitOfN returns a list of variables 
representing each bit of t.
Otherwise, it retursn an empty list.
-/
def bitOfN : ℕ → term → list (option term) :=
λ n t, 
match t with 
| (val (value.bitvec l) s₁) := mkBitsVal (val (value.bitvec l) s₁)
| const p s₁ := let l := (mkRevBitsConst n t n) in list.reverse l
| _ := []
end

/-
Given option terms t₁ and t₂ of type (bv n), 
bblastBvEq t₁ t₂ returns an option term representing 
the bit-blasted version of their equality, which is a 
conjunction of the equality of their corresponding bits.
-/
def bblastBvEq : option term → option term → option term :=
  λ ot₁ ot₂,
    do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortof t₁, s₂ ← sortof t₂,
    match (s₁, s₂) with
    |  (bv m, bv n) := 
      if (m = n) then (
        let l₁ := bitOfN m t₁,
            l₂ := bitOfN m t₂ in
            mkAndN (zip l₁ l₂ mkEq)
      ) else none
    | (_, _) := none
    end
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
    λ t, do s ← sortof t, 
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

end term

end proof

constant bblastBvEq {t₁ t₂ : option term} : 
  holds [mkNot (proof.term.mkBvEq t₁ t₂), (proof.term.bblastBvEq t₁ t₂)]