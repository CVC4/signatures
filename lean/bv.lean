import term
import aux
import cdclt 

open proof
open proof.sort proof.term
open rules

namespace proof

section
open pos_num
@[pattern] def bvBitOfNum : pos_num := succ forall_num
@[pattern] def bvEqNum : pos_num := succ bvBitOfNum
@[pattern] def bvNotNum : pos_num := succ bvEqNum
@[pattern] def bvAndNum : pos_num := succ bvNotNum
@[pattern] def bvOrNum : pos_num := succ bvAndNum
end

namespace term

-- Sort definition
@[pattern] def bvsort := sort.bv

-- term definitions
--set_option trace.eqn_compiler.elim_match true
def bit_to_term : bool → option term :=
  λ b, if b then some top else some bot

/-
def bitOf : option term → ℕ → option term := 
  λ ot n, 
    do t ← ot, 
    match t with
    | val (value.bitvec l) s := 
      (match (list.nth l n) with
      | some b := bit_to_term b
      | none := none
      end)
    | const p _ := 
      do s ← sortof t,
      (match s with
      | bv m := 
        if (n < (cast_pos_num m)) then none/- This is incorrect -/else none
      | _ := none
      end)
    | _ := none
    end
-/

@[pattern] def bitOf : pos_num → term → term → term := λ n, toBinary $ cstr bvBitOfNum (bv n)
@[pattern] def bvEq : pos_num → term → term → term := λ n, toBinary $ cstr bvEqNum (bv n)

@[simp] def mkBvEq : option term → option term → option term :=
  λ ot₁ ot₂, 
  do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortof t₁, s₂ ← sortof t₂,
  match (s₁, s₂) with
  | (bv m, bv n) := if (m = n) then (bvEq m t₁ t₂) else none
  | (_, _) := none
  end

/- mkBitOf bv n, returns the nth element
   of bv if it exists; none otherwise -/
def mkBitOf : term → ℕ → option term :=
λ t m, do s ← sortof t, 
match s with
| bv n := if (m < (cast_pos_num n)) then
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
def bitOfN : term → ℕ → ℕ → list (option term)
| t n₁ n₂ := if n₁ < n₂ then 
              (mkBitOf t n₁) :: (bitOfN  t (n₁ + 1) n₂)
             else
              []
-/

def mkRevBitsConst : pos_num → term → ℕ → list (option term)
| p t 0 := []
| p t (n + 1) := (bitOf p t (val (value.integer n) (bv p))) :: mkRevBitsConst p t n

def mkBitsVal : term → list (option term)
| (val (value.bitvec (h :: t)) s) := 
  if h then 
    (some top) :: mkBitsVal (val (value.bitvec t) s)
  else
    (some bot) :: mkBitsVal (val (value.bitvec t) s)
| (val (value.bitvec []) s) := []
| _ := []

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

def bblastBvEq : option term → option term → option term :=
  λ ot₁ ot₂,
    do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortof t₁, s₂ ← sortof t₂,
    match (s₁, s₂) with
    |  (bv m, bv n) := 
      if (m = n) then (
        let l₁ := bitOfN t₁,
            l₂ := bitOfN t₂ in
            mkAndN (zip l₁ l₂ mkEq)
      ) else none
    | (_, _) := none
    end
/-
@[pattern] def mkBvNot : pos_num → term → term := 
  λ (n : pos_num), 
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
| bvconst : pos_num → list term → term → bblast_term 
| ill_formed : bblast_term

def check_bv_const : list term → list bool → bool
  | (bot :: t1) (false :: t2) := check_bv_const t1 t2
  | (top :: t1) (true :: t2) := check_bv_const t1 t2
  | _ _ := false

@[pattern] def mk_bvconst : pos_num → list term → term → bblast_term :=
  λ (n : pos_num) (f : list term) (b : term), 
  match (f,b) with 
    | (fl,  val (value.bitvec bl) s) := 
      if check_bv_const fl bl then 
        bblast_term.bvconst n f b
      else 
        bblast_term.ill_formed
  | _ := bblast_term.ill_formed
  end

constant bvconst {n : pos_num} {l : list term} {t : term} {b : bblast_term}
-/

end term

end proof

constant bblastBvEq {t₁ t₂ : option term} : 
  holds [mkNot (proof.term.mkBvEq t₁ t₂), (proof.term.bblastBvEq t₁ t₂)]