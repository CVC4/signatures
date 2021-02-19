import term
import aux
import cdclt 

open proof
open proof.sort proof.term
open rules

namespace proof

section
open pos_num
@[pattern] def bvnot_num : pos_num := succ forall_num
@[pattern] def bvand_num : pos_num := succ bvnot_num
@[pattern] def bvor_num : pos_num := succ bvand_num
@[pattern] def bveq_num : pos_num := succ bvor_num
end

namespace term

-- Boolean sort definition
@[pattern] def bvsort := sort.bv

-- term definitions
--set_option trace.eqn_compiler.elim_match true
def bit_to_term : bool → option term :=
  λ b, if b then some top else some bot

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

@[pattern] def bveq : pos_num → term → term → term := λ n, toBinary $ cstr bveq_num (bv n)

-- try removing the pos_num
@[simp] def mkbvEq : pos_num → option term → option term → option term :=
  λ (n : pos_num), constructBinaryTerm eq (λ s₁ s₂, (s₁ = (bv n)) ∧ (s₂ = (bv n)))

def bblast_bvEq : option term → option term → option term :=
  λ ot₁ ot₂,
    do t₁ ← ot₁, t₂ ← ot₂, s₁ ← sortof t₁, s₂ ← sortof t₂,
    match (s₁, s₂) with
    |  (bv m, bv n) := 
      if (m = n) then (match (t₁, t₂) with 
      | (val (value.bitvec l1) _, val (value.bitvec l2) _) := 
        let l₁ := (list.map bit_to_term l1),
            l₂ := (list.map bit_to_term l2) in
            mkAndN (zip l₁ l₂ mkEq) 
      | (_, _) := none
      end) else none
    | (_, _) := none
    end

@[pattern] def bvnot : pos_num → term → term := 
  λ (n : pos_num), 
  toUnary $ cstr bvnot_num (arrow (bvsort n) (bvsort n))

def bv_not : list bool → list bool := 
  λ b, list.map bnot b

def bvand : list bool → list bool → list bool := 
  λ b1 b2, if (list.length b1 = list.length b2) then (list.map₂ band b1 b2) else []

def bvor : list bool → list bool → list bool :=
  λ b1 b2, if (list.length b1 = list.length b2) then (list.map₂ bor b1 b2) else []
  
def mkBvnot : option term → option term :=
  flip option.bind $
    λ t, do s ← sortof t, 
    match s with
    | bv n := 
      match t with
      | val (value.bitvec b) s := some (val (value.bitvec (bv_not b)) s)
      | _ := none
      end
    | _ := none
    end

/-
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

--constant bvconst {n : pos_num} {l : list term} {t : term} {b : bblast_term}
-/

end term

end proof

constant bblast_bveq {t₁ t₂ : option term} (n : pos_num): 
  holds [mkNot (proof.term.mkbvEq n t₁ t₂), (proof.term.bblast_bvEq t₁ t₂)]