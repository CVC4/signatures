import term

open smt
open smt.sort smt.term

-- define calculus
notation `clause` := list (option term)

def mynth : clause → ℕ → option term := comp2 monad.join (@list.nth (option term))
def get_last : clause → option term := λ c, mynth c (c.length - 1)

#eval monad.join (some (some 1))
#eval mynth [top, bot, const 20 boolsort, const 21 boolsort] 0
#eval list.nth [top, bot, const 20 boolsort, const 21 boolsort] 0
#eval get_last [top, bot, const 20 boolsort, const 21 boolsort]

-- eventually should give Prop
constant holds : clause → Type
def concat_cl : clause → clause → clause := @list.append (option term)
def remove_duplicates : clause → clause
| [] := []
| (h::t) := if h ∈ t then remove_duplicates t else h::(remove_duplicates t)
#check holds [const 20 boolsort, const 21 boolsort]

-- ground resolution rules
def resolveR₀ (n : option term) (c₁ c₂: clause) : clause :=
  concat_cl (remove n c₁) (remove (mkNot n) c₂)

def resolveR₁ (n : option term) (c₁ c₂: clause) : clause :=
  concat_cl (remove (mkNot n) c₁) (remove n c₂)

constant R0 : Π {c₁ c₂ : clause}
  (p₁ : holds c₁) (p₂ : holds c₂) (n : option term),
  holds (resolveR₀ n c₁ c₂)

constant R1 : Π {c₁ c₂ : clause}
  (p₁ : holds c₁) (p₂ : holds c₂) (n : term),
  holds (resolveR₁ n c₁ c₂)

constant factoring : Π {c : clause} (p : holds c),
  holds (remove_duplicates c)

#check (λ (p₀ : holds [const 20 boolsort]) 
          (p₁ : holds [mkNot (const 20 boolsort)]), 
         (R0 p₀ p₁ (const 20 boolsort) : holds []))
#check (λ (p₀ : holds [const 20 boolsort]) 
          (p₁ : holds [mkNot (const 20 boolsort)]), 
         (R0 p₀ p₁ (const 20 boolsort)) 
  : holds [const 20 boolsort] → holds [mkNot (const 20 boolsort)] → holds [])
def l1 := const 20 boolsort
def l2 := const 21 boolsort
constant c1 : holds [l1, l2]
constant c2 : holds [mkNot l1, l2]
#check R0 c1 c2 l1

/-*************** Simplifications ***************-/

-- holes
constant trust : Π {c₁ : clause} (p : holds c₁) {c₂ : clause},
  holds c₂

def reduce_not_not : clause → clause :=
  list.map $ λ c : option term, do t ← c,
    match t with
    | not $ not t' := t'
    | _ := t
    end

constant not_not : Π {c : clause} (p : holds c),
  holds (reduce_not_not c)

def simp_iff_clause : clause → clause :=
  list.map $ (flip bind) $ λ t : term,
    match t with
    | (iff t₀ t₁) := mkIffSimp t₀ t₁
    | (not (iff t₀ t₁)) := mkNot (mkIffSimp t₀ t₁)
    | _ := t
    end

constant simp_iff : Π {c : clause} (p : holds c),
  holds (simp_iff_clause c)

/-*************** ITE ***************-/

def mkIteDef : option term → option term
| (option.some $ f_ite c t₀ t₁) :=
  let ite_term := (f_ite c t₀ t₁) in
    option.some $ b_ite c (eq ite_term t₀) (eq ite_term t₁)
| _ := option.some top

constant ite_intro : Π {t : term}, holds [mkIteDef t]

/-------------------- with premises ---------------/


-- get n-th element in AND chain (right-associative)
def reduce_and_nth : ℕ → term → option term
| 0            (and t _)           := t
| 1            (and _ t)           := t
| (nat.succ n) (and  _ (and t₀ t₁)) :=
    reduce_and_nth n (and t₀ t₁)
| _            _                   := option.none
def reduce_and (n : ℕ) : option term → option term :=
  flip bind (reduce_and_nth n)
constant cnf_and : Π {t : option term} (p : holds [t]) (n : nat),
  holds [reduce_and n t]

-- get n-th in NOT-OR chain (right-associative)
def reduce_or_nth : ℕ → term → option term
| 0            (or t _)          := t
| 1            (or _ t)          := t
| (nat.succ n) (or _ (or t₀ t₁)) := reduce_or_nth n (or t₀ t₁)
| _            _                 := option.none
def reduce_not_or (n : ℕ) : option term → option term :=
  (flip bind) $ λ t,
    match t with
    | not t' := mkNot $ reduce_or_nth n t'
    | _ := option.none
    end
constant cnf_not_or : Π {t : option term} (p : holds [t]) (n : nat),
  holds [reduce_not_or n t]

-- collect all terms in OR / NOT AND chain (right-associative)

def is_or : term → bool
| (const or_num _) := tt
| _ := ff

def reduce_or_aux : term → clause
| t@(c₁ • t₀ • (c₂ • t₁ • t₂)) :=
    if is_or c₁ ∧ is_or c₂
    then t₀::t₁::(reduce_or_aux t₂)
    else [mkNot t]
| t@(c₁ • t₀ • t₁)             :=
    if is_or c₁ then [t₀, t₁] else [mkNot t]
| _                            := [option.none]

def reduce_or : clause → clause :=
 (flip bind) (λ ot,
    match ot with
    | (option.some t) := reduce_or_aux t
    | option.none := [option.none]
    end)

constant cnf_or : Π {c : clause} (p : holds c), holds (reduce_or c)

def is_and : term → bool
| (const and_num _) := tt
| _ := ff

def reduce_not_and_aux : term → clause
| t@(c₁ • t₀ • (c₂ • t₁ • t₂)) :=
    if is_and c₁ ∧ is_and c₂
    then mkNot t₀ :: mkNot t₁ :: reduce_not_and_aux t₂
    else [mkNot t]
| (c₁ • t₀ • t₁) := [mkNot t₀, mkNot t₁]
| t := [mkNot t]

def reduce_not_and : option term → clause
| (option.some t) := reduce_not_and_aux t
| option.none     := [option.none]

constant cnf_not_and : Π {t : option term} (p : holds [t]),
  holds (reduce_not_and t)

-- xor

def reduce_xor_aux : term → nat → clause
| (xor t₀ t₁) 0 := [t₀, t₁]
| (xor t₀ t₁) 1 := [mkNot t₀, mkNot t₁]
| _           _ := [option.none]

def reduce_xor : option term → nat → clause
| (option.some t) n := reduce_xor_aux t n
| option.none     _ := [option.none]

constant cnf_xor : Π {t : option term} (p : holds [t]) (n : nat),
  holds (reduce_xor t n)

def reduce_not_xor_aux : term → nat → clause
| (not $ xor t₀ t₁) 0 := [t₀, mkNot t₁]
| (not $ xor t₀ t₁) 1 := [mkNot t₀, t₁]
| _                 _ := [option.none]

def reduce_not_xor : option term → nat → clause
| (option.some t) n := reduce_not_xor_aux t n
| _               _ := [option.none]

constant cnf_not_xor : Π {t : option term} (p : holds [t]) (n : nat),
  holds (reduce_not_xor t n)


-- implies

def reduce_imp_aux : term → clause
| (implies a c) := [mkNot a, c]
| _             := [option.none]

def reduce_imp : option term → clause
| (option.some t) := reduce_imp_aux t
| option.none     := [option.none]

constant cnf_implies : Π {ot : option term} (p : holds [ot]),
  holds (reduce_imp ot)

def reduce_not_implies' : nat → term → option term
| 0 (not $ implies t₀ t₁) := t₀
| 1 (not $ implies t₀ t₁) := mkNot t₁
| _ _                     := option.none

def reduce_not_implies (n : nat) : option term → option term :=
 (flip bind) (reduce_not_implies' n)

constant cnf_not_implies :
    Π {ot : option term} (p : holds [ot]) (n : nat),
        holds [reduce_not_implies n ot]

-- iff

def reduce_iff_aux : term → nat → clause
| (iff t₀ t₁) 0 := [mkNot t₀, t₁]
| (iff t₀ t₁) 1 := [t₀, mkNot t₁]
| _           _ := [option.none]

def reduce_iff : option term → nat → clause
| (option.some t) n := reduce_iff_aux t n
| option.none     _ := [option.none]

constant cnf_iff : Π {ot : option term} (p : holds [ot]) (n : nat),
  holds (reduce_iff ot n)

def reduce_not_iff_aux : term → nat → clause
| (not $ iff t₀ t₁) 0 := [t₀, t₁]
| (not $ iff t₀ t₁) 1 := [mkNot t₀, mkNot t₁]
| _ _ := [option.none]

def reduce_not_iff : option term → nat → clause
| (option.some t) n := reduce_not_iff_aux t n
| option.none     _ := [option.none]

constant cnf_not_iff : Π {ot : option term} (p : holds [ot]) (n : nat),
  holds (reduce_not_iff ot n)

-- ite

def reduce_ite_aux : term → nat → clause
| (b_ite c t₀ t₁) 0 := [mkNot c, t₀]
| (b_ite c t₀ t₁) 1 := [c, t₁]
| _             _ := [option.none]

def reduce_ite : option term → nat → clause
| (option.some t) n := reduce_ite_aux t n
| option.none     _ := [option.none]

constant cnf_ite : Π {ot : option term} (p : holds [ot]) (n : nat),
  holds (reduce_ite ot n)

def reduce_not_ite_aux : term → nat → clause
| (not $ b_ite c t₀ t₁) 0 := [c, mkNot t₁]
| (not $ b_ite c t₀ t₁) 1 := [mkNot c, mkNot t₀]
| _                   _ := [option.none]

def reduce_not_ite : option term → nat → clause
| (option.some t) n := reduce_not_ite_aux t n
| option.none     _ := [option.none]

constant cnf_not_ite : Π {ot : option term} (p : holds [ot]) (n : nat),
  holds (reduce_not_ite ot n)

/-------------------- n-ary ---------------/

constant cnf_and_pos {l : clause} {n : nat} :
  holds [mkNot $ mkAndN l, mynth l n]
constant cnf_or_neg {l : clause} {n : nat} :
  holds [mkOrN l, mkNot $ mynth l n]

def mkNotList : clause → clause
| [] := []
| (h::t) := mkNotSimp h :: mkNotList t

-- implicitly doing double negation elimination
constant cnf_and_neg_n {l : clause} : holds $ mkAndN l :: mkNotList l
constant cnf_or_pos_n {l : clause} : holds $ (mkNot $ mkOrN l) :: l

/-------------------- binary ---------------/

constant cnf_and_pos_0 {t₁ t₂ : option term} : holds [mkNot $ mkAnd t₁ t₂, t₁]
constant cnf_and_pos_1 {t₁ t₂ : option term} : holds [mkNot $ mkAnd t₁ t₂, t₂]

constant cnf_and_neg {t₁ t₂ : option term} :
  holds [mkAnd t₁ t₂, mkNot t₁, mkNot t₂]

constant cnf_or_pos {t₀ t₁ : option term} :
  holds [mkNot $ mkOr t₀ t₁, mkOr t₀ t₁]

constant cnf_or_neg_0 {t₀ t₁ : option term} : holds [mkOr t₀ t₁, mkNot t₀]
constant cnf_or_neg_1 {t₀ t₁ : option term} : holds [mkOr t₀ t₁, mkNot t₁]

constant cnf_xor_pos_0 {t₀ t₁ : option term} :
  holds [mkNot $ mkXor t₀ t₁, t₀, t₁]
constant cnf_xor_pos_1 {t₀ t₁ : option term} :
  holds [mkNot $ mkXor t₀ t₁, mkNot t₀, mkNot t₁]

constant cnf_xor_neg_0 {t₀ t₁ : option term} :
  holds [mkXor t₀ t₁, t₀, mkNot t₁]
constant cnf_xor_neg_1 {t₀ t₁ : option term} :
  holds [mkXor t₀ t₁, mkNot t₀, t₁]

constant cnf_implies_pos {t₀ t₁ : option term} :
  holds [mkNot $ mkImplies t₀ t₁, mkNot t₀, t₁]
constant cnf_implies_neg_0 {t₀ t₁ : option term} : holds [mkImplies t₀ t₁, t₀]
constant cnf_implies_neg_1 {t₀ t₁ : option term} :
  holds [mkImplies t₀ t₁, mkNot t₁]

constant cnf_iff_pos_0 {t₀ t₁ : option term} :
  holds [mkNot $ mkIff t₀ t₁, t₀, mkNot t₁]
constant cnf_iff_pos_1 {t₀ t₁ : option term} :
  holds [mkNot $ mkIff t₀ t₁, mkNot t₀, t₁]

constant cnf_iff_neg_0 {t₀ t₁ : option term} :
  holds [mkIff t₀ t₁, mkNot t₀, mkNot t₁]
constant cnf_iff_neg_1 {t₀ t₁ : option term} : holds [mkIff t₀ t₁, t₀, t₁]

constant cnf_ite_pos_0 {c t₀ t₁ : option term} :
  holds [mkNot $ mkIte c t₀ t₁, mkNot c, t₀]
constant cnf_ite_pos_1 {c t₀ t₁ : option term} :
  holds [mkNot $ mkIte c t₀ t₁, c, t₁]
constant cnf_ite_pos_2 {c t₀ t₁ : option term} :
  holds [mkNot $ mkIte c t₀ t₁, t₀, t₁]

constant cnf_ite_neg_0 {c t₀ t₁ : option term} :
  holds [mkIte c t₀ t₁, c, mkNot t₀]
constant cnf_ite_neg_1 {c t₀ t₁ : option term} :
  holds [mkIte c t₀ t₁, mkNot c, mkNot t₁]
constant cnf_ite_neg_2 {c t₀ t₁ : option term} :
  holds [mkIte c t₀ t₁, mkNot t₀, mkNot t₁]

/-*************** congruence ***************-/

constant smtrefl {t : option term} : holds [mkEq t t]

constant smtsymm {t₁ t₂ : option term} : holds [mkIneq t₁ t₂, mkEq t₂ t₁]

constant smttrans : Π {t₁ t₂ t₃ : option term},
        holds ([mkIneq t₁ t₂, mkIneq t₂ t₃, mkEq t₁ t₃])

constant smtcong : Π {f₁ x₁ : option term} {f₂ x₂ : option term},
        holds ([mkIneq f₁ f₂, mkIneq x₁ x₂,
                   mkEq (mkApp f₁ x₁) (mkApp f₂ x₂)])

def reduce_smttransn : clause → clause
| (h₁::h₂::t) := (mkIneq h₁ h₂) :: reduce_smttransn (h₂::t)
| _ := []

constant smttransn : Π {c : clause},
        holds (list.append (reduce_smttransn c)
                   [mkEq (mynth c 0) (get_last c)])

def reduce_smtcongn : clause → clause → clause
| (h₁::t₁) (h₂::t₂) := (mkIneq h₁ h₂) :: reduce_smtcongn t₁ t₂
| _ _ := []

constant smtcongn : Π {f : option term} {c₁ c₂ : clause},
        holds (list.append (reduce_smtcongn c₁ c₂)
                   [mkEq (mkAppN f c₁) (mkAppN f c₂)])

-- for predicates

constant smtrefl_p {t : option term} : holds [mkIff t t]

constant smtsymm_p {t₁ t₂ : option term} : holds [mkNot $ mkIff t₁ t₂, mkIff t₂ t₁]

constant smttrans_p : Π {t₁ t₂ t₃ : option term},
        holds ([mkNot (mkIff t₁ t₂), mkNot (mkIff t₂ t₃), mkIff t₁ t₃])

constant smtcong_p : Π {a₁ b₁ : option term} {a₂ b₂ : option term},
        holds ([mkNot (mkIff a₁ b₁), mkNot (mkIff a₂ b₂),
                   mkIff (mkApp a₁ a₂) (mkApp b₁ b₂)])

constant smtcongn_p : Π {f : term} {c₁ c₂ : clause} ,
         holds (list.append (reduce_smtcongn c₁ c₂)
                   [mkIff (mkAppN f c₁) (mkAppN f c₂)])


/-*************** instantiation ***************-/

def substitute : pos_num → term → term → option term
-- if finds shadowing, break
| p₁ (qforall p₂ body) t :=
   if p₁ = p₂ then option.none else
                               do res ← (substitute p₁ body t), (qforall p₂ res)
-- if found variable, replace by instantiation term *if types match*,
-- otherwise fail
| p₁ (const p₂ os) t :=
  do s ← os, st ← sortof t,
    if p₁ ≠ p₂ then (const p₂ s) else if s = st then t else option.none
-- replace each term in application
| p₁ (f • t₁) t :=
  do fs ← (substitute p₁ f t), t₁s ← (substitute p₁ t₁ t), fs • t₁s

constant inst_forall : Π {v : pos_num} {body : term} (term : term),
  holds [mkNot $ mkForall v body, substitute v body term]