import term

open proof
open proof.sort proof.term

namespace rules
-- define calculus
notation `clause` := list (option term)

def mynth : clause → ℕ → option term := comp2 monad.join (@list.nth (option term))
def get_last : clause → option term := λ c, mynth c (c.length - 1)

-- eventually should give Prop
constant holds : clause → Type
constant thHolds : option term → Type

-- clause manipulation rules
def concat_cl : clause → clause → clause := @list.append (option term)
def remove_duplicates : clause → clause
| [] := []
| (h::t) := if h ∈ t then remove_duplicates t else h::(remove_duplicates t)

-- collect all terms in OR chain (right-associative)

def reduceOrAux : term → clause
| ((const or_num _) • t₀ • ((const orNum _) • t₁ • t₂))
          := t₀::t₁::(reduceOrAux t₂)
| ((const or_num _) • t₀ • t₁) := [t₀, t₁]
| t                            := [t]

def reduceOr : clause → clause :=
 (flip bind) (λ ot,
               match ot with
               | (some t) := reduceOrAux t
               | none := [none]
               end
             )

-- clausal reasoning
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

-- connecting theory reasoning and clausal reasoning

constant clAssume : Π {t : option term}, thHolds t → holds [t]

constant clOr : Π {t : option term} (p : thHolds t), holds (reduceOr [t])

constant scope : Π {t₁ t₂ : option term}
  (p₁ : thHolds t₁) (p₂ : thHolds t₂), thHolds (mkOr (mkNot t₁) t₂)

/-*************** Simplifications ***************-/

-- holes
constant trust : Π {c₁ : clause} (p : holds c₁) {c₂ : clause},
  holds c₂

constant thTrust : Π {t₁ t₂ : option term}, thHolds t₁ → thHolds t₂

def reduce_not_not : clause → clause :=
  list.map $ λ c : option term, do t ← c,
    match t with
    | not $ not t' := t'
    | _ := t
    end

constant not_not : Π {c : clause} (p : holds c),
  holds (reduce_not_not c)

/-------------------- with premises ---------------/


-- get n-th element in AND chain (right-associative)
def reduce_and_nth : ℕ → term → option term
| 0            (and t _)           := t
| 1            (and _ t)           := t
| (n+1) (and  _ (and t₀ t₁)) :=
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
| (n+1) (or _ (or t₀ t₁)) := reduce_or_nth n (or t₀ t₁)
| _            _                 := option.none
def reduce_not_or (n : ℕ) : option term → option term :=
  (flip bind) $ λ t,
    match t with
    | not t' := mkNot $ reduce_or_nth n t'
    | _ := option.none
    end
constant cnf_not_or : Π {t : option term} (p : holds [t]) (n : nat),
  holds [reduce_not_or n t]

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

-- ite

def reduce_ite_aux : term → nat → clause
| (bIte c t₀ t₁) 0 := [mkNot c, t₀]
| (bIte c t₀ t₁) 1 := [c, t₁]
| _             _ := [option.none]

def reduce_ite : option term → nat → clause
| (option.some t) n := reduce_ite_aux t n
| option.none     _ := [option.none]

constant cnf_ite : Π {ot : option term} (p : holds [ot]) (n : nat),
  holds (reduce_ite ot n)

def reduce_not_ite_aux : term → nat → clause
| (not $ bIte c t₀ t₁) 0 := [c, mkNot t₁]
| (not $ bIte c t₀ t₁) 1 := [mkNot c, mkNot t₀]
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

end rules
