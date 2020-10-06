import init.control.combinators
import data.num.basic

def genPairs {α : Type} [s : decidable_eq α] (a : α) : list α → list (α × α) :=
  list.filter_map (λ x : α, if a = x then option.none else option.some (a,x))

def genAllPairs {α : Type} [s : decidable_eq α] : list α → list (α×α)
| [] := []
| (h::t) := genPairs h t ++ genAllPairs t

namespace smt

def {u} remove {α : Type u} [decidable_eq α] : α → list α → list α
| x [] := []
| x (y :: c) := if x = y then c else y :: remove x c

@[derive decidable_eq]
inductive sort : Type
| constructor : sort
| atom : pos_num → sort
| arrow : sort → sort → sort

section
open pos_num
@[pattern] def bot_num     : pos_num := one
@[pattern] def not_num     : pos_num := succ bot_num
@[pattern] def or_num      : pos_num := succ not_num
@[pattern] def and_num     : pos_num := succ or_num
@[pattern] def implies_num : pos_num := succ and_num
@[pattern] def xor_num     : pos_num := succ implies_num
@[pattern] def iff_num     : pos_num := succ xor_num
@[pattern] def b_ite_num   : pos_num := succ iff_num
@[pattern] def f_ite_num   : pos_num := succ b_ite_num
@[pattern] def eq_num      : pos_num := succ f_ite_num
@[pattern] def forall_num  : pos_num := succ eq_num

def bool_num  : pos_num := one
end

namespace sort
-- the special sort for predicates. Later on this should change to Prop
def sort_to_string : sort → string
| constructor := "constructor"
| (atom pos) := repr pos
| (arrow s1 s2) :=
  "(→ " ++ (sort_to_string s1) ++ " " ++ (sort_to_string s2) ++ ")"

meta instance: has_repr sort := ⟨sort_to_string⟩

def mkArrowN_aux : sort → list sort → sort
| hd [] := hd
| hd (h::t) := arrow hd (mkArrowN_aux h t)

def mkArrowN (l : list (option sort)) : option sort :=
do sort_list ← monad.sequence l,
 match sort_list with
 | [] := option.none
 | (h :: t) := mkArrowN_aux h t
 end

end sort

@[derive decidable_eq]
inductive term : Type
| const : pos_num → option sort → term
| app : term → term → term
| qforall : pos_num → term → term

namespace term

open sort

infixl ` • ` :20  := app
infixl ` » ` :21  := qforall

#check (λ (p : pos_num) (t : term), p » t)

def toUnary (t : term) : term → term := λ t₁: term, t • t₁
def toBinary (t : term) : term → term → term := λ t₁ t₂ : term, t • t₁ • t₂
def toTernary (t : term) : term → term → term → term := λ t₁ t₂ t₃ : term, t • t₁ • t₂ • t₃

def cstr (p : pos_num) : term := const p (option.some constructor)

@[pattern] def boolsort := sort.atom bool_num
@[pattern] def b_ite : term → term → term → term := toTernary $ cstr b_ite_num
@[pattern] def f_ite : term → term → term → term := toTernary $ cstr f_ite_num
@[pattern] def not : term → term := toUnary $ cstr not_num
@[pattern] def bot : term := cstr bot_num
@[pattern] def top : term := not bot
@[pattern] def eq      : term → term → term := toBinary $ cstr eq_num
@[pattern] def or      : term → term → term := toBinary $ cstr or_num
@[pattern] def and     : term → term → term := toBinary $ cstr and_num
@[pattern] def implies : term → term → term := toBinary $ cstr implies_num
@[pattern] def xor     : term → term → term := toBinary $ cstr xor_num
@[pattern] def iff     : term → term → term := toBinary $ cstr iff_num

def term_to_string : term → string
| (const name option.none) := "(" ++ repr name ++ ":none)"
| (const name (option.some srt)) :=  repr name ++ ":" ++ sort_to_string srt
| (app f t) :=
  "(" ++ (term_to_string f) ++ " " ++ (term_to_string t) ++ ")"
| (qforall p t) := repr p ++ " » " ++ term_to_string t

meta instance: has_repr term := ⟨term_to_string⟩

def sortof_aux : term → option sort
| (const bot_num _) := boolsort
| (const not_num _) := (arrow boolsort boolsort)
| (const or_num  _) := (arrow boolsort (arrow boolsort boolsort))
| (const and_num _)  := (arrow boolsort (arrow boolsort boolsort))
| (const implies_num _)  := (arrow boolsort (arrow boolsort boolsort))
| (const xor_num _)  := (arrow boolsort (arrow boolsort boolsort))
| (const iff_num _)  := (arrow boolsort (arrow boolsort boolsort))
| (const _ s)      := s
| (qforall p₁ t₁)  :=
  do s₁ ← sortof_aux t₁,
    if s₁ = boolsort then boolsort else option.none
| (eq t₁ t₂) :=
  do s₁ ← sortof_aux t₁, s₂ ← sortof_aux t₂,
    if s₁ = s₂ then boolsort else option.none
| (f_ite t₁ t₂ t₃) :=
    do s₁ ← sortof_aux t₁, s₂ ← sortof_aux t₂, s₃ ← sortof_aux t₂,
        if s₁ = boolsort ∧ s₂ = s₃ then s₂ else option.none
| (f • t)  :=
  do sf ← sortof_aux f, s ← sortof_aux t,
    match sf with
    | (arrow s1 s2) := if s1 = s then s2 else option.none
    | _ := option.none
    end

def sortof : option term → option sort :=
 (flip option.bind) sortof_aux

def mkApp_aux : term → term → option term :=
  λ t₁ t₂,
    do s₁ ← sortof t₁, s₂ ← sortof t₂,
      match s₁ with
      | (arrow srt _) := if srt = s₂ then option.some (app t₁ t₂) else option.none
      | _ := option.none
      end

def bind2 {m : Type → Type} [has_bind m] {α β γ : Type} (f : α → β → m γ) (a : m α) (b : m β) : m γ :=
  do a' ← a, b' ← b, f a' b'
def bind3 {m : Type → Type} [has_bind m] {α β γ δ : Type} (f : α → β → γ → m δ) (a : m α) (b : m β) (c : m γ) : m δ :=
  do a' ← a, b' ← b, c' ← c, f a' b' c'

def mkApp : option term → option term → option term := bind2 mkApp_aux
def mkAppN (t : option term) (l : list (option term)) : option term :=
  do s ← t, l' ← monad.sequence l, mfoldl mkApp_aux s l'

def mkIte_aux (c t₀ t₁ : term) : option term :=
  if (sortof c) = option.some boolsort
  then
    do s₀ ← sortof t₀, s₁ ← sortof t₁,
      match (s₀,s₁) with
      | (boolsort, boolsort) := option.some $ b_ite c t₀ t₁
      | (_,_) :=  if s₀ = s₁ then f_ite c t₀ t₁ else option.none
      end
  else option.none

def mkIte : option term → option term → option term → option term := bind3 mkIte_aux

def mkNot : option term → option term :=
  flip option.bind $
    λ t, do s ← sortof t, if s = boolsort then not t else option.none

def mkNotSimp : option term → option term
| (option.some (not s')) := option.some s'
| (option.some t)        := mkNot (option.some t)
| _                      := option.none

def constructBinaryTerm (constructor : term → term → term) (test : sort → sort → bool) : option term → option term → option term :=
  bind2 $ λ t₁ t₂,
            do s₁ ← sortof t₁, s₂ ← sortof t₂,
                if test s₁ s₂ then constructor t₁ t₂ else option.none

def constructNaryTerm (constructor : term → term → term) (test : sort → sort → bool) : option term → list (option term) → option term :=
  λ ot₁ ots₂,
  let auxfxn : term → term → option term := (λ t₁ t₂,
            do s₁ ← sortof t₁, s₂ ← sortof t₂,
                if test s₁ s₂ then constructor t₁ t₂ else option.none)
    in (do t₁ ← ot₁, ts₂ ← monad.sequence ots₂, mfoldl auxfxn t₁ ts₂)


def comp2 {α β γ δ : Type} (f : γ → δ) (g : α → β → γ) : α → β → δ :=
λ a b, f (g a b)

@[simp] def mkEq : option term → option term → option term :=
  constructBinaryTerm eq (λ s₁ s₂, s₁ = s₂)
def mkIneq : option term → option term → option term :=
  comp2 mkNot mkEq
def mkOr : option term → option term → option term :=
  constructBinaryTerm or (λ s₁ s₂, s₁ = boolsort ∧ s₂ = boolsort)
def mkOrSimp : option term → option term → option term :=
  constructBinaryTerm (λ t₁ t₂, if t₁ = bot then t₂ else (if t₂ = bot then t₁ else or t₁ t₂))
    (λ s₁ s₂, s₁ = boolsort ∧ s₂ = boolsort)
def mkOrN : list (option term) → option term :=
    constructNaryTerm or (λ s₁ s₂, s₁ = boolsort ∧ s₂ = boolsort) bot
def mkAnd : option term → option term → option term :=
  constructBinaryTerm and (λ s₁ s₂, s₁ = boolsort ∧ s₂ = boolsort)
def mkAndSimp : option term → option term → option term :=
  constructBinaryTerm (λ t₁ t₂, if t₁ = top then t₂ else (if t₂ = top then t₁ else and t₁ t₂))
    (λ s₁ s₂, s₁ = boolsort ∧ s₂ = boolsort)
def mkAndN : list (option term) → option term :=
    constructNaryTerm and (λ s₁ s₂, s₁ = boolsort ∧ s₂ = boolsort) top
def mkImplies : option term → option term → option term :=
  constructBinaryTerm implies (λ s₁ s₂, s₁ = boolsort ∧ s₂ = boolsort)
def mkXor : option term → option term → option term :=
  constructBinaryTerm xor (λ s₁ s₂, s₁ = boolsort ∧ s₂ = boolsort)
def mkIff : option term → option term → option term :=
  constructBinaryTerm iff (λ s₁ s₂, s₁ = boolsort ∧ s₂ = boolsort)
def mkIffSimp : option term → option term → option term :=
  constructBinaryTerm (λ t₁ t₂ : term,
        match t₁ with
        | bot := not t₂
        | top := t₂
        | _ := match t₂ with
               | bot := not t₁
               | top := t₁
               | _ := iff t₁ t₂
               end
        end)
    (λ s₁ s₂, s₁ = boolsort ∧ s₂ = boolsort)

def mkDistinct : list (option term) → option term :=
  λ ol, mkAndN $ list.map (function.uncurry mkIneq) (genAllPairs ol)

-- retrieve the identifier of a constant
def numOf : term → option pos_num
| (const n _) := n
| _ := option.none

-- define calculus
notation `clause` := list (option term)

def mynth : clause → ℕ → option term := comp2 monad.join (@list.nth (option term))
def get_last : clause → option term := λ c, mynth c (c.length - 1)

-- eventually should give Prop
constant holds : clause → Type
def concat_cl : clause → clause → clause := @list.append (option term)
def remove_duplicates : clause → clause
| [] := []
| (h::t) := if h ∈ t then remove_duplicates t else h::(remove_duplicates t)

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


-- get n-th element in AND / NOT OR chain (right-associative)


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


-- recursively find all constants with p, and replace with other term
def substitute : option term → option term → option term
| (option.some (qforall p₁ (const p₂ os₁))) ot₂ :=
    if p₁ = p₂
    then (do t₂ ← ot₂, s₂ ← sortof t₂, s₁ ← os₁,
             if s₁ = s₂ then ot₂ else option.none)
    else (const p₂ os₁)
| (option.some (qforall p₁ (t₁₁ • t₁₂))) ot₂ :=
  do left_term ← substitute (qforall p₁ t₁₁) ot₂,
     right_term ← substitute (qforall p₁ t₁₂) ot₂,
   left_term • right_term
| _ _ := option.none


constant inst_forall : Π (quant instTerm : term),
         holds [mkNot quant, substitute quant instTerm]

end term

end smt

namespace debug
open smt
open smt.sort smt.term
def s := boolsort
def f := const 50 (arrow s s)
def x₁ := const 51 s
def x₂ := const 52 s

noncomputable lemma lem : holds [mkIneq x₁ x₂, mkEq (mkApp f x₁) (mkApp f x₂)] :=
  let s₀ := @smtcong f x₁ f x₂ in
  let s₁ := @smtrefl f in
   R0 s₁ s₀ (mkEq f f)

noncomputable theorem test_theorem (s₀ : holds [mkEq x₁ x₂]) (s₁ : holds [mkIneq (mkApp f x₁) (mkApp f x₂)]) : holds [] :=
 have s₂ : holds [mkEq (mkApp f x₁) (mkApp f x₂)], from R0 s₀ lem (mkEq x₁ x₂),
   R0 s₂ s₁ (mkEq (mkApp f x₁) (mkApp f x₂))

-- does not go through
--noncomputable lemma wrong :
--  holds ([mkIneq x₁ x₂, mkIneq f x₂, mkEq (mkApp f x₂) (mkApp f x₂)]) :=
--    @smtcong f f a b

def u1 := atom 1
def u2 := atom 2
def x := (const 60 u1)
def f1 := const 61 (arrow u1 u1)
def t1  := const 62 u1
def t2 := const 63 u2
def p1 := const 64 (arrow u1 boolsort)

def myquant := qforall 60 (f1 • x) -- this binds the variable

-- noncomputable lemma testInst : holds [mkNot myquant, f1 • t1] :=
--   inst_forall myquant t1

-- does not go through
-- noncomputable lemma testInst2 : holds [mkNot myquant, f1 • t2] :=
--   @inst_forall myquant t2

end debug
