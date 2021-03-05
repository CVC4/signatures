import aux

namespace proof

/- dep is the sort for terms that have dependent types such as
   equality and forall. We handle these in a special way to
   avoid dependent types.
   Additionally, we have atomic sorts, parameterized by a
   nat, arrow or functional sorts, and bitvector sorts
   parameterized by their length -/
@[derive decidable_eq]
inductive sort : Type
| dep : sort
| atom : ℕ → sort
| arrow : sort → sort → sort
| bv : ℕ → sort

/- Each predefined function is also parameterized by a
   nat, an application of terms is parametrized
   by all the nats involved in the application,
   thus giving unique sets of nats to unique terms -/
section
@[pattern] def bot_num     : ℕ := 0
@[pattern] def not_num     : ℕ := bot_num + 1
@[pattern] def or_num      : ℕ := not_num + 1
@[pattern] def and_num     : ℕ := or_num + 1
@[pattern] def implies_num : ℕ := and_num + 1
@[pattern] def xor_num     : ℕ := implies_num + 1
@[pattern] def b_ite_num   : ℕ := xor_num + 1
@[pattern] def f_ite_num   : ℕ := b_ite_num + 1
@[pattern] def eq_num      : ℕ := f_ite_num + 1
@[pattern] def forall_num  : ℕ := eq_num + 1
@[pattern] def bvBitOfNum : ℕ := forall_num + 1
@[pattern] def bvEqNum : ℕ := bvBitOfNum + 1
@[pattern] def bvNotNum : ℕ := bvEqNum + 1
@[pattern] def bvAndNum : ℕ := bvNotNum + 1
@[pattern] def bvOrNum : ℕ := bvAndNum + 1

def bool_num  : ℕ := 0
def int_num : ℕ := bool_num + 1
end

namespace sort

def sort_to_string : sort → string
| dep := "dep"
| (atom n) :=
  match n with
  | 0 := "bool"
  | 1 := "int"
  | _ := repr n
  end
| (arrow s1 s2) :=
  "(" ++ (sort_to_string s1) ++ " → " ++ (sort_to_string s2) ++ ")"
| (bv n) := "bv " ++ (repr n)

def option_sort_to_string : option sort → string
| (some x) := sort_to_string x
| none := "none"

meta instance: has_repr sort := ⟨sort_to_string⟩

/- mkArrowN curries multi-argument types
   f : X₁ × X₂ × ... into
   f : X₁ → X₂ → ... -/
def mkArrowN_aux : sort → list sort → sort
| hd [] := hd
| hd (h::t) := arrow hd (mkArrowN_aux h t)

def mkArrowN (l : list (option sort)) : option sort :=
do sort_list ← monad.sequence l,
 match sort_list with
 | [] := none
 | (h :: t) := mkArrowN_aux h t
 end

end sort

@[derive decidable_eq]
inductive value : Type
| bitvec : list bool → value
| integer : ℤ → value

def bv_to_string : list bool → string
| [] := ""
| (h :: t) := (if h then "1" else "0") ++ bv_to_string t

--set_option trace.eqn_compiler.elim_match true
def value_to_string : value → string
| (value.bitvec l) := bv_to_string l
| (value.integer i) := repr i

meta instance: has_repr value := ⟨value_to_string⟩

/- terms are values (nullary constants),
   constants of a sort, applications,
   or quantified formulas
   Quantified variables are also
   parameterized by a nat -/
@[derive decidable_eq]
inductive term : Type
| val : value → option sort → term
| const : ℕ → option sort → term
| app : term → term → term
| qforall : ℕ → term → term

namespace term

open sort

infixl ` • ` :20  := app
infixl ` » ` :21  := qforall

#check (λ (p : ℕ) (t : term), p » t)

-- unary, binary and ternary applications
def toUnary (t : term) : term → term := λ t₁: term, t • t₁
def toBinary (t : term) : term → term → term := λ t₁ t₂ : term, t • t₁ • t₂
def toTernary (t : term) : term → term → term → term := λ t₁ t₂ t₃ : term, t • t₁ • t₂ • t₃

-- constant term constructor
def cstr (p : ℕ) (s : sort): term := const p (some s)

-- Sort definitions
@[pattern] def boolsort := sort.atom bool_num
@[pattern] def intsort := sort.atom int_num

#eval sort_to_string dep
#eval sort_to_string boolsort
#eval sort_to_string (arrow boolsort boolsort)
#eval sort_to_string (arrow boolsort (arrow boolsort boolsort))
#eval option_sort_to_string (mkArrowN [some boolsort, some boolsort, some boolsort])
#check const 19 (some (bv 2))

-- term definitions
@[pattern] def b_ite : term → term → term → term := toTernary $ cstr b_ite_num
  (arrow boolsort (arrow boolsort (arrow boolsort boolsort)))
@[pattern] def f_ite : term → term → term → term := toTernary $ cstr f_ite_num dep
@[pattern] def not : term → term := toUnary $ cstr not_num (arrow boolsort boolsort)
@[pattern] def bot : term := cstr bot_num boolsort
@[pattern] def top : term := not bot
@[pattern] def eq      : term → term → term := toBinary $ cstr eq_num dep
@[pattern] def or      : term → term → term := toBinary $ cstr or_num
  (arrow boolsort (arrow boolsort boolsort))
@[pattern] def and     : term → term → term := toBinary $ cstr and_num
  (arrow boolsort (arrow boolsort boolsort))
@[pattern] def implies : term → term → term := toBinary $ cstr implies_num
  (arrow boolsort (arrow boolsort boolsort))
@[pattern] def xor     : term → term → term := toBinary $ cstr xor_num
  (arrow boolsort (arrow boolsort boolsort))
-- term definitions
-- bv 0 doesn't exist
-- check int is in range
@[pattern] def bitOf : ℕ → term → term → term := λ n, toBinary $ cstr bvBitOfNum
  (arrow (bv n) (arrow intsort boolsort))
@[pattern] def bvEq : ℕ → term → term → term := λ n, toBinary $ cstr bvEqNum
  (arrow (bv n) (arrow (bv n) (boolsort)))

def nat_to_string : ℕ → string
| bot_num := "⊥"
| not_num := "¬"
| or_num := "∨"
| and_num := "∧"
| implies_num := "⇒"
| xor_num := "⊕"
| b_ite_num := "b_ite"
| f_ite_num := "f_ite"
| eq_num := "≃"
| forall_num := "∀"
| bvBitOfNum := "[ ]"
| bvEqNum := "≃bv"
| bvNotNum := "¬bv"
| bvAndNum := "∧bv"
| bvOrNum := "∨bv"
| x := repr x

def term_to_string : term → string
| (val (value.bitvec l) _) := bv_to_string l
| (val (value.integer i) _) := repr i
| ((const or_num _) • t1 • t2) := term_to_string t1 ++ " ∨ " ++ term_to_string t2
| ((const and_num _) • t1 • t2) := term_to_string t1 ++ " ∧ " ++ term_to_string t2
| ((const implies_num _) • t1 • t2) := term_to_string t1 ++ " ⇒ " ++ term_to_string t2
| ((const xor_num _) • t1 • t2) := term_to_string t1 ++ " ⊕ " ++ term_to_string t2
| ((const eq_num _) • t1 • t2) := term_to_string t1 ++ " ≃ " ++ term_to_string t2
| ((const bvBitOfNum _) • t1 • t2) := term_to_string t1 ++ "[" ++ term_to_string t2 ++ "]"
| (const name _) := nat_to_string name
| (app (const not_num _) t) := "¬ " ++ term_to_string t
| (app f t) := "(" ++ (term_to_string f) ++ " " ++ (term_to_string t) ++ ")"
| (qforall p t) := "∀ " ++ repr p ++ " . " ++ term_to_string t

def sorted_term_to_string : term → string
| (val (value.bitvec l) none) := (bv_to_string l) ++ ":none"
| (val (value.bitvec l) (some srt)) := (bv_to_string l) ++ sort_to_string srt
| (val (value.integer i) none) := (repr i) ++ ":none"
| (val (value.integer i) (some srt)) := (repr i) ++ sort_to_string srt
| (const name none) := "(" ++ nat_to_string name ++ ":none)"
| (const name (some srt)) :=  nat_to_string name ++ ":" ++ sort_to_string srt
| (app f t) :=
  "(" ++ (sorted_term_to_string f) ++ " " ++ (sorted_term_to_string t) ++ ")"
| (qforall p t) := "∀ " ++ repr p ++ " . " ++ sorted_term_to_string t

meta instance: has_repr term := ⟨term_to_string⟩

/-
def option_term_to_string : option term → string
| (some x) := term_to_string x
| none := "none"

meta instance: has_repr (option term) := ⟨option_term_to_string⟩
-/

#eval bot
#eval top
#eval (not bot)
#eval (not top)
#eval (and bot bot)
#eval (b_ite top bot top)
#eval (eq bot bot)
#eval (const bot_num none)
#eval (qforall 1 bot)

#eval sorted_term_to_string bot
#eval sorted_term_to_string top
#eval sorted_term_to_string (not bot)
#eval sorted_term_to_string (not top)
#eval sorted_term_to_string (and bot bot)
#eval sorted_term_to_string (b_ite top bot top)
#eval sorted_term_to_string (eq bot bot)
#eval sorted_term_to_string (const bot_num none)
#eval sorted_term_to_string (qforall 1 bot)

-- sort of terms
set_option trace.eqn_compiler.elim_match true
def sortof_aux : term → option sort
| (val (value.bitvec l) _) := if ((list.length l) = 0) then
                                none
                              else
                                bv (list.length l)
| (val (value.integer i) _) := intsort
| (const bot_num _) := boolsort
| (const not_num _) := (arrow boolsort boolsort)
| (const or_num  _) := (arrow boolsort (arrow boolsort boolsort))
| (const and_num _)  := (arrow boolsort (arrow boolsort boolsort))
| (const implies_num _)  := (arrow boolsort (arrow boolsort boolsort))
| (const xor_num _)  := (arrow boolsort (arrow boolsort boolsort))
| (const _ s)      := s
| (bitOf n t₁ t₂) := 
  do s₁ ← sortof_aux t₁, s₂ ← sortof_aux t₂, 
    if s₁ = (bv n) ∧ s₂ = intsort then 
      boolsort
    else none
| (bvEq n t₁ t₂) := 
  do s₁ ← sortof_aux t₁, s₂ ← sortof_aux t₂,
    if s₁ = (bv n) ∧ s₂ = (bv n) then
      boolsort
    else none
| (qforall p₁ t₁)  :=
  do s₁ ← sortof_aux t₁,
    if s₁ = boolsort then boolsort else none
| (eq t₁ t₂) :=
  do s₁ ← sortof_aux t₁, s₂ ← sortof_aux t₂,
    if s₁ = s₂ then boolsort else none
| (f_ite t₁ t₂ t₃) :=
    do s₁ ← sortof_aux t₁, s₂ ← sortof_aux t₂, s₃ ← sortof_aux t₂,
        if s₁ = boolsort ∧ s₂ = s₃ then s₂ else none
| (f • t)  :=
  do sf ← sortof_aux f, s ← sortof_aux t,
    match sf with
    | (arrow s1 s2) := if s1 = s then s2 else none
    | _ := none
    end
/- bind : (m : option term) → (f : (term → option sort))
   unpacks the term from m and applies f to it.
   Here, we have f first and expect sortof to take m as
   the argument so we use flip to reverse the argument
   order -/
def sortof : option term → option sort :=
 (flip option.bind) sortof_aux

#eval sortof_aux (eq bot bot)
#eval sortof (eq bot bot)
/- Sorts can only be none for ill-formed
   `forall`, `eq`, `f_ite` and `app` -/
#eval sortof_aux (const 1 none)
#eval sortof (const 1 none)
#eval sortof (app (const (20 : ℕ) (arrow boolsort boolsort)) bot)
#eval option_sort_to_string (sortof_aux (eq bot bot))
#eval option_sort_to_string (sortof (eq bot bot))
#eval option_sort_to_string (sortof_aux (const 1 none))
#eval option_sort_to_string (sortof (const 1 none))
#eval option_sort_to_string (sortof (app (const (20 : ℕ) (arrow boolsort boolsort)) bot))

-- application of term to term
def mkApp_aux : term → term → option term :=
  λ t₁ t₂,
    do s₁ ← sortof t₁, s₂ ← sortof t₂,
      match s₁ with
      | (arrow srt _) := if srt = s₂ then some (app t₁ t₂) else none
      | _ := none
      end

/- bind : (x : m α) → (f : (α → m α))
   unpacks the term from the monad x and applies
   f to it. bind2 and bind3 are versions of bind where
   f is binary and ternary respectively, with the
   arguments reordered, as in sortof -/
def bind2 {m : Type → Type} [has_bind m] {α β γ : Type}
  (f : α → β → m γ) (a : m α) (b : m β) : m γ :=
    do a' ← a, b' ← b, f a' b'
def bind3 {m : Type → Type} [has_bind m] {α β γ δ : Type}
  (f : α → β → γ → m δ) (a : m α) (b : m β) (c : m γ) : m δ :=
    do a' ← a, b' ← b, c' ← c, f a' b' c'

-- binary and n-ary application
def mkApp : option term → option term → option term := bind2 mkApp_aux
def mkAppN (t : option term) (l : list (option term)) : option term :=
  do s ← t, l' ← monad.sequence l, mfoldl mkApp_aux s l'

#check (λ (n:term), bot)
--#check mkApp (λ (n:term), bot) bot
#eval mkApp (const (20 : ℕ) (arrow boolsort boolsort)) bot
#eval mkAppN (const (21 : ℕ) (arrow boolsort (arrow boolsort boolsort))) [bot, bot]


-- if-then-else
def mkIte_aux (c t₀ t₁ : term) : option term :=
  if (sortof c) = some boolsort
  then
    do s₀ ← sortof t₀, s₁ ← sortof t₁,
      match (s₀,s₁) with
      | (boolsort, boolsort) := some $ b_ite c t₀ t₁
      | (_,_) :=  if s₀ = s₁ then f_ite c t₀ t₁ else none
      end
  else none

def mkIte : option term → option term → option term → option term :=
  bind3 mkIte_aux

#eval (mkIte (eq bot bot) bot top)


-- negation
def mkNot : option term → option term :=
  flip option.bind $
    λ t, do s ← sortof t, if s = boolsort then not t else none

def mkNotSimp : option term → option term
| (some (not s')) := some s'
| (some t)        := mkNot (some t)
| _                      := none

-- Notice mkNotSimp gives double negation elimination
#eval mkNot bot
#eval mkNot top
#eval mkNotSimp bot
#eval mkNotSimp top
#eval mkNotSimp (mkNotSimp (mkNotSimp top))


/- term constructors for binary and n-ary terms. `test` is the predicate on the sort of
   the arguments that needs to be satisfied -/
def constructBinaryTerm (constructor : term → term → term) (test : sort → sort → bool) :
  option term → option term → option term :=
  bind2 $ λ t₁ t₂,
            do s₁ ← sortof t₁, s₂ ← sortof t₂,
                if test s₁ s₂ then constructor t₁ t₂ else none

def constructNaryTerm (constructor : term → term → term) (test : sort → sort → bool) : option term → list (option term) → option term :=
  λ ot₁ ots₂,
  let auxfxn : term → term → option term := (λ t₁ t₂,
            do s₁ ← sortof t₁, s₂ ← sortof t₂,
                if test s₁ s₂ then constructor t₁ t₂ else none)
    in (do t₁ ← ot₁, ts₂ ← monad.sequence ots₂, mfoldl auxfxn t₁ ts₂)


def comp2 {α β γ δ : Type} (f : γ → δ) (g : α → β → γ) : α → β → δ :=
λ a b, f (g a b)


-- Boolean ops
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

def mkDistinct : list (option term) → option term :=
  λ ol, mkAndN $ list.map (function.uncurry mkIneq) (genAllPairs ol)

def mkForall (p : ℕ) (obody : option term) : option term :=
  do body ← obody, (qforall p body)

#eval mkEq top bot
#eval mkIneq top bot
#eval mkOr top (const 22 boolsort)
#eval mkOrSimp top (const 22 boolsort)
#eval mkOrSimp bot (const 22 boolsort)
#eval mkOrN [const 20 boolsort, const 21 boolsort, const 23 boolsort]
#eval mkAnd top bot
#eval mkAndSimp top bot
#eval mkAndN [const 20 boolsort, const 21 boolsort, const 23 boolsort]
#eval mkImplies bot (const 20 boolsort)
#eval mkXor top top

-- retrieve the identifier of a constant
def numOf : term → option ℕ
| (const n _) := n
| _ := none

end term

end proof
