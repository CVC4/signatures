import aux

namespace smt

/- dep is the sort for terms that have dependent types such as 
   equality and forall. We handle these in a special way to 
   avoid dependent types.
   Additionally, we have atomic sorts, parametrized by a positive number,
   and arrow or functional sorts -/
@[derive decidable_eq]
inductive sort : Type
| dep : sort
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

def sort_to_string : sort → string
| dep := "dep"
| (atom pos) := 
  match pos with
  | 1 := "bool"
  | _ := repr pos
  end
| (arrow s1 s2) := 
  "(" ++ (sort_to_string s1) ++ " → " ++ (sort_to_string s2) ++ ")"

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
 | [] := option.none
 | (h :: t) := mkArrowN_aux h t
 end

end sort

-- terms are constants of a sort, applications,
-- or quantified formulas
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

-- unary, binary and ternary applications
def toUnary (t : term) : term → term := λ t₁: term, t • t₁
def toBinary (t : term) : term → term → term := λ t₁ t₂ : term, t • t₁ • t₂
def toTernary (t : term) : term → term → term → term := λ t₁ t₂ t₃ : term, t • t₁ • t₂ • t₃

-- constant term constructor
def cstr (p : pos_num) (s : sort): term := const p (option.some s)

-- Boolean sort definition

@[pattern] def boolsort := sort.atom bool_num

#eval sort_to_string dep
#eval sort_to_string boolsort
#eval sort_to_string (arrow boolsort boolsort)
#eval sort_to_string (arrow boolsort (arrow boolsort boolsort))
#eval option_sort_to_string (mkArrowN [some boolsort, some boolsort, some boolsort])

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
@[pattern] def iff     : term → term → term := toBinary $ cstr iff_num
  (arrow boolsort (arrow boolsort boolsort))

def pos_to_string : pos_num → string
| bot_num := "bot"
| not_num := "not"
| or_num := "or"
| and_num := "and"
| implies_num := "implies"
| xor_num := "xor"
| iff_num := "iff"
| b_ite_num := "b_ite"
| f_ite_num := "f_ite"
| eq_num := "eq"
| forall_num := "forall"
| _ := "ILL-TYPED"

def term_to_string : term → string
| (const name _) := pos_to_string name
| (app f t) := "(" ++ (term_to_string f) ++ " " ++ (term_to_string t) ++ ")"
| (qforall p t) := pos_to_string p ++ " » " ++ term_to_string t

def sorted_term_to_string : term → string
| (const name option.none) := "(" ++ repr name ++ ":none)"
| (const name (option.some srt)) :=  repr name ++ ":" ++ sort_to_string srt
| (app f t) :=
  "(" ++ (sorted_term_to_string f) ++ " " ++ (sorted_term_to_string t) ++ ")"
| (qforall p t) := repr p ++ " » " ++ sorted_term_to_string t

#eval term_to_string bot
#eval term_to_string top
#eval term_to_string (not bot)
#eval term_to_string (not top)
#eval term_to_string (and bot bot)
#eval term_to_string (b_ite top bot top)
#eval term_to_string (eq bot bot)
#eval term_to_string (const bot_num none)

#eval sorted_term_to_string bot
#eval sorted_term_to_string top
#eval sorted_term_to_string (not bot)
#eval sorted_term_to_string (not top)
#eval sorted_term_to_string (and bot bot)
#eval sorted_term_to_string (b_ite top bot top)
#eval sorted_term_to_string (eq bot bot)
#eval sorted_term_to_string (const bot_num none)

meta instance: has_repr term := ⟨sorted_term_to_string⟩

-- sort of terms
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
#eval sortof (app (const (20 : pos_num) (arrow boolsort boolsort)) bot)
#eval option_sort_to_string (sortof_aux (eq bot bot))
#eval option_sort_to_string (sortof (eq bot bot))
#eval option_sort_to_string (sortof_aux (const 1 none))
#eval option_sort_to_string (sortof (const 1 none))
#eval option_sort_to_string (sortof (app (const (20 : pos_num) (arrow boolsort boolsort)) bot))

-- application of term to term
def mkApp_aux : term → term → option term :=
  λ t₁ t₂,
    do s₁ ← sortof t₁, s₂ ← sortof t₂,
      match s₁ with
      | (arrow srt _) := if srt = s₂ then option.some (app t₁ t₂) else option.none
      | _ := option.none
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
#eval mkApp (const (20 : pos_num) (arrow boolsort boolsort)) bot
#eval mkAppN (const (21 : pos_num) (arrow boolsort (arrow boolsort boolsort))) [bot, bot]


-- if-then-else
def mkIte_aux (c t₀ t₁ : term) : option term :=
  if (sortof c) = option.some boolsort
  then
    do s₀ ← sortof t₀, s₁ ← sortof t₁,
      match (s₀,s₁) with
      | (boolsort, boolsort) := option.some $ b_ite c t₀ t₁
      | (_,_) :=  if s₀ = s₁ then f_ite c t₀ t₁ else option.none
      end
  else option.none

def mkIte : option term → option term → option term → option term := 
  bind3 mkIte_aux

#eval (mkIte (eq bot bot) bot top)


-- negation
def mkNot : option term → option term :=
  flip option.bind $
    λ t, do s ← sortof t, if s = boolsort then not t else option.none

def mkNotSimp : option term → option term
| (option.some (not s')) := option.some s'
| (option.some t)        := mkNot (option.some t)
| _                      := option.none

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
                if test s₁ s₂ then constructor t₁ t₂ else option.none

def constructNaryTerm (constructor : term → term → term) (test : sort → sort → bool) : option term → list (option term) → option term :=
  λ ot₁ ots₂,
  let auxfxn : term → term → option term := (λ t₁ t₂,
            do s₁ ← sortof t₁, s₂ ← sortof t₂,
                if test s₁ s₂ then constructor t₁ t₂ else option.none)
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

def mkForall (p : pos_num) (obody : option term) : option term :=
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
#eval mkIff (mkAndN [top , top , bot]) (mkOr bot bot)
#eval mkIffSimp bot bot

-- retrieve the identifier of a constant
def numOf : term → option pos_num
| (const n _) := n
| _ := option.none



end term

end smt