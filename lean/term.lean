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
@[pattern] def botNum     : ℕ := 0
@[pattern] def notNum     : ℕ := botNum + 1
@[pattern] def orNum      : ℕ := notNum + 1
@[pattern] def andNum     : ℕ := orNum + 1
@[pattern] def impliesNum : ℕ := andNum + 1
@[pattern] def xorNum     : ℕ := impliesNum + 1
@[pattern] def bIteNum   : ℕ := xorNum + 1
@[pattern] def fIteNum   : ℕ := bIteNum + 1
@[pattern] def eqNum      : ℕ := fIteNum + 1
@[pattern] def forallNum  : ℕ := eqNum + 1
@[pattern] def bvBitOfNum : ℕ := forallNum + 1
@[pattern] def bvEqNum : ℕ := bvBitOfNum + 1
@[pattern] def bvNotNum : ℕ := bvEqNum + 1
@[pattern] def bvAndNum : ℕ := bvNotNum + 1
@[pattern] def bvOrNum : ℕ := bvAndNum + 1
@[pattern] def bbTNum : ℕ := bvOrNum + 1

def boolNum  : ℕ := 0
def intNum : ℕ := boolNum + 1
end

namespace sort

def sortToString : sort → string
| dep := "dep"
| (atom n) :=
  match n with
  | 0 := "bool"
  | 1 := "int"
  | _ := repr n
  end
| (arrow s1 s2) :=
  "(" ++ (sortToString s1) ++ " → " ++ (sortToString s2) ++ ")"
| (bv n) := "bv " ++ (repr n)

def optionSortToString : option sort → string
| (some x) := sortToString x
| none := "none"

meta instance: has_repr sort := ⟨sortToString⟩

/- mkArrowN curries multi-argument types
   f : X₁ × X₂ × ... into
   f : X₁ → X₂ → ... -/
def mkArrowNAux : sort → list sort → sort
| hd [] := hd
| hd (h::t) := arrow hd (mkArrowNAux h t)

def mkArrowN (l : list (option sort)) : option sort :=
do sortList ← monad.sequence l,
 match sortList with
 | [] := none
 | (h :: t) := mkArrowNAux h t
 end

end sort

@[derive decidable_eq]
inductive value : Type
| bitvec : list bool → value
| integer : ℤ → value

def bvToString : list bool → string
| [] := ""
| (h :: t) := (if h then "1" else "0") ++ bvToString t

--set_option trace.eqn_compiler.elim_match true
def valueToString : value → string
| (value.bitvec l) := bvToString l
| (value.integer i) := repr i

meta instance: has_repr value := ⟨valueToString⟩

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

-- unary, binary and ternary applications
def toUnary (t : term) : term → term := λ t₁: term, t • t₁
def toBinary (t : term) : term → term → term := λ t₁ t₂ : term, t • t₁ • t₂
def toTernary (t : term) : term → term → term → term := λ t₁ t₂ t₃ : term, t • t₁ • t₂ • t₃

-- constant term constructor
def cstr (p : ℕ) (s : sort): term := const p (some s)

-- Sort definitions
@[pattern] def boolsort := sort.atom boolNum
@[pattern] def intsort := sort.atom intNum

-- term definitions
@[pattern] def bIte : term → term → term → term := toTernary $ cstr bIteNum
  (arrow boolsort (arrow boolsort (arrow boolsort boolsort)))
@[pattern] def fIte : term → term → term → term := toTernary $ cstr fIteNum dep
@[pattern] def not : term → term := toUnary $ cstr notNum (arrow boolsort boolsort)
@[pattern] def bot : term := cstr botNum boolsort
@[pattern] def top : term := not bot
@[pattern] def eq      : term → term → term := toBinary $ cstr eqNum dep
@[pattern] def or      : term → term → term := toBinary $ cstr orNum
  (arrow boolsort (arrow boolsort boolsort))
@[pattern] def and     : term → term → term := toBinary $ cstr andNum
  (arrow boolsort (arrow boolsort boolsort))
@[pattern] def implies : term → term → term := toBinary $ cstr impliesNum
  (arrow boolsort (arrow boolsort boolsort))
@[pattern] def xor     : term → term → term := toBinary $ cstr xorNum
  (arrow boolsort (arrow boolsort boolsort))
-- term definitions
-- bv 0 doesn't exist
-- check int is in range
@[pattern] def bitOf : ℕ → term → term → term := λ n, toBinary $ cstr bvBitOfNum
  (arrow (bv n) (arrow intsort boolsort))
@[pattern] def bvNot : ℕ → term → term := λ n, toUnary $ cstr bvNotNum
  (arrow (bv n) (bv n))
@[pattern] def bvEq : ℕ → term → term → term := λ n, toBinary $ cstr bvEqNum
  (arrow (bv n) (arrow (bv n) (boolsort)))
@[pattern] def bvAnd : ℕ → term → term → term := λ n, toBinary $ cstr bvAndNum
  (arrow (bv n) (arrow (bv n) (bv n)))
@[pattern] def bvOr : ℕ → term → term → term := λ n, toBinary $ cstr bvOrNum
  (arrow (bv n) (arrow (bv n) (bv n)))
@[pattern] def bbT (n : ℕ) := const bbTNum
  (mkArrowN (list.append (list.repeat (some boolsort) n) [bv n]))

def natToString : ℕ → string
| botNum := "⊥"
| notNum := "¬"
| orNum := "∨"
| andNum := "∧"
| impliesNum := "⇒"
| xorNum := "⊕"
| bIteNum := "bIte"
| fIteNum := "fIte"
| eqNum := "≃"
| forallNum := "∀"
| bvBitOfNum := "[ ]"
| bvEqNum := "≃bv"
| bvNotNum := "¬bv"
| bvAndNum := "∧bv"
| bvOrNum := "∨bv"
| x := repr x

def termToString : term → string
| (val (value.bitvec l) _) := bvToString l
| (val (value.integer i) _) := repr i
| ((const orNum _) • t1 • t2) := termToString t1 ++ " ∨ " ++ termToString t2
| ((const andNum _) • t1 • t2) := termToString t1 ++ " ∧ " ++ termToString t2
| ((const impliesNum _) • t1 • t2) := termToString t1 ++ " ⇒ " ++ termToString t2
| ((const xorNum _) • t1 • t2) := termToString t1 ++ " ⊕ " ++ termToString t2
| ((const eqNum _) • t1 • t2) := termToString t1 ++ " ≃ " ++ termToString t2
| ((const bvBitOfNum _) • t1 • t2) := termToString t1 ++ "[" ++ termToString t2 ++ "]"
| ((const bvEqNum _) • t1 • t2) := termToString t1 ++ " ≃bv " ++ termToString t2
| ((const bvOrNum _) • t1 • t2) := termToString t1 ++ " ∨bv " ++ termToString t2
| ((const bvAndNum _) • t1 • t2) := termToString t1 ++ " ∧bv " ++ termToString t2
| (const name _) := natToString name
| (app (const notNum _) t) := "¬ " ++ termToString t
| (app (const bvNotNum _) t) := "¬bv " ++ termToString t
| (app f t) := "(" ++ (termToString f) ++ " " ++ (termToString t) ++ ")"
| (qforall p t) := "∀ " ++ repr p ++ " . " ++ termToString t

def sortedTermToString : term → string
| (val (value.bitvec l) none) := (bvToString l) ++ ":none"
| (val (value.bitvec l) (some srt)) := (bvToString l) ++ sortToString srt
| (val (value.integer i) none) := (repr i) ++ ":none"
| (val (value.integer i) (some srt)) := (repr i) ++ sortToString srt
| (const name none) := "(" ++ natToString name ++ ":none)"
| (const name (some srt)) :=  natToString name ++ ":" ++ sortToString srt
| (app f t) :=
  "(" ++ (sortedTermToString f) ++ " " ++ (sortedTermToString t) ++ ")"
| (qforall p t) := "∀ " ++ repr p ++ " . " ++ sortedTermToString t

meta instance: has_repr term := ⟨termToString⟩

-- sort of terms
def sortOfAux : term → option sort
| (val (value.bitvec l) _) := if ((list.length l) = 0) then
                                none
                              else
                                bv (list.length l)
| (val (value.integer i) _) := intsort
| (const botNum _) := boolsort
| (const notNum _) := (arrow boolsort boolsort)
| (const orNum  _) := (arrow boolsort (arrow boolsort boolsort))
| (const andNum _)  := (arrow boolsort (arrow boolsort boolsort))
| (const impliesNum _)  := (arrow boolsort (arrow boolsort boolsort))
| (const xorNum _)  := (arrow boolsort (arrow boolsort boolsort))
| (const _ s)      := s
| (bitOf n t₁ t₂) :=
  do s₁ ← sortOfAux t₁, s₂ ← sortOfAux t₂,
    if s₁ = (bv n) ∧ s₂ = intsort then
      boolsort
    else none
| (bvEq n t₁ t₂) :=
  do s₁ ← sortOfAux t₁, s₂ ← sortOfAux t₂,
    if s₁ = (bv n) ∧ s₂ = (bv n) then
      boolsort
    else none
| (bvAnd n t₁ t₂) :=
  do s₁ ← sortOfAux t₁, s₂ ← sortOfAux t₂,
    if s₁ = (bv n) ∧ s₂ = (bv n) then
      boolsort
    else none
| (bvOr n t₁ t₂) :=
  do s₁ ← sortOfAux t₁, s₂ ← sortOfAux t₂,
    if s₁ = (bv n) ∧ s₂ = (bv n) then
      boolsort
    else none
| (qforall p₁ t₁)  :=
  do s₁ ← sortOfAux t₁,
    if s₁ = boolsort then boolsort else none
| (eq t₁ t₂) :=
  do s₁ ← sortOfAux t₁, s₂ ← sortOfAux t₂,
    if s₁ = s₂ then boolsort else none
| (fIte t₁ t₂ t₃) :=
    do s₁ ← sortOfAux t₁, s₂ ← sortOfAux t₂, s₃ ← sortOfAux t₂,
        if s₁ = boolsort ∧ s₂ = s₃ then s₂ else none
| (f • t)  :=
  do sf ← sortOfAux f, s ← sortOfAux t,
    match sf with
    | (arrow s1 s2) := if s1 = s then s2 else none
    | _ := none
    end
/- bind : (m : option term) → (f : (term → option sort))
   unpacks the term from m and applies f to it.
   Here, we have f first and expect sortOf to take m as
   the argument so we use flip to reverse the argument
   order -/
def sortOf : option term → option sort :=
 (flip option.bind) sortOfAux

-- application of term to term
def mkAppAux : term → term → option term :=
  λ t₁ t₂,
    do s₁ ← sortOf t₁, s₂ ← sortOf t₂,
      match s₁ with
      | (arrow srt _) := if srt = s₂ then some (app t₁ t₂) else none
      | _ := none
      end

/- bind : (x : m α) → (f : (α → m α))
   unpacks the term from the monad x and applies
   f to it. bind2 and bind3 are versions of bind where
   f is binary and ternary respectively, with the
   arguments reordered, as in sortOf -/
def bind2 {m : Type → Type} [has_bind m] {α β γ : Type}
  (f : α → β → m γ) (a : m α) (b : m β) : m γ :=
    do a' ← a, b' ← b, f a' b'
def bind3 {m : Type → Type} [has_bind m] {α β γ δ : Type}
  (f : α → β → γ → m δ) (a : m α) (b : m β) (c : m γ) : m δ :=
    do a' ← a, b' ← b, c' ← c, f a' b' c'

-- binary and n-ary application
def mkApp : option term → option term → option term := bind2 mkAppAux
def mkAppN (t : option term) (l : list (option term)) : option term :=
  do s ← t, l' ← monad.sequence l, mfoldl mkAppAux s l'


-- if-then-else
def mkIteAux (c t₀ t₁ : term) : option term :=
  if (sortOf c) = some boolsort
  then
    do s₀ ← sortOf t₀, s₁ ← sortOf t₁,
      match (s₀,s₁) with
      | (boolsort, boolsort) := some $ bIte c t₀ t₁
      | (_,_) :=  if s₀ = s₁ then fIte c t₀ t₁ else none
      end
  else none

def mkIte : option term → option term → option term → option term :=
  bind3 mkIteAux

-- negation
def mkNot : option term → option term :=
  flip option.bind $
    λ t, do s ← sortOf t, if s = boolsort then not t else none

def mkNotSimp : option term → option term
| (some (not s')) := some s'
| (some t)        := mkNot (some t)
| _                      := none

/- term constructors for binary and n-ary terms. `test` is the predicate on the sort of
   the arguments that needs to be satisfied -/
def constructBinaryTerm (constructor : term → term → term) (test : sort → sort → bool) :
  option term → option term → option term :=
  bind2 $ λ t₁ t₂,
            do s₁ ← sortOf t₁, s₂ ← sortOf t₂,
                if test s₁ s₂ then constructor t₁ t₂ else none

def constructNaryTerm (constructor : term → term → term) (test : sort → sort → bool) :
  option term → list (option term) → option term :=
  λ ot₁ ots₂,
  let auxfxn : term → term → option term := (λ t₁ t₂,
            do s₁ ← sortOf t₁, s₂ ← sortOf t₂,
                if test s₁ s₂ then constructor t₁ t₂ else none)
    in (do t₁ ← ot₁, ts₂ ← monad.sequence ots₂, mfoldl auxfxn t₁ ts₂)


def comp2 {α β γ δ : Type} (f : γ → δ) (g : α → β → γ) : α → β → δ :=
λ a b, f (g a b)


-- Boolean ops
@[simp] def mkEq : option term → option term → option term :=
  constructBinaryTerm eq (λ s₁ s₂, s₁ = s₂)

def mkUneq : option term → option term → option term :=
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
  λ ol, mkAndN $ list.map (function.uncurry mkUneq) (genAllPairs ol)

def mkForall (p : ℕ) (obody : option term) : option term :=
  do body ← obody, (qforall p body)

-- retrieve the identifier of a constant
def numOf : term → option ℕ
| (const n _) := n
| _ := none

end term

end proof
