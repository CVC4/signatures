open List

namespace proof

/- dep is the sort for terms that have polymorphic sorts such as
   equality and ITE. These sorts are handled in a special way in the
   type checker.

   Additionally, we have atomic sorts, parameterized by a Nat, arrow
   for functional sorts, and bitvector sorts parameterized by their
   length -/
inductive sort : Type where
| dep : sort
| atom : Nat → sort
| arrow : sort → sort → sort
| bv : Nat → sort
deriving DecidableEq

namespace sort

/- Each predefined function is also parameterized by a
   Nat, an application of terms is parametrized
   by all the Nats involved in the application,
   thus giving unique sets of Nats to unique terms -/
def botNum     : Nat := 0
def notNum     : Nat := botNum + 1
def orNum      : Nat := notNum + 1
def andNum     : Nat := orNum + 1
def impliesNum : Nat := andNum + 1
def xorNum     : Nat := impliesNum + 1
def bIteNum   : Nat := xorNum + 1
def fIteNum   : Nat := bIteNum + 1
def eqNum      : Nat := fIteNum + 1
def forallNum  : Nat := eqNum + 1
def bvBitOfNum : Nat := forallNum + 1
def bvBbTNum : Nat := bvBitOfNum + 1
def bvEqNum : Nat := bvBbTNum + 1
def bvNotNum : Nat := bvEqNum + 1
def bvAndNum : Nat := bvNotNum + 1
def bvOrNum : Nat := bvAndNum + 1
def bvUltNum : Nat := bvOrNum + 1
def bvUgtNum : Nat := bvUltNum + 1
def bvSltNum : Nat := bvUgtNum + 1
def bvSgtNum : Nat := bvSltNum + 1
def bvAddNum : Nat := bvSgtNum + 1
def plusNum : Nat := bvAddNum + 1
def minusNum : Nat := plusNum + 1
def multNum : Nat := minusNum + 1
def gtNum : Nat := multNum + 1
def gteNum : Nat := gtNum + 1
def ltNum : Nat := gteNum + 1
def lteNum : Nat := ltNum + 1
def boolNum : Nat := 1
def intNum : Nat := boolNum + 1
def strNum : Nat := intNum + 1

def sortToString : sort → String
| dep => "blah"
| atom n => toString n
| arrow s1 s2 => "(" ++ sortToString s1 ++ " → " ++ sortToString s2 ++ ")"
| bv n => "bv " ++ toString n

instance : ToString sort where toString := sortToString

/- mkArrowN curries multi-argument types
   f : X₁ × X₂ × ... into
   f : X₁ → X₂ → ... -/
def mkArrowN : List (Option sort) → Option sort
| some s::t =>
  match t with
  | [] => s
  | _ => mkArrowN t >>= λ x => arrow s x
| _ => none

end sort

inductive value : Type where
| bool : Bool → value
| bitvec : List Bool → value
| char : Nat → value
| integer : Int → value
deriving DecidableEq

def bvToString : List Bool → String
| [] => ""
| h :: t => (if h then "1" else "0") ++ bvToString t

def valueToString : value → String
| value.bool true => "⊥"
| value.bool false => "⊤"
| value.bitvec l => bvToString l
| value.char c => toString $ Char.ofNat c
| value.integer i => toString i

instance: ToString value where toString := valueToString

/- terms are values (interpreted constants),
   constants of a sort, applications,
   or quantified formulas
   Quantified variables are also
   parameterized by a Nat -/
inductive term : Type where
| val : value → Option sort → term
| const : Nat → Option sort → term
| app : term → term → term
| qforall : Nat → term → term
deriving DecidableEq

namespace term

infixl:20  " • " => app

open sort
open value

-- Sort definitions
@[matchPattern] def boolSort := atom boolNum
@[matchPattern] def intSort := atom intNum
@[matchPattern] def stringSort := atom strNum

-- Interpreted constants
@[matchPattern] def botConst := const botNum boolSort
@[matchPattern] def notConst := const notNum (arrow boolSort boolSort)
@[matchPattern] def orConst :=
  const orNum (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def andConst :=
  const andNum (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def impliesConst :=
  const impliesNum (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def xorConst :=
  const xorNum (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def bIteConst :=
  const bIteNum (arrow boolSort (arrow boolSort (arrow boolSort boolSort)))

@[matchPattern] def eqConst := const eqNum dep
@[matchPattern] def fIteConst := const fIteNum dep

@[matchPattern] def plusConst :=
  const plusNum (arrow intSort (arrow intSort intSort))
@[matchPattern] def minusConst :=
  const minusNum (arrow intSort (arrow intSort intSort))
@[matchPattern] def multConst :=
  const multNum (arrow intSort (arrow intSort intSort))
@[matchPattern] def gtConst :=
  const gtNum (arrow intSort (arrow intSort boolSort))
@[matchPattern] def gteConst :=
  const gteNum (arrow intSort (arrow intSort boolSort))
@[matchPattern] def ltConst :=
  const ltNum (arrow intSort (arrow intSort boolSort))
@[matchPattern] def lteConst :=
  const lteNum (arrow intSort (arrow intSort boolSort))

@[matchPattern] def bitOfConst (n : Nat) :=
  const bvBitOfNum (arrow (bv n) (arrow intSort boolSort))
@[matchPattern] def bbTConst (n : Nat) :=
  const bvBbTNum (mkArrowN (List.append (List.replicate n (some boolSort)) [bv n]))
@[matchPattern] def bvEqConst (n : Nat) :=
  const bvEqNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvNotConst (n : Nat) :=
  const bvNotNum (arrow (bv n) (bv n))
@[matchPattern] def bvAndConst (n : Nat) :=
  const bvAndNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvOrConst (n : Nat) :=
  const bvOrNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvUltConst (n : Nat) :=
  const bvUltNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvUgtConst (n : Nat) :=
  const bvUgtNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvSltConst (n : Nat) :=
  const bvSltNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvSgtConst (n : Nat) :=
  const bvSgtNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvAddConst (n : Nat) :=
  const bvAddNum (arrow (bv n) (arrow (bv n) (bv n)))

-- macros for creating terms with interpreted constants
@[matchPattern] def bot : term := val (bool false) boolSort
@[matchPattern] def top : term := val (bool true) boolSort
@[matchPattern] def not : term → term := λ t => notConst • t
@[matchPattern] def or : term → term → term := λ t₁ t₂ => orConst • t₁ • t₂
@[matchPattern] def and : term → term → term := λ t₁ t₂ => andConst • t₁ • t₂
@[matchPattern] def implies : term → term → term :=
  λ t₁ t₂ => impliesConst • t₁ • t₂
@[matchPattern] def xor : term → term → term := λ t₁ t₂ => xorConst • t₁ • t₂
@[matchPattern] def bIte : term → term → term → term :=
  λ c t₁ t₂ => bIteConst • c • t₁ • t₂

@[matchPattern] def plus : term → term → term := λ t₁ t₂ => plusConst • t₁ • t₂
@[matchPattern] def minus : term → term → term :=
  λ t₁ t₂ => minusConst • t₁ • t₂
@[matchPattern] def mult : term → term → term := λ t₁ t₂ => multConst • t₁ • t₂
@[matchPattern] def gt : term → term → term := λ t₁ t₂ => gtConst • t₁ • t₂
@[matchPattern] def gte : term → term → term := λ t₁ t₂ => gteConst • t₁ • t₂
@[matchPattern] def lt : term → term → term := λ t₁ t₂ => ltConst • t₁ • t₂
@[matchPattern] def lte : term → term → term := λ t₁ t₂ => lteConst • t₁ • t₂

@[matchPattern] def fIte : term → term → term → term :=
  λ t₁ t₂ t₃ => fIteConst • t₁ • t₂ • t₃
@[matchPattern] def eq : term → term → term := λ t₁ t₂ => eqConst • t₁ • t₂

@[matchPattern] def bitOf : Nat → term → term → term :=
  λ n t₁ t₂ => bitOfConst n • t₁ • t₂
@[matchPattern] def bbT : Nat → term := λ n => bbTConst n
@[matchPattern] def bvEq : Nat → term → term → term :=
  λ n t₁ t₂ => bvEqConst n • t₁ • t₂
@[matchPattern] def bvNot : Nat → term → term :=
  λ n t => bvNotConst n • t
@[matchPattern] def bvAnd : Nat → term → term → term :=
  λ n t₁ t₂ => bvAndConst n • t₁ • t₂
@[matchPattern] def bvOr : Nat → term → term → term :=
  λ n t₁ t₂ => bvAndConst n • t₁ • t₂
@[matchPattern] def bvUlt : Nat → term → term → term :=
  λ n t₁ t₂ => bvUltConst n • t₁ • t₂
@[matchPattern] def bvUgt : Nat → term → term → term :=
  λ n t₁ t₂ => bvUgtConst n • t₁ • t₂
@[matchPattern] def bvSlt : Nat → term → term → term :=
  λ n t₁ t₂ => bvSltConst n • t₁ • t₂
@[matchPattern] def bvSgt : Nat → term → term → term :=
  λ n t₁ t₂ => bvSgtConst n • t₁ • t₂
@[matchPattern] def bvAdd : Nat → term → term → term :=
  λ n t₁ t₂ => bvAddConst n • t₁ • t₂

def termToString : term → String
| val v s => valueToString v
| not t => "¬" ++ termToString t
| or t₁ t₂ => termToString t₁ ++ " ∨ " ++ termToString t₂
| and t₁ t₂ => termToString t₁ ++ " ∧ " ++ termToString t₂
| xor t₁ t₂ => termToString t₁ ++ " ⊕ " ++ termToString t₂
| implies t₁ t₂ => termToString t₁ ++ " ⇒ " ++ termToString t₂
| bIte c t₁ t₂ =>
  termToString c ++ " ? " ++ termToString t₁ ++ " : " ++ termToString t₂
| eq t₁ t₂ => termToString t₁ ++ " ≃ " ++ termToString t₂
| fIte c t₁ t₂ =>
  termToString c ++ " ? " ++ termToString t₁ ++ " : " ++ termToString t₂
| plus t₁ t₂ => termToString t₁ ++ " + " ++ termToString t₂
| minus t₁ t₂ => termToString t₁ ++ " - " ++ termToString t₂
| mult t₁ t₂ => termToString t₁ ++ " * " ++ termToString t₂
| gt t₁ t₂ => termToString t₁ ++ " > " ++ termToString t₂
| gte t₁ t₂ => termToString t₁ ++ " ≥ " ++ termToString t₂
| lt t₁ t₂ => termToString t₁ ++ " < " ++ termToString t₂
| lte t₁ t₂ => termToString t₁ ++ " ≤ " ++ termToString t₂
| bitOf _ t₁ t₂ => termToString t₁ ++ "[" ++ termToString t₂ ++ "]"
/-| bbT _ => "bbT"
| bvEq _ t₁ t₂ => termToString t₁ ++ " ≃_bv " ++ termToString t₂
| bvNot _ t => "¬_bv" ++ termToString t
| bvAnd _ t₁ t₂ => termToString t₁ ++ " ∧_bv " ++ termToString t₂
| bvOr _ t₁ t₂ => termToString t₁ ++ " ∨_bv " ++ termToString t₂
| bvUlt _ t₁ t₂ => termToString t₁ ++ " <ᵤ " ++ termToString t₂
| bvUgt _ t₁ t₂ => termToString t₁ ++ " >ᵤ " ++ termToString t₂
| bvSlt _ t₁ t₂ => termToString t₁ ++ " <ₛ " ++ termToString t₂
| bvSgt _ t₁ t₂ => termToString t₁ ++ " >ₛ " ++ termToString t₂
| bvAdd _ t₁ t₂ => termToString t₁ ++ " +_bv " ++ termToString t₂-/
| const id _ => toString id
| f • t =>  "(" ++ (termToString f) ++ " " ++ (termToString t) ++ ")"
| qforall v t => "∀ " ++ toString v ++ " . " ++ termToString t

instance : ToString term where toString := termToString

-- computing the sort of terms
def sortOfAux : term → Option sort
| val (value.bool _) _ => boolSort
| val (bitvec l) _ =>
    do let len ← List.length l if len = 0 then none else bv len
| val (value.char _) _ => stringSort
| val (integer _) _ => intSort
| eq t₁ t₂ =>
    sortOfAux t₁ >>= λ s₁ =>
    sortOfAux t₂ >>= λ s₂ =>
    if s₁ = s₂ then boolSort else none
| fIte c t₁ t₂ =>
    sortOfAux c >>= λ s₁ =>
    sortOfAux t₁ >>= λ s₂ =>
    sortOfAux t₂ >>= λ s₃ =>
    if s₁ = boolSort ∧ s₂ = s₃ then s₂ else none
| f • t =>
    sortOfAux f >>= λ sf =>
    sortOfAux t >>= λ st =>
    match sf with
    | arrow st s => s
    | _ => none
| qforall v t =>
    sortOfAux t >>= λ st => if st = boolSort then st else none
| const _ s => s

def sortOf (t : Option term) : Option sort := t >>= λ t' => sortOfAux t'

/- bind : (x : m α) → (f : (α → m α))
   unpacks the term from the monad x and applies
   f to it. bind2 and bind3 are versions of bind where
   f is binary and ternary respectively, with the
   arguments reordered. -/
def bind2 {m : Type → Type} [Monad m] {α β γ : Type}
  (f : α → β → m γ) (a : m α) (b : m β) : m γ :=
    a >>= λ a' => b >>= λ b' => f a' b'

def bind3 {m : Type → Type} [Monad m] {α β γ δ : Type}
  (f : α → β → γ → m δ) (a : m α) (b : m β) (c : m γ) : m δ :=
    a >>= λ a' => b >>= λ b' => c >>= λ c' => f a' b' c'

/-  return : α → m α
    (return x) puts x in a monad box -/
/- Similar to above, but for unpacking a list -/
def bindN {m : Type u → Type v} [Monad m] {α : Type u}
  : List (m α) → m (List α)
| [] => return []
| h :: t => h >>= λ h' => bindN t >>= λ t' => return h' :: t'

/- term constructors for binary and n-ary terms. `test` is the
   predicate on the sort of the arguments that needs to be satisfied -/
def constructBinaryTerm (constructor : term → term → term)
  (test : sort → sort → Bool) : Option term → Option term → Option term :=
  bind2 $ λ t₁ t₂ => sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
          if test s₁ s₂ then constructor t₁ t₂ else none

def constructNaryTerm (constructor : term → term → term)
  (test : sort → sort → Bool) (l : List (Option term)) : Option term :=
      bindN l >>= λ l' =>
      match l' with
      | h₁ :: h₂ :: t =>
        List.foldlM (λ t₁ t₂ : term =>
           sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
             if test s₁ s₂ then constructor t₁ t₂ else none) h₁ (h₂ :: t)
      | _ => none

-- application of term to term
def mkAppAux : term → term → Option term :=
  λ t₁ t₂ =>
    sortOf t₁ >>= λ s₁ =>
    sortOf t₂ >>= λ s₂ =>
    match s₁ with
    | arrow s₂ _ => t₁ • t₂
    | _ => none

-- binary and n-ary application
def mkApp : Option term → Option term → Option term := bind2 mkAppAux

def mkAppN (t : Option term) (l : List (Option term)) : Option term :=
  t >>= λ t' => bindN l >>= λ l' => List.foldlM mkAppAux t' l'

-- equality
def mkEq : Option term → Option term → Option term :=
  constructBinaryTerm eq (λ s₁ s₂ => s₁ = s₂)

-- if-then-else
def mkIteAux (c t₁ t₂ : term) : Option term :=
  match sortOf c with
  | some boolSort => match sortOf t₁, sortOf t₂ with
                     | some boolSort, some boolSort => bIte c t₁ t₂
                     | some s₁, some s₂ => if s₁ = s₂ then fIte c t₁ t₂ else none
                     | _, _ => none
  | _ => none

def mkIte : Option term → Option term → Option term → Option term :=
  bind3 mkIteAux

-- negation
def mkNot (t : Option term) : Option term :=
  t >>= λ t' => match sortOf t' with
                  | some boolSort => not t'
                  | _ => none

-- Boolean ops
def mkOr : Option term → Option term → Option term :=
  constructBinaryTerm or (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkOrN : List (Option term) → Option term :=
    constructNaryTerm or (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkAnd : Option term → Option term → Option term :=
  constructBinaryTerm and (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkAndN : List (Option term) → Option term :=
  constructNaryTerm and (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkImplies : Option term → Option term → Option term :=
  constructBinaryTerm implies (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkXor : Option term → Option term → Option term :=
  constructBinaryTerm xor (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkForall (v : Nat) (body : Option term) : Option term :=
  body >>= λ body' => (qforall v body')

end term

end proof
