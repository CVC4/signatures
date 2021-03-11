-- import Std.Data

open List

namespace proof

/- dep is the sort for terms that have polymorphic sorts such as
   equality and ITE. These sorts are handled in a special way in the
   type checker.

   Additionally, we have atomic sorts, parameterized by a nat, arrow
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
   nat, an application of terms is parametrized
   by all the nats involved in the application,
   thus giving unique sets of nats to unique terms -/
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
def bvEqNum : Nat := bvBitOfNum + 1
def bvNotNum : Nat := bvEqNum + 1
def bvAndNum : Nat := bvNotNum + 1
def bvOrNum : Nat := bvAndNum + 1

def boolNum : Nat := 1
def intNum : Nat := boolNum + 1

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
  | _ => mkArrowN t >>= fun x => arrow s x
| _ => none

end sort

inductive value : Type where
| bitvec : List Bool → value
| integer : Int → value
deriving DecidableEq

def bvToString : List Bool → String
| [] => ""
| h :: t => (if h then "1" else "0") ++ bvToString t

--set_option trace.eqn_compiler.elim_match true
def valueToString : value → String
| value.bitvec l => bvToString l
| value.integer i => toString i

instance: ToString value where toString := valueToString

/- terms are values (nullary constants),
   constants of a sort, applications,
   or quantified formulas
   Quantified variables are also
   parameterized by a nat -/
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
def wildcardSort := atom 0
def boolSort := atom boolNum
def intSort := atom intNum

-- Interpreted constants
def botConst := const botNum boolSort
def notConst := const notNum (arrow boolSort boolSort)
def orConst := const orNum (arrow boolSort (arrow boolSort boolSort))
def andConst := const andNum (arrow boolSort (arrow boolSort boolSort))
def impliesConst := const impliesNum (arrow boolSort (arrow boolSort boolSort))
def xorConst := const xorNum (arrow boolSort (arrow boolSort boolSort))

def eqConst := const eqNum dep
def fIteConst := const fIteNum dep

def bitOfConst (n : Nat) :=
  const bvBitOfNum (arrow (bv n) (arrow intSort boolSort))
def bvEqConst (n : Nat) :=
  const bvEqNum (arrow (bv n) (arrow (bv n) boolSort))

-- macros for creating terms with interpreted constants
@[matchPattern] def not : term → term := fun t => notConst • t
@[matchPattern] def top : term := not botConst
@[matchPattern] def or : term → term → term := fun t₁ t₂ => orConst • t₁ • t₂
@[matchPattern] def and : term → term → term := fun t₁ t₂ => andConst • t₁ • t₂
@[matchPattern] def implies : term → term → term :=
  fun t₁ t₂ => impliesConst • t₁ • t₂
@[matchPattern] def xor : term → term → term := fun t₁ t₂ => xorConst • t₁ • t₂

@[matchPattern] def fIte : term → term → term → term :=
  fun t₁ t₂ t₃ => fIteConst • t₁ • t₂ • t₃
@[matchPattern] def eq : term → term → term := fun t₁ t₂ => eqConst • t₁ • t₂

@[matchPattern] def bitOf : Nat → term → term → term :=
  fun n t₁ t₂ => bitOfConst n • t₁ • t₂
@[matchPattern] def bvEq : Nat → term → term → term :=
  fun n t₁ t₂ => bvEqConst n • t₁ • t₂

-- computing the sort of terms
def sortOfAux : term → Option sort
| val (integer i) _ => intSort
| val (bitvec l) _ =>
    do let len ← List.length l if len = 0 then none else bv len
| eq t₁ t₂ =>
    sortOfAux t₁ >>= fun s₁ =>
    sortOfAux t₂ >>= fun s₂ =>
    if s₁ = s₂ then boolSort else none
| fIte c t₁ t₂ =>
    sortOfAux c >>= fun s₁ =>
    sortOfAux t₁ >>= fun s₂ =>
    sortOfAux t₂ >>= fun s₃ =>
    if s₁ = boolSort ∧ s₂ = s₃ then s₂ else none
| f • t =>
    sortOfAux f >>= fun sf =>
    sortOfAux t >>= fun st =>
    match sf with
    | arrow st s => s
    | _ => none
| qforall v t =>
    sortOfAux t >>= fun st => if st = boolSort then st else none
-- parametric operators are by default well-solted, with a special default type
| const _ dep => wildcardSort
| const _ s => s

def sortOf (t : Option term) : Option sort := t >>= fun t' => sortOfAux t'

/- bind : (x : m α) → (f : (α → m α))
   unpacks the term from the monad x and applies
   f to it. bind2 and bind3 are versions of bind where
   f is binary and ternary respectively, with the
   arguments reordered. -/
def bind2 {m : Type → Type} [Monad m] {α β γ : Type}
  (f : α → β → m γ) (a : m α) (b : m β) : m γ :=
    a >>= fun a' => b >>= fun b' => f a' b'

def bind3 {m : Type → Type} [Monad m] {α β γ δ : Type}
  (f : α → β → γ → m δ) (a : m α) (b : m β) (c : m γ) : m δ :=
    a >>= fun a' => b >>= fun b' => c >>= fun c' => f a' b' c'

-- application of term to term
def mkAppAux : term → term → Option term :=
  fun t₁ t₂ =>
    sortOf t₁ >>= fun s₁ =>
    sortOf t₂ >>= fun s₂ =>
    match s₁ with
    | arrow s₂ _ => t₁ • t₂
    | _ => none

-- binary and n-ary application
def mkApp : Option term → Option term → Option term := bind2 mkAppAux

end term

end proof
