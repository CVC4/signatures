-- import Std.Data

open List

namespace proof

/- dep is the sort for terms that have polymorphic sorts such as
   equality and ITE. These sorts are handled in a special way in the
   type checker.

   Additionally, we have atomic sorts, parameterized by a nat, arrow
   for functional sorts, and bitvector sorts parameterized by their
   length -/
inductive sort  : Type where
| dep : sort
| atom : Nat → sort
| arrow : sort → sort → sort
| bv : Nat → sort

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

def boolNum  : Nat := 0
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

namespace term

infixl:20  " • " => app

open sort
open value

-- Sort definitions
def boolSort := sort.atom boolNum
def intSort := sort.atom intNum

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
def not : term → term := fun t => notConst • t
def top : term := not botConst
def or : term → term → term := fun t₁ t₂ => orConst • t₁ • t₂
def and : term → term → term := fun t₁ t₂ => andConst • t₁ • t₂
def implies : term → term → term := fun t₁ t₂ => impliesConst • t₁ • t₂
def xor : term → term → term := fun t₁ t₂ => xorConst • t₁ • t₂

def fIte : term → term → term → term := fun t₁ t₂ t₃ => fIteConst • t₁ • t₂ • t₃
def eq : term → term → term := fun t₁ t₂ => eqConst • t₁ • t₂

def bitOf : Nat → term → term → term := fun n t₁ t₂ => bitOfConst n • t₁ • t₂
def bvEq : Nat → term → term → term := fun n t₁ t₂ => bvEqConst n • t₁ • t₂

-- computing the sort of terms
def sortOfAux : term → Option sort
| val (integer i) _ => intSort
| val (bitvec l) _ =>
  do
  let len ← List.length l
  if len = 0 then none else bv len
| _ => boolSort

end term

end proof
