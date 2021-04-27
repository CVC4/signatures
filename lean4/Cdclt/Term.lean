import Lean

instance [DecidableEq α] : DecidableEq (OptionM α) :=
  instDecidableEqOption

instance [ToString α] : ToString (OptionM α) :=
  instToStringOption

instance [Lean.Eval α] [ToString α] : Lean.Eval (OptionM α) :=
  Lean.instEval

instance [Lean.MetaEval α] [ToString α] : Lean.MetaEval (OptionM α) :=
  Lean.instMetaEval


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
def bvXorNum : Nat := bvOrNum + 1
def bvNandNum : Nat := bvXorNum + 1
def bvNorNum : Nat := bvNandNum + 1
def bvXnorNum : Nat := bvNorNum + 1
def bvCompNum : Nat := bvXnorNum + 1
def bvUltNum : Nat := bvCompNum + 1
def bvUleNum : Nat := bvUltNum + 1
def bvUgtNum : Nat := bvUleNum + 1
def bvUgeNum : Nat := bvUgtNum + 1
def bvSltNum : Nat := bvUgeNum + 1
def bvSleNum : Nat := bvSltNum + 1
def bvSgtNum : Nat := bvSleNum + 1
def bvSgeNum : Nat := bvSgtNum + 1
def bvAddNum : Nat := bvSgeNum + 1
def bvNegNum : Nat := bvAddNum + 1
def bvSubNum : Nat := bvNegNum + 1
def bvMulNum : Nat := bvSubNum + 1
def bvUDivNum : Nat := bvMulNum + 1
def bvURemNum : Nat := bvUDivNum + 1
def bvShlNum : Nat := bvURemNum + 1
def bvLShrNum : Nat := bvShlNum + 1
def bvAShrNum : Nat := bvLShrNum + 1
def bvExtractNum : Nat := bvAShrNum + 1
def bvConcatNum : Nat := bvExtractNum + 1
def bvZeroExtNum : Nat := bvConcatNum + 1
def bvSignExtNum : Nat := bvZeroExtNum + 1
def bvRepeatNum : Nat := bvSignExtNum + 1
def plusNum : Nat := bvRepeatNum + 1
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
def mkArrowN : List (OptionM sort) → OptionM sort
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
| value.bool true => "⊤"
| value.bool false => "⊥"
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
| val : value → OptionM sort → term
| const : Nat → OptionM sort → term
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
@[matchPattern] def bvXorConst (n : Nat) :=
  const bvXorNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvNandConst (n : Nat) :=
  const bvNandNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvNorConst (n : Nat) :=
  const bvNorNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvXnorConst (n : Nat) :=
  const bvXnorNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvCompConst (n : Nat) :=
  const bvCompNum (arrow (bv n) (arrow (bv n) (bv 1)))
@[matchPattern] def bvUltConst (n : Nat) :=
  const bvUltNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvUleConst (n : Nat) :=
  const bvUleNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvUgtConst (n : Nat) :=
  const bvUgtNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvUgeConst (n : Nat) :=
  const bvUgeNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvSltConst (n : Nat) :=
  const bvSltNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvSleConst (n : Nat) :=
  const bvSleNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvSgtConst (n : Nat) :=
  const bvSgtNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvSgeConst (n : Nat) :=
  const bvSgeNum (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvAddConst (n : Nat) :=
  const bvAddNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvNegConst (n : Nat) :=
  const bvNegNum (arrow (bv n) (bv n))
@[matchPattern] def bvSubConst (n : Nat) :=
  const bvSubNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvMulConst (n : Nat) :=
  const bvMulNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvShlConst (n : Nat) :=
  const bvShlNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvLShrConst (n : Nat) :=
  const bvLShrNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvAShrConst (n : Nat) :=
  const bvAShrNum (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvExtractConst (n i j : Nat) :=
  const bvExtractNum (arrow (bv n) (arrow intSort (arrow intSort (bv (i - j + 1)))))
@[matchPattern] def bvConcatConst (m n : Nat) :=
  const bvConcatNum (arrow (bv m) (arrow (bv n) (bv (m+n))))
@[matchPattern] def bvZeroExtConst (n i : Nat) :=
  const bvZeroExtNum (arrow (bv n) (arrow intSort (bv (n + i))))
@[matchPattern] def bvSignExtConst (n i : Nat) :=
  const bvSignExtNum (arrow (bv n) (arrow intSort (bv (n + i))))
@[matchPattern] def bvRepeatConst (n i : Nat) :=
  const bvRepeatNum (arrow intSort (arrow (bv n) (bv (n * i))))


-- macros for creating terms with interpreted constants
@[matchPattern] def bot : term := val (bool false) boolSort
@[matchPattern] def top : term := val (bool true) boolSort
@[matchPattern] def not : term → term := λ t => notConst • t
@[matchPattern] def or : term → term → term := λ t₁ t₂ => orConst • t₁ • t₂
@[matchPattern] def and : term → term → term := λ t₁ t₂ => andConst • t₁ • t₂
@[matchPattern] def implies : term → term → term :=
  λ t₁ t₂ => impliesConst • t₁ • t₂
@[matchPattern] def iff : term → term → term :=
  λ t₁ t₂ => andConst • (impliesConst • t₁ • t₂) • (impliesConst • t₂ • t₁)
@[matchPattern] def xor : term → term → term := λ t₁ t₂ => xorConst • t₁ • t₂
@[matchPattern] def nand : term → term → term := λ t₁ t₂ => notConst • (andConst • t₁ • t₂)
@[matchPattern] def nor : term → term → term := λ t₁ t₂ => notConst • (orConst • t₁ • t₂)
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
@[matchPattern] def bvXor : Nat → term → term → term :=
  λ n t₁ t₂ => bvXorConst n • t₁ • t₂
@[matchPattern] def bvNand : Nat → term → term → term :=
  λ n t₁ t₂ => bvNandConst n • t₁ • t₂
@[matchPattern] def bvNor : Nat → term → term → term :=
  λ n t₁ t₂ => bvNorConst n • t₁ • t₂
@[matchPattern] def bvXnor : Nat → term → term → term :=
  λ n t₁ t₂ => bvXnorConst n • t₁ • t₂
@[matchPattern] def bvComp : Nat → term → term → term :=
  λ n t₁ t₂ => bvCompConst n • t₁ • t₂
@[matchPattern] def bvUlt : Nat → term → term → term :=
  λ n t₁ t₂ => bvUltConst n • t₁ • t₂
@[matchPattern] def bvUle : Nat → term → term → term :=
  λ n t₁ t₂ => bvUleConst n • t₁ • t₂
@[matchPattern] def bvUgt : Nat → term → term → term :=
  λ n t₁ t₂ => bvUgtConst n • t₁ • t₂
@[matchPattern] def bvUge : Nat → term → term → term :=
  λ n t₁ t₂ => bvUgeConst n • t₁ • t₂
@[matchPattern] def bvSlt : Nat → term → term → term :=
  λ n t₁ t₂ => bvSltConst n • t₁ • t₂
@[matchPattern] def bvSle : Nat → term → term → term :=
  λ n t₁ t₂ => bvSleConst n • t₁ • t₂
@[matchPattern] def bvSgt : Nat → term → term → term :=
  λ n t₁ t₂ => bvSgtConst n • t₁ • t₂
@[matchPattern] def bvSge : Nat → term → term → term :=
  λ n t₁ t₂ => bvSgeConst n • t₁ • t₂
@[matchPattern] def bvAdd : Nat → term → term → term :=
  λ n t₁ t₂ => bvAddConst n • t₁ • t₂
@[matchPattern] def bvNeg : Nat → term → term :=
  λ n t => bvNegConst n • t
@[matchPattern] def bvSub : Nat → term → term → term :=
  λ n t₁ t₂ => bvSubConst n • t₁ • t₂
@[matchPattern] def bvMul : Nat → term → term → term :=
  λ n t₁ t₂ => bvMulConst n • t₁ • t₂
@[matchPattern] def bvShl : Nat → term → term → term :=
  λ n t₁ t₂ => bvShlConst n • t₁ • t₂
@[matchPattern] def bvLShr : Nat → term → term → term :=
  λ n t₁ t₂ => bvLShrConst n • t₁ • t₂
@[matchPattern] def bvAShr : Nat → term → term → term :=
  λ n t₁ t₂ => bvAShrConst n • t₁ • t₂
@[matchPattern] def bvExtract :
  Nat → Nat → Nat → term → term → term → term :=
  λ n i j t₁ t₂ t₃ => bvExtractConst n i j • t₁ • t₂ • t₃
@[matchPattern] def bvConcat : Nat → Nat → term → term → term :=
  λ n m t₁ t₂ => bvConcatConst n m • t₁ • t₂
@[matchPattern] def bvZeroExt : Nat → Nat → term → term → term :=
  λ n i t₁ t₂ => bvZeroExtConst n i • t₁ • t₂
@[matchPattern] def bvSignExt : Nat → Nat → term → term → term :=
  λ n i t₁ t₂ => bvSignExtConst n i • t₁ • t₂
@[matchPattern] def bvRepeat : Nat → Nat → term → term → term :=
  λ n i t₁ t₂ => bvRepeatConst n i • t₁ • t₂

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
| const 11 _ => "bbT"
/-| bvEq _ t₁ t₂ => termToString t₁ ++ " ≃_bv " ++ termToString t₂
| bvNot _ t => "¬_bv" ++ termToString t
| bvAnd _ t₁ t₂ => termToString t₁ ++ " ∧_bv " ++ termToString t₂
| bvOr _ t₁ t₂ => termToString t₁ ++ " ∨_bv " ++ termToString t₂
| bvXor _ t₁ t₂ => termToString t₁ ++ " ⊕_bv " ++ termToString t₂
| bvNand _ t₁ t₂ => "BVNand " ++ termToString t₁ ++ " " ++ termToString t₂
| bvNor _ t₁ t₂ => "BVNor " ++ termToString t₁ ++ " " ++ termToString t₂
| bvXnor _ t₁ t₂ => "BVXnor " ++ termToString t₁ ++ " " ++ termToString t₂
| bvComp _ t₁ t₂ => "BVComp " ++ termToString t₁ ++ " " ++ termToString t₂
| bvUlt _ t₁ t₂ => termToString t₁ ++ " <ᵤ " ++ termToString t₂
| bvUle _ t₁ t₂ => termToString t₁ ++ " ≤ᵤ " ++ termToString t₂
| bvUgt _ t₁ t₂ => termToString t₁ ++ " >ᵤ " ++ termToString t₂
| bvUge _ t₁ t₂ => termToString t₁ ++ " ≥ᵤ " ++ termToString t₂
| bvSlt _ t₁ t₂ => termToString t₁ ++ " <ₛ " ++ termToString t₂
| bvSle _ t₁ t₂ => termToString t₁ ++ " ≤ₛ " ++ termToString t₂
| bvSgt _ t₁ t₂ => termToString t₁ ++ " >ₛ " ++ termToString t₂
| bvSge _ t₁ t₂ => termToString t₁ ++ " ≥ₛ " ++ termToString t₂
| bvAdd _ t₁ t₂ => termToString t₁ ++ " +_bv " ++ termToString t₂
| bvNeg _ t => "-_bv " ++ termToString t
| bvSub _ t₁ t₂ => termToString t₁ ++ " -_bv " ++ termToString t₂
| bvMul _ t₁ t₂ => termToString t₁ ++ " *_bv " ++ termToString t₂
| bvShl _ t₁ t₂ => termToString t₁ ++ " << " ++ termToString t₂
| bvLShr _ t₁ t₂ => termToString t₁ ++ " >> " ++ termToString t₂
| bvAShr _ t₁ t₂ => termToString t₁ ++ " >>ₐ " ++ termToString t₂-/
/-| bvExtract _ _ _ t₁ t₂ t₃ => ((termToString t₁) ++ "[" ++ (termToString t₂) ++ ":" ++ (termToString t₃) ++ "]")
| bvConcat _ _ t₁ t₂ => termToString t₁ ++ " ++ " ++ termToString t₂
| bvZeroExt _ _ t₁ t₂ => "zeroExt " ++ termToString t₁ ++ " " ++ termToString t₂
| bvSignExt _ _ t₁ t₂ => "signExt " ++ termToString t₁ ++ " " ++ termToString t₂
| bvRepeat _ _ t₁ t₂ => "repeat " ++ termToString t₁ ++ " " ++ termToString t₂-/
| const id _ => toString id
| f • t =>  "(" ++ (termToString f) ++ " " ++ (termToString t) ++ ")"
| qforall v t => "∀ " ++ toString v ++ " . " ++ termToString t

instance : ToString term where toString := termToString

-- computing the sort of terms
def sortOfAux : term → OptionM sort
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
| eqConst • t => sortOfAux t >>= λ s => arrow s boolSort
| f • t =>
    sortOfAux f >>= λ sf =>
    sortOfAux t >>= λ st =>
    match sf with
    | arrow st s => s
    | _ => none
| qforall v t =>
    sortOfAux t >>= λ st => if st = boolSort then st else none
| const _ s => s

-- def sortOf (t : OptionM term) : OptionM sort := t >>= λ t' => sortOfAux t'
def sortOf (t : OptionM term) : OptionM sort := t >>= λ t' => dep

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
  (test : sort → sort → Bool) : OptionM term → OptionM term → OptionM term :=
  bind2 $ λ t₁ t₂ => sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
          -- if test s₁ s₂ then constructor t₁ t₂ else none
          constructor t₁ t₂

def constructNaryTerm (constructor : term → term → term)
  (test : sort → sort → Bool) (l : List (OptionM term)) : OptionM term :=
      bindN l >>= λ l' =>
      match l' with
      | h₁ :: h₂ :: t =>
        List.foldlM (λ t₁ t₂ : term =>
           sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
             -- if test s₁ s₂ then constructor t₁ t₂ else none) h₁ (h₂ :: t)
             constructor t₁ t₂) h₁ (h₂ :: t)
      | _ => none

-- application of term to term
def mkAppAux : term → term → OptionM term :=
  λ t₁ t₂ => t₁ • t₂
    -- sortOf t₁ >>= λ s₁ =>
    -- sortOf t₂ >>= λ s₂ =>
    -- match s₁ with
    -- | arrow s₂ _ => t₁ • t₂
    -- | dep => t₁ • t₂
    -- | _ => none

-- binary and n-ary application
def mkApp : OptionM term → OptionM term → OptionM term := bind2 mkAppAux

def mkAppN (t : OptionM term) (l : List (OptionM term)) : OptionM term :=
  t >>= λ t' => bindN l >>= λ l' => List.foldlM mkAppAux t' l'

-- equality
def mkEq : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm eq (λ s₁ s₂ => s₁ = s₂)

-- if-then-else
def mkIteAux (c t₁ t₂ : term) : OptionM term :=
  match sortOf c with
  | some boolSort => match sortOf t₁, sortOf t₂ with
                     | some boolSort, some boolSort => bIte c t₁ t₂
                     | some s₁, some s₂ => if s₁ = s₂ then fIte c t₁ t₂ else none
                     | _, _ => none
  | _ => none

def mkIte : OptionM term → OptionM term → OptionM term → OptionM term :=
  bind3 mkIteAux

-- negation
def mkNot (t : OptionM term) : OptionM term :=
  t >>= λ t' => not t'

  -- t >>= λ t' => match sortOf t' with
  --                 | some boolSort => not t'
  --                 | _ => none

-- Boolean ops
def mkOr : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm or (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkOrN : List (OptionM term) → OptionM term :=
    constructNaryTerm or (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkAnd : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm and (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkAndN : List (OptionM term) → OptionM term :=
  constructNaryTerm and (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkImplies : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm implies (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkIff : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm iff (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkXor : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm xor (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkNand : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm nand (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkNor : OptionM term → OptionM term → OptionM term :=
  constructBinaryTerm nor (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkForall (v : Nat) (body : OptionM term) : OptionM term :=
  body >>= λ body' => (qforall v body')


/- Aux functions to create values -/
def mkValInt : Int → term :=
λ i => val (value.integer i) intSort

def mkValBV : List Bool → term :=
λ l => val (value.bitvec l) (bv (List.length l))
#eval (mkValInt 0)
#eval mkValInt 5
#eval mkValBV [true, false]
end term

end proof
