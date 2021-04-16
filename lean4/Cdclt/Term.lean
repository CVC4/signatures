import Std.Data.AssocList

inductive StrTree where
| leaf (s : String)
| node (children : List $ StrTree)
deriving Repr

inductive Name where
  | anonymous : Name
  | str : Name → String → Name
deriving DecidableEq, Repr

def mkName (s : String) := Name.str Name.anonymous s

open List
namespace proof

/- dep is the sort for Terms that have polymorphic sorts such as
   eqality and ITE. These sorts are handled in a special way in the
   type checker.

   Additionally, we have atomic sorts, parameterized by a Nat, arrow
   for functional sorts, and bitvector sorts parameterized by their
   length -/
inductive sort : Type where
| dep : sort
| atom : Name → sort
| arrow : sort → sort → sort
| bv : Nat → sort
deriving DecidableEq, Repr

namespace sort

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

inductive Value : Type where
| bool : Bool → Value
| bitvec : List Bool → Value
| char : Char → Value
| integer : Int → Value
| str : String → Value
deriving Repr, DecidableEq

def BVToStringAux : List Bool → String
| h :: t => (if h then "1" else "0") ++ (BVToStringAux t)
| [] => ""

def BVToString : List Bool → String :=
λ l => "[" ++ BVToStringAux l ++ "]"

def ValueToString : Value → String
| Value.bool b => if b then "true" else "false"
| Value.bitvec l => BVToString l
| Value.char c => String.singleton c
| Value.integer i =>  "i" -- Change to ToString i
| Value.str s => s

/- Terms are values (interpreted constants),
   constants of a sort, applications,
   or quantified formulas
   Quantified variables are also
   parameterized by a Nat -/
inductive Term : Type where
| val : Value → Option sort → Term -- interpreted constant
| const : Name → Option sort → Term -- uninterpreted constant
| app : Term → Term → Term
| qforall : Name → Term → Term
deriving DecidableEq, Repr, BEq

namespace Term

infixl:20  " • " => app

open sort
open Value


-- Sort definitions
@[matchPattern] def boolSort := atom (mkName "bool")
@[matchPattern] def intSort := atom (mkName "int")
@[matchPattern] def stringSort := atom (mkName "string")

@[matchPattern] def bot : Term := val (bool false) boolSort
@[matchPattern] def top : Term := val (bool true) boolSort

@[matchPattern] def notConst : Term :=
  const (mkName "not") (arrow boolSort boolSort)
@[matchPattern] def orConst : Term :=
  const (mkName "or") (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def andConst : Term :=
  const (mkName "and") (arrow boolSort (arrow boolSort boolSort))

@[matchPattern] def impliesConst : Term :=
  const (mkName "implies") (arrow boolSort (arrow boolSort boolSort))

@[matchPattern] def xorConst : Term  :=
  const (mkName "xor") (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def bIteConst : Term :=
  const (mkName "bIte") (arrow boolSort (arrow boolSort (arrow boolSort boolSort)))
@[matchPattern] def fIteConst : Term := const (mkName "fIte") dep
@[matchPattern] def eqConst : Term := const (mkName "eq") dep

@[matchPattern] def plusConst : Term :=
  const (mkName "plus") (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def minusConst : Term :=
  const (mkName "minus") (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def multConst : Term :=
  const (mkName "mult") (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def gtConst : Term :=
  const (mkName "gt") (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def gteConst : Term :=
  const (mkName "gte") (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def ltConst : Term :=
  const (mkName "lt") (arrow boolSort (arrow boolSort boolSort))
@[matchPattern] def lteConst : Term :=
  const (mkName "lte") (arrow boolSort (arrow boolSort boolSort))

def liftUnary (t : Term) : (Term → Term) := λ t₁ => t • t₁
def liftBinary (t : Term) : (Term → Term → Term) := λ t₁ t₂ => t • t₁ • t₂
def liftTernary (t : Term) : (Term → Term → Term → Term) := λ t₁ t₂ t₃ => t • t₁ • t₂ • t₃

-- macros for creating Terms with interpreted constants

@[matchPattern] def not : Term → Term := liftUnary notConst
@[matchPattern] def or : Term → Term → Term := liftBinary orConst
@[matchPattern] def and : Term → Term → Term := liftBinary andConst
@[matchPattern] def implies : Term → Term → Term := liftBinary impliesConst
@[matchPattern] def xor : Term → Term → Term := liftBinary xorConst
@[matchPattern] def bIte : Term → Term → Term → Term := liftTernary bIteConst
@[matchPattern] def fIte : Term → Term → Term → Term := liftTernary fIteConst
@[matchPattern] def eq : Term → Term → Term := liftBinary eqConst

-- bitvec

@[matchPattern] def bitOfConst (n : Nat) : Term :=
  const (mkName "bitOf") (arrow (bv n) (arrow intSort boolSort))
@[matchPattern] def bbTConst (n : Nat) : Term :=
  const (mkName "bbT") (mkArrowN (List.append (List.replicate n (some boolSort)) [bv n]))

@[matchPattern] def bvEqConst (n : Nat) : Term :=
  const (mkName "bvEq") (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvNotConst (n : Nat) : Term :=
  const (mkName "bvNot") (arrow (bv n) (bv n))
@[matchPattern] def bvAndConst (n : Nat) : Term :=
  const (mkName "bvAnd") (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvOrConst (n : Nat) : Term :=
 const (mkName "bvOr") (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvUltConst (n : Nat) : Term :=
 const (mkName "bvUlt") (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvUgtConst (n : Nat) : Term :=
 const (mkName "bvUgt") (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvSltConst (n : Nat) : Term :=
 const (mkName "bvSlt") (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvSgtConst (n : Nat) : Term :=
 const (mkName "bvSlt") (arrow (bv n) (arrow (bv n) boolSort))
@[matchPattern] def bvAddConst (n : Nat) : Term :=
 const (mkName "bvAdd") (arrow (bv n) (arrow (bv n) (bv n)))
@[matchPattern] def bvNegConst (n : Nat) : Term :=
  const (mkName "bvNeg") (arrow (bv n) (bv n))
@[matchPattern] def bvExtractConst (n i j : Nat) : Term :=
  const (mkName "bvExtract") (arrow (bv n) (arrow intSort (arrow intSort (bv (i - j + 1)))))
@[matchPattern] def bvConcatConst (m n : Nat) : Term :=
  const (mkName "bvConcat") (arrow (bv m) (arrow (bv n) (bv (m + n))))
@[matchPattern] def bvZeroExtConst (n i : Nat) : Term :=
  const (mkName "bvZeroExt") (arrow (bv n) (arrow intSort (bv (n + i))))
@[matchPattern] def bvSignExtConst (n i : Nat) : Term :=
  const (mkName "bvSignExt") (arrow (bv n) (arrow intSort (bv (n + i))))

@[matchPattern] def bitOf (n : Nat) : Term → Term → Term :=  liftBinary $ bitOfConst n
@[matchPattern] def bvEq (n : Nat) : Term → Term → Term := liftBinary $ bvEqConst n
@[matchPattern] def bvNot (n : Nat) : Term → Term := liftUnary $ bvNotConst n
@[matchPattern] def bvAnd (n : Nat) : Term → Term → Term :=  liftBinary $ bvAndConst n
@[matchPattern] def bvOr (n : Nat) : Term → Term → Term := liftBinary $ bvOrConst n
@[matchPattern] def bvUlt (n : Nat) : Term → Term → Term := liftBinary $ bvUltConst n
@[matchPattern] def bvUgt (n : Nat) : Term → Term → Term := liftBinary $ bvUgtConst n
@[matchPattern] def bvSlt (n : Nat) : Term → Term → Term :=liftBinary $ bvSltConst n
@[matchPattern] def bvSgt (n : Nat) : Term → Term → Term := liftBinary $ bvSgtConst n
@[matchPattern] def bvAdd (n : Nat) : Term → Term → Term := liftBinary $ bvAddConst n
@[matchPattern] def bvNeg (n : Nat) : Term → Term := liftUnary $ bvNegConst n
@[matchPattern] def bvExtract (n i j : Nat) : Term → Term → Term → Term :=  liftTernary $ bvExtractConst n i j
@[matchPattern] def bvConcat (m n : Nat) : Term → Term → Term := liftBinary $ bvConcatConst m n
@[matchPattern] def bvZeroExt (n i : Nat) : Term → Term → Term := liftBinary $ bvZeroExtConst n i
@[matchPattern] def bvSignExt (n i : Nat) : Term → Term → Term := liftBinary $ bvSignExtConst n i



--def TermToString : Term → String
--| val v s => ValueToString v
--| not t => "¬" ++ TermToString t
--| or t₁ t₂ => TermToString t₁ ++ " ∨ " ++ TermToString t₂
--| and t₁ t₂ => TermToString t₁ ++ " ∧ " ++ TermToString t₂
--| xor t₁ t₂ => TermToString t₁ ++ " ⊕ " ++ TermToString t₂
--| implies t₁ t₂ => TermToString t₁ ++ " ⇒ " ++ TermToString t₂
--| bIte c t₁ t₂ =>
--  TermToString c ++ " ? " ++ TermToString t₁ ++ " : " ++ TermToString t₂
--| eq t₁ t₂ => TermToString t₁ ++ " ≃ " ++ TermToString t₂
--| fIte c t₁ t₂ =>
--  TermToString c ++ " ? " ++ TermToString t₁ ++ " : " ++ TermToString t₂
--| bitOf _ t₁ t₂ => TermToString t₁ ++ "[" ++ TermToString t₂ ++ "]"
--/-| bbT _ => "bbT"
--| bvEq _ t₁ t₂ => TermToString t₁ ++ " ≃_bv " ++ TermToString t₂
--| bvNot _ t => "¬_bv" ++ TermToString t
--| bvAnd _ t₁ t₂ => TermToString t₁ ++ " ∧_bv " ++ TermToString t₂
--| bvOr _ t₁ t₂ => TermToString t₁ ++ " ∨_bv " ++ TermToString t₂
--| bvUlt _ t₁ t₂ => TermToString t₁ ++ " <ᵤ " ++ TermToString t₂
--| bvUgt _ t₁ t₂ => TermToString t₁ ++ " >ᵤ " ++ TermToString t₂
--| bvSlt _ t₁ t₂ => TermToString t₁ ++ " <ₛ " ++ TermToString t₂
--| bvSgt _ t₁ t₂ => TermToString t₁ ++ " >ₛ " ++ TermToString t₂-/
--| const id _ => toString id
--| f • t =>  "(" ++ (TermToString f) ++ " " ++ (TermToString t) ++ ")"
--| qforall v t => "∀ " ++ toString v ++ " . " ++ TermToString t
--

--def OptionTermToString : Option Term → String
--| some t => TermToString t
--| none => "none"
--
--instance : ToString Term where toString := TermToString
--instance : ToString (Option Term) where toString := OptionTermToString


-- computing the sort of Terms
def sortOfAux : Term → OptionM sort
| val (Value.bool _) _ => boolSort
| val (Value.str _) _ => stringSort
| val (bitvec l) _ =>
    do let len ← List.length l if len = 0 then none else bv l.length
| val (Value.char _) _ => stringSort
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

def sortOf (t : OptionM Term) : OptionM sort := t >>= λ t' => sortOfAux t'

/- bind : (x : m α) → (f : (α → m α))
   unpacks the Term from the monad x and applies
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

/- Term constructors for binary and n-ary Terms. (mkName "test(mkName " is the
   predicate on the sort of the arguments that needs to be satisfied -/
def constructBinaryTerm (constructor : Term → Term → Term)
  (test : sort → sort → Bool) : OptionM Term → OptionM Term → OptionM Term :=
  bind2 $ λ t₁ t₂ => sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
          if test s₁ s₂ then constructor t₁ t₂ else none

def constructNaryTerm (constructor : Term → Term → Term)
  (test : sort → sort → Bool) (l : List (OptionM Term)) : OptionM Term :=
      bindN l >>= λ l' =>
      match l' with
      | h₁ :: h₂ :: t =>
        List.foldlM (λ t₁ t₂ : Term =>
           sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
             if test s₁ s₂ then constructor t₁ t₂ else none) h₁ (h₂ :: t)
      | _ => none

-- application of Term to Term
def mkAppAux : Term → Term → OptionM Term :=
  λ t₁ t₂ =>
    sortOf t₁ >>= λ s₁ =>
    sortOf t₂ >>= λ s₂ =>
    match s₁ with
    | arrow s₂ _ => t₁ • t₂
    | dep => t₁ • t₂
    | _ => none

-- binary and n-ary application
def mkApp : OptionM Term → OptionM Term → OptionM Term := bind2 mkAppAux

def mkAppN (t : OptionM Term) (l : List (OptionM Term)) : OptionM Term :=
  t >>= λ t' => bindN l >>= λ l' => List.foldlM mkAppAux t' l'

-- eqality
def mkEq : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm eq (λ s₁ s₂ => s₁ = s₂)

-- if-then-else
--def mkIteAux (c t₁ t₂ : Term) : OptionM Term :=
--  match sortOf c with
--  | some boolSort => match sortOf t₁, sortOf t₂ with
--                     | some boolSort, some boolSort => bIte c t₁ t₂
--                     | some s₁, some s₂ => if s₁ = s₂ then fIte c t₁ t₂ else none
--                     | _, _ => none
--  | _ => none

def mkIteAux (c t₁ t₂ : Term) : OptionM Term :=
 do
  match (← sortOf c) with
   | boolSort => match (← sortOf t₁), (← sortOf t₂) with
                  | boolSort, boolSort => bIte c t₁ t₂
                  | s₁, s₂ => if s₁ = s₂ then fIte c t₁ t₂ else none
   | _ => none


def mkIte : OptionM Term → OptionM Term → OptionM Term → OptionM Term :=
  bind3 mkIteAux

-- negation

def mkNot (t : OptionM Term) : OptionM Term :=
  t >>= λ t' => do match (← (sortOf t')) with
                  | boolSort => not t'
                  | _ => none



-- Boolean ops
def mkOr : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm or (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkOrN : List (OptionM Term) → OptionM Term :=
    constructNaryTerm or (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkAnd : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm and (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkAndN : List (OptionM Term) → OptionM Term :=
  constructNaryTerm and (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkImplies : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm implies (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkXor : OptionM Term → OptionM Term → OptionM Term :=
  constructBinaryTerm xor (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkForall (v : Name) (body : OptionM Term) : OptionM Term :=
  body >>= λ body' => (qforall v body')

end Term

end proof
