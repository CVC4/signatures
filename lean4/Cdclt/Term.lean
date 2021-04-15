import Std.Data.AssocList
import Lean.Meta

inductive Name where
  | anonymous : Name
  | str : Name → String → Name
deriving DecidableEq, Repr

def mkName : String → Name := Name.str Name.anonymous

def NameToStringAux : Name → String
| Name.anonymous => ""
| Name.str n s => s ++ NameToStringAux n
def NameToString : Name → String :=
λ n => ("'" ++ NameToStringAux n ++ "'")

instance : Bind Option where
  bind :=
   λ ot f => match ot with
             | none => none
             | some a => f a

instance : Pure Option := ⟨fun a => Option.some a⟩

instance : Functor Option :=
 { map := fun f o => match o with
   | (Option.some x) => f x
   | _ => none,
   mapConst := fun a o => pure a }

instance : Seq Option where seq o₁ o₂ := match (o₁,o₂) with
                                         | (some f, some x) => some (f x)
                                         | _ => none
instance : SeqLeft Option where seqLeft o₁ o₂ := o₁
instance : SeqRight Option where seqRight o₁ o₂ := o₂

instance : Monad Option where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y x
  seqLeft  x y := bind x fun a => bind y (fun _ => pure a)
  seqRight x y := bind x fun _ => y

open List
namespace proof

/- dep is the sort for Terms that have polymorphic sorts such as
   equality and ITE. These sorts are handled in a special way in the
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

def boolNum : Nat := 1
def intNum : Nat := boolNum + 1
def strNum : Nat := intNum + 1

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

inductive Value : Type where
| bool : Bool → Value
| bitvec : List Bool → Value
| char : Char → Value
| integer : Int → Value
deriving DecidableEq, Repr

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
deriving DecidableEq, Repr

namespace Term

infixl:20  " • " => app

open sort
open Value


-- Sort definitions
@[matchPattern] def boolSort := atom (mkName "bool")
@[matchPattern] def intSort := atom (mkName "int")
@[matchPattern] def stringSort := atom (mkName "string")

@[matchPattern] def ltConst : Term :=
  const (mkName "lt") (arrow intSort (arrow intSort boolSort))

-- macros for creating Terms with interpreted constants
@[matchPattern] def bot : Term := val (bool false) boolSort
@[matchPattern] def top : Term := val (bool true) boolSort

@[matchPattern] def not : Term → Term :=
  λ t => const (mkName "not") (arrow boolSort boolSort) • t

@[matchPattern] def or : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "or") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂
@[matchPattern] def and : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "and") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂
@[matchPattern] def implies : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "implies") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂
@[matchPattern] def xor : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "xor") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂
@[matchPattern] def bIte : Term → Term → Term → Term :=
  λ c t₁ t₂ =>
    const (mkName "bIte") (arrow boolSort (arrow boolSort (arrow boolSort boolSort)))
     • c • t₁ • t₂

@[matchPattern] def fIte : Term → Term → Term → Term :=
  λ t₁ t₂ t₃ => const (mkName "fIte") dep • t₁ • t₂ • t₃
@[matchPattern] def eq : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "eq") dep • t₁ • t₂

-- arith

@[matchPattern] def plus : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "plus") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂
@[matchPattern] def minus : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "minus") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂
@[matchPattern] def mult : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "mult") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂
@[matchPattern] def gt : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "gt") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂
@[matchPattern] def gte : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "gte") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂
@[matchPattern] def lt : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "lt") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂
@[matchPattern] def lte : Term → Term → Term :=
  λ t₁ t₂ => const (mkName "lte") (arrow boolSort (arrow boolSort boolSort)) • t₁ • t₂

-- bitvec

@[matchPattern] def bitOf : Nat → Term → Term → Term :=
  λ n t₁ t₂ => const (mkName "bitOf") (arrow (bv n) (arrow intSort boolSort)) • t₁ • t₂
@[matchPattern] def bbT : Nat → Term :=
  λ n => const (mkName "bbT") (mkArrowN (List.append (List.replicate n (some boolSort)) [bv n]))
@[matchPattern] def bvEq : Nat → Term → Term → Term :=
  λ n t₁ t₂ => const (mkName "bvEq") (arrow (bv n) (arrow (bv n) boolSort)) • t₁ • t₂
@[matchPattern] def bvNot : Nat → Term → Term :=
  λ n t => const (mkName "bvNot") (arrow (bv n) (bv n)) • t
@[matchPattern] def bvAnd : Nat → Term → Term → Term :=
  λ n t₁ t₂ => const (mkName "bvAnd") (arrow (bv n) (arrow (bv n) (bv n))) • t₁ • t₂
@[matchPattern] def bvOr : Nat → Term → Term → Term :=
  λ n t₁ t₂ => const (mkName "bvOr") (arrow (bv n) (arrow (bv n) (bv n))) • t₁ • t₂
@[matchPattern] def bvUlt : Nat → Term → Term → Term :=
  λ n t₁ t₂ => const (mkName "bvUlt") (arrow (bv n) (arrow (bv n) boolSort)) • t₁ • t₂
@[matchPattern] def bvUgt : Nat → Term → Term → Term :=
  λ n t₁ t₂ => const (mkName "bvUgt") (arrow (bv n) (arrow (bv n) boolSort)) • t₁ • t₂
@[matchPattern] def bvSlt : Nat → Term → Term → Term :=
  λ n t₁ t₂ => const (mkName "bvSlt") (arrow (bv n) (arrow (bv n) boolSort)) • t₁ • t₂
@[matchPattern] def bvSgt : Nat → Term → Term → Term :=
  λ n t₁ t₂ => const (mkName "bvSlt") (arrow (bv n) (arrow (bv n) boolSort)) • t₁ • t₂
@[matchPattern] def bvAdd : Nat → Term → Term → Term :=
  λ n t₁ t₂ => const (mkName "bvAdd") (arrow (bv n) (arrow (bv n) (bv n))) • t₁ • t₂
@[matchPattern] def bvNeg : Nat → Term → Term :=
  λ n t => const (mkName "bvNeg") (arrow (bv n) (bv n)) • t
@[matchPattern] def bvExtract : Nat → Nat → Nat → Term → Term → Term → Term :=
  λ n i j t₁ t₂ t₃ => const (mkName "bvExtract") 
                  (arrow (bv n) (arrow intSort (arrow intSort (bv (i - j + 1)))))
                  • t₁ • t₂ • t₃
@[matchPattern] def bvConcat : Nat → Nat → Term → Term → Term :=
  λ m n t₁ t₂ => const (mkName "bvConcat") (arrow (bv m) (arrow (bv n) (bv (m + n))))
                  • t₁ • t₂
@[matchPattern] def bvZeroExt : Nat → Nat → Term → Term :=
  λ n i t => const (mkName "bvZeroExt") (arrow (bv n) (arrow intSort (bv (n + i)))) 
                  • t
@[matchPattern] def bvSignExt : Nat → Nat → Term → Term :=
  λ n i t => const (mkName "bvSignExt") (arrow (bv n) (arrow intSort (bv (n + i)))) 
                  • t
def TermToString : Term → String
| val v s => ValueToString v
| not t => "¬" ++ TermToString t
| or t₁ t₂ => TermToString t₁ ++ " ∨ " ++ TermToString t₂
| and t₁ t₂ => TermToString t₁ ++ " ∧ " ++ TermToString t₂
| xor t₁ t₂ => TermToString t₁ ++ " ⊕ " ++ TermToString t₂
| implies t₁ t₂ => TermToString t₁ ++ " ⇒ " ++ TermToString t₂
| bIte c t₁ t₂ => TermToString c ++ " ? " ++ TermToString t₁ 
                  ++ " : " ++ TermToString t₂
| eq t₁ t₂ => TermToString t₁ ++ " ≃ " ++ TermToString t₂
| fIte c t₁ t₂ => TermToString c ++ " ? " ++ TermToString t₁ 
                  ++ " : " ++ TermToString t₂
| bitOf _ t₁ t₂ => TermToString t₁ ++ "[" ++ TermToString t₂ ++ "]"
/-| bbT _ => "bbT"
| bvEq _ t₁ t₂ => TermToString t₁ ++ " ≃_bv " ++ TermToString t₂
| bvNot _ t => "¬_bv" ++ TermToString t
| bvAnd _ t₁ t₂ => TermToString t₁ ++ " ∧_bv " ++ TermToString t₂
| bvOr _ t₁ t₂ => TermToString t₁ ++ " ∨_bv " ++ TermToString t₂
| bvUlt _ t₁ t₂ => TermToString t₁ ++ " <ᵤ " ++ TermToString t₂
| bvUgt _ t₁ t₂ => TermToString t₁ ++ " >ᵤ " ++ TermToString t₂
| bvSlt _ t₁ t₂ => TermToString t₁ ++ " <ₛ " ++ TermToString t₂
| bvSgt _ t₁ t₂ => TermToString t₁ ++ " >ₛ " ++ TermToString t₂-/
| const n _ => NameToString n
| f • t =>  "(" ++ (TermToString f) ++ " " ++ (TermToString t) ++ ")"
| qforall v t => "∀ " ++ NameToString v ++ " . " ++ TermToString t

def OptionTermToString : Option Term → String
| some t => TermToString t
| none => "none"

instance : ToString Term where toString := TermToString
instance : ToString (Option Term) where toString := OptionTermToString


-- computing the sort of Terms
def sortOfAux : Term → Option sort
| val (Value.bool _) _ => boolSort
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
| f • t =>
    sortOfAux f >>= λ sf =>
    sortOfAux t >>= λ st =>
    match sf with
    | arrow st s => s
    | _ => none
| qforall v t =>
    sortOfAux t >>= λ st => if st = boolSort then st else none
| const _ s => s

def sortOf (t : Option Term) : Option sort := t >>= λ t' => sortOfAux t'

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

/- Term constructors for binary and n-ary Terms. `test` is the
   predicate on the sort of the arguments that needs to be satisfied -/
def constructBinaryTerm (constructor : Term → Term → Term)
  (test : sort → sort → Bool) : Option Term → Option Term → Option Term :=
  bind2 $ λ t₁ t₂ => sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
          if test s₁ s₂ then constructor t₁ t₂ else none

def constructNaryTerm (constructor : Term → Term → Term)
  (test : sort → sort → Bool) (l : List (Option Term)) : Option Term :=
      bindN l >>= λ l' =>
      match l' with
      | h₁ :: h₂ :: t =>
        List.foldlM (λ t₁ t₂ : Term =>
           sortOf t₁ >>= λ s₁ => sortOf t₂ >>= λ s₂ =>
             if test s₁ s₂ then constructor t₁ t₂ else none) h₁ (h₂ :: t)
      | _ => none

-- application of Term to Term
def mkAppAux : Term → Term → Option Term :=
  λ t₁ t₂ =>
    sortOf t₁ >>= λ s₁ =>
    sortOf t₂ >>= λ s₂ =>
    match s₁ with
    | arrow s₂ _ => t₁ • t₂
    | _ => none

-- binary and n-ary application
def mkApp : Option Term → Option Term → Option Term := bind2 mkAppAux

def mkAppN (t : Option Term) (l : List (Option Term)) : Option Term :=
  t >>= λ t' => bindN l >>= λ l' => List.foldlM mkAppAux t' l'

-- equality
def mkEq : Option Term → Option Term → Option Term :=
  constructBinaryTerm eq (λ s₁ s₂ => s₁ = s₂)

-- if-then-else
def mkIteAux (c t₁ t₂ : Term) : Option Term :=
  match sortOf c with
  | some boolSort => match sortOf t₁, sortOf t₂ with
                     | some boolSort, some boolSort => bIte c t₁ t₂
                     | some s₁, some s₂ => if s₁ = s₂ then fIte c t₁ t₂ else none
                     | _, _ => none
  | _ => none

def mkIte : Option Term → Option Term → Option Term → Option Term :=
  bind3 mkIteAux

-- negation
def mkNot (t : Option Term) : Option Term :=
  t >>= λ t' => match sortOf t' with
                  | some boolSort => not t'
                  | _ => none

-- Boolean ops
def mkOr : Option Term → Option Term → Option Term :=
  constructBinaryTerm or (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkOrN : List (Option Term) → Option Term :=
    constructNaryTerm or (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkAnd : Option Term → Option Term → Option Term :=
  constructBinaryTerm and (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkAndN : List (Option Term) → Option Term :=
  constructNaryTerm and (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkImplies : Option Term → Option Term → Option Term :=
  constructBinaryTerm implies (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkXor : Option Term → Option Term → Option Term :=
  constructBinaryTerm xor (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def mkForall (v : Name) (body : Option Term) : Option Term :=
  body >>= λ body' => (qforall v body')

#check Lean.Quote

syntax "`[Term|" term "]" : term
macro_rules
 | `(`[Term|top]) => `((top : Term))
 | `(`[Term|bot]) => `((bot : Term))
 | `(`[Term|mkAppN $a $l]) => `(($a : Term)) --match l with `(match $l with
                              --  | then $a else mkApp $a `[Term| mkAppN $(List.car l) $(List.cdr l)])
 | `(`[Term|$x < $y]) => `(`[Term|mkAppN ltConst [$x, $y]])
 | `(`[Term|$x:ident]) => `(($(Lean.quote x.getId.toString) : Term))

#check `[Term|top]

--#check let x := Term.val (Value.integer 2) _;
--        let y := Term.val (Value.integer 3) _;
--         `[Term|x < y]



end Term

end proof