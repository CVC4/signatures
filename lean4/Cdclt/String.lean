import Cdclt.Term
import Cdclt.Boolean
import Cdclt.Arith
import Cdclt.TermEval

open proof
open proof.sort proof.term
open rules

namespace proof
namespace term

def a_char : term := mkValChar 'a'
def b_char : term := mkValChar 'b'
def abc := mkValChars ['a','b','c']
def abcd := strPlus (mkValChars ['a','b']) (mkValChars ['c','d'])

def reverseStr : term → term
| (strPlus s₁ s₂) => strPlus (reverseStr s₂) (reverseStr s₁)
| s => s

#eval reverseStr a_char
#eval reverseStr abc

def cba := reverseStr abc

def removeEmptyStr : term → term
| (strPlus s₁ s₂) =>
  if s₁ == emptyStr then removeEmptyStr s₂ else
  if s₂ == emptyStr then removeEmptyStr s₁ else
  strPlus (removeEmptyStr s₁) (removeEmptyStr s₂)
| s => s

#eval removeEmptyStr a_char
#eval removeEmptyStr abc
#eval removeEmptyStr cba

partial def stringFlatten : term → term
| (strPlus (strPlus s₁ s₂) s₃) => stringFlatten $ strPlus s₁ (strPlus s₂ s₃)
| (strPlus s₁ s₂) => strPlus s₁ (stringFlatten s₂)
| s => s

#eval stringFlatten emptyStr
#eval stringFlatten a_char
#eval stringFlatten abc
#eval stringFlatten abcd

partial def normalize : term → term := stringFlatten ∘ removeEmptyStr

#eval normalize abcd


def removeEqualPrefixAux : term → term → term × term
| a@(strPlus s₁ s₂), b@(strPlus t₁ t₂) =>
  if s₁ = t₁ then removeEqualPrefixAux s₂ t₂ else (a,b)
| a@(val (value.char c₁) _), b@(strPlus s₁ s₂) =>
  if a == s₁ then (emptyStr, s₂) else (a,b)
| a@(strPlus s₁ s₂), b@(val (value.char c₁) _) =>
  if s₁ == b then (emptyStr, s₂) else (a,b)
| a,b =>
  if a == b then (emptyStr, emptyStr) else (a,b)

def removeEqualPrefix : term → term → term × term :=
  λ t₁ t₂ => removeEqualPrefixAux (normalize t₁) (normalize t₂)

#eval removeEqualPrefix emptyStr emptyStr
#eval removeEqualPrefix emptyStr a_char
#eval removeEqualPrefix a_char a_char
#eval removeEqualPrefix a_char b_char
#eval removeEqualPrefix abc b_char
#eval removeEqualPrefix abc a_char
#eval removeEqualPrefix abc abcd


-- ======== Concat eq
-- Children: (P1:(= (str.++ t1 ... tn t) (str.++ t1 ... tn s)))
-- Arguments: (b), indicating if reverse direction
-- ---------------------
-- Conclusion: (= t s)
--
-- Notice that t or s may be empty, in which case they are implicit in the
-- concatenation above. For example, if
-- P1 concludes (= x (str.++ x z)), then
-- (CONCAT_EQ P1 :args false) concludes (= "" z)
--
-- Also note that constants are split, such that if
-- P1 concludes (= (str.++ "abc" x) (str.++ "a" y)), then
-- (CONCAT_EQ P1 :args false) concludes (= (str.++ "bc" x) y)
-- This splitting is done only for constants such that Word::splitConstant
-- returns non-null.
axiom concatEq : -- does reverse mean reverse both strings?
  (s₁ s₂ t₁ t₂ : term) → thHolds (eq (strPlus s₁ s₂) (strPlus t₁ t₂)) →
   thHolds (eq s₁ t₁) → thHolds (eq s₂ t₂)

-- ======== Concat unify
-- Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
--            P2:(= (str.len t1) (str.len s1)))
-- Arguments: (b), indicating if reverse direction
-- ---------------------
-- Conclusion: (= t1 s1)

axiom concatUnify :
  (s₁ s₂ t₁ t₂ : term) → thHolds (eq (strPlus s₁ s₂) (strPlus t₁ t₂)) →
    thHolds (eq (strLength s₁) (strLength t₁)) →
    thHolds (eq s₂ t₂)


abbrev Function.comp2 (f : γ → δ) (g : α → β → γ) : α → β → δ :=
  fun x y => f (g x y)
infixr:90 " ∘₂ "  => Function.comp2

def isPrefix : term → term → Bool :=
  (λ s => s == emptyStr) ∘₂ Prod.fst ∘₂ removeEqualPrefix

-- ======== Concat conflict
-- Children: (P1:(= (str.++ c1 t) (str.++ c2 s)))
-- Arguments: (b), indicating if reverse direction
-- ---------------------
-- Conclusion: false
-- Where c1, c2 are constants such that Word::splitConstant(c1,c2,index,b)
-- is null, in other words, neither is a prefix of the other.


axiom concatConflict :
  (s₁ s₂ t₁ t₂ : term) → (h : ¬(isPrefix s₁ t₁) ∧ ¬ (isPrefix t₁ s₁)) →
    thHolds (eq (strPlus s₁ s₂) (strPlus t₁ t₂)) → holds []

-- not sure about CoeSort

-- TODO write out skolem condition
--axiom concatSplit :
--  (s₁ s₂ t₁ t₂ rₜ rₛ : term) → (h : eq (strPlus t₁ t₂) (strPlus s₁ s₂)) →
--   (not (eq (strLen t₁) (strLen s₁))) →
--   (eq rₜ )
--   or (eq t₁ (strPlus s₁ rₜ)) (eq s₁ (strPlus t₁ rₛ))

-- ======== Concat constant split
-- Children: (P1:(= (str.++ t1 t2) (str.++ c s2)),
--            P2:(not (= (str.len t1) 0)))
-- Arguments: (false)
-- ---------------------
-- Conclusion: (= t1 (str.++ c r))
-- where
--   r = (witness ((z String)) (= z (suf t1 1))).
--
-- or the reverse form of the above:
--
-- Children: (P1:(= (str.++ t1 t2) (str.++ s1 c)),
--            P2:(not (= (str.len t2) 0)))
-- Arguments: (true)
-- ---------------------
-- Conclusion: (= t2 (str.++ r c))
-- where
--   r = (witness ((z String)) (= z (pre t2 (- (str.len t2) 1)))).

-- concatCSplit

-- ======== Concat length propagate
-- Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
--            P2:(> (str.len t1) (str.len s1)))
-- Arguments: (false)
-- ---------------------
-- Conclusion: (= t1 (str.++ s1 r_t))
-- where
--   r_t = (witness ((z String)) (= z (suf t1 (str.len s1))))
--
-- or the reverse form of the above:
--
-- Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
--            P2:(> (str.len t2) (str.len s2)))
-- Arguments: (false)
-- ---------------------
-- Conclusion: (= t2 (str.++ r_t s2))
-- where
--   r_t = (witness ((z String)) (= z (pre t2 (- (str.len t2) (str.len
--   s2))))).


-- concatLProp

-- ======== Concat constant propagate
-- Children: (P1:(= (str.++ t1 w1 t2) (str.++ w2 s)),
--            P2:(not (= (str.len t1) 0)))
-- Arguments: (false)
-- ---------------------
-- Conclusion: (= t1 (str.++ w3 r))
-- where
--   w1, w2, w3, w4 are words,
--   w3 is (pre w2 p),
--   w4 is (suf w2 p),
--   p = Word::overlap((suf w2 1), w1),
--   r = (witness ((z String)) (= z (suf t1 (str.len w3)))).
-- In other words, w4 is the largest suffix of (suf w2 1) that can contain a
-- prefix of w1; since t1 is non-empty, w3 must therefore be contained in t1.
--
-- or the reverse form of the above:
--
-- Children: (P1:(= (str.++ t1 w1 t2) (str.++ s w2)),
--            P2:(not (= (str.len t2) 0)))
-- Arguments: (true)
-- ---------------------
-- Conclusion: (= t2 (str.++ r w3))
-- where
--   w1, w2, w3, w4 are words,
--   w3 is (suf w2 (- (str.len w2) p)),
--   w4 is (pre w2 (- (str.len w2) p)),
--   p = Word::roverlap((pre w2 (- (str.len w2) 1)), w1),
--   r = (witness ((z String)) (= z (pre t2 (- (str.len t2) (str.len w3))))).
-- In other words, w4 is the largest prefix of (pre w2 (- (str.len w2) 1))
-- that can contain a suffix of w1; since t2 is non-empty, w3 must therefore
-- be contained in t2.

-- ======== Concat constant propagate
-- Children: (P1:(= (str.++ t1 w1 t2) (str.++ w2 s)),
--            P2:(not (= (str.len t1) 0)))
-- Arguments: (false)
-- ---------------------
-- Conclusion: (= t1 (str.++ w3 r))
-- where
--   w1, w2, w3, w4 are words,
--   w3 is (pre w2 p),
--   w4 is (suf w2 p),
--   p = Word::overlap((suf w2 1), w1),
--   r = (witness ((z String)) (= z (suf t1 (str.len w3)))).
-- In other words, w4 is the largest suffix of (suf w2 1) that can contain a
-- prefix of w1; since t1 is non-empty, w3 must therefore be contained in t1.
--
-- or the reverse form of the above:
--
-- Children: (P1:(= (str.++ t1 w1 t2) (str.++ s w2)),
--            P2:(not (= (str.len t2) 0)))
-- Arguments: (true)
-- ---------------------
-- Conclusion: (= t2 (str.++ r w3))
-- where
--   w1, w2, w3, w4 are words,
--   w3 is (suf w2 (- (str.len w2) p)),
--   w4 is (pre w2 (- (str.len w2) p)),
--   p = Word::roverlap((pre w2 (- (str.len w2) 1)), w1),
--   r = (witness ((z String)) (= z (pre t2 (- (str.len t2) (str.len w3))))).
-- In other words, w4 is the largest prefix of (pre w2 (- (str.len w2) 1))
-- that can contain a suffix of w1; since t2 is non-empty, w3 must therefore
-- be contained in t2.

-- concatCProp

-- ======== String decompose
-- Children: (P1: (>= (str.len t) n)
-- Arguments: (false)
-- ---------------------
-- Conclusion: (and (= t (str.++ w1 w2)) (= (str.len w1) n))
-- or
-- Children: (P1: (>= (str.len t) n)
-- Arguments: (true)
-- ---------------------
-- Conclusion: (and (= t (str.++ w1 w2)) (= (str.len w2) n))
-- where
--   w1 is (witness ((z String)) (= z (pre t n)))
--   w2 is (witness ((z String)) (= z (suf t n)))

-- stringDecompose

-- ======== Length positive
-- Children: none
-- Arguments: (t)
-- ---------------------
-- Conclusion: (or (and (= (str.len t) 0) (= t "")) (> (str.len t 0)))


axiom stringLengthPos :
  (s : term) →
   thHolds $ or (and (eq (strLength s) (mkValInt 0)) (eq s emptyStr))
                  (gt (strLength s) (mkValInt 0))

-- ======== Length non-empty
-- Children: (P1:(not (= t "")))
-- Arguments: none
-- ---------------------
-- Conclusion: (not (= (str.len t) 0))


axiom stringLengthNonEmpty :
  (s : term) → (h : thHolds $ not (eq s emptyStr)) →
   thHolds (not (eq (strLength s) (mkValInt 0)))

--======================== Extended functions
-- ======== Reduction
-- Children: none
-- Arguments: (t)
-- ---------------------
-- Conclusion: (and R (= t w))
-- where w = strings::StringsPreprocess::reduce(t, R, ...).
-- In other words, R is the reduction predicate for extended term t, and w is
--   (witness ((z T)) (= z t))
-- Notice that the free variables of R are w and the free variables of t.


axiom stringReduction : -- this is a guess
  (s : term) → thHolds (eq s (normalize s))

-- ======== Eager Reduction
-- Children: none
-- Arguments: (t, id?)
-- ---------------------
-- Conclusion: R
-- where R = strings::TermRegistry::eagerReduce(t, id).
--  STRING_EAGER_REDUCTION,

axiom stringEagerReduction : -- for now the same as stringReduction
  (s : term) → thHolds (eq s (normalize s))

-- axiom eagerStringReduction ?

--======================== Regular expressions
-- ======== Regular expression intersection
-- Children: (P:(str.in.re t R1), P:(str.in.re t R2))
-- Arguments: none
-- ---------------------
-- Conclusion: (str.in.re t (re.inter R1 R2)).
--  RE_INTER,

-- had to change name from REInter to prevent class with REInter function
axiom REIntersect : (s r₁ r₂ : term) →
 thHolds (inRE s r₁) → thHolds (inRE s r₂) →
 thHolds (inRE s (REInter r₁ r₂))

  -- reduceRegExpPos
  -- Return the unfolded form of mem of the form (str.in_re s r).

axiom reduceRegExpPos : term → term
--axiom REUnfoldPos : (t R : term) → inRE t R → reduceRegExpPos (inRE t R)
--axiom REUnfoldNeg : (t R : term) → not (inRE t R) → (reduceRegExpNeg (not (inRE t R)))
-- RE_UNFOLD_NEG_CONCAT_FIXED,
-- RE_ELIM,

-- stringCodeInj
-- stringSeqUnitInj

axiom stringTrust : (s : term) → thHolds s

#eval (termEval (lt (mkValInt 1) (mkValInt 0)))
axiom evaluate : (s : term) → thHolds (eq s (termEval s))

end term
end proof
