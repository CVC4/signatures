namespace sort

def sortToString : sort → String
| (atom id) => toString id
| (arrow s1 s2) =>
  "(" ++ (sortToString s1) ++ " → " ++ (sortToString s2) ++ ")"
| (bv n) => "bv " ++ (toString n)

#check atom 0

#eval sortToString $ sort.atom 0

end sort

section
open Nat

def buildIds : List Nat := do
  let mut l := []
  let mut currId := 0
  l := currId :: l
  currId := currId + 1
  l := currId :: l
  return l

#eval buildIds





-- #eval currId
-- def currId := currId + 1
-- #eval currId



-- -- booleans
-- def botId : Nat := id
-- def notId : Nat := succ
-- def orId : Nat := succ notId
-- def andId : Nat := succ orId
-- def impliesId : Nat := succ andId
-- def xorId : Nat := succ andId
-- def iffId : Nat := succ andId
-- def bIteId : Nat := succ andId
-- -- euf
-- def fIteId : Nat := succ andId
-- def eqId : Nat := succ andId
-- bv
-- arrays
end


#eval 0 + 1


def main : IO Unit :=
  IO.println "Hello, world!"
