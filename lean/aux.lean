import init.control.combinators
import data.num.basic

/- Takes element a and list l, and generates list l' of all possible pairs of 
   a along with elements in l, except pairs containing the same element twice -/
def genPairs {α : Type} [s : decidable_eq α] (a : α) : list α → list (α × α) :=
  list.filter_map (λ x : α, if a = x then option.none else option.some (a,x))
#eval genPairs 1 [1,2,3]
--[(1, 2), (1, 3)]

/- All possible pairwise combinations of the elements in the input list 
   except pairs containing the same element twice -/
def genAllPairs {α : Type} [s : decidable_eq α] : list α → list (α×α)
| [] := []
| (h::t) := genPairs h t ++ genAllPairs t
#eval genAllPairs [1,2,3] --[(1, 2), (1, 3), (2, 3)]
#eval genAllPairs [1,2,3,2] --[(1, 2), (1, 3), (1, 2), (2, 3), (3, 2)]
/- Prevents (2,2) but not (1,2) being repeated -/

/- remove a l removes the first occurrence of a in list l if 
   a occurs in l, otherwise it returns the list unchanged -/
def {u} remove {α : Type u} [decidable_eq α] : α → list α → list α
| x [] := []
| x (y :: c) := if x = y then c else y :: remove x c
#eval remove 7 [4,7,10] -- [4,10]
#eval remove 1 [2,3,4] -- [2,3,4]
#eval remove 3 [3,3,3] -- [3,3]

/- Given two lists, and a function that transforms elements of 
   each list into a third type, apply the function index-wise 
   on the lists -/
def zip {α β γ : Type} : list α → list β →  (α → β → γ) → list γ
   | (h₁ :: t₁) (h₂ :: t₂) p := (p h₁ h₂) :: (zip t₁ t₂ p)
   | _ _ _ := []