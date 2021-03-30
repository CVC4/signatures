import term
import data.list.perm
import cdclt

universe variables uu vv
variables {α : Type uu} {β : Type vv}

open list

#check @perm
#check @perm.refl
#check @perm.swap

#check (perm.swap 0 2 [1])

theorem rotate3 : [2,0,1] ~ [0,1,2] :=
 have h₀ : [2,0,1] ~ [0,2,1], from perm.swap 0 2 [1],
 have h₁ : [0,2,1] ~ [0,1,2], from perm.cons 0 (perm.swap 1 2 []),
 perm.trans h₀ h₁

theorem rotate3' : [2,0,1] ~ [0,1,2] :=
 perm.trans (perm.swap 0 2 [1]) (perm.cons 0 (perm.swap 1 2 []))

@[reducible]
def swap_nth : ℕ → list α → list α
| 0     (a::b::l) := b::a::l
| (n+1) (a::l)    := a::(swap_nth n l)
| _ l := l

#eval swap_nth 0 [0,1,2]
#eval swap_nth 1 [0,1,2]
#eval swap_nth 2 [0,1,2]
#eval swap_nth 3 [0,1,2]

theorem perm.swap_nth : ∀ (n:ℕ) (l:list α), l ~ (swap_nth n l)
| n [] := by cases n; exact perm.nil
| 0 (a::nil) := perm.refl (a::nil)
| 0 (a::b::l)  := perm.swap b a l
| (n+1) (a::l) := by { rw [swap_nth, perm_cons], exact (perm.swap_nth n l) }

theorem rotate3'' : [2,0,1] ~ [0,1,2] :=
 have h₀ : [2,0,1] ~ [0,2,1], from perm.swap_nth 0 [2,0,1],
 have h₁ : [0,2,1] ~ [0,1,2], from perm.swap_nth 1 [0,2,1],
 perm.trans h₀ h₁

theorem rotate4 : [3,0,1,2] ~ [0,1,2,3] :=
 have h₀ : [3,0,1,2] ~ [0,3,1,2], from perm.swap_nth 0 [3,0,1,2],
 have h₁ : [0,3,1,2] ~ [0,1,3,2], from perm.swap_nth 1 [0,3,1,2],
 have h₂ : [0,1,3,2] ~ [0,1,2,3], from perm.swap_nth 2 [0,1,3,2],
 perm.trans h₀ (perm.trans h₁ h₂)

#check perm.trans (perm.swap_nth 0 [3,0,1,2]) $
        (perm.trans
          (perm.swap_nth 1 [0,3,1,2])
          (perm.swap_nth 2 [0,1,3,2]))

#check @list.foldr

#eval range 3
#check list.length

theorem rotate (a:α) (l : list α) : a::l ~ l++[a] :=
 list.foldr
  (λ (n:ℕ), λ (x:list α), perm.trans x (perm.swap_nth n x))
  l (range l.length)

def swap_nonlocal : ℕ → ℕ → list α → list α := sorry

def gen_permutation : list α → list (ℕ×ℕ) → perm _ _ := sorry

-- so need to enact a sorting algorithm
-- bubble sort

-- bubble [1] -> [1]
#check decidable_linear_order

def bubble_insert [h_dec : decidable_linear_order α] : α → list α → list α
| a [] := [a]
| a (h::t) := if a <= h then a::h::t else h::(insert a t)
#check bubble_insert

def bubble [h_dec : decidable_linear_order α] : list α → list α
| [] := []
| (h::t) := bubble_insert h (bubble t)
