import Cdclt.Term

open proof
open proof.sort proof.Term

namespace proof

namespace Term

partial def TermEval (ot : Option Term) : Option Term :=
  ot >>= λ t =>
  match t with
  | top => top
  | bot => bot
  | Term.not t₁ =>
    do let t₁' ← TermEval t₁
       match t₁' with
       | top => bot
       | bot => top
       | _ => t
  | and t₁ t₂ =>
    do let t₁' ← TermEval t₁
       let t₂' ← TermEval t₂
       match t₁', t₂' with
       | top, top => top
       | bot, _ => bot
       | _, bot => bot
       | _, _ => t
  | or t₁ t₂ =>
    do let t₁' ← TermEval t₁
       let t₂' ← TermEval t₂
       match t₁', t₂' with
       | bot, bot => bot
       | top, _ => top
       | _, top => top
       | _, _ => t
  | implies t₁ t₂ =>
    do let t₁' ← TermEval t₁
       let t₂' ← TermEval t₂
       match t₁', t₂' with
       | bot, _ => top
       | top, bot => bot
       | top, top => top
       | _, _ => t
  | xor t₁ t₂ =>
    do let t₁' ← TermEval t₁
       let t₂' ← TermEval t₂
       match t₁', t₂' with
       | bot, top => top
       | top, bot => top
       | top, top => bot
       | bot, bot => bot
       | _, _ => t
  | eq t₁ t₂ =>
    do let t₁' ← TermEval t₁
       let t₂' ← TermEval t₂
       match t₁', t₂' with
       | bot, top => bot
       | top, bot => bot
       | top, top => top
       | bot, bot => top
       | _, _ => t
  | bIte c t₁ t₂ =>
    do let c' ← TermEval c
       match c' with
       | top => TermEval t₁
       | bot => TermEval t₂
       | _ => t
  | app t₁ t₂ =>
    do let t₁' ← TermEval t₁
       let t₂' ← TermEval t₂
       (app t₁' t₂')
  | _ => t

#check TermEval (mkAnd top bot)
#eval TermEval (mkAnd top bot)
end Term

end proof
