import Cdclt.Term

open proof
open proof.sort proof.term

namespace proof

namespace term

partial def termEval (ot : Option term) : Option term :=
  ot >>= λ t =>
  match t with
  | top => top
  | bot => bot
  | term.not t₁ =>
    do let t₁' ← termEval t₁
       match t₁' with
       | top => bot
       | bot => top
       | _ => t
  | and t₁ t₂ =>
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       match t₁', t₂' with
       | top, top => top
       | bot, _ => bot
       | _, bot => bot
       | _, _ => t
  | or t₁ t₂ =>
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       match t₁', t₂' with
       | bot, bot => bot
       | top, _ => top
       | _, top => top
       | _, _ => t
  | implies t₁ t₂ =>
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       match t₁', t₂' with
       | bot, _ => top
       | top, bot => bot
       | top, top => top
       | _, _ => t
  | xor t₁ t₂ =>
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       match t₁', t₂' with
       | bot, top => top
       | top, bot => top
       | top, top => bot
       | bot, bot => bot
       | _, _ => t
  | eq t₁ t₂ => 
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       match t₁', t₂' with
       | bot, top => bot
       | top, bot => bot
       | top, top => top
       | bot, bot => top
       | _, _ => t
  | bIte c t₁ t₂ =>
    do let c' ← termEval c
       match c' with
       | top => termEval t₁
       | bot => termEval t₂
       | _ => t
  | _ => t

#check termEval (mkAnd top bot)

#eval termEval (mkAnd top bot)

end term

end proof
