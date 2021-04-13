import Cdclt.Term

open proof
open proof.sort proof.Term

namespace proof

namespace term

partial def termEval (ot : Option Term) : Option Term :=
  ot >>= λ t =>
  match t with
  | top => top
  | bot => bot
  | Term.not t₁ =>
    do let t₁' ← termEval t₁
       match t₁' with
       | top => bot
       | bot => top
       | _ => t
  | Term.and t₁ t₂ =>
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       match t₁', t₂' with
       | top, top => top
       | bot, _ => bot
       | _, bot => bot
       | _, _ => t
  | Term.or t₁ t₂ =>
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       match t₁', t₂' with
       | bot, bot => bot
       | top, _ => top
       | _, top => top
       | _, _ => t
  | Term.implies t₁ t₂ =>
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       match t₁', t₂' with
       | bot, _ => top
       | top, bot => bot
       | top, top => top
       | _, _ => t
  | Term.xor t₁ t₂ =>
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       match t₁', t₂' with
       | bot, top => top
       | top, bot => top
       | top, top => bot
       | bot, bot => bot
       | _, _ => t
  | Term.eq t₁ t₂ => 
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       match t₁', t₂' with
       | bot, top => bot
       | top, bot => bot
       | top, top => top
       | bot, bot => top
       | _, _ => t
  | Term.bIte c t₁ t₂ =>
    do let c' ← termEval c
       match c' with
       | top => termEval t₁
       | bot => termEval t₂
       | _ => t
  | Term.app t₁ t₂ =>
    do let t₁' ← termEval t₁
       let t₂' ← termEval t₂
       (app t₁' t₂')
  | _ => t

#check termEval (mkAnd top bot)
#eval termEval (mkAnd top bot)
end term

end proof