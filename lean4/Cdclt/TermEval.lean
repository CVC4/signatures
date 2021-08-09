import Cdclt.Term

open proof
open proof.sort proof.term

namespace proof

namespace term


partial def termEval (t : term) : term :=
  match t with
  | top => top
  | bot => bot
  | term.not t₁ =>
    let t₁' := termEval t₁
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
    let t₁' := termEval t₁
    let t₂' := termEval t₂
    match t₁', t₂' with
    | bot, top => top
    | top, bot => top
    | top, top => bot
    | bot, bot => bot
    | _, _ => t
  | eq t₁ t₂ =>
    do let t₁' := termEval t₁
       let t₂' := termEval t₂
       match t₁', t₂' with
       | bot, top => bot
       | top, bot => bot
       | top, top => top
       | bot, bot => top
       | _, _ => t
  | bIte c t₁ t₂ =>
    let c' := termEval c
    match c' with
    | top => termEval t₁
    | bot => termEval t₂
    | _ => t
  | fIte c t₁ t₂ =>
    let c' := termEval c
    match c' with
    | top => termEval t₁
    | bot => termEval t₂
    | _ => t
  | bitOf b'' i'' =>
    let b' := termEval b''
    let i' := termEval i''
    match b', i' with
    | val (value.bitvec b) (bv n), val (value.integer i) _ =>
      match (List.get? (Int.toNat (n - i - 1)) b) with
        | some bit => if bit then top else bot
        | none => term.undef
    | _, _ => t
  | gt (mkValInt i₁) (mkValInt i₂) => if i₁ > i₂ then term.top else term.bot
  | gte (mkValInt i₁) (mkValInt i₂) => if i₁ >= i₂ then term.top else term.bot
  | lt (mkValInt i₁) (mkValInt i₂) => if i₁ < i₂ then term.top else term.bot
  | lte (mkValInt i₁) (mkValInt i₂) => if i₁ <= i₂ then term.top else term.bot
  | app t₁ t₂ =>
    let t₁' := termEval t₁
    let t₂' := termEval t₂
    (app t₁' t₂')
  | _ => t

#check termEval (and top bot)
#eval termEval (and top bot)
end term

end proof
