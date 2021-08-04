import Lean.Elab.Command

open Lean Lean.Elab Lean.Elab.Command

syntax (name := print_prefix) "#print prefix" ident : command

deriving instance Inhabited for ConstantInfo -- required for Array.qsort

-- @[commandElab print_prefix] def elabPrintPrefix : CommandElab
--   | `(#print prefix%$tk $i) => do
--     let env ← getEnv
--     let matches := env.constants.fold (fun xs name val =>
--       if i.getId.isPrefixOf name then xs.push (name, val) else xs) #[]
--     let matches := matches.qsort (fun p q => p.1.lt q.1)
--     for (name, val) in matches do
--       logInfoAt tk m!"{name} : {val.type}"
--   | _ => throwUnsupportedSyntax
open List
