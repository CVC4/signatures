import Lean.Elab.Frontend
import Cdclt.Euf

open Lean

open IO

section
open Lean.Elab

-- Create environment from file
def environmentFromFile (fname:String) (moduleName:String) (opts : Options := {})
  : IO (MessageLog × Environment) := do
  let input ← IO.FS.readFile fname
  let inputCtx := Parser.mkInputContext input fname
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx
  let env := env.setMainModule moduleName
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages opts)
  pure (s.commandState.messages, s.commandState.env)

end

def main (args : List String) : IO Unit :=
  match args with
  | [fname] => do
    Lean.initSearchPath (some "/home/hbarbosa/.elan/toolchains/leanprover-lean4-nightly-2021-04-27/lib/lean")
    let (msgs, env) ← environmentFromFile fname "Test"
    if (← msgs.hasErrors) then
      IO.println s!"Errors loading {fname}..."
      for msg in msgs.toList do
        IO.print s!"  {← msg.toString (includeEndPos := Lean.Elab.getPrintMessageEndPos {})}"
    else
      IO.println "Successfully checked"
  | _ => IO.println "no file given"
