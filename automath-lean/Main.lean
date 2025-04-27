import Automath

structure State where

abbrev M := StateT State IO

def processItem : Item → M Unit
  | .comment => pure ()
  | .openSection _ => pure () -- TODO
  | .reopenSection _ => pure () -- TODO
  | .closeSection _ => pure () -- TODO
  | .setContext _ => pure () -- TODO
  | .parameter _ _ => pure () -- TODO
  | .axiom_ _ _ => pure () -- TODO
  | .def_ _ _ _ => pure () -- TODO

def main : IO Unit := do
  let grundlagen ← IO.FS.readFile "../aut-4.2/grundlagen.aut"
  let items ← match items.run grundlagen with
    | .ok e => pure e
    | .error e => throw (.userError e)
  let (_, _s) ← StateT.run (s := {}) do
    for it in items do processItem it
