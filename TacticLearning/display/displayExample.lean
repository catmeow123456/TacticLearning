import «TacticLearning».display.showdecl

example (a b c : Prop)
  (h₁: a → b) (h₂: b → c): a → c := by
  showtype Prop
  showtype _ -> _
  sorry

open Lean Meta Elab Tactic
def ListLocalDeclOfEqType? : TermElabM (Array FVarId) := do
  let tsyntax ← `(term| _ = _)
  let t ← Term.elabTerm tsyntax none
  let result ← ListLocalDeclWithType? t
  pure result

elab "showtype_of_eq" : tactic => do
  let fvarids ← ListLocalDeclOfEqType?
  logInfo (← FvarIdsToMessageData fvarids)

example (a b c : Prop)
  (h₁: a = b) (h₂: b → c): a → c := by
  showtype Prop
  showtype _ -> _
  showtype_of_eq
  sorry
