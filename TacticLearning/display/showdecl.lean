import Lean

open Lean Meta Elab Tactic

elab "#stx" "[" t:term "]" : command => do
  logInfo m!"Syntax: {t};\n{repr t}"

elab "#expr" "[" t:term "]" : command =>
  Command.liftTermElabM do
  let t ← Term.elabTerm t none
  let t ← instantiateMVars t
  logInfo m!"Expression: {t}:\n{repr t}"
  let t ← reduce t
  let t ← instantiateMVars t
  logInfo m!"Reduced: {t}:\n{repr t}"

#expr[Nat]
#check Lean.Expr.const

/-- Return a local declaration whose type is definitionally equal to `type`. -/
def findLocalDeclWithType? (type : Expr) : MetaM (Option FVarId) := do
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else if (← isDefEq type localDecl.type) then
      return some localDecl.fvarId
    else
      return none

#check TSyntax `Term

elab "elabterm" t:term : tactic => do
  let t ← Term.elabTerm t none
  logInfo m!"Message Data: {t}"; logInfo s!"String Data: {t}"
  pure ()

example (h : 1 = 2) (w : Nat) : 1 = 2 := by
  elabterm (1:Nat)
  elabterm (w)
  elabterm (h)

  sorry

#check OfNat.ofNat
