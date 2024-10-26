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

#check TacticM -- ReaderT Context $ StateRefT State TermElabM
#check TermElabM -- ReaderT Context $ StateRefT State MetaM
#check MetaM -- ReaderT Context $ StateRefT State CoreM
#check CoreM -- ReaderT Context $ StateRefT State (EIO Exception)

#check isDefEq
/-- Return a local declaration whose type is definitionally equal to `type`. -/
def ListLocalDeclWithType? (type : Expr) : MetaM (Array FVarId) := do
  let list_change: MetaM $ Array FVarId :=
    (← getLCtx).foldl (init := do pure #[]) fun lst decl =>
      if decl.isImplementationDetail then
        lst
      else do
        if (← isDefEq type decl.type) then
          return (← lst).push decl.fvarId
        else
          lst
  return (← list_change)

#check TSyntax `Term

elab "elabterm" t:term : tactic => do
  let t ← Term.elabTerm t none
  logInfo m!"Message Data: {t}"; logInfo s!"String Data: {t}"
  pure ()

#check TacticM

elab "showtype" t:term : tactic => do
  let t ← Term.elabTerm t none
  liftMetaTactic fun mvarId => do
    let result ← ListLocalDeclWithType? t
    match result with
    | #[] => throwError "No local declaration with type {t}"
    | _ =>
      let msg: MessageData := ← result.foldl (init := do pure "")
        fun s fvarId => do
          let fvar := mkFVar fvarId
          pure ((← s) ++ " " ++ m!"{fvar}")
      logInfo (m!"Local declarations with type {t}:\n" ++ msg)
      return [mvarId]

example (h h2: 1 = 2) (w₁ w₂ : Nat) : 1 = 2 ∧ 2 = 1:= by
  constructor
  elabterm (1:Nat)
  elabterm (w₁)
  elabterm (h)
  showtype (1 = 2)
  showtype (Nat)
  · sorry
  sorry

#check OfNat.ofNat
