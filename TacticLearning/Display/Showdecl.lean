import Lean

open Lean Meta Elab Tactic


/-!

# Syntax
In Lean, `Syntax` is a datatype that represents the abstract syntax tree of a Lean expression.
One can use ```(abcd | efgh)`` to use the parser `abcd` and get the syntax tree `efgh`.
  for example, ```(term| 1 + 2)`` will be parsed as a simple arithmetic expression.
  for example, ```(tactic| exact rfl)`` will be parsed as a tactic script.
And then, one can use `Term.elabterm` to elaborate the syntax tree into an `Expr`.
The elaborated `Expr` can be further processed by tactics.

# Expr
In Lean, an `Expr` is a datatype that represents fully elaborated expressions,
including terms, types, sorts, and so on.

`FVarId` and `MVarId` are two important components of `Expr`.
In a tactic proof state, there are multiple local declarations (free variables `FvarId`) and
multiple unsolved subgoals (meta variables `MVarId`) in the context. The final goal is to complete
all the subgoals, i.e. to assign a value to each meta variable.

- meta variable   `MVarId`    ? : SomeType
- free variable   `FVarId`    h : SomeType

One can use `mkFVar`/`mkMVar` or `Expr.fvar`/`.mvar` to build an atomic expr from a `FVarId`/`MVarId`.
-/

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

elab "#tactic" "[" t:tactic "]" : command =>
  Command.liftTermElabM do
  logInfo s!"Tactic: {t}:\n{repr t}"

#stx [Nat]
#expr [Nat]
#stx [Nat.succ Nat.zero]
#expr [Nat.succ Nat.zero]
#stx [List.cons Nat.zero List.nil]
#expr [List.cons Nat.zero List.nil]
#check Lean.Expr.const
#tactic [exact (t _ _) t]

#check isDefEq
/--
Return an array of local declarations (`FVarId`)
whose type is definitionally equal to `type`.
-/
def ListLocalDeclWithType (type : Expr) : MetaM (Array FVarId) := do
  let list_change: MetaM $ Array FVarId :=
    (← getLCtx).foldl (init := do pure #[]) fun lst decl =>
      if decl.isImplementationDetail then
        lst
      else do
        let s ← saveState
        if (← isDefEq type decl.type) then
          s.restore
          return (← lst).push decl.fvarId
        else
          lst
  return (← list_change)

elab "elabterm" t:term : tactic => do
  let t ← Term.elabTerm t none
  logInfo m!"Message Data: {t}"; logInfo s!"String Data: {t}"
  pure ()

def FvarIdsToMessageData (fvarIds: Array FVarId) : MetaM MessageData :=
  fvarIds.foldl (init := do pure "")
    fun s fvarId => do
      let fvar: Expr := .fvar fvarId
      let fvartype: Expr := (← inferType fvar)
      pure ((← s) ++ " " ++ m!"{fvar}: {fvartype}\n")

partial def showtypedef : Syntax → TacticM Unit := fun `(term| $t) => do
  let expr ← Term.elabTerm t none
  let result: Array FVarId ← ListLocalDeclWithType expr
  match result with
  | #[] => throwError "No local declaration with type {t}"
  | _ => logInfo (
      m!"Local declarations with type {t}:\n" ++
      (← FvarIdsToMessageData result))

elab "showtype" t:term : tactic => showtypedef t

example (h h2: 1 = 2) (w₁ w₂ : Nat) (hw: w₁ = w₂)
  (h₁ : ∀ i : Nat, i < i + 1) (h₂ : ∀ j₁ j₂ : List Nat, j₁ ++ j₂ = j₂ ++ j₁)
  (h₃ : ∃ x : Nat, x > 0) (h₄ : (i:Type) × (i → i))
    : False := by
  elabterm (1:Nat)
  elabterm (w₁ + w₂)
  elabterm (h₁ w₁)
  elabterm (1 :: [2])
  showtype (1 = _)
  showtype (Nat)
  showtype _ = _
  showtype ∀ _, _
  showtype ∃ _, _
  showtype Σ _, _
  stop {}
