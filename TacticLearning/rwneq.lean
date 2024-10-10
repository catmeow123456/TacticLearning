import Lean
import Mathlib.Data.Real.Basic
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

/-
inductive Lean.Expr : Type
number of parameters: 0
constructors:
Lean.Expr.bvar : Nat → Expr
Lean.Expr.fvar : FVarId → Expr
Lean.Expr.mvar : MVarId → Expr
Lean.Expr.sort : Level → Expr
Lean.Expr.const : Name → List Level → Expr
Lean.Expr.app : Expr → Expr → Expr
Lean.Expr.lam : Name → Expr → Expr → BinderInfo → Expr
Lean.Expr.forallE : Name → Expr → Expr → BinderInfo → Expr
Lean.Expr.letE : Name → Expr → Expr → Expr → Bool → Expr
Lean.Expr.lit : Literal → Expr
Lean.Expr.mdata : MData → Expr → Expr
Lean.Expr.proj : Name → Nat → Expr → Expr
-/
#print Expr

/-
inductive Lean.Syntax : Type
number of parameters: 0
constructors:
Lean.Syntax.missing : Syntax
Lean.Syntax.node : SourceInfo → SyntaxNodeKind → Array Syntax → Syntax
Lean.Syntax.atom : SourceInfo → String → Syntax
Lean.Syntax.ident : SourceInfo → Substring → Name → List Syntax.Preresolved → Syntax
-/
#print Syntax
#stx [1 + 2]
#expr [fun n : Nat => n]




/-!
## Rewriting with Inequalities: `rw_le`

We now give a more substantial example. This can be done with just macros, but we will use metaprogramming to illustrate the principles.

The tactic `rw_le h` works if the goal is of the form `a ≤ b` and `h` is a proof of `c ≤ d`, with `a`, `b`, `c` and `d` all natural numbers. If `a = c` or `b = d` or both, then it rewrites the goal.

Our first step is to recognize when an expression (for example the goal) is of the correct form.
-/
#check Expr.eq? -- Expr → Option (Expr × Expr × Expr)
#check Expr.app2? -- Expr → Name → Option (Expr × Expr)

def matchLe (e: Expr) :
    MetaM <| Option (Expr × Expr) := do
  let real := mkConst ``Real
  let a ← mkFreshExprMVar real
  let b ← mkFreshExprMVar real
  let ineq ← mkAppM `LE.le #[a, b]
  logInfo m!"Trying to match {ineq} with {e}"
  if ← isDefEq ineq e then
    return some (a, b)
  else
    return none

elab "match_le" : tactic => withMainContext do
  match ← matchLe (← getMainTarget) with
  | some (a, b) =>
    logInfo m!"Matched inequality; a = {a}, b = {b}"
  | none =>
    logWarning m!"Main target not of the correct form"

elab "match_le_hyp" t:term : tactic =>
  withMainContext do
  let h ← elabTerm t none
  match ← matchLe (← inferType h) with
  | some (a, b) =>
    logInfo m!"Matched inequality; a = {a}, b = {b}"
  | none =>
    logWarning m!"Main target not of the correct form"

example (x y: Real)(h : x ≤ y) : x > y := by
  match_le
  match_le_hyp h
  sorry

elab "rw_le" t:term : tactic =>
  withMainContext do
    let h ← elabTerm t none
    let hType ← inferType h
    let target ← getMainTarget
    match ← matchLe hType, ← matchLe target with
    | some (a, b), some (c, d) =>
      let firstEq ← isDefEq a c
      let secondEq ← isDefEq b d
      if firstEq && secondEq then
        closeMainGoal `rw_le h
      else
      if firstEq then
        -- have `a = c`, so `h` is `c ≤ b` and we need `b ≤ d`
        let newTarget ← mkAppM ``Nat.le #[b, d]
        let newGoal ← mkFreshExprMVar newTarget
        let proof ← mkAppM ``Nat.le_trans #[h, newGoal]
        let goal ← getMainGoal
        goal.assign proof
        replaceMainGoal [newGoal.mvarId!]
      else
      if secondEq then
        -- have `b = d`, so `h` is `a ≤ d` and we need `c ≤ a`
        let newTarget ← mkAppM ``Nat.le #[c, a]
        let newGoal ← mkFreshExprMVar newTarget
        let proof ← mkAppM ``Nat.le_trans #[newGoal, h]
        let goal ← getMainGoal
        goal.assign proof
        replaceMainGoal [newGoal.mvarId!]
      else
        throwError "Neither ends matched"
    | _, _ =>
      throwError "Did not get inequalities"


example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  by
    rw_le h₁
    exact h₂

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  by
    rw_le h₂
    exact h₁


example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ y :=
  by
    rw_le h₁



/-
⊢ (MVarId → MetaM (List MVarId)) → TacticM Unit
-/
#check liftMetaTactic

/-
⊢ MVarId →
  Expr →
    optParam ApplyConfig
        { newGoals := ApplyNewGoals.nonDependentFirst, synthAssignedInstances := true, allowSynthFailures := false,
          approx := true } →
      MetaM (List MVarId)
-/
#check MVarId.apply

def Lean.MVarId.rewriteLeM (goal: MVarId) (h: Expr) :
    MetaM <| List MVarId :=
    goal.withContext do
      let hType ← inferType h
      let target ← goal.getType
      match ← matchLe hType, ← matchLe target with
      | some (a, b), some (c, d) =>
        let firstEq ← isDefEq a c
        let secondEq ← isDefEq b d
        if firstEq && secondEq then
          goal.assign h
          return []
        else
        if firstEq then
          -- have `a = c`, so `h` is `c ≤ b` and we need `b ≤ d`
          let newTarget ← mkAppM ``Nat.le #[b, d]
          let newGoal ← mkFreshExprMVar newTarget
          let proof ← mkAppM ``Nat.le_trans #[h, newGoal]
          goal.assign proof
          return [newGoal.mvarId!]
        else
        if secondEq then
          -- have `b = d`, so `h` is `a ≤ d` and we need `c ≤ a`
          let newTarget ← mkAppM ``Nat.le #[c, a]
          let newGoal ← mkFreshExprMVar newTarget
          let proof ← mkAppM ``Nat.le_trans #[newGoal, h]
          goal.assign proof
          return [newGoal.mvarId!]
        else
          throwError "Neither ends matched"
      | _, _ =>
        throwError "Did not get inequalities"


elab "rw_leq" t:term : tactic => do
  let h ← elabTerm t none
  liftMetaTactic fun goal => goal.rewriteLeM h


example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  by
    rw_leq h₁
    exact h₂

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  by
    rw_leq h₂
    exact h₁


example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ y :=
  by
    rw_leq h₁
