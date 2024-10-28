import Lean
import TacticLearning.Display.Showdecl
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
open Lean Meta Elab Tactic


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

#check Expr.eq? -- Expr → Option (Expr × Expr × Expr)
#check Expr.app2? -- Expr → Name → Option (Expr × Expr)

#expr[Type]
#eval ppExpr (Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero)))

#expr[∀ {α : Type} [_h:LE α], ∀ {a b: α}, LE.le a b]
#eval ppExpr (Lean.Expr.forallE `α (Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))) (Lean.Expr.forallE `_h (Lean.Expr.app (Lean.Expr.const `LE [Lean.Level.zero]) (Lean.Expr.bvar 0)) (Lean.Expr.forallE `a (Lean.Expr.bvar 1) (Lean.Expr.forallE `b (Lean.Expr.bvar 2) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.bvar 3)) (Lean.Expr.bvar 2)) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 0)) (Lean.BinderInfo.implicit)) (Lean.BinderInfo.implicit)) (Lean.BinderInfo.instImplicit)) (Lean.BinderInfo.implicit))

def matchLe (e: Expr) :
    MetaM <| Option (Expr × Expr × Expr) := do
  let type := Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))
  let m1 ← mkFreshExprMVar type -- Type
  let m2 ← mkFreshExprMVar (Lean.Expr.app (Lean.Expr.const `LE [Lean.Level.zero]) m1) -- inst
  let le := (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) m1) m2)
  let a ← mkFreshExprMVar m1
  let b ← mkFreshExprMVar m1
  let ineq := Lean.Expr.app (Lean.Expr.app le a) b
  if ← isDefEq ineq e then
    return some (a, b, m2)
  else
    return none

def matchLt (e: Expr) :
    MetaM <| Option (Expr × Expr × Expr) := do
  let type := Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))
  let m1 ← mkFreshExprMVar type -- Type
  let m2 ← mkFreshExprMVar (Lean.Expr.app (Lean.Expr.const `LT [Lean.Level.zero]) m1) -- inst
  let lt := (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) m1) m2)
  let a ← mkFreshExprMVar m1
  let b ← mkFreshExprMVar m1
  let ineq := Lean.Expr.app (Lean.Expr.app lt a) b
  if ← isDefEq ineq e then
    return some (a, b, m2)
  else
    return none

elab "match_le_or_lt" : tactic => withMainContext do
  let goal ← getMainTarget
  match ← matchLe goal with
  | some (a, b, inst) =>
    logInfo m!"Matched inequality (a ≤ b); a = {a}, b = {b}, inst = {inst}"
  | none =>
    match ← matchLt goal with
    | some (a, b, inst) =>
      logInfo m!"Matched inequality (a < b); a = {a}, b = {b}, inst = {inst}"
    | none => logWarning m!"Main target not of the correct form"

elab "match_le_or_lt_hyp" t:term : tactic =>
  withMainContext do
  let h ← elabTerm t none
  let hType ← inferType h
  match ← matchLe hType with
  | some (a, b, inst) =>
    logInfo m!"Matched inequality (a ≤ b); a = {a}, b = {b}, inst = {inst}"
  | none =>
    match ← matchLt hType with
    | some (a, b, inst) =>
      logInfo m!"Matched inequality (a < b); a = {a}, b = {b}, inst = {inst}"
    | none => logWarning m!"Main target not of the correct form"

set_option linter.unusedTactic false in
example (x y: Nat)(h : 2+1 < 12) : 1+2 > 2 := by
  match_le_or_lt
  match_le_or_lt_hyp h
  sorry

#check TacticM

def Lean.MVarId.rewriteLeM (goal: MVarId) (h: Expr) :
    MetaM <| List MVarId :=
  goal.withContext do
  let hType ← inferType h
  let target ← goal.getType
  match ← matchLe hType, ← matchLe target with
  | some (a, b, _), some (c, d, _) =>
    let firstEq ← isDefEq a c
    let secondEq ← isDefEq b d
    if firstEq && secondEq then
      goal.assign h
      return []
    else
    if firstEq then
      -- have `a = c`, so `h` is `c ≤ b` and we need `b ≤ d`
      let newTarget ← mkAppM ``LE.le #[b, d]
      let newGoal ← mkFreshExprMVar newTarget
      let proof ← mkAppM ``LE.le.trans #[h, newGoal]
      goal.assign proof
      return [newGoal.mvarId!]
    else
    if secondEq then
      -- have `b = d`, so `h` is `a ≤ d` and we need `c ≤ a`
      let newTarget ← mkAppM ``LE.le #[c, a]
      let newGoal ← mkFreshExprMVar newTarget
      let proof ← mkAppM ``LE.le.trans #[newGoal, h]
      goal.assign proof
      return [newGoal.mvarId!]
    else
      throwError "Neither ends matched"
  | _, _ =>
    throwError "Did not get inequalities"

elab "rw_le" t:term : tactic => do
  let h ← elabTerm t none
  liftMetaTactic fun goal => goal.rewriteLeM h


example (x y z : Int) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by
  rw_le h₁
  exact h₂

example (x y z : Real) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by
  rw_le h₂
  exact h₁

example {G : Type} [Group G] (x y z : Subgroup G) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by
  rw_le h₁
  exact h₂
