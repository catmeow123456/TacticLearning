import Lean.Elab.Tactic.Location
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import TacticLearning.Display.Basic

open Lean Meta Elab Tactic
open Polynomial

#check Polynomial
#expr[Polynomial _]
#expr[Polynomial ℤ]
#expr[Semiring ℤ]
#expr[X.coeff Nat.zero = Nat.zero]
#check ℤ

elab "coeff_zero" t:term : tactic => do
  let type := Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))
  let m1 ← mkFreshExprMVar type
  let m2 ← mkFreshExprMVar (.app (.const `Semiring [Lean.Level.zero]) m1 : Expr)
  let expr : Expr := .app (.app (.const `Polynomial [Lean.Level.zero]) m1) m2
  let e ← elabTermEnsuringType t expr
  logInfo m!"information: {t} -> {e} : {← inferType e}"
  let goal : Expr ← elabTerm (← `(term | ($t).coeff 0 = _)) none
  let unsolved_goal ← mkFreshExprMVar goal
  liftMetaTactic1 fun g => do
    let (_, g) ← g.note `hhh unsolved_goal
    pure g
  let mvarId := unsolved_goal.mvarId!
  let goals ← getGoals
  replaceMainGoal (mvarId :: goals)
  (← getMainGoal).withContext do
    evalTactic (← `(tactic|try simp;try rfl))

example (p: Polynomial ℤ) (h : p = 1+1+1 + X): p.coeff 0 = 3 := by
  coeff_zero (1+1+1 + X : ℤ[X])
  rwa [h]
