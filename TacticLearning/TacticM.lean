import Lean

open Lean Meta Elab Tactic

#check getMainTarget -- TacticM Expr
#check getMainGoal -- TacticM MVarId
#check getGoals -- TacticM (List MVarId)
#check setGoals -- List MVarId → TacticM Unit

elab "evil" : tactic => do
  setGoals []

-- example : 0 = 1 := by
--   evil

elab "todo" s:str : tactic => do
  logInfo m!"Message: {s}"
  let target ← getMainTarget
  let sorryExpr ←
    mkAppM ``sorryAx #[target, mkConst ``false]
  closeMainGoal `todo sorryExpr

example : 3 ≤ 15 ∧ 4 ≤ 5:= by
  constructor
  · todo "TODO: 3 <= 15"
  todo "TODO: 4 <= 5"
