import Mathlib.Control.Basic
import Mathlib.Topology.Instances.Real

open Lean Elab Tactic Meta
open Batteries

namespace Continuous


def getLemmaRecommended (e : Expr) : Option (Name × List Expr) :=
  match e.getAppFnArgs with
  | (``Continuous, #[_, _, _, _, f]) =>
    match f.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, f₁, f₂]) =>
      some (``Continuous.add, [f₁, f₂])
    | (``HMul.hMul, #[_, _, _, _, f₁, f₂]) =>
      some (``Continuous.mul, [f₁, f₂])
    | _ => none
  | _ => none


partial def runContinuous (g : MVarId)
    (hyps : List Expr) : MetaM (List MVarId) := do
  -- elaborate the goal
  let goal_expr ← withReducible g.getType'
  -- get the next step
  let nextstep := getLemmaRecommended goal_expr
  -- logInfo m!"goal_expr: {goal_expr}, nextstep: {nextstep}"
  match nextstep with
  | some (lemma_name, args) => do
    -- logInfo m!"applying lemma {lemma_name}"
    let w ← g.apply (← mkConst' lemma_name)
    let alltogether : MetaM (List MVarId) :=
      w.foldl (init := do pure []) fun α β => do
        pure ((← α) ++ (← runContinuous β hyps))
    pure (← alltogether)
  | none => do
    if ← MVarId.assumptionCore g then
      pure []
    else
      pure [g]

syntax (name := continuous) "continuous" linarithArgsRest : tactic

elab_rules : tactic
  | `(tactic| continuous) => do
    let g ← getMainGoal
    setGoals (← runContinuous g [])
    pure ()

end Continuous
