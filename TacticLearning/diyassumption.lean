import Lean
import Mathlib

open Lean Meta Elab Tactic

def throwErr {α: Type} (tacticName : Name) (mvarId : MVarId)
    (msg? : Option MessageData := none) : MetaM α :=
  match msg? with
  | none => throwError "tactic '{tacticName}' failed\n{mvarId}"
  | some msg => throwError "tactic '{tacticName}' failed, {msg}\n{mvarId}"

def Lean.MVarId.assumptCore (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    mvarId.checkNotAssigned `assumption
    match (← findLocalDeclWithType? (← mvarId.getType)) with
    | none => return false
    | some fvarId => mvarId.assign (mkFVar fvarId); return true

def Lean.MVarId.assumpt (mvarId : MVarId) : MetaM Unit :=
  unless (← mvarId.assumptCore) do
    throwErr `assumption mvarId

elab "diyAssumption" : tactic => do
  liftMetaTactic fun mvarId => do mvarId.assumpt; pure []

theorem test (h : 1 ≤ 2) : 1 ≤ 2 := by
  exact h
  -- diyAssumption

def foo (n : Nat) : Nat := by
  diyAssumption

def test2 (h : Nat -> Nat): Nat -> Nat := by
  diyAssumption

elab "myExact" t:term : tactic => withMainContext do
  closeMainGoalUsing `myExact (checkUnassigned := false) fun type => do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let r ← elabTermEnsuringType t type
  logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
  return r

example (h : 1 = 42) : 1 = 42 := by exact h

syntax (name := myExact_syn) "myExact_syn " term : tactic

elab_rules : tactic | `(tactic| myExact_syn $stx:term) => focus <| withMainContext do
  closeMainGoalUsing `myExact_syn (checkUnassigned := false) fun type => do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let r ← elabTermEnsuringType stx type
    logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
    return r

example (h : 1 = 42) : 1 = 42 := by myExact_syn h

open Polynomial

example : (1 + X + X ^ 2: ℤ[X]).degree = 2 := by compute_degree!
