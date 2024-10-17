import Lean
import Mathlib

open Lean Meta Elab Tactic

def throwErr (tacticName : Name) (mvarId : MVarId)
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
  diyAssumption

def foo (n : Nat) : Nat := by
  diyAssumption

def test2 (h : Nat -> Nat): Nat -> Nat := by
  diyAssumption
