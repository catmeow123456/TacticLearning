import Lean
import Mathlib

open Lean Meta Elab Tactic


/-
throwErr 扔出报错信息，包括 tactic 名称，元变量 id，以及可选的报错信息
-/
def throwErr {α: Type} (tacticName : Name) (mvarId : MVarId)
    (msg? : Option MessageData := none) : MetaM α :=
  match msg? with
  | none => throwError "tactic '{tacticName}' failed\n{mvarId}"
  | some msg => throwError "tactic '{tacticName}' failed, {msg}\n{mvarId}"

/-
assumptCore 用于检查在 LocalContext 中是否有一个类型与当前 MVar 的类型相同的 LocalDecl，
-/
def Lean.MVarId.assumptCore (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    mvarId.checkNotAssigned `assumption
    match (← findLocalDeclWithType? (← mvarId.getType)) with
    | none => return false
    | some fvarId => mvarId.assign (mkFVar fvarId); return true

/-
assumpt 包装了 assumptCore，如果 assumptCore 返回 false，则抛出一个错误
-/
def Lean.MVarId.assumpt (mvarId : MVarId) : MetaM Unit :=
  unless (← mvarId.assumptCore) do
    throwErr `assumption mvarId

/-
将 diyAssumption 解释为一个 tactic，它调用 assumpt
-/
elab "diyAssumption" : tactic => do
  liftMetaTactic fun mvarId => do mvarId.assumpt; pure []

theorem test (h : 1 ≤ 2) : 1 ≤ 2 := by
  diyAssumption

def foo (n : Nat) : Nat := by
  diyAssumption

def test2 (h : Nat -> Nat): Nat -> Nat := by
  diyAssumption
