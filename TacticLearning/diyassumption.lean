import Lean
import Mathlib

open Lean Meta Elab Tactic


/-!

# diyassumption

在这个文件中，我们定义了一个 tactic `diyAssumption`，
它检查 LocalContext 中是否有一个类型与当前待赋值目标的类型相同的 LocalDecl，
如果有，则将这个 LocalDecl 的 fvarid 赋值给当前目标。

## 主要定义

* `throwErr` : throwErr 扔出报错信息，包括 tactic 名称，元变量 id，以及可选的报错信息

* `assumptCore` : 用于检查在 LocalContext 中是否有一个类型与当前 MVar 的类型相同的 LocalDecl，

* `assumpt` : 包装了 assumptCore，如果 assumptCore 返回 false，则抛出一个错误

-/

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

/-
将 diyAssumption 解释为一个 tactic，它调用 assumpt
-/
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
