import Lean
import Mathlib
import Lean.Elab.Tactic.Location

open Lean Meta Elab Tactic


/-!

# diyassumption

在这个文件中，我们定义了一个 tactic `diyAssumption`，
它检查 LocalContext 中是否有一个类型与当前待赋值目标的类型相同的 LocalDecl，
如果有，则将这个 LocalDecl 的 fvarid 赋值给当前目标。

# myExact

In this file we also declear in two formats a tactic called `myExact` realising `exact` functions. Some part of the `exact` code are still to be understood, but simple cases work anyway.

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

/--
  将 diyAssumption 解释为一个 tactic，它调用 assumpt
-/
elab "diyAssumption" : tactic => do
  liftMetaTactic fun mvarId => do mvarId.assumpt; pure []

theorem test (h : 1 ≤ 2) : 1 ≤ 2 := by
  -- exact h
  diyAssumption

def foo (n : Nat) : Nat := by
  diyAssumption

def test2 (h : Nat -> Nat): Nat -> Nat := by
  diyAssumption

elab "myExact" t:term : tactic => withMainContext do
  closeMainGoalUsing `myExact fun type => do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let r ← elabTermEnsuringType t type
  logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
  return r

example (h : 1 = 42) : 1 = 42 := by myExact h

/-- Syntax - elab_rules method for making a tactic. Studied from `compute_degree`, and we can add an optional `!` to it. -/

syntax (name := myExact_syn) "myExact_syn " term : tactic

elab_rules : tactic | `(tactic| myExact_syn $stx:term) => focus <| withMainContext do
  closeMainGoalUsing `myExact_syn fun type => do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let r ← elabTermEnsuringType stx type
    logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
    return r

-- Simple examples to show that the tactic works.

example (h : 1 = 42) : 1 = 42 := by myExact_syn h

example (h : 1 = 42) : 42 = 1 := by myExact_syn h.symm

example (a b c : ℝ) (h₁ : a < b) (h₂ : b < c) : a < c := by myExact_syn gt_trans h₂ h₁

-- Sorry

example (h : 1 = 42) : 1 = 42 := by myExact_syn h

syntax myLocationWildcard := " *"

syntax myLocationHyp := (ppSpace colGt term:max)+ patternIgnore(ppSpace (atomic("|" noWs "-") <|> "⊢"))?

syntax myLocation := withPosition(" at" (myLocationWildcard <|> myLocationHyp))

syntax (name := mySymm) "mySymm" (myLocation)? : tactic

def myWithLocation (loc : Location) (atLocal : FVarId → TacticM Unit) (atTarget : TacticM Unit) (failed : MVarId → TacticM Unit) : TacticM Unit := do
  match loc with
  | Location.targets hyps type =>
    logInfo m!"!!!!! Location.targets {hyps} {type}"
    hyps.forM fun hyp => withMainContext do
      let fvarId ← getFVarId hyp
      atLocal fvarId
    if type then
      withMainContext atTarget
  | Location.wildcard =>
    logInfo m!"!!!!! Location.wildcard}"
    let worked ← tryTactic <| withMainContext <| atTarget
    let g ← try getMainGoal catch _ => return () -- atTarget closed the goal
    g.withContext do
      let mut worked := worked
      -- We must traverse backwards because the given `atLocal` may use the revert/intro idiom
      for fvarId in (← getLCtx).getFVarIds.reverse do
        if (← fvarId.getDecl).isImplementationDetail then
          continue
        worked := worked || (← tryTactic <| withMainContext <| atLocal fvarId)
      unless worked do
        failed (← getMainGoal)

elab_rules : tactic | `(tactic| mySymm $(loc?)?) => do
  let atHyp h := liftMetaTactic1 fun g => g.applySymmAt h
    let atTarget := liftMetaTactic1 fun g => g.applySymm
    let loc := match loc? with
      | none => Location.targets #[] true
      | some loc => expandLocation loc
    myWithLocation loc atHyp atTarget fun _ => throwError "symm made no progress"

example (h : 1 = 56) (h_symm : 1 = 42) (p : 1 = 41): 1 = 42 := by
  -- mySymm at h_symm p ⊢
  try symm_saturate
  sorry

@[builtin_tactic Lean.Parser.Tactic.symm]
def evalSymm : Tactic := fun stx =>
  match stx with
  | `(tactic| symm $(loc?)?) => do
    let atHyp h := liftMetaTactic1 fun g => g.applySymmAt h
    let atTarget := liftMetaTactic1 fun g => g.applySymm
    let loc := if let some loc := loc? then expandLocation loc else Location.targets #[] true
    withLocation loc atHyp atTarget fun _ => throwError "symm made no progress"
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.symmSaturate]
def evalSymmSaturate : Tactic := fun stx =>
  match stx with
  | `(tactic| symm_saturate) => do
    liftMetaTactic1 fun g => g.symmSaturate
  | _ => throwUnsupportedSyntax

def mySymmSaturate (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g' := g
  let hyps ← getLocalHyps
  let types ← hyps.mapM inferType
  for h in hyps do try
    let symm ← h.applySymm
    let symmType ← inferType symm
    if ¬ (← types.anyM (isDefEq symmType)) then
      (_, g') ← g'.note ((← h.fvarId!.getUserName).appendAfter "_symm") symm
  catch _ => g' ← pure g'
  return g'

elab "myExactSymm" t:term : tactic => withMainContext do
  do try
    closeMainGoalUsing `myExact fun type => do
      let mvarCounterSaved := (← getMCtx).mvarCounter
      let r ← elabTermEnsuringType t type
      logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
      return r
  catch _ => try
    liftMetaTactic1 fun g => g.applySymm
    closeMainGoalUsing `myExact fun type => do
      let mvarCounterSaved := (← getMCtx).mvarCounter
      let r ← elabTermEnsuringType t type
      logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
      return r
  catch _ =>
    logInfo "myExactSymm failed"

example (h : 42 = 1) : 1 = 42 := by
  myExactSymm h

#check Expr.const `Nat

elab "myAssumption" : tactic => withMainContext do
  try
    evalTactic (← `(tactic|diyAssumption))
  catch _ => try
    liftMetaTactic1 fun g => g.applySymm
    evalTactic (← `(tactic|diyAssumption))
  catch _ => throwError "myAssumption failed"

example (h₂ : 9 = 8) (h₁ : 1 = 42): 42 = 1 ∧ 1 = 42 := by
  constructor
  · myAssumption
  myAssumption

example (g : 8 = 9) (h : ∀ i:Nat, i = 1) : 1 = 42 := by
  let w : 1 = 42 := sorry
  myExactSymm g
  -- myExactSymm w
  myExactSymm (h _)

open Polynomial

example : (1 + X : ℤ[X]).degree = 1 := by compute_degree!
