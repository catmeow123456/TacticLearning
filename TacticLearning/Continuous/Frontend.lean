import Mathlib.Control.Basic
import Mathlib.Topology.Instances.Real

open Lean Elab Tactic Meta
open Batteries

namespace Continuous


def getLemmaRecommended (e : Expr) : Option (Name × Array Expr) :=
  match e.getAppFnArgs with
  | (``Continuous, #[f]) =>
    match f.getAppFnArgs with
    | (``HAdd.hAdd, #[f₁, f₂]) =>
      some (``Continuous.add, #[f₁, f₂])
    | (``HMul.hMul, #[f₁, f₂]) =>
      some (``Continuous.mul, #[f₁, f₂])
    | _ => none
  | _ => none


def runContinuous (g : MVarId)
    (hyps : List Expr) : MetaM Unit := do
  sorry

end Continuous
