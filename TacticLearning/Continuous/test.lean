import TacticLearning.Continuous.Basic
import Mathlib.Topology.Instances.Real
import TacticLearning.Display.Basic

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Add Y] [ContinuousAdd Y]

example (f₁ f₂ : X → Y) (h₁ : Continuous f₁) (h₂ : Continuous f₂):
    Continuous (f₁ + f₂) := by
  showtype (Continuous (_ : X → Y))
  apply Continuous.add
  exact h₁
  exact h₂

example : (fun x : ℝ => x * x) = (fun x : ℝ => x) * (fun x : ℝ => x) := rfl

example : Continuous (fun x : ℝ => x * x) := by
  apply Continuous.mul
  exact continuous_id
  exact continuous_id

#expr [Nat.zero + Nat.zero]
