import TacticLearning.Continuous.Basic
import Mathlib.Topology.Instances.Real
import TacticLearning.Display.Basic

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [Add Y] [ContinuousAdd Y]
variable [Mul Y] [ContinuousMul Y]

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

example : Continuous (fun x : ℝ => x * x) := by
  continuity

example (f₁ f₂: Y → Y) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
  (f₃: X → Y) (f₄: Y → X) (h₃ : Continuous f₃) (h₄ : Continuous f₄) :
    Continuous (
      (f₁ + (f₂ * (f₂ ∘ f₁) + f₂) * f₁ + id) ∘ (f₃ ∘ f₄ ∘ f₃)
    ) := by
  continuous
