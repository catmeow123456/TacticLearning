import TacticLearning.Display.Basic
import TacticLearning.Continuous.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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
  fun_prop

set_option trace.aesop.debug true in
example : Continuous (fun x : ℝ => x * x) := by
  aesop (rule_sets := [Continuous])

example (f₁ f₂: Y → Y) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
  (f₃: X → Y) (f₄: Y → X) (h₃ : Continuous f₃) (h₄ : Continuous f₄) :
    Continuous (
      (f₁ + (f₂ * (f₂ ∘ f₁) + f₂) * f₁ + id) ∘ (f₃ ∘ f₄ ∘ f₃)
    ) := by
  continuous

#find Continuous (?_a * ?_b)

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_mul' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Mul Y] [ContinuousMul Y] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
  Continuous (f * g) := by
  continuous

#find Continuous (?_a * ?_b)

example (f₁ f₂: Y → Y) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
  (f₃: X → Y) (f₄: Y → X) (h₃ : Continuous f₃) (h₄ : Continuous f₄) :
    Continuous (
      (f₁ + (f₂ * (f₂ ∘ f₁) + f₂) * f₁ + id) ∘ (f₃ ∘ f₄ ∘ f₃)
    ) := by
  fun_prop


example (f₁ f₂: ℝ → ℝ) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
  (f₃: ℝ → ℝ) (f₄: ℝ → ℝ) (h₃ : Continuous f₃) (h₄ : Continuous f₄) :
    Continuous (
      (f₁ + (f₂ * (f₂ ∘ f₁) + f₂) * f₁ + id) ∘ ((Real.sin ∘ f₃) ∘ f₄ ∘ f₃)
    ) := by
  fun_prop

set_option trace.Meta.Tactic.fun_prop true
example : Continuous (Real.sin * Real.cos) := by
  fun_prop

set_option trace.Meta.Tactic.fun_prop true
example : Continuous (Real.sin ∘ Real.cos) := by
  fun_prop

example : Continuous (Real.sin ∘ Real.cos) := by
  continuous <;> continuity

example : Continuous (Real.sin ∘ Real.cos) := by
  fun_prop

example : Real.sin ∘ Real.cos = (λ x => Real.sin (Real.cos x)) := rfl
