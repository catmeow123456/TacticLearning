import Lean
import TacticLearning.Linarith.Basic

example (a b : Nat): a + (b + a) <= a * 2 + b + 1 := by
  linarith
