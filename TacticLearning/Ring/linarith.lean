import Lean
import TacticLearning.Linarith.Basic

example (a b : Nat): a + (b + a) <= a * 2 + b + 1 := by
  linarith

example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith (config := { oracle := .simplexAlgorithmDense })
    only [h1, h2, h3]
